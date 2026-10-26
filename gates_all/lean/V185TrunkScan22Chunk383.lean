import V185TrunkScan22Chunk382

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3415431 : List Nat := [1, 1, 4, 2, 2, 2, 2, 1, 7]
def baseStart_3415431 : Nat := 118140960795 + 3415431 * 2 ^ 59
def prefixEnd_3415431 : Nat := 4983230072969 + 3 ^ 40 * 3415431 * 2
def baseEnd_3415431 : Nat := 389723943392518187601161

theorem tailTrace_3415431 : CollatzResearch.WordTrace tailWord_3415431 prefixEnd_3415431 389723943392518187601161 := by
  unfold tailWord_3415431
  simp only [CollatzResearch.WordTrace]
  refine ⟨124571002489484271020294147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83047334992989514013529431 124571002489484271020294147)
  ·
    refine ⟨186856503734226406530441221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124571002489484271020294147 186856503734226406530441221)
    ·
      refine ⟨35035594450167451224457729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 186856503734226406530441221 35035594450167451224457729)
      ·
        refine ⟨26276695837625588418343297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35035594450167451224457729 26276695837625588418343297)
        ·
          refine ⟨19707521878219191313757473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26276695837625588418343297 19707521878219191313757473)
          ·
            refine ⟨14780641408664393485318105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19707521878219191313757473 14780641408664393485318105)
            ·
              refine ⟨11085481056498295113988579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14780641408664393485318105 11085481056498295113988579)
              ·
                refine ⟨16628221584747442670982869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11085481056498295113988579 16628221584747442670982869)
                ·
                  refine ⟨389723943392518187601161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16628221584747442670982869 389723943392518187601161)
                  ·
                    rfl

theorem cell22_3415431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 7].length) (baseStart_3415431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3415431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3415431 prefixEnd_3415431 := by exact prefixLift 3415431
  have htrace : WordTrace (prefixWord ++ tailWord_3415431) baseStart_3415431 baseEnd_3415431 := by
    simpa [prefixWord, tailWord_3415431, baseEnd_3415431] using wordTrace_append hprefix tailTrace_3415431
  have hstable : (prefixWord ++ tailWord_3415431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415431).length < 2 ^ (prefixWord ++ tailWord_3415431).sum := by decide
  have hdescent : baseEnd_3415431 < baseStart_3415431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415510 : List Nat := [5, 2, 1, 1, 1, 3, 1, 2, 6]
def baseStart_3415510 : Nat := 118140960795 + 3415510 * 2 ^ 59
def prefixEnd_3415510 : Nat := 4983230072969 + 3 ^ 40 * 3415510 * 2
def baseEnd_3415510 : Nat := 389732957830674896692747

theorem tailTrace_3415510 : CollatzResearch.WordTrace tailWord_3415510 prefixEnd_3415510 389732957830674896692747 := by
  unfold tailWord_3415510
  simp only [CollatzResearch.WordTrace]
  refine ⟨7785867741012379219526249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83049255904132045008279989 7785867741012379219526249)
  ·
    refine ⟨5839400805759284414644687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7785867741012379219526249 5839400805759284414644687)
    ·
      refine ⟨8759101208638926621967031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5839400805759284414644687 8759101208638926621967031)
      ·
        refine ⟨13138651812958389932950547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8759101208638926621967031 13138651812958389932950547)
        ·
          refine ⟨19707977719437584899425821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13138651812958389932950547 19707977719437584899425821)
          ·
            refine ⟨7390491644789094337284683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19707977719437584899425821 7390491644789094337284683)
            ·
              refine ⟨11085737467183641505927025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7390491644789094337284683 11085737467183641505927025)
              ·
                refine ⟨8314303100387731129445269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11085737467183641505927025 8314303100387731129445269)
                ·
                  refine ⟨389732957830674896692747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8314303100387731129445269 389732957830674896692747)
                  ·
                    rfl

theorem cell22_3415510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_3415510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3415510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3415510 prefixEnd_3415510 := by exact prefixLift 3415510
  have htrace : WordTrace (prefixWord ++ tailWord_3415510) baseStart_3415510 baseEnd_3415510 := by
    simpa [prefixWord, tailWord_3415510, baseEnd_3415510] using wordTrace_append hprefix tailTrace_3415510
  have hstable : (prefixWord ++ tailWord_3415510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415510).length < 2 ^ (prefixWord ++ tailWord_3415510).sum := by decide
  have hdescent : baseEnd_3415510 < baseStart_3415510 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415523 : List Nat := [1, 1, 1, 6, 2, 2, 1, 1, 1, 6]
def baseStart_3415523 : Nat := 118140960795 + 3415523 * 2 ^ 59
def prefixEnd_3415523 : Nat := 4983230072969 + 3 ^ 40 * 3415523 * 2
def baseEnd_3415523 : Nat := 1169203323657696989503201

theorem tailTrace_3415523 : CollatzResearch.WordTrace tailWord_3415523 prefixEnd_3415523 1169203323657696989503201 := by
  unfold tailWord_3415523
  simp only [CollatzResearch.WordTrace]
  refine ⟨124574358005150970732643223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83049572003433980488428815 124574358005150970732643223)
  ·
    refine ⟨186861537007726456098964835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124574358005150970732643223 186861537007726456098964835)
    ·
      refine ⟨280292305511589684148447253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186861537007726456098964835 280292305511589684148447253)
      ·
        refine ⟨13138701820855766444458465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 280292305511589684148447253 13138701820855766444458465)
        ·
          refine ⟨9854026365641824833343849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13138701820855766444458465 9854026365641824833343849)
          ·
            refine ⟨7390519774231368625007887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9854026365641824833343849 7390519774231368625007887)
            ·
              refine ⟨11085779661347052937511831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7390519774231368625007887 11085779661347052937511831)
              ·
                refine ⟨16628669492020579406267747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11085779661347052937511831 16628669492020579406267747)
                ·
                  refine ⟨24943004238030869109401621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16628669492020579406267747 24943004238030869109401621)
                  ·
                    refine ⟨1169203323657696989503201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24943004238030869109401621 1169203323657696989503201)
                    ·
                      rfl

theorem cell22_3415523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 6].length) (baseStart_3415523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3415523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3415523 prefixEnd_3415523 := by exact prefixLift 3415523
  have htrace : WordTrace (prefixWord ++ tailWord_3415523) baseStart_3415523 baseEnd_3415523 := by
    simpa [prefixWord, tailWord_3415523, baseEnd_3415523] using wordTrace_append hprefix tailTrace_3415523
  have hstable : (prefixWord ++ tailWord_3415523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415523).length < 2 ^ (prefixWord ++ tailWord_3415523).sum := by decide
  have hdescent : baseEnd_3415523 < baseStart_3415523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415538 : List Nat := [3, 2, 1, 4, 1, 2, 9]
def baseStart_3415538 : Nat := 118140960795 + 3415538 * 2 ^ 59
def prefixEnd_3415538 : Nat := 4983230072969 + 3 ^ 40 * 3415538 * 2
def baseEnd_3415538 : Nat := 43304016980157109273265

theorem tailTrace_3415538 : CollatzResearch.WordTrace tailWord_3415538 prefixEnd_3415538 43304016980157109273265 := by
  unfold tailWord_3415538
  simp only [CollatzResearch.WordTrace]
  refine ⟨31143726275024157073609817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83049936733397752196292845 31143726275024157073609817)
  ·
    refine ⟨23357794706268117805207363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31143726275024157073609817 23357794706268117805207363)
    ·
      refine ⟨35036692059402176707811045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23357794706268117805207363 35036692059402176707811045)
      ·
        refine ⟨6569379761137908132714571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35036692059402176707811045 6569379761137908132714571)
        ·
          refine ⟨9854069641706862199071857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6569379761137908132714571 9854069641706862199071857)
          ·
            refine ⟨7390552231280146649303893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9854069641706862199071857 7390552231280146649303893)
            ·
              refine ⟨43304016980157109273265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7390552231280146649303893 43304016980157109273265)
              ·
                rfl

theorem cell22_3415538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 9].length) (baseStart_3415538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3415538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3415538 prefixEnd_3415538 := by exact prefixLift 3415538
  have htrace : WordTrace (prefixWord ++ tailWord_3415538) baseStart_3415538 baseEnd_3415538 := by
    simpa [prefixWord, tailWord_3415538, baseEnd_3415538] using wordTrace_append hprefix tailTrace_3415538
  have hstable : (prefixWord ++ tailWord_3415538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415538).length < 2 ^ (prefixWord ++ tailWord_3415538).sum := by decide
  have hdescent : baseEnd_3415538 < baseStart_3415538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415542 : List Nat := [5, 1, 1, 1, 2, 2, 3, 2, 2, 3]
def baseStart_3415542 : Nat := 118140960795 + 3415542 * 2 ^ 59
def prefixEnd_3415542 : Nat := 4983230072969 + 3 ^ 40 * 3415542 * 2
def baseEnd_3415542 : Nat := 1169209827745987273278143

theorem tailTrace_3415542 : CollatzResearch.WordTrace tailWord_3415542 prefixEnd_3415542 1169209827745987273278143 := by
  unfold tailWord_3415542
  simp only [CollatzResearch.WordTrace]
  refine ⟨7785940687005133561099055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83050033994721424651723253 7785940687005133561099055)
  ·
    refine ⟨11678911030507700341648583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7785940687005133561099055 11678911030507700341648583)
    ·
      refine ⟨17518366545761550512472875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11678911030507700341648583 17518366545761550512472875)
      ·
        refine ⟨26277549818642325768709313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17518366545761550512472875 26277549818642325768709313)
        ·
          refine ⟨19708162363981744326531985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26277549818642325768709313 19708162363981744326531985)
          ·
            refine ⟨14781121772986308244898989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19708162363981744326531985 14781121772986308244898989)
            ·
              refine ⟨5542920664869865591837121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14781121772986308244898989 5542920664869865591837121)
              ·
                refine ⟨4157190498652399193877841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5542920664869865591837121 4157190498652399193877841)
                ·
                  refine ⟨3117892873989299395408381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4157190498652399193877841 3117892873989299395408381)
                  ·
                    refine ⟨1169209827745987273278143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3117892873989299395408381 1169209827745987273278143)
                    ·
                      rfl

theorem cell22_3415542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 2, 2, 3].length) (baseStart_3415542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3415542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3415542 prefixEnd_3415542 := by exact prefixLift 3415542
  have htrace : WordTrace (prefixWord ++ tailWord_3415542) baseStart_3415542 baseEnd_3415542 := by
    simpa [prefixWord, tailWord_3415542, baseEnd_3415542] using wordTrace_append hprefix tailTrace_3415542
  have hstable : (prefixWord ++ tailWord_3415542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415542).length < 2 ^ (prefixWord ++ tailWord_3415542).sum := by decide
  have hdescent : baseEnd_3415542 < baseStart_3415542 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415551 : List Nat := [1, 1, 2, 2, 1, 2, 2, 3, 2, 6]
def baseStart_3415551 : Nat := 118140960795 + 3415551 * 2 ^ 59
def prefixEnd_3415551 : Nat := 4983230072969 + 3 ^ 40 * 3415551 * 2
def baseEnd_3415551 : Nat := 1169212908629914249803115

theorem tailTrace_3415551 : CollatzResearch.WordTrace tailWord_3415551 prefixEnd_3415551 1169212908629914249803115 := by
  unfold tailWord_3415551
  simp only [CollatzResearch.WordTrace]
  refine ⟨124575379249049531514662507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83050252832699687676441671 124575379249049531514662507)
  ·
    refine ⟨186863068873574297271993761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124575379249049531514662507 186863068873574297271993761)
    ·
      refine ⟨140147301655180722953995321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186863068873574297271993761 140147301655180722953995321)
      ·
        refine ⟨105110476241385542215496491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140147301655180722953995321 105110476241385542215496491)
        ·
          refine ⟨157665714362078313323244737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105110476241385542215496491 157665714362078313323244737)
          ·
            refine ⟨118249285771558734992433553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157665714362078313323244737 118249285771558734992433553)
            ·
              refine ⟨88686964328669051244325165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118249285771558734992433553 88686964328669051244325165)
              ·
                refine ⟨33257611623250894216621937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88686964328669051244325165 33257611623250894216621937)
                ·
                  refine ⟨24943208717438170662466453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33257611623250894216621937 24943208717438170662466453)
                  ·
                    refine ⟨1169212908629914249803115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24943208717438170662466453 1169212908629914249803115)
                    ·
                      rfl

theorem cell22_3415551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 6].length) (baseStart_3415551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3415551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3415551 prefixEnd_3415551 := by exact prefixLift 3415551
  have htrace : WordTrace (prefixWord ++ tailWord_3415551) baseStart_3415551 baseEnd_3415551 := by
    simpa [prefixWord, tailWord_3415551, baseEnd_3415551] using wordTrace_append hprefix tailTrace_3415551
  have hstable : (prefixWord ++ tailWord_3415551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415551).length < 2 ^ (prefixWord ++ tailWord_3415551).sum := by decide
  have hdescent : baseEnd_3415551 < baseStart_3415551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415677 : List Nat := [1, 4, 1, 1, 4, 1, 2, 3, 2, 3]
def baseStart_3415677 : Nat := 118140960795 + 3415677 * 2 ^ 59
def prefixEnd_3415677 : Nat := 4983230072969 + 3 ^ 40 * 3415677 * 2
def baseEnd_3415677 : Nat := 1169256041004891921152729

theorem tailTrace_3415677 : CollatzResearch.WordTrace tailWord_3415677 prefixEnd_3415677 1169256041004891921152729 := by
  unfold tailWord_3415677
  simp only [CollatzResearch.WordTrace]
  refine ⟨124579974846593055033749285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83053316564395370022499523 124579974846593055033749285)
  ·
    refine ⟨23358745283736197818827991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124579974846593055033749285 23358745283736197818827991)
    ·
      refine ⟨35038117925604296728241987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23358745283736197818827991 35038117925604296728241987)
      ·
        refine ⟨52557176888406445092362981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35038117925604296728241987 52557176888406445092362981)
        ·
          refine ⟨9854470666576208454818059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52557176888406445092362981 9854470666576208454818059)
          ·
            refine ⟨14781705999864312682227089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9854470666576208454818059 14781705999864312682227089)
            ·
              refine ⟨11086279499898234511670317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14781705999864312682227089 11086279499898234511670317)
              ·
                refine ⟨4157354812461837941876369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11086279499898234511670317 4157354812461837941876369)
                ·
                  refine ⟨3118016109346378456407277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4157354812461837941876369 3118016109346378456407277)
                  ·
                    refine ⟨1169256041004891921152729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3118016109346378456407277 1169256041004891921152729)
                    ·
                      rfl

theorem cell22_3415677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 3, 2, 3].length) (baseStart_3415677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3415677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3415677 prefixEnd_3415677 := by exact prefixLift 3415677
  have htrace : WordTrace (prefixWord ++ tailWord_3415677) baseStart_3415677 baseEnd_3415677 := by
    simpa [prefixWord, tailWord_3415677, baseEnd_3415677] using wordTrace_append hprefix tailTrace_3415677
  have hstable : (prefixWord ++ tailWord_3415677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415677).length < 2 ^ (prefixWord ++ tailWord_3415677).sum := by decide
  have hdescent : baseEnd_3415677 < baseStart_3415677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415711 : List Nat := [1, 1, 2, 7, 1, 2, 1, 2, 2, 3]
def baseStart_3415711 : Nat := 118140960795 + 3415711 * 2 ^ 59
def prefixEnd_3415711 : Nat := 4983230072969 + 3 ^ 40 * 3415711 * 2
def baseEnd_3415711 : Nat := 1169267679899727165802625

theorem tailTrace_3415711 : CollatzResearch.WordTrace tailWord_3415711 prefixEnd_3415711 1169267679899727165802625 := by
  unfold tailWord_3415711
  simp only [CollatzResearch.WordTrace]
  refine ⟨124581214928469878840486987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83054143285646585893657991 124581214928469878840486987)
  ·
    refine ⟨186871822392704818260730481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124581214928469878840486987 186871822392704818260730481)
    ·
      refine ⟨140153866794528613695547861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186871822392704818260730481 140153866794528613695547861)
      ·
        refine ⟨3284856252996764383489403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 140153866794528613695547861 3284856252996764383489403)
        ·
          refine ⟨4927284379495146575234105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3284856252996764383489403 4927284379495146575234105)
          ·
            refine ⟨3695463284621359931425579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4927284379495146575234105 3695463284621359931425579)
            ·
              refine ⟨5543194926932039897138369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3695463284621359931425579 5543194926932039897138369)
              ·
                refine ⟨4157396195199029922853777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5543194926932039897138369 4157396195199029922853777)
                ·
                  refine ⟨3118047146399272442140333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4157396195199029922853777 3118047146399272442140333)
                  ·
                    refine ⟨1169267679899727165802625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3118047146399272442140333 1169267679899727165802625)
                    ·
                      rfl

theorem cell22_3415711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 2, 2, 3].length) (baseStart_3415711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3415711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3415711 prefixEnd_3415711 := by exact prefixLift 3415711
  have htrace : WordTrace (prefixWord ++ tailWord_3415711) baseStart_3415711 baseEnd_3415711 := by
    simpa [prefixWord, tailWord_3415711, baseEnd_3415711] using wordTrace_append hprefix tailTrace_3415711
  have hstable : (prefixWord ++ tailWord_3415711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415711).length < 2 ^ (prefixWord ++ tailWord_3415711).sum := by decide
  have hdescent : baseEnd_3415711 < baseStart_3415711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415773 : List Nat := [1, 4, 3, 3, 2, 1, 1, 1, 3, 3]
def baseStart_3415773 : Nat := 118140960795 + 3415773 * 2 ^ 59
def prefixEnd_3415773 : Nat := 4983230072969 + 3 ^ 40 * 3415773 * 2
def baseEnd_3415773 : Nat := 1169288903766779670752435

theorem tailTrace_3415773 : CollatzResearch.WordTrace tailWord_3415773 prefixEnd_3415773 1169288903766779670752435 := by
  unfold tailWord_3415773
  simp only [CollatzResearch.WordTrace]
  refine ⟨124583476254245263429243973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83055650836163508952829315 124583476254245263429243973)
  ·
    refine ⟨23359401797670986892983245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124583476254245263429243973 23359401797670986892983245)
    ·
      refine ⟨8759775674126620084868717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23359401797670986892983245 8759775674126620084868717)
      ·
        refine ⟨3284915877797482531825769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8759775674126620084868717 3284915877797482531825769)
        ·
          refine ⟨2463686908348111898869327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3284915877797482531825769 2463686908348111898869327)
          ·
            refine ⟨3695530362522167848303991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2463686908348111898869327 3695530362522167848303991)
            ·
              refine ⟨5543295543783251772455987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3695530362522167848303991 5543295543783251772455987)
              ·
                refine ⟨8314943315674877658683981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5543295543783251772455987 8314943315674877658683981)
                ·
                  refine ⟨3118103743378079122006493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8314943315674877658683981 3118103743378079122006493)
                  ·
                    refine ⟨1169288903766779670752435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3118103743378079122006493 1169288903766779670752435)
                    ·
                      rfl

theorem cell22_3415773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_3415773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3415773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3415773 prefixEnd_3415773 := by exact prefixLift 3415773
  have htrace : WordTrace (prefixWord ++ tailWord_3415773) baseStart_3415773 baseEnd_3415773 := by
    simpa [prefixWord, tailWord_3415773, baseEnd_3415773] using wordTrace_append hprefix tailTrace_3415773
  have hstable : (prefixWord ++ tailWord_3415773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415773).length < 2 ^ (prefixWord ++ tailWord_3415773).sum := by decide
  have hdescent : baseEnd_3415773 < baseStart_3415773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415812 : List Nat := [2, 3, 2, 2, 1, 3, 1, 2, 1, 5]
def baseStart_3415812 : Nat := 118140960795 + 3415812 * 2 ^ 59
def prefixEnd_3415812 : Nat := 4983230072969 + 3 ^ 40 * 3415812 * 2
def baseEnd_3415812 : Nat := 1169302254263796569027315

theorem tailTrace_3415812 : CollatzResearch.WordTrace tailWord_3415812 prefixEnd_3415812 1169302254263796569027315 := by
  unfold tailWord_3415812
  simp only [CollatzResearch.WordTrace]
  refine ⟨62292449350551986544956845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83056599134069315393275793 62292449350551986544956845)
  ·
    refine ⟨23359668506456994954358817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62292449350551986544956845 23359668506456994954358817)
    ·
      refine ⟨17519751379842746215769113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23359668506456994954358817 17519751379842746215769113)
      ·
        refine ⟨13139813534882059661826835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17519751379842746215769113 13139813534882059661826835)
        ·
          refine ⟨19709720302323089492740253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13139813534882059661826835 19709720302323089492740253)
          ·
            refine ⟨7391145113371158559777595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19709720302323089492740253 7391145113371158559777595)
            ·
              refine ⟨11086717670056737839666393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7391145113371158559777595 11086717670056737839666393)
              ·
                refine ⟨8315038252542553379749795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11086717670056737839666393 8315038252542553379749795)
                ·
                  refine ⟨12472557378813830069624693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8315038252542553379749795 12472557378813830069624693)
                  ·
                    refine ⟨1169302254263796569027315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12472557378813830069624693 1169302254263796569027315)
                    ·
                      rfl

theorem cell22_3415812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_3415812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3415812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3415812 prefixEnd_3415812 := by exact prefixLift 3415812
  have htrace : WordTrace (prefixWord ++ tailWord_3415812) baseStart_3415812 baseEnd_3415812 := by
    simpa [prefixWord, tailWord_3415812, baseEnd_3415812] using wordTrace_append hprefix tailTrace_3415812
  have hstable : (prefixWord ++ tailWord_3415812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415812).length < 2 ^ (prefixWord ++ tailWord_3415812).sum := by decide
  have hdescent : baseEnd_3415812 < baseStart_3415812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415829 : List Nat := [1, 3, 2, 1, 2, 4, 2, 2, 2, 3]
def baseStart_3415829 : Nat := 118140960795 + 3415829 * 2 ^ 59
def prefixEnd_3415829 : Nat := 4983230072969 + 3 ^ 40 * 3415829 * 2
def baseEnd_3415829 : Nat := 1169308073711214191352263

theorem tailTrace_3415829 : CollatzResearch.WordTrace tailWord_3415829 prefixEnd_3415829 1169308073711214191352263 := by
  unfold tailWord_3415829
  simp only [CollatzResearch.WordTrace]
  refine ⟨124585518742042384993282541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83057012494694923328855027 124585518742042384993282541)
  ·
    refine ⟨46719569528265894372480953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124585518742042384993282541 46719569528265894372480953)
    ·
      refine ⟨35039677146199420779360715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46719569528265894372480953 35039677146199420779360715)
      ·
        refine ⟨52559515719299131169041073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35039677146199420779360715 52559515719299131169041073)
        ·
          refine ⟨39419636789474348376780805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52559515719299131169041073 39419636789474348376780805)
          ·
            refine ⟨7391181898026440320646401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39419636789474348376780805 7391181898026440320646401)
            ·
              refine ⟨5543386423519830240484801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7391181898026440320646401 5543386423519830240484801)
              ·
                refine ⟨4157539817639872680363601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5543386423519830240484801 4157539817639872680363601)
                ·
                  refine ⟨3118154863229904510272701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4157539817639872680363601 3118154863229904510272701)
                  ·
                    refine ⟨1169308073711214191352263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3118154863229904510272701 1169308073711214191352263)
                    ·
                      rfl

theorem cell22_3415829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 2, 2, 3].length) (baseStart_3415829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3415829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3415829 prefixEnd_3415829 := by exact prefixLift 3415829
  have htrace : WordTrace (prefixWord ++ tailWord_3415829) baseStart_3415829 baseEnd_3415829 := by
    simpa [prefixWord, tailWord_3415829, baseEnd_3415829] using wordTrace_append hprefix tailTrace_3415829
  have hstable : (prefixWord ++ tailWord_3415829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415829).length < 2 ^ (prefixWord ++ tailWord_3415829).sum := by decide
  have hdescent : baseEnd_3415829 < baseStart_3415829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415831 : List Nat := [1, 1, 3, 4, 2, 3, 2, 2, 4]
def baseStart_3415831 : Nat := 118140960795 + 3415831 * 2 ^ 59
def prefixEnd_3415831 : Nat := 4983230072969 + 3 ^ 40 * 3415831 * 2
def baseEnd_3415831 : Nat := 389769586117362284267419

theorem tailTrace_3415831 : CollatzResearch.WordTrace tailWord_3415831 prefixEnd_3415831 389769586117362284267419 := by
  unfold tailWord_3415831
  simp only [CollatzResearch.WordTrace]
  refine ⟨124585591688035139334855347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83057061125356759556570231 124585591688035139334855347)
  ·
    refine ⟨186878387532052709002283021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124585591688035139334855347 186878387532052709002283021)
    ·
      refine ⟨70079395324519765875856133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186878387532052709002283021 70079395324519765875856133)
      ·
        refine ⟨13139886623347456101723025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70079395324519765875856133 13139886623347456101723025)
        ·
          refine ⟨9854914967510592076292269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13139886623347456101723025 9854914967510592076292269)
          ·
            refine ⟨3695593112816472028609601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9854914967510592076292269 3695593112816472028609601)
            ·
              refine ⟨2771694834612354021457201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3695593112816472028609601 2771694834612354021457201)
              ·
                refine ⟨2078771125959265516092901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2771694834612354021457201 2078771125959265516092901)
                ·
                  refine ⟨389769586117362284267419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2078771125959265516092901 389769586117362284267419)
                  ·
                    rfl

theorem cell22_3415831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 2, 2, 4].length) (baseStart_3415831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3415831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3415831 prefixEnd_3415831 := by exact prefixLift 3415831
  have htrace : WordTrace (prefixWord ++ tailWord_3415831) baseStart_3415831 baseEnd_3415831 := by
    simpa [prefixWord, tailWord_3415831, baseEnd_3415831] using wordTrace_append hprefix tailTrace_3415831
  have hstable : (prefixWord ++ tailWord_3415831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415831).length < 2 ^ (prefixWord ++ tailWord_3415831).sum := by decide
  have hdescent : baseEnd_3415831 < baseStart_3415831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415857 : List Nat := [1, 2, 2, 3, 2, 2, 1, 1, 5, 3]
def baseStart_3415857 : Nat := 118140960795 + 3415857 * 2 ^ 59
def prefixEnd_3415857 : Nat := 4983230072969 + 3 ^ 40 * 3415857 * 2
def baseEnd_3415857 : Nat := 1169317658683431451652177

theorem tailTrace_3415857 : CollatzResearch.WordTrace tailWord_3415857 prefixEnd_3415857 1169317658683431451652177 := by
  unfold tailWord_3415857
  simp only [CollatzResearch.WordTrace]
  refine ⟨124586539985940945775301825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83057693323960630516867883 124586539985940945775301825)
  ·
    refine ⟨93439904989455709331476369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124586539985940945775301825 93439904989455709331476369)
    ·
      refine ⟨70079928742091781998607277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93439904989455709331476369 70079928742091781998607277)
      ·
        refine ⟨26279973278284418249477729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70079928742091781998607277 26279973278284418249477729)
        ·
          refine ⟨19709979958713313687108297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26279973278284418249477729 19709979958713313687108297)
          ·
            refine ⟨14782484969034985265331223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19709979958713313687108297 14782484969034985265331223)
            ·
              refine ⟨22173727453552477897996835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14782484969034985265331223 22173727453552477897996835)
              ·
                refine ⟨33260591180328716846995253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22173727453552477897996835 33260591180328716846995253)
                ·
                  refine ⟨3118180423155817204405805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33260591180328716846995253 3118180423155817204405805)
                  ·
                    refine ⟨1169317658683431451652177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3118180423155817204405805 1169317658683431451652177)
                    ·
                      rfl

theorem cell22_3415857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 5, 3].length) (baseStart_3415857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3415857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3415857 prefixEnd_3415857 := by exact prefixLift 3415857
  have htrace : WordTrace (prefixWord ++ tailWord_3415857) baseStart_3415857 baseEnd_3415857 := by
    simpa [prefixWord, tailWord_3415857, baseEnd_3415857] using wordTrace_append hprefix tailTrace_3415857
  have hstable : (prefixWord ++ tailWord_3415857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415857).length < 2 ^ (prefixWord ++ tailWord_3415857).sum := by decide
  have hdescent : baseEnd_3415857 < baseStart_3415857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415861 : List Nat := [1, 3, 3, 1, 5, 1, 1, 1, 2, 4]
def baseStart_3415861 : Nat := 118140960795 + 3415861 * 2 ^ 59
def prefixEnd_3415861 : Nat := 4983230072969 + 3 ^ 40 * 3415861 * 2
def baseEnd_3415861 : Nat := 1169319027965176774552165

theorem tailTrace_3415861 : CollatzResearch.WordTrace tailWord_3415861 prefixEnd_3415861 1169319027965176774552165 := by
  unfold tailWord_3415861
  simp only [CollatzResearch.WordTrace]
  refine ⟨124586685877926454458447437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83057790585284302972298291 124586685877926454458447437)
  ·
    refine ⟨46720007204222420421917789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124586685877926454458447437 46720007204222420421917789)
    ·
      refine ⟨17520002701583407658219171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46720007204222420421917789 17520002701583407658219171)
      ·
        refine ⟨26280004052375111487328757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17520002701583407658219171 26280004052375111487328757)
        ·
          refine ⟨2463750379910166701937071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26280004052375111487328757 2463750379910166701937071)
          ·
            refine ⟨3695625569865250052905607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2463750379910166701937071 3695625569865250052905607)
            ·
              refine ⟨5543438354797875079358411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3695625569865250052905607 5543438354797875079358411)
              ·
                refine ⟨8315157532196812619037617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5543438354797875079358411 8315157532196812619037617)
                ·
                  refine ⟨6236368149147609464278213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8315157532196812619037617 6236368149147609464278213)
                  ·
                    refine ⟨1169319027965176774552165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6236368149147609464278213 1169319027965176774552165)
                    ·
                      rfl

theorem cell22_3415861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 1, 2, 4].length) (baseStart_3415861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3415861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3415861 prefixEnd_3415861 := by exact prefixLift 3415861
  have htrace : WordTrace (prefixWord ++ tailWord_3415861) baseStart_3415861 baseEnd_3415861 := by
    simpa [prefixWord, tailWord_3415861, baseEnd_3415861] using wordTrace_append hprefix tailTrace_3415861
  have hstable : (prefixWord ++ tailWord_3415861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415861).length < 2 ^ (prefixWord ++ tailWord_3415861).sum := by decide
  have hdescent : baseEnd_3415861 < baseStart_3415861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415904 : List Nat := [2, 1, 1, 3, 3, 3, 3, 1, 5]
def baseStart_3415904 : Nat := 118140960795 + 3415904 * 2 ^ 59
def prefixEnd_3415904 : Nat := 4983230072969 + 3 ^ 40 * 3415904 * 2
def baseEnd_3415904 : Nat := 389777915914646331909011

theorem tailTrace_3415904 : CollatzResearch.WordTrace tailWord_3415904 prefixEnd_3415904 389777915914646331909011 := by
  unfold tailWord_3415904
  simp only [CollatzResearch.WordTrace]
  refine ⟨62294127108385336401131383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83058836144513781868175177 62294127108385336401131383)
  ·
    refine ⟨93441190662578004601697075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62294127108385336401131383 93441190662578004601697075)
    ·
      refine ⟨140161785993867006902545613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93441190662578004601697075 140161785993867006902545613)
      ·
        refine ⟨52560669747700127588454605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140161785993867006902545613 52560669747700127588454605)
        ·
          refine ⟨19710251155387547845670477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52560669747700127588454605 19710251155387547845670477)
          ·
            refine ⟨7391344183270330442126429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19710251155387547845670477 7391344183270330442126429)
            ·
              refine ⟨2771754068726373915797411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7391344183270330442126429 2771754068726373915797411)
              ·
                refine ⟨4157631103089560873696117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2771754068726373915797411 4157631103089560873696117)
                ·
                  refine ⟨389777915914646331909011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4157631103089560873696117 389777915914646331909011)
                  ·
                    rfl

theorem cell22_3415904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 3, 1, 5].length) (baseStart_3415904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3415904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3415904 prefixEnd_3415904 := by exact prefixLift 3415904
  have htrace : WordTrace (prefixWord ++ tailWord_3415904) baseStart_3415904 baseEnd_3415904 := by
    simpa [prefixWord, tailWord_3415904, baseEnd_3415904] using wordTrace_append hprefix tailTrace_3415904
  have hstable : (prefixWord ++ tailWord_3415904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415904).length < 2 ^ (prefixWord ++ tailWord_3415904).sum := by decide
  have hdescent : baseEnd_3415904 < baseStart_3415904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415917 : List Nat := [1, 5, 1, 1, 1, 1, 2, 3, 3, 4]
def baseStart_3415917 : Nat := 118140960795 + 3415917 * 2 ^ 59
def prefixEnd_3415917 : Nat := 4983230072969 + 3 ^ 40 * 3415917 * 2
def baseEnd_3415917 : Nat := 1169338197909611295151993

theorem tailTrace_3415917 : CollatzResearch.WordTrace tailWord_3415917 prefixEnd_3415917 1169338197909611295151993 := by
  unfold tailWord_3415917
  simp only [CollatzResearch.WordTrace]
  refine ⟨124588728365723576022486005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83059152243815717348324003 124588728365723576022486005)
  ·
    refine ⟨11680193284286585252108063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 124588728365723576022486005 11680193284286585252108063)
    ·
      refine ⟨17520289926429877878162095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11680193284286585252108063 17520289926429877878162095)
      ·
        refine ⟨26280434889644816817243143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17520289926429877878162095 26280434889644816817243143)
        ·
          refine ⟨39420652334467225225864715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26280434889644816817243143 39420652334467225225864715)
          ·
            refine ⟨59130978501700837838797073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39420652334467225225864715 59130978501700837838797073)
            ·
              refine ⟨44348233876275628379097805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59130978501700837838797073 44348233876275628379097805)
              ·
                refine ⟨16630587703603360642161677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44348233876275628379097805 16630587703603360642161677)
                ·
                  refine ⟨6236470388851260240810629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16630587703603360642161677 6236470388851260240810629)
                  ·
                    refine ⟨1169338197909611295151993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6236470388851260240810629 1169338197909611295151993)
                    ·
                      rfl

theorem cell22_3415917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_3415917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3415917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3415917 prefixEnd_3415917 := by exact prefixLift 3415917
  have htrace : WordTrace (prefixWord ++ tailWord_3415917) baseStart_3415917 baseEnd_3415917 := by
    simpa [prefixWord, tailWord_3415917, baseEnd_3415917] using wordTrace_append hprefix tailTrace_3415917
  have hstable : (prefixWord ++ tailWord_3415917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415917).length < 2 ^ (prefixWord ++ tailWord_3415917).sum := by decide
  have hdescent : baseEnd_3415917 < baseStart_3415917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416026 : List Nat := [3, 1, 1, 2, 5, 1, 1, 2, 3, 3]
def baseStart_3416026 : Nat := 118140960795 + 3416026 * 2 ^ 59
def prefixEnd_3416026 : Nat := 4983230072969 + 3 ^ 40 * 3416026 * 2
def baseEnd_3416026 : Nat := 1169375510837171344176659

theorem tailTrace_3416026 : CollatzResearch.WordTrace tailWord_3416026 prefixEnd_3416026 1169375510837171344176659 := by
  unfold tailWord_3416026
  simp only [CollatzResearch.WordTrace]
  refine ⟨31148175980582171909550983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83061802614885791758802621 31148175980582171909550983)
  ·
    refine ⟨46722263970873257864326475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31148175980582171909550983 46722263970873257864326475)
    ·
      refine ⟨70083395956309886796489713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46722263970873257864326475 70083395956309886796489713)
      ·
        refine ⟨52562546967232415097367285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70083395956309886796489713 52562546967232415097367285)
        ·
          refine ⟨4927738778178038915378183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52562546967232415097367285 4927738778178038915378183)
          ·
            refine ⟨7391608167267058373067275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4927738778178038915378183 7391608167267058373067275)
            ·
              refine ⟨11087412250900587559600913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7391608167267058373067275 11087412250900587559600913)
              ·
                refine ⟨8315559188175440669700685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11087412250900587559600913 8315559188175440669700685)
                ·
                  refine ⟨3118334695565790251137757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8315559188175440669700685 3118334695565790251137757)
                  ·
                    refine ⟨1169375510837171344176659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3118334695565790251137757 1169375510837171344176659)
                    ·
                      rfl

theorem cell22_3416026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 2, 3, 3].length) (baseStart_3416026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3416026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3416026 prefixEnd_3416026 := by exact prefixLift 3416026
  have htrace : WordTrace (prefixWord ++ tailWord_3416026) baseStart_3416026 baseEnd_3416026 := by
    simpa [prefixWord, tailWord_3416026, baseEnd_3416026] using wordTrace_append hprefix tailTrace_3416026
  have hstable : (prefixWord ++ tailWord_3416026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416026).length < 2 ^ (prefixWord ++ tailWord_3416026).sum := by decide
  have hdescent : baseEnd_3416026 < baseStart_3416026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416099 : List Nat := [1, 1, 1, 4, 3, 1, 1, 1, 6, 3]
def baseStart_3416099 : Nat := 118140960795 + 3416099 * 2 ^ 59
def prefixEnd_3416099 : Nat := 4983230072969 + 3 ^ 40 * 3416099 * 2
def baseEnd_3416099 : Nat := 1169400500229023487101435

theorem tailTrace_3416099 : CollatzResearch.WordTrace tailWord_3416099 prefixEnd_3416099 1169400500229023487101435 := by
  unfold tailWord_3416099
  simp only [CollatzResearch.WordTrace]
  refine ⟨124595366451064221105611351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83063577634042814070407567 124595366451064221105611351)
  ·
    refine ⟨186893049676596331658417027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124595366451064221105611351 186893049676596331658417027)
    ·
      refine ⟨280339574514894497487625541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186893049676596331658417027 280339574514894497487625541)
      ·
        refine ⟨52563670221542718278929789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 280339574514894497487625541 52563670221542718278929789)
        ·
          refine ⟨19711376333078519354598671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52563670221542718278929789 19711376333078519354598671)
          ·
            refine ⟨29567064499617779031898007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19711376333078519354598671 29567064499617779031898007)
            ·
              refine ⟨44350596749426668547847011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29567064499617779031898007 44350596749426668547847011)
              ·
                refine ⟨66525895124140002821770517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44350596749426668547847011 66525895124140002821770517)
                ·
                  refine ⟨3118401333944062632270493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 66525895124140002821770517 3118401333944062632270493)
                  ·
                    refine ⟨1169400500229023487101435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3118401333944062632270493 1169400500229023487101435)
                    ·
                      rfl

theorem cell22_3416099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 6, 3].length) (baseStart_3416099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3416099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3416099 prefixEnd_3416099 := by exact prefixLift 3416099
  have htrace : WordTrace (prefixWord ++ tailWord_3416099) baseStart_3416099 baseEnd_3416099 := by
    simpa [prefixWord, tailWord_3416099, baseEnd_3416099] using wordTrace_append hprefix tailTrace_3416099
  have hstable : (prefixWord ++ tailWord_3416099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416099).length < 2 ^ (prefixWord ++ tailWord_3416099).sum := by decide
  have hdescent : baseEnd_3416099 < baseStart_3416099 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416101 : List Nat := [1, 3, 1, 2, 2, 3, 3, 3, 4]
def baseStart_3416101 : Nat := 118140960795 + 3416101 * 2 ^ 59
def prefixEnd_3416101 : Nat := 4983230072969 + 3 ^ 40 * 3416101 * 2
def baseEnd_3416101 : Nat := 389800394956632049517143

theorem tailTrace_3416101 : CollatzResearch.WordTrace tailWord_3416101 prefixEnd_3416101 389800394956632049517143 := by
  unfold tailWord_3416101
  simp only [CollatzResearch.WordTrace]
  refine ⟨124595439397056975447184157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83063626264704650298122771 124595439397056975447184157)
  ·
    refine ⟨46723289773896365792694059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124595439397056975447184157 46723289773896365792694059)
    ·
      refine ⟨70084934660844548689041089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46723289773896365792694059 70084934660844548689041089)
      ·
        refine ⟨52563700995633411516780817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70084934660844548689041089 52563700995633411516780817)
        ·
          refine ⟨39422775746725058637585613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52563700995633411516780817 39422775746725058637585613)
          ·
            refine ⟨14783540905021896989094605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39422775746725058637585613 14783540905021896989094605)
            ·
              refine ⟨5543827839383211370910477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14783540905021896989094605 5543827839383211370910477)
              ·
                refine ⟨2078935439768704264091429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5543827839383211370910477 2078935439768704264091429)
                ·
                  refine ⟨389800394956632049517143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2078935439768704264091429 389800394956632049517143)
                  ·
                    rfl

theorem cell22_3416101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 3, 4].length) (baseStart_3416101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3416101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3416101 prefixEnd_3416101 := by exact prefixLift 3416101
  have htrace : WordTrace (prefixWord ++ tailWord_3416101) baseStart_3416101 baseEnd_3416101 := by
    simpa [prefixWord, tailWord_3416101, baseEnd_3416101] using wordTrace_append hprefix tailTrace_3416101
  have hstable : (prefixWord ++ tailWord_3416101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416101).length < 2 ^ (prefixWord ++ tailWord_3416101).sum := by decide
  have hdescent : baseEnd_3416101 < baseStart_3416101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416112 : List Nat := [2, 1, 1, 1, 2, 5, 10]
def baseStart_3416112 : Nat := 118140960795 + 3416112 * 2 ^ 59
def prefixEnd_3416112 : Nat := 4983230072969 + 3 ^ 40 * 3416112 * 2
def baseEnd_3416112 : Nat := 43311294459062806908385

theorem tailTrace_3416112 : CollatzResearch.WordTrace tailWord_3416112 prefixEnd_3416112 43311294459062806908385 := by
  unfold tailWord_3416112
  simp only [CollatzResearch.WordTrace]
  refine ⟨62297920300008562162917295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83063893733344749550556393 62297920300008562162917295)
  ·
    refine ⟨93446880450012843244375943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62297920300008562162917295 93446880450012843244375943)
    ·
      refine ⟨140170320675019264866563915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93446880450012843244375943 140170320675019264866563915)
      ·
        refine ⟨210255481012528897299845873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140170320675019264866563915 210255481012528897299845873)
        ·
          refine ⟨157691610759396672974884405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210255481012528897299845873 157691610759396672974884405)
          ·
            refine ⟨14783588508693438091395413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 157691610759396672974884405 14783588508693438091395413)
            ·
              refine ⟨43311294459062806908385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14783588508693438091395413 43311294459062806908385)
              ·
                rfl

theorem cell22_3416112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 10].length) (baseStart_3416112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3416112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3416112 prefixEnd_3416112 := by exact prefixLift 3416112
  have htrace : WordTrace (prefixWord ++ tailWord_3416112) baseStart_3416112 baseEnd_3416112 := by
    simpa [prefixWord, tailWord_3416112, baseEnd_3416112] using wordTrace_append hprefix tailTrace_3416112
  have hstable : (prefixWord ++ tailWord_3416112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416112).length < 2 ^ (prefixWord ++ tailWord_3416112).sum := by decide
  have hdescent : baseEnd_3416112 < baseStart_3416112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416114 : List Nat := [3, 2, 1, 1, 2, 3, 1, 1, 4, 4]
def baseStart_3416114 : Nat := 118140960795 + 3416114 * 2 ^ 59
def prefixEnd_3416114 : Nat := 4983230072969 + 3 ^ 40 * 3416114 * 2
def baseEnd_3416114 : Nat := 1169405635035568447976389

theorem tailTrace_3416114 : CollatzResearch.WordTrace tailWord_3416114 prefixEnd_3416114 1169405635035568447976389 := by
  unfold tailWord_3416114
  simp only [CollatzResearch.WordTrace]
  refine ⟨31148978386502469666851849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83063942364006585778271597 31148978386502469666851849)
  ·
    refine ⟨23361733789876852250138887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31148978386502469666851849 23361733789876852250138887)
    ·
      refine ⟨35042600684815278375208331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23361733789876852250138887 35042600684815278375208331)
      ·
        refine ⟨52563901027222917562812497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35042600684815278375208331 52563901027222917562812497)
        ·
          refine ⟨39422925770417188172109373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52563901027222917562812497 39422925770417188172109373)
          ·
            refine ⟨14783597163906445564541015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39422925770417188172109373 14783597163906445564541015)
            ·
              refine ⟨22175395745859668346811523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14783597163906445564541015 22175395745859668346811523)
              ·
                refine ⟨33263093618789502520217285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22175395745859668346811523 33263093618789502520217285)
                ·
                  refine ⟨6236830053523031722540741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33263093618789502520217285 6236830053523031722540741)
                  ·
                    refine ⟨1169405635035568447976389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6236830053523031722540741 1169405635035568447976389)
                    ·
                      rfl

theorem cell22_3416114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 4, 4].length) (baseStart_3416114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3416114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3416114 prefixEnd_3416114 := by exact prefixLift 3416114
  have htrace : WordTrace (prefixWord ++ tailWord_3416114) baseStart_3416114 baseEnd_3416114 := by
    simpa [prefixWord, tailWord_3416114, baseEnd_3416114] using wordTrace_append hprefix tailTrace_3416114
  have hstable : (prefixWord ++ tailWord_3416114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416114).length < 2 ^ (prefixWord ++ tailWord_3416114).sum := by decide
  have hdescent : baseEnd_3416114 < baseStart_3416114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416129 : List Nat := [1, 2, 5, 1, 2, 1, 1, 9]
def baseStart_3416129 : Nat := 118140960795 + 3416129 * 2 ^ 59
def prefixEnd_3416129 : Nat := 4983230072969 + 3 ^ 40 * 3416129 * 2
def baseEnd_3416129 : Nat := 129934529982457045427927

theorem tailTrace_3416129 : CollatzResearch.WordTrace tailWord_3416129 prefixEnd_3416129 129934529982457045427927 := by
  unfold tailWord_3416129
  simp only [CollatzResearch.WordTrace]
  refine ⟨124596460640955536229203441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83064307093970357486135627 124596460640955536229203441)
  ·
    refine ⟨93447345480716652171902581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124596460640955536229203441 93447345480716652171902581)
    ·
      refine ⟨8760688638817186141115867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 93447345480716652171902581 8760688638817186141115867)
      ·
        refine ⟨13141032958225779211673801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8760688638817186141115867 13141032958225779211673801)
        ·
          refine ⟨9855774718669334408755351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13141032958225779211673801 9855774718669334408755351)
          ·
            refine ⟨14783662078004001613133027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9855774718669334408755351 14783662078004001613133027)
            ·
              refine ⟨22175493117006002419699541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14783662078004001613133027 22175493117006002419699541)
              ·
                refine ⟨129934529982457045427927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22175493117006002419699541 129934529982457045427927)
                ·
                  rfl

theorem cell22_3416129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 9].length) (baseStart_3416129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3416129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3416129 prefixEnd_3416129 := by exact prefixLift 3416129
  have htrace : WordTrace (prefixWord ++ tailWord_3416129) baseStart_3416129 baseEnd_3416129 := by
    simpa [prefixWord, tailWord_3416129, baseEnd_3416129] using wordTrace_append hprefix tailTrace_3416129
  have hstable : (prefixWord ++ tailWord_3416129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416129).length < 2 ^ (prefixWord ++ tailWord_3416129).sum := by decide
  have hdescent : baseEnd_3416129 < baseStart_3416129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416189 : List Nat := [1, 4, 1, 1, 3, 2, 1, 1, 1, 7]
def baseStart_3416189 : Nat := 118140960795 + 3416189 * 2 ^ 59
def prefixEnd_3416189 : Nat := 4983230072969 + 3 ^ 40 * 3416189 * 2
def baseEnd_3416189 : Nat := 1169431309068293252351159

theorem tailTrace_3416189 : CollatzResearch.WordTrace tailWord_3416189 prefixEnd_3416189 1169431309068293252351159 := by
  unfold tailWord_3416189
  simp only [CollatzResearch.WordTrace]
  refine ⟨124598649020738166476387621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83065766013825444317591747 124598649020738166476387621)
  ·
    refine ⟨23362246691388406214322679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124598649020738166476387621 23362246691388406214322679)
    ·
      refine ⟨35043370037082609321484019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23362246691388406214322679 35043370037082609321484019)
      ·
        refine ⟨52565055055623913982226029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35043370037082609321484019 52565055055623913982226029)
        ·
          refine ⟨19711895645858967743334761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52565055055623913982226029 19711895645858967743334761)
          ·
            refine ⟨14783921734394225807501071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19711895645858967743334761 14783921734394225807501071)
            ·
              refine ⟨22175882601591338711251607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14783921734394225807501071 22175882601591338711251607)
              ·
                refine ⟨33263823902387008066877411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22175882601591338711251607 33263823902387008066877411)
                ·
                  refine ⟨49895735853580512100316117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33263823902387008066877411 49895735853580512100316117)
                  ·
                    refine ⟨1169431309068293252351159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49895735853580512100316117 1169431309068293252351159)
                    ·
                      rfl

theorem cell22_3416189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_3416189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3416189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3416189 prefixEnd_3416189 := by exact prefixLift 3416189
  have htrace : WordTrace (prefixWord ++ tailWord_3416189) baseStart_3416189 baseEnd_3416189 := by
    simpa [prefixWord, tailWord_3416189, baseEnd_3416189] using wordTrace_append hprefix tailTrace_3416189
  have hstable : (prefixWord ++ tailWord_3416189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416189).length < 2 ^ (prefixWord ++ tailWord_3416189).sum := by decide
  have hdescent : baseEnd_3416189 < baseStart_3416189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416249 : List Nat := [1, 2, 1, 4, 1, 2, 1, 1, 3, 6]
def baseStart_3416249 : Nat := 118140960795 + 3416249 * 2 ^ 59
def prefixEnd_3416249 : Nat := 4983230072969 + 3 ^ 40 * 3416249 * 2
def baseEnd_3416249 : Nat := 1169451848294473095850975

theorem tailTrace_3416249 : CollatzResearch.WordTrace tailWord_3416249 prefixEnd_3416249 1169451848294473095850975 := by
  unfold tailWord_3416249
  simp only [CollatzResearch.WordTrace]
  refine ⟨124600837400520796723571801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83067224933680531149047867 124600837400520796723571801)
  ·
    refine ⟨93450628050390597542678851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124600837400520796723571801 93450628050390597542678851)
    ·
      refine ⟨140175942075585896314018277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93450628050390597542678851 140175942075585896314018277)
      ·
        refine ⟨26282989139172355558878427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140175942075585896314018277 26282989139172355558878427)
        ·
          refine ⟨39424483708758533338317641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26282989139172355558878427 39424483708758533338317641)
          ·
            refine ⟨29568362781568900003738231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39424483708758533338317641 29568362781568900003738231)
            ·
              refine ⟨44352544172353350005607347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29568362781568900003738231 44352544172353350005607347)
              ·
                refine ⟨66528816258530025008411021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44352544172353350005607347 66528816258530025008411021)
                ·
                  refine ⟨24948306096948759378154133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66528816258530025008411021 24948306096948759378154133)
                  ·
                    refine ⟨1169451848294473095850975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24948306096948759378154133 1169451848294473095850975)
                    ·
                      rfl

theorem cell22_3416249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 6].length) (baseStart_3416249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3416249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3416249 prefixEnd_3416249 := by exact prefixLift 3416249
  have htrace : WordTrace (prefixWord ++ tailWord_3416249) baseStart_3416249 baseEnd_3416249 := by
    simpa [prefixWord, tailWord_3416249, baseEnd_3416249] using wordTrace_append hprefix tailTrace_3416249
  have hstable : (prefixWord ++ tailWord_3416249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416249).length < 2 ^ (prefixWord ++ tailWord_3416249).sum := by decide
  have hdescent : baseEnd_3416249 < baseStart_3416249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416266 : List Nat := [3, 1, 2, 1, 3, 1, 2, 3, 2, 4]
def baseStart_3416266 : Nat := 118140960795 + 3416266 * 2 ^ 59
def prefixEnd_3416266 : Nat := 4983230072969 + 3 ^ 40 * 3416266 * 2
def baseEnd_3416266 : Nat := 1169457667741890718175923

theorem tailTrace_3416266 : CollatzResearch.WordTrace tailWord_3416266 prefixEnd_3416266 1169457667741890718175923 := by
  unfold tailWord_3416266
  simp only [CollatzResearch.WordTrace]
  refine ⟨31150364360364802156735163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83067638294306139084627101 31150364360364802156735163)
  ·
    refine ⟨46725546540547203235102745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31150364360364802156735163 46725546540547203235102745)
    ·
      refine ⟨35044159905410402426327059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46725546540547203235102745 35044159905410402426327059)
      ·
        refine ⟨52566239858115603639490589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35044159905410402426327059 52566239858115603639490589)
        ·
          refine ⟨19712339946793351364808971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52566239858115603639490589 19712339946793351364808971)
          ·
            refine ⟨29568509920190027047213457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19712339946793351364808971 29568509920190027047213457)
            ·
              refine ⟨22176382440142520285410093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29568509920190027047213457 22176382440142520285410093)
              ·
                refine ⟨8316143415053445107028785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22176382440142520285410093 8316143415053445107028785)
                ·
                  refine ⟨6237107561290083830271589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8316143415053445107028785 6237107561290083830271589)
                  ·
                    refine ⟨1169457667741890718175923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6237107561290083830271589 1169457667741890718175923)
                    ·
                      rfl

theorem cell22_3416266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 3, 2, 4].length) (baseStart_3416266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3416266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3416266 prefixEnd_3416266 := by exact prefixLift 3416266
  have htrace : WordTrace (prefixWord ++ tailWord_3416266) baseStart_3416266 baseEnd_3416266 := by
    simpa [prefixWord, tailWord_3416266, baseEnd_3416266] using wordTrace_append hprefix tailTrace_3416266
  have hstable : (prefixWord ++ tailWord_3416266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416266).length < 2 ^ (prefixWord ++ tailWord_3416266).sum := by decide
  have hdescent : baseEnd_3416266 < baseStart_3416266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416270 : List Nat := [4, 1, 1, 1, 4, 3, 1, 3, 4]
def baseStart_3416270 : Nat := 118140960795 + 3416270 * 2 ^ 59
def prefixEnd_3416270 : Nat := 4983230072969 + 3 ^ 40 * 3416270 * 2
def baseEnd_3416270 : Nat := 389819679007878680358637

theorem tailTrace_3416270 : CollatzResearch.WordTrace tailWord_3416270 prefixEnd_3416270 389819679007878680358637 := by
  unfold tailWord_3416270
  simp only [CollatzResearch.WordTrace]
  refine ⟨15575200416680589663760783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83067735555629811540057509 15575200416680589663760783)
  ·
    refine ⟨23362800625020884495641175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15575200416680589663760783 23362800625020884495641175)
    ·
      refine ⟨35044200937531326743461763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23362800625020884495641175 35044200937531326743461763)
      ·
        refine ⟨52566301406296990115192645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35044200937531326743461763 52566301406296990115192645)
        ·
          refine ⟨9856181513680685646598621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52566301406296990115192645 9856181513680685646598621)
          ·
            refine ⟨3696068067630257117474483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9856181513680685646598621 3696068067630257117474483)
            ·
              refine ⟨5544102101445385676211725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3696068067630257117474483 5544102101445385676211725)
              ·
                refine ⟨2079038288042019628579397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5544102101445385676211725 2079038288042019628579397)
                ·
                  refine ⟨389819679007878680358637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2079038288042019628579397 389819679007878680358637)
                  ·
                    rfl

theorem cell22_3416270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 3, 4].length) (baseStart_3416270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3416270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3416270 prefixEnd_3416270 := by exact prefixLift 3416270
  have htrace : WordTrace (prefixWord ++ tailWord_3416270) baseStart_3416270 baseEnd_3416270 := by
    simpa [prefixWord, tailWord_3416270, baseEnd_3416270] using wordTrace_append hprefix tailTrace_3416270
  have hstable : (prefixWord ++ tailWord_3416270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416270).length < 2 ^ (prefixWord ++ tailWord_3416270).sum := by decide
  have hdescent : baseEnd_3416270 < baseStart_3416270 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416343 : List Nat := [1, 1, 3, 4, 1, 3, 2, 2, 5]
def baseStart_3416343 : Nat := 118140960795 + 3416343 * 2 ^ 59
def prefixEnd_3416343 : Nat := 4983230072969 + 3 ^ 40 * 3416343 * 2
def baseEnd_3416343 : Nat := 389828008805162728000229

theorem tailTrace_3416343 : CollatzResearch.WordTrace tailWord_3416343 prefixEnd_3416343 389828008805162728000229 := by
  unfold tailWord_3416343
  simp only [CollatzResearch.WordTrace]
  refine ⟨124604265862180250777493683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83069510574786833851662455 124604265862180250777493683)
  ·
    refine ⟨186906398793270376166240525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124604265862180250777493683 186906398793270376166240525)
    ·
      refine ⟨70089899547476391062340197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186906398793270376166240525 70089899547476391062340197)
      ·
        refine ⟨13141856165151823324188787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70089899547476391062340197 13141856165151823324188787)
        ·
          refine ⟨19712784247727734986283181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13141856165151823324188787 19712784247727734986283181)
          ·
            refine ⟨7392294092897900619856193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19712784247727734986283181 7392294092897900619856193)
            ·
              refine ⟨5544220569673425464892145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7392294092897900619856193 5544220569673425464892145)
              ·
                refine ⟨4158165427255069098669109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5544220569673425464892145 4158165427255069098669109)
                ·
                  refine ⟨389828008805162728000229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4158165427255069098669109 389828008805162728000229)
                  ·
                    rfl

theorem cell22_3416343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 2, 5].length) (baseStart_3416343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3416343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3416343 prefixEnd_3416343 := by exact prefixLift 3416343
  have htrace : WordTrace (prefixWord ++ tailWord_3416343) baseStart_3416343 baseEnd_3416343 := by
    simpa [prefixWord, tailWord_3416343, baseEnd_3416343] using wordTrace_append hprefix tailTrace_3416343
  have hstable : (prefixWord ++ tailWord_3416343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416343).length < 2 ^ (prefixWord ++ tailWord_3416343).sum := by decide
  have hdescent : baseEnd_3416343 < baseStart_3416343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416371 : List Nat := [1, 1, 1, 2, 5, 1, 3, 2, 6]
def baseStart_3416371 : Nat := 118140960795 + 3416371 * 2 ^ 59
def prefixEnd_3416371 : Nat := 4983230072969 + 3 ^ 40 * 3416371 * 2
def baseEnd_3416371 : Nat := 389831203795901814766867

theorem tailTrace_3416371 : CollatzResearch.WordTrace tailWord_3416371 prefixEnd_3416371 389831203795901814766867 := by
  unfold tailWord_3416371
  simp only [CollatzResearch.WordTrace]
  refine ⟨124605287106078811559512967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83070191404052541039675311 124605287106078811559512967)
  ·
    refine ⟨186907930659118217339269451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124605287106078811559512967 186907930659118217339269451)
    ·
      refine ⟨280361895988677326008904177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186907930659118217339269451 280361895988677326008904177)
      ·
        refine ⟨210271421991507994506678133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280361895988677326008904177 210271421991507994506678133)
        ·
          refine ⟨19712945811703874485001075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 210271421991507994506678133 19712945811703874485001075)
          ·
            refine ⟨29569418717555811727501613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19712945811703874485001075 29569418717555811727501613)
            ·
              refine ⟨11088532019083429397813105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29569418717555811727501613 11088532019083429397813105)
              ·
                refine ⟨8316399014312572048359829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11088532019083429397813105 8316399014312572048359829)
                ·
                  refine ⟨389831203795901814766867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8316399014312572048359829 389831203795901814766867)
                  ·
                    rfl

theorem cell22_3416371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 2, 6].length) (baseStart_3416371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3416371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3416371 prefixEnd_3416371 := by exact prefixLift 3416371
  have htrace : WordTrace (prefixWord ++ tailWord_3416371) baseStart_3416371 baseEnd_3416371 := by
    simpa [prefixWord, tailWord_3416371, baseEnd_3416371] using wordTrace_append hprefix tailTrace_3416371
  have hstable : (prefixWord ++ tailWord_3416371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416371).length < 2 ^ (prefixWord ++ tailWord_3416371).sum := by decide
  have hdescent : baseEnd_3416371 < baseStart_3416371 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416373 : List Nat := [1, 3, 3, 1, 2, 1, 2, 4, 1, 4]
def baseStart_3416373 : Nat := 118140960795 + 3416373 * 2 ^ 59
def prefixEnd_3416373 : Nat := 4983230072969 + 3 ^ 40 * 3416373 * 2
def baseEnd_3416373 : Nat := 1169494296028578105750595

theorem tailTrace_3416373 : CollatzResearch.WordTrace tailWord_3416373 prefixEnd_3416373 1169494296028578105750595 := by
  unfold tailWord_3416373
  simp only [CollatzResearch.WordTrace]
  refine ⟨124605360052071565901085773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83070240034714377267390515 124605360052071565901085773)
  ·
    refine ⟨46727010019526837212907165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124605360052071565901085773 46727010019526837212907165)
    ·
      refine ⟨17522628757322563954840187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46727010019526837212907165 17522628757322563954840187)
      ·
        refine ⟨26283943135983845932260281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17522628757322563954840187 26283943135983845932260281)
        ·
          refine ⟨19712957351987884449195211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26283943135983845932260281 19712957351987884449195211)
          ·
            refine ⟨29569436027981826673792817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19712957351987884449195211 29569436027981826673792817)
            ·
              refine ⟨22177077020986370005344613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29569436027981826673792817 22177077020986370005344613)
              ·
                refine ⟨4158201941434944376002115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22177077020986370005344613 4158201941434944376002115)
                ·
                  refine ⟨6237302912152416564003173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4158201941434944376002115 6237302912152416564003173)
                  ·
                    refine ⟨1169494296028578105750595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6237302912152416564003173 1169494296028578105750595)
                    ·
                      rfl

theorem cell22_3416373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_3416373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3416373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3416373 prefixEnd_3416373 := by exact prefixLift 3416373
  have htrace : WordTrace (prefixWord ++ tailWord_3416373) baseStart_3416373 baseEnd_3416373 := by
    simpa [prefixWord, tailWord_3416373, baseEnd_3416373] using wordTrace_append hprefix tailTrace_3416373
  have hstable : (prefixWord ++ tailWord_3416373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416373).length < 2 ^ (prefixWord ++ tailWord_3416373).sum := by decide
  have hdescent : baseEnd_3416373 < baseStart_3416373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416403 : List Nat := [1, 1, 1, 2, 1, 1, 4, 6, 2, 3]
def baseStart_3416403 : Nat := 118140960795 + 3416403 * 2 ^ 59
def prefixEnd_3416403 : Nat := 4983230072969 + 3 ^ 40 * 3416403 * 2
def baseEnd_3416403 : Nat := 1169504565641668027500503

theorem tailTrace_3416403 : CollatzResearch.WordTrace tailWord_3416403 prefixEnd_3416403 1169504565641668027500503 := by
  unfold tailWord_3416403
  simp only [CollatzResearch.WordTrace]
  refine ⟨124606454241962881024677863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83070969494641920683118575 124606454241962881024677863)
  ·
    refine ⟨186909681362944321537016795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124606454241962881024677863 186909681362944321537016795)
    ·
      refine ⟨280364522044416482305525193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186909681362944321537016795 280364522044416482305525193)
      ·
        refine ⟨210273391533312361729143895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280364522044416482305525193 210273391533312361729143895)
        ·
          refine ⟨315410087299968542593715843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210273391533312361729143895 315410087299968542593715843)
          ·
            refine ⟨473115130949952813890573765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315410087299968542593715843 473115130949952813890573765)
            ·
              refine ⟨88709087053116152604482581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 473115130949952813890573765 88709087053116152604482581)
              ·
                refine ⟨4158238455614819653335121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 88709087053116152604482581 4158238455614819653335121)
                ·
                  refine ⟨3118678841711114740001341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4158238455614819653335121 3118678841711114740001341)
                  ·
                    refine ⟨1169504565641668027500503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3118678841711114740001341 1169504565641668027500503)
                    ·
                      rfl

theorem cell22_3416403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 6, 2, 3].length) (baseStart_3416403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3416403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3416403 prefixEnd_3416403 := by exact prefixLift 3416403
  have htrace : WordTrace (prefixWord ++ tailWord_3416403) baseStart_3416403 baseEnd_3416403 := by
    simpa [prefixWord, tailWord_3416403, baseEnd_3416403] using wordTrace_append hprefix tailTrace_3416403
  have hstable : (prefixWord ++ tailWord_3416403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416403).length < 2 ^ (prefixWord ++ tailWord_3416403).sum := by decide
  have hdescent : baseEnd_3416403 < baseStart_3416403 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416418 : List Nat := [3, 3, 2, 1, 1, 2, 1, 2, 1, 6]
def baseStart_3416418 : Nat := 118140960795 + 3416418 * 2 ^ 59
def prefixEnd_3416418 : Nat := 4983230072969 + 3 ^ 40 * 3416418 * 2
def baseEnd_3416418 : Nat := 1169509700448212988375457

theorem tailTrace_3416418 : CollatzResearch.WordTrace tailWord_3416418 prefixEnd_3416418 1169509700448212988375457 := by
  unfold tailWord_3416418
  simp only [CollatzResearch.WordTrace]
  refine ⟨31151750334227134646618477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83071334224605692390982605 31151750334227134646618477)
  ·
    refine ⟨11681906375335175492481929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31151750334227134646618477 11681906375335175492481929)
    ·
      refine ⟨8761429781501381619361447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11681906375335175492481929 8761429781501381619361447)
      ·
        refine ⟨13142144672252072429042171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8761429781501381619361447 13142144672252072429042171)
        ·
          refine ⟨19713217008378108643563257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13142144672252072429042171 19713217008378108643563257)
          ·
            refine ⟨14784912756283581482672443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19713217008378108643563257 14784912756283581482672443)
            ·
              refine ⟨22177369134425372224008665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14784912756283581482672443 22177369134425372224008665)
              ·
                refine ⟨16633026850819029168006499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22177369134425372224008665 16633026850819029168006499)
                ·
                  refine ⟨24949540276228543752009749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16633026850819029168006499 24949540276228543752009749)
                  ·
                    refine ⟨1169509700448212988375457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24949540276228543752009749 1169509700448212988375457)
                    ·
                      rfl

theorem cell22_3416418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_3416418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3416418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3416418 prefixEnd_3416418 := by exact prefixLift 3416418
  have htrace : WordTrace (prefixWord ++ tailWord_3416418) baseStart_3416418 baseEnd_3416418 := by
    simpa [prefixWord, tailWord_3416418, baseEnd_3416418] using wordTrace_append hprefix tailTrace_3416418
  have hstable : (prefixWord ++ tailWord_3416418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416418).length < 2 ^ (prefixWord ++ tailWord_3416418).sum := by decide
  have hdescent : baseEnd_3416418 < baseStart_3416418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416553 : List Nat := [1, 2, 1, 1, 1, 2, 1, 7, 2, 4]
def baseStart_3416553 : Nat := 118140960795 + 3416553 * 2 ^ 59
def prefixEnd_3416553 : Nat := 4983230072969 + 3 ^ 40 * 3416553 * 2
def baseEnd_3416553 : Nat := 1169555913707117636250043

theorem tailTrace_3416553 : CollatzResearch.WordTrace tailWord_3416553 prefixEnd_3416553 1169555913707117636250043 := by
  unfold tailWord_3416553
  simp only [CollatzResearch.WordTrace]
  refine ⟨124611925191419456642638313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83074616794279637761758875 124611925191419456642638313)
  ·
    refine ⟨93458943893564592481978735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124611925191419456642638313 93458943893564592481978735)
    ·
      refine ⟨140188415840346888722968103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93458943893564592481978735 140188415840346888722968103)
      ·
        refine ⟨210282623760520333084452155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140188415840346888722968103 210282623760520333084452155)
        ·
          refine ⟨315423935640780499626678233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210282623760520333084452155 315423935640780499626678233)
          ·
            refine ⟨236567951730585374720008675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 315423935640780499626678233 236567951730585374720008675)
            ·
              refine ⟨354851927595878062080013013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236567951730585374720008675 354851927595878062080013013)
              ·
                refine ⟨8316842053028392080000305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 354851927595878062080013013 8316842053028392080000305)
                ·
                  refine ⟨6237631539771294060000229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8316842053028392080000305 6237631539771294060000229)
                  ·
                    refine ⟨1169555913707117636250043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6237631539771294060000229 1169555913707117636250043)
                    ·
                      rfl

theorem cell22_3416553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 7, 2, 4].length) (baseStart_3416553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3416553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3416553 prefixEnd_3416553 := by exact prefixLift 3416553
  have htrace : WordTrace (prefixWord ++ tailWord_3416553) baseStart_3416553 baseEnd_3416553 := by
    simpa [prefixWord, tailWord_3416553, baseEnd_3416553] using wordTrace_append hprefix tailTrace_3416553
  have hstable : (prefixWord ++ tailWord_3416553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416553).length < 2 ^ (prefixWord ++ tailWord_3416553).sum := by decide
  have hdescent : baseEnd_3416553 < baseStart_3416553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416557 : List Nat := [1, 5, 1, 3, 1, 1, 1, 5, 4]
def baseStart_3416557 : Nat := 118140960795 + 3416557 * 2 ^ 59
def prefixEnd_3416557 : Nat := 4983230072969 + 3 ^ 40 * 3416557 * 2
def baseEnd_3416557 : Nat := 389852427662954319716677

theorem tailTrace_3416557 : CollatzResearch.WordTrace tailWord_3416557 prefixEnd_3416557 389852427662954319716677 := by
  unfold tailWord_3416557
  simp only [CollatzResearch.WordTrace]
  refine ⟨124612071083404965325783925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83074714055603310217189283 124612071083404965325783925)
  ·
    refine ⟨11682381664069215499292243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 124612071083404965325783925 11682381664069215499292243)
    ·
      refine ⟨17523572496103823248938365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11682381664069215499292243 17523572496103823248938365)
      ·
        refine ⟨6571339686038933718351887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17523572496103823248938365 6571339686038933718351887)
        ·
          refine ⟨9857009529058400577527831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6571339686038933718351887 9857009529058400577527831)
          ·
            refine ⟨14785514293587600866291747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9857009529058400577527831 14785514293587600866291747)
            ·
              refine ⟨22178271440381401299437621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14785514293587600866291747 22178271440381401299437621)
              ·
                refine ⟨2079212947535756371822277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22178271440381401299437621 2079212947535756371822277)
                ·
                  refine ⟨389852427662954319716677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2079212947535756371822277 389852427662954319716677)
                  ·
                    rfl

theorem cell22_3416557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 5, 4].length) (baseStart_3416557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3416557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3416557 prefixEnd_3416557 := by exact prefixLift 3416557
  have htrace : WordTrace (prefixWord ++ tailWord_3416557) baseStart_3416557 baseEnd_3416557 := by
    simpa [prefixWord, tailWord_3416557, baseEnd_3416557] using wordTrace_append hprefix tailTrace_3416557
  have hstable : (prefixWord ++ tailWord_3416557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416557).length < 2 ^ (prefixWord ++ tailWord_3416557).sum := by decide
  have hdescent : baseEnd_3416557 < baseStart_3416557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416589 : List Nat := [1, 7, 1, 1, 1, 1, 3, 1, 1, 5]
def baseStart_3416589 : Nat := 118140960795 + 3416589 * 2 ^ 59
def prefixEnd_3416589 : Nat := 4983230072969 + 3 ^ 40 * 3416589 * 2
def baseEnd_3416589 : Nat := 1169568237242825542349933

theorem tailTrace_3416589 : CollatzResearch.WordTrace tailWord_3416589 prefixEnd_3416589 1169568237242825542349933 := by
  unfold tailWord_3416589
  simp only [CollatzResearch.WordTrace]
  refine ⟨124613238219289034790948821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83075492146192689860632547 124613238219289034790948821)
  ·
    refine ⟨2920622770764586752912863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 124613238219289034790948821 2920622770764586752912863)
    ·
      refine ⟨4380934156146880129369295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2920622770764586752912863 4380934156146880129369295)
      ·
        refine ⟨6571401234220320194053943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4380934156146880129369295 6571401234220320194053943)
        ·
          refine ⟨9857101851330480291080915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6571401234220320194053943 9857101851330480291080915)
          ·
            refine ⟨14785652776995720436621373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9857101851330480291080915 14785652776995720436621373)
            ·
              refine ⟨5544619791373395163733015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14785652776995720436621373 5544619791373395163733015)
              ·
                refine ⟨8316929687060092745599523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5544619791373395163733015 8316929687060092745599523)
                ·
                  refine ⟨12475394530590139118399285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8316929687060092745599523 12475394530590139118399285)
                  ·
                    refine ⟨1169568237242825542349933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12475394530590139118399285 1169568237242825542349933)
                    ·
                      rfl

theorem cell22_3416589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_3416589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3416589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3416589 prefixEnd_3416589 := by exact prefixLift 3416589
  have htrace : WordTrace (prefixWord ++ tailWord_3416589) baseStart_3416589 baseEnd_3416589 := by
    simpa [prefixWord, tailWord_3416589, baseEnd_3416589] using wordTrace_append hprefix tailTrace_3416589
  have hstable : (prefixWord ++ tailWord_3416589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416589).length < 2 ^ (prefixWord ++ tailWord_3416589).sum := by decide
  have hdescent : baseEnd_3416589 < baseStart_3416589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416613 : List Nat := [1, 3, 1, 2, 2, 1, 3, 2, 7]
def baseStart_3416613 : Nat := 118140960795 + 3416613 * 2 ^ 59
def prefixEnd_3416613 : Nat := 4983230072969 + 3 ^ 40 * 3416613 * 2
def baseEnd_3416613 : Nat := 389858817644432493249953

theorem tailTrace_3416613 : CollatzResearch.WordTrace tailWord_3416613 prefixEnd_3416613 389858817644432493249953 := by
  unfold tailWord_3416613
  simp only [CollatzResearch.WordTrace]
  refine ⟨124614113571202086889822493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83076075714134724593214995 124614113571202086889822493)
  ·
    refine ⟨46730292589200782583683435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124614113571202086889822493 46730292589200782583683435)
    ·
      refine ⟨70095438883801173875525153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46730292589200782583683435 70095438883801173875525153)
      ·
        refine ⟨52571579162850880406643865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70095438883801173875525153 52571579162850880406643865)
        ·
          refine ⟨39428684372138160304982899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52571579162850880406643865 39428684372138160304982899)
          ·
            refine ⟨59143026558207240457474349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39428684372138160304982899 59143026558207240457474349)
            ·
              refine ⟨22178634959327715171552881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59143026558207240457474349 22178634959327715171552881)
              ·
                refine ⟨16633976219495786378664661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22178634959327715171552881 16633976219495786378664661)
                ·
                  refine ⟨389858817644432493249953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16633976219495786378664661 389858817644432493249953)
                  ·
                    rfl

theorem cell22_3416613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 7].length) (baseStart_3416613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3416613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3416613 prefixEnd_3416613 := by exact prefixLift 3416613
  have htrace : WordTrace (prefixWord ++ tailWord_3416613) baseStart_3416613 baseEnd_3416613 := by
    simpa [prefixWord, tailWord_3416613, baseEnd_3416613] using wordTrace_append hprefix tailTrace_3416613
  have hstable : (prefixWord ++ tailWord_3416613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416613).length < 2 ^ (prefixWord ++ tailWord_3416613).sum := by decide
  have hdescent : baseEnd_3416613 < baseStart_3416613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416621 : List Nat := [1, 5, 4, 1, 1, 1, 1, 2, 2, 4]
def baseStart_3416621 : Nat := 118140960795 + 3416621 * 2 ^ 59
def prefixEnd_3416621 : Nat := 4983230072969 + 3 ^ 40 * 3416621 * 2
def baseEnd_3416621 : Nat := 1169579191496788125549835

theorem tailTrace_3416621 : CollatzResearch.WordTrace tailWord_3416621 prefixEnd_3416621 1169579191496788125549835 := by
  unfold tailWord_3416621
  simp only [CollatzResearch.WordTrace]
  refine ⟨124614405355173104256113717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83076270236782069504075811 124614405355173104256113717)
  ·
    refine ⟨11682600502047478524010661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 124614405355173104256113717 11682600502047478524010661)
    ·
      refine ⟨2190487594133902223251999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11682600502047478524010661 2190487594133902223251999)
      ·
        refine ⟨3285731391200853334877999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2190487594133902223251999 3285731391200853334877999)
        ·
          refine ⟨4928597086801280002316999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3285731391200853334877999 4928597086801280002316999)
          ·
            refine ⟨7392895630201920003475499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4928597086801280002316999 7392895630201920003475499)
            ·
              refine ⟨11089343445302880005213249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7392895630201920003475499 11089343445302880005213249)
              ·
                refine ⟨8317007583977160003909937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11089343445302880005213249 8317007583977160003909937)
                ·
                  refine ⟨6237755687982870002932453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8317007583977160003909937 6237755687982870002932453)
                  ·
                    refine ⟨1169579191496788125549835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6237755687982870002932453 1169579191496788125549835)
                    ·
                      rfl

theorem cell22_3416621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_3416621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3416621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3416621 prefixEnd_3416621 := by exact prefixLift 3416621
  have htrace : WordTrace (prefixWord ++ tailWord_3416621) baseStart_3416621 baseEnd_3416621 := by
    simpa [prefixWord, tailWord_3416621, baseEnd_3416621] using wordTrace_append hprefix tailTrace_3416621
  have hstable : (prefixWord ++ tailWord_3416621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416621).length < 2 ^ (prefixWord ++ tailWord_3416621).sum := by decide
  have hdescent : baseEnd_3416621 < baseStart_3416621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416647 : List Nat := [1, 1, 4, 1, 4, 1, 4, 1, 5]
def baseStart_3416647 : Nat := 118140960795 + 3416647 * 2 ^ 59
def prefixEnd_3416647 : Nat := 4983230072969 + 3 ^ 40 * 3416647 * 2
def baseEnd_3416647 : Nat := 389862697276044241466585

theorem tailTrace_3416647 : CollatzResearch.WordTrace tailWord_3416647 prefixEnd_3416647 389862697276044241466585 := by
  unfold tailWord_3416647
  simp only [CollatzResearch.WordTrace]
  refine ⟨124615353653078910696560195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83076902435385940464373463 124615353653078910696560195)
  ·
    refine ⟨186923030479618366044840293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124615353653078910696560195 186923030479618366044840293)
    ·
      refine ⟨35048068214928443633407555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 186923030479618366044840293 35048068214928443633407555)
      ·
        refine ⟨52572102322392665450111333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35048068214928443633407555 52572102322392665450111333)
        ·
          refine ⟨9857269185448624771895875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52572102322392665450111333 9857269185448624771895875)
          ·
            refine ⟨14785903778172937157843813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9857269185448624771895875 14785903778172937157843813)
            ·
              refine ⟨2772356958407425717095715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14785903778172937157843813 2772356958407425717095715)
              ·
                refine ⟨4158535437611138575643573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2772356958407425717095715 4158535437611138575643573)
                ·
                  refine ⟨389862697276044241466585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4158535437611138575643573 389862697276044241466585)
                  ·
                    rfl

theorem cell22_3416647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 4, 1, 5].length) (baseStart_3416647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3416647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3416647 prefixEnd_3416647 := by exact prefixLift 3416647
  have htrace : WordTrace (prefixWord ++ tailWord_3416647) baseStart_3416647 baseEnd_3416647 := by
    simpa [prefixWord, tailWord_3416647, baseEnd_3416647] using wordTrace_append hprefix tailTrace_3416647
  have hstable : (prefixWord ++ tailWord_3416647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416647).length < 2 ^ (prefixWord ++ tailWord_3416647).sum := by decide
  have hdescent : baseEnd_3416647 < baseStart_3416647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416703 : List Nat := [1, 1, 2, 2, 1, 1, 1, 13]
def baseStart_3416703 : Nat := 118140960795 + 3416703 * 2 ^ 59
def prefixEnd_3416703 : Nat := 4983230072969 + 3 ^ 40 * 3416703 * 2
def baseEnd_3416703 : Nat := 129956362419174138333287

theorem tailTrace_3416703 : CollatzResearch.WordTrace tailWord_3416703 prefixEnd_3416703 129956362419174138333287 := by
  unfold tailWord_3416703
  simp only [CollatzResearch.WordTrace]
  refine ⟨124617396140876032260598763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83078264093917354840399175 124617396140876032260598763)
  ·
    refine ⟨186926094211314048390898145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124617396140876032260598763 186926094211314048390898145)
    ·
      refine ⟨140194570658485536293173609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186926094211314048390898145 140194570658485536293173609)
      ·
        refine ⟨105145927993864152219880207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140194570658485536293173609 105145927993864152219880207)
        ·
          refine ⟨157718891990796228329820311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105145927993864152219880207 157718891990796228329820311)
          ·
            refine ⟨236578337986194342494730467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157718891990796228329820311 236578337986194342494730467)
            ·
              refine ⟨354867506979291513742095701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236578337986194342494730467 354867506979291513742095701)
              ·
                refine ⟨129956362419174138333287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 354867506979291513742095701 129956362419174138333287)
                ·
                  rfl

theorem cell22_3416703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 13].length) (baseStart_3416703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3416703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3416703 prefixEnd_3416703 := by exact prefixLift 3416703
  have htrace : WordTrace (prefixWord ++ tailWord_3416703) baseStart_3416703 baseEnd_3416703 := by
    simpa [prefixWord, tailWord_3416703, baseEnd_3416703] using wordTrace_append hprefix tailTrace_3416703
  have hstable : (prefixWord ++ tailWord_3416703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416703).length < 2 ^ (prefixWord ++ tailWord_3416703).sum := by decide
  have hdescent : baseEnd_3416703 < baseStart_3416703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416705 : List Nat := [1, 2, 4, 2, 1, 1, 2, 2, 1, 6]
def baseStart_3416705 : Nat := 118140960795 + 3416705 * 2 ^ 59
def prefixEnd_3416705 : Nat := 4983230072969 + 3 ^ 40 * 3416705 * 2
def baseEnd_3416705 : Nat := 1169607946413439906449577

theorem tailTrace_3416705 : CollatzResearch.WordTrace tailWord_3416705 prefixEnd_3416705 1169607946413439906449577 := by
  unfold tailWord_3416705
  simp only [CollatzResearch.WordTrace]
  refine ⟨124617469086868786602171569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83078312724579191068114379 124617469086868786602171569)
  ·
    refine ⟨93463101815151589951628677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124617469086868786602171569 93463101815151589951628677)
    ·
      refine ⟨17524331590340923115930377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93463101815151589951628677 17524331590340923115930377)
      ·
        refine ⟨13143248692755692336947783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17524331590340923115930377 13143248692755692336947783)
        ·
          refine ⟨19714873039133538505421675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13143248692755692336947783 19714873039133538505421675)
          ·
            refine ⟨29572309558700307758132513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19714873039133538505421675 29572309558700307758132513)
            ·
              refine ⟨22179232169025230818599385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29572309558700307758132513 22179232169025230818599385)
              ·
                refine ⟨16634424126768923113949539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22179232169025230818599385 16634424126768923113949539)
                ·
                  refine ⟨24951636190153384670924309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16634424126768923113949539 24951636190153384670924309)
                  ·
                    refine ⟨1169607946413439906449577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24951636190153384670924309 1169607946413439906449577)
                    ·
                      rfl

theorem cell22_3416705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_3416705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3416705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3416705 prefixEnd_3416705 := by exact prefixLift 3416705
  have htrace : WordTrace (prefixWord ++ tailWord_3416705) baseStart_3416705 baseEnd_3416705 := by
    simpa [prefixWord, tailWord_3416705, baseEnd_3416705] using wordTrace_append hprefix tailTrace_3416705
  have hstable : (prefixWord ++ tailWord_3416705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416705).length < 2 ^ (prefixWord ++ tailWord_3416705).sum := by decide
  have hdescent : baseEnd_3416705 < baseStart_3416705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416707 : List Nat := [1, 1, 1, 3, 3, 1, 4, 3, 2, 3]
def baseStart_3416707 : Nat := 118140960795 + 3416707 * 2 ^ 59
def prefixEnd_3416707 : Nat := 4983230072969 + 3 ^ 40 * 3416707 * 2
def baseEnd_3416707 : Nat := 1169608631054312567899571

theorem tailTrace_3416707 : CollatzResearch.WordTrace tailWord_3416707 prefixEnd_3416707 1169608631054312567899571 := by
  unfold tailWord_3416707
  simp only [CollatzResearch.WordTrace]
  refine ⟨124617542032861540943744375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83078361355241027295829583 124617542032861540943744375)
  ·
    refine ⟨186926313049292311415616563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124617542032861540943744375 186926313049292311415616563)
    ·
      refine ⟨280389469573938467123424845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186926313049292311415616563 280389469573938467123424845)
      ·
        refine ⟨105146051090226925171284317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 280389469573938467123424845 105146051090226925171284317)
        ·
          refine ⟨39429769158835096939231619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105146051090226925171284317 39429769158835096939231619)
          ·
            refine ⟨59144653738252645408847429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39429769158835096939231619 59144653738252645408847429)
            ·
              refine ⟨11089622575922371014158893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59144653738252645408847429 11089622575922371014158893)
              ·
                refine ⟨4158608465970889130309585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11089622575922371014158893 4158608465970889130309585)
                ·
                  refine ⟨3118956349478166847732189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4158608465970889130309585 3118956349478166847732189)
                  ·
                    refine ⟨1169608631054312567899571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3118956349478166847732189 1169608631054312567899571)
                    ·
                      rfl

theorem cell22_3416707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 3, 2, 3].length) (baseStart_3416707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3416707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3416707 prefixEnd_3416707 := by exact prefixLift 3416707
  have htrace : WordTrace (prefixWord ++ tailWord_3416707) baseStart_3416707 baseEnd_3416707 := by
    simpa [prefixWord, tailWord_3416707, baseEnd_3416707] using wordTrace_append hprefix tailTrace_3416707
  have hstable : (prefixWord ++ tailWord_3416707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416707).length < 2 ^ (prefixWord ++ tailWord_3416707).sum := by decide
  have hdescent : baseEnd_3416707 < baseStart_3416707 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416722 : List Nat := [3, 2, 3, 1, 2, 2, 1, 1, 1, 6]
def baseStart_3416722 : Nat := 118140960795 + 3416722 * 2 ^ 59
def prefixEnd_3416722 : Nat := 4983230072969 + 3 ^ 40 * 3416722 * 2
def baseEnd_3416722 : Nat := 1169613765860857528774525

theorem tailTrace_3416722 : CollatzResearch.WordTrace tailWord_3416722 prefixEnd_3416722 1169613765860857528774525 := by
  unfold tailWord_3416722
  simp only [CollatzResearch.WordTrace]
  refine ⟨31154522281951799626385105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83078726085204799003693613 31154522281951799626385105)
  ·
    refine ⟨23365891711463849719788829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31154522281951799626385105 23365891711463849719788829)
    ·
      refine ⟨8762209391798943644920811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23365891711463849719788829 8762209391798943644920811)
      ·
        refine ⟨13143314087698415467381217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8762209391798943644920811 13143314087698415467381217)
        ·
          refine ⟨9857485565773811600535913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13143314087698415467381217 9857485565773811600535913)
          ·
            refine ⟨7393114174330358700401935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9857485565773811600535913 7393114174330358700401935)
            ·
              refine ⟨11089671261495538050602903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7393114174330358700401935 11089671261495538050602903)
              ·
                refine ⟨16634506892243307075904355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11089671261495538050602903 16634506892243307075904355)
                ·
                  refine ⟨24951760338364960613856533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16634506892243307075904355 24951760338364960613856533)
                  ·
                    refine ⟨1169613765860857528774525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24951760338364960613856533 1169613765860857528774525)
                    ·
                      rfl

theorem cell22_3416722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_3416722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3416722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3416722 prefixEnd_3416722 := by exact prefixLift 3416722
  have htrace : WordTrace (prefixWord ++ tailWord_3416722) baseStart_3416722 baseEnd_3416722 := by
    simpa [prefixWord, tailWord_3416722, baseEnd_3416722] using wordTrace_append hprefix tailTrace_3416722
  have hstable : (prefixWord ++ tailWord_3416722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416722).length < 2 ^ (prefixWord ++ tailWord_3416722).sum := by decide
  have hdescent : baseEnd_3416722 < baseStart_3416722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416758 : List Nat := [5, 1, 3, 1, 3, 1, 1, 1, 1, 5]
def baseStart_3416758 : Nat := 118140960795 + 3416758 * 2 ^ 59
def prefixEnd_3416758 : Nat := 4983230072969 + 3 ^ 40 * 3416758 * 2
def baseEnd_3416758 : Nat := 1169626089396565434874415

theorem tailTrace_3416758 : CollatzResearch.WordTrace tailWord_3416758 prefixEnd_3416758 1169626089396565434874415 := by
  unfold tailWord_3416758
  simp only [CollatzResearch.WordTrace]
  refine ⟨7788712634729798540865683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83079601437117851102567285 7788712634729798540865683)
  ·
    refine ⟨11683068952094697811298525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7788712634729798540865683 11683068952094697811298525)
    ·
      refine ⟨4381150857035511679236947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11683068952094697811298525 4381150857035511679236947)
      ·
        refine ⟨6571726285553267518855421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4381150857035511679236947 6571726285553267518855421)
        ·
          refine ⟨2464397357082475319570783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6571726285553267518855421 2464397357082475319570783)
          ·
            refine ⟨3696596035623712979356175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2464397357082475319570783 3696596035623712979356175)
            ·
              refine ⟨5544894053435569469034263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3696596035623712979356175 5544894053435569469034263)
              ·
                refine ⟨8317341080153354203551395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5544894053435569469034263 8317341080153354203551395)
                ·
                  refine ⟨12476011620230031305327093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8317341080153354203551395 12476011620230031305327093)
                  ·
                    refine ⟨1169626089396565434874415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12476011620230031305327093 1169626089396565434874415)
                    ·
                      rfl

theorem cell22_3416758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_3416758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3416758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3416758 prefixEnd_3416758 := by exact prefixLift 3416758
  have htrace : WordTrace (prefixWord ++ tailWord_3416758) baseStart_3416758 baseEnd_3416758 := by
    simpa [prefixWord, tailWord_3416758, baseEnd_3416758] using wordTrace_append hprefix tailTrace_3416758
  have hstable : (prefixWord ++ tailWord_3416758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416758).length < 2 ^ (prefixWord ++ tailWord_3416758).sum := by decide
  have hdescent : baseEnd_3416758 < baseStart_3416758 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416803 : List Nat := [1, 1, 1, 7, 1, 2, 3, 2, 1, 3]
def baseStart_3416803 : Nat := 118140960795 + 3416803 * 2 ^ 59
def prefixEnd_3416803 : Nat := 4983230072969 + 3 ^ 40 * 3416803 * 2
def baseEnd_3416803 : Nat := 1169641493816200317499277

theorem tailTrace_3416803 : CollatzResearch.WordTrace tailWord_3416803 prefixEnd_3416803 1169641493816200317499277 := by
  unfold tailWord_3416803
  simp only [CollatzResearch.WordTrace]
  refine ⟨124621043440513749339239063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83080695627009166226159375 124621043440513749339239063)
  ·
    refine ⟨186931565160770624008858595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124621043440513749339239063 186931565160770624008858595)
    ·
      refine ⟨280397347741155936013287893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186931565160770624008858595 280397347741155936013287893)
      ·
        refine ⟨6571812837683342250311435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 280397347741155936013287893 6571812837683342250311435)
        ·
          refine ⟨9857719256525013375467153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6571812837683342250311435 9857719256525013375467153)
          ·
            refine ⟨7393289442393760031600365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9857719256525013375467153 7393289442393760031600365)
            ·
              refine ⟨2772483540897660011850137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7393289442393760031600365 2772483540897660011850137)
              ·
                refine ⟨2079362655673245008887603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2772483540897660011850137 2079362655673245008887603)
                ·
                  refine ⟨3119043983509867513331405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2079362655673245008887603 3119043983509867513331405)
                  ·
                    refine ⟨1169641493816200317499277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3119043983509867513331405 1169641493816200317499277)
                    ·
                      rfl

theorem cell22_3416803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 3, 2, 1, 3].length) (baseStart_3416803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3416803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3416803 prefixEnd_3416803 := by exact prefixLift 3416803
  have htrace : WordTrace (prefixWord ++ tailWord_3416803) baseStart_3416803 baseEnd_3416803 := by
    simpa [prefixWord, tailWord_3416803, baseEnd_3416803] using wordTrace_append hprefix tailTrace_3416803
  have hstable : (prefixWord ++ tailWord_3416803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416803).length < 2 ^ (prefixWord ++ tailWord_3416803).sum := by decide
  have hdescent : baseEnd_3416803 < baseStart_3416803 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416825 : List Nat := [1, 2, 1, 3, 1, 1, 1, 2, 5, 5]
def baseStart_3416825 : Nat := 118140960795 + 3416825 * 2 ^ 59
def prefixEnd_3416825 : Nat := 4983230072969 + 3 ^ 40 * 3416825 * 2
def baseEnd_3416825 : Nat := 1169649024865799593449209

theorem tailTrace_3416825 : CollatzResearch.WordTrace tailWord_3416825 prefixEnd_3416825 1169649024865799593449209 := by
  unfold tailWord_3416825
  simp only [CollatzResearch.WordTrace]
  refine ⟨124621845846434047096539929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83081230564289364731026619 124621845846434047096539929)
  ·
    refine ⟨93466384384825535322404947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124621845846434047096539929 93466384384825535322404947)
    ·
      refine ⟨140199576577238302983607421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93466384384825535322404947 140199576577238302983607421)
      ·
        refine ⟨52574841216464363618852783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140199576577238302983607421 52574841216464363618852783)
        ·
          refine ⟨78862261824696545428279175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52574841216464363618852783 78862261824696545428279175)
          ·
            refine ⟨118293392737044818142418763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78862261824696545428279175 118293392737044818142418763)
            ·
              refine ⟨177440089105567227213628145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118293392737044818142418763 177440089105567227213628145)
              ·
                refine ⟨133080066829175420410221109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 177440089105567227213628145 133080066829175420410221109)
                ·
                  refine ⟨12476256265235195663458229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 133080066829175420410221109 12476256265235195663458229)
                  ·
                    refine ⟨1169649024865799593449209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12476256265235195663458229 1169649024865799593449209)
                    ·
                      rfl

theorem cell22_3416825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 5, 5].length) (baseStart_3416825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3416825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3416825 prefixEnd_3416825 := by exact prefixLift 3416825
  have htrace : WordTrace (prefixWord ++ tailWord_3416825) baseStart_3416825 baseEnd_3416825 := by
    simpa [prefixWord, tailWord_3416825, baseEnd_3416825] using wordTrace_append hprefix tailTrace_3416825
  have hstable : (prefixWord ++ tailWord_3416825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416825).length < 2 ^ (prefixWord ++ tailWord_3416825).sum := by decide
  have hdescent : baseEnd_3416825 < baseStart_3416825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416842 : List Nat := [3, 1, 2, 2, 1, 2, 3, 2, 1, 5]
def baseStart_3416842 : Nat := 118140960795 + 3416842 * 2 ^ 59
def prefixEnd_3416842 : Nat := 4983230072969 + 3 ^ 40 * 3416842 * 2
def baseEnd_3416842 : Nat := 1169654844313217215774157

theorem tailTrace_3416842 : CollatzResearch.WordTrace tailWord_3416842 prefixEnd_3416842 1169654844313217215774157 := by
  unfold tailWord_3416842
  simp only [CollatzResearch.WordTrace]
  refine ⟨31155616471843114749977195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83081643924914972666605853 31155616471843114749977195)
  ·
    refine ⟨46733424707764672124965793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31155616471843114749977195 46733424707764672124965793)
    ·
      refine ⟨35050068530823504093724345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46733424707764672124965793 35050068530823504093724345)
      ·
        refine ⟨26287551398117628070293259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35050068530823504093724345 26287551398117628070293259)
        ·
          refine ⟨39431327097176442105439889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26287551398117628070293259 39431327097176442105439889)
          ·
            refine ⟨29573495322882331579079917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39431327097176442105439889 29573495322882331579079917)
            ·
              refine ⟨11090060746080874342154969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29573495322882331579079917 11090060746080874342154969)
              ·
                refine ⟨8317545559560655756616227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11090060746080874342154969 8317545559560655756616227)
                ·
                  refine ⟨12476318339340983634924341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8317545559560655756616227 12476318339340983634924341)
                  ·
                    refine ⟨1169654844313217215774157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12476318339340983634924341 1169654844313217215774157)
                    ·
                      rfl

theorem cell22_3416842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 2, 1, 5].length) (baseStart_3416842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3416842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3416842 prefixEnd_3416842 := by exact prefixLift 3416842
  have htrace : WordTrace (prefixWord ++ tailWord_3416842) baseStart_3416842 baseEnd_3416842 := by
    simpa [prefixWord, tailWord_3416842, baseEnd_3416842] using wordTrace_append hprefix tailTrace_3416842
  have hstable : (prefixWord ++ tailWord_3416842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416842).length < 2 ^ (prefixWord ++ tailWord_3416842).sum := by decide
  have hdescent : baseEnd_3416842 < baseStart_3416842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416855 : List Nat := [1, 1, 3, 4, 13]
def baseStart_3416855 : Nat := 118140960795 + 3416855 * 2 ^ 59
def prefixEnd_3416855 : Nat := 4983230072969 + 3 ^ 40 * 3416855 * 2
def baseEnd_3416855 : Nat := 4813412734481026811519

theorem tailTrace_3416855 : CollatzResearch.WordTrace tailWord_3416855 prefixEnd_3416855 4813412734481026811519 := by
  unfold tailWord_3416855
  simp only [CollatzResearch.WordTrace]
  refine ⟨124622940036325362220132019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83081960024216908146754679 124622940036325362220132019)
  ·
    refine ⟨186934410054488043330198029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124622940036325362220132019 186934410054488043330198029)
    ·
      refine ⟨70100403770433016248824261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186934410054488043330198029 70100403770433016248824261)
      ·
        refine ⟨13143825706956190546654549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70100403770433016248824261 13143825706956190546654549)
        ·
          refine ⟨4813412734481026811519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 13143825706956190546654549 4813412734481026811519)
          ·
            rfl

theorem cell22_3416855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 13].length) (baseStart_3416855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3416855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3416855 prefixEnd_3416855 := by exact prefixLift 3416855
  have htrace : WordTrace (prefixWord ++ tailWord_3416855) baseStart_3416855 baseEnd_3416855 := by
    simpa [prefixWord, tailWord_3416855, baseEnd_3416855] using wordTrace_append hprefix tailTrace_3416855
  have hstable : (prefixWord ++ tailWord_3416855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416855).length < 2 ^ (prefixWord ++ tailWord_3416855).sum := by decide
  have hdescent : baseEnd_3416855 < baseStart_3416855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416917 : List Nat := [1, 3, 2, 2, 2, 1, 3, 1, 7]
def baseStart_3416917 : Nat := 118140960795 + 3416917 * 2 ^ 59
def prefixEnd_3416917 : Nat := 4983230072969 + 3 ^ 40 * 3416917 * 2
def baseEnd_3416917 : Nat := 389893506115314006716309

theorem tailTrace_3416917 : CollatzResearch.WordTrace tailWord_3416917 prefixEnd_3416917 389893506115314006716309 := by
  unfold tailWord_3416917
  simp only [CollatzResearch.WordTrace]
  refine ⟨124625201362100746808889005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83083467574733831205926003 124625201362100746808889005)
  ·
    refine ⟨46734450510787780053333377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124625201362100746808889005 46734450510787780053333377)
    ·
      refine ⟨35050837883090835040000033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46734450510787780053333377 35050837883090835040000033)
      ·
        refine ⟨26288128412318126280000025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35050837883090835040000033 26288128412318126280000025)
        ·
          refine ⟨19716096309238594710000019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26288128412318126280000025 19716096309238594710000019)
          ·
            refine ⟨29574144463857892065000029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19716096309238594710000019 29574144463857892065000029)
            ·
              refine ⟨11090304173946709524375011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29574144463857892065000029 11090304173946709524375011)
              ·
                refine ⟨16635456260920064286562517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11090304173946709524375011 16635456260920064286562517)
                ·
                  refine ⟨389893506115314006716309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16635456260920064286562517 389893506115314006716309)
                  ·
                    rfl

theorem cell22_3416917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 7].length) (baseStart_3416917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3416917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3416917 prefixEnd_3416917 := by exact prefixLift 3416917
  have htrace : WordTrace (prefixWord ++ tailWord_3416917) baseStart_3416917 baseEnd_3416917 := by
    simpa [prefixWord, tailWord_3416917, baseEnd_3416917] using wordTrace_append hprefix tailTrace_3416917
  have hstable : (prefixWord ++ tailWord_3416917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416917).length < 2 ^ (prefixWord ++ tailWord_3416917).sum := by decide
  have hdescent : baseEnd_3416917 < baseStart_3416917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416921 : List Nat := [1, 2, 1, 2, 2, 4, 2, 4, 1, 3]
def baseStart_3416921 : Nat := 118140960795 + 3416921 * 2 ^ 59
def prefixEnd_3416921 : Nat := 4983230072969 + 3 ^ 40 * 3416921 * 2
def baseEnd_3416921 : Nat := 1169681887627687343048915

theorem tailTrace_3416921 : CollatzResearch.WordTrace tailWord_3416921 prefixEnd_3416921 1169681887627687343048915 := by
  unfold tailWord_3416921
  simp only [CollatzResearch.WordTrace]
  refine ⟨124625347254086255492034617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83083564836057503661356411 124625347254086255492034617)
  ·
    refine ⟨93469010440564691619025963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124625347254086255492034617 93469010440564691619025963)
    ·
      refine ⟨140203515660847037428538945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93469010440564691619025963 140203515660847037428538945)
      ·
        refine ⟨105152636745635278071404209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140203515660847037428538945 105152636745635278071404209)
        ·
          refine ⟨78864477559226458553553157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105152636745635278071404209 78864477559226458553553157)
          ·
            refine ⟨14787089542354960978791217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78864477559226458553553157 14787089542354960978791217)
            ·
              refine ⟨11090317156766220734093413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14787089542354960978791217 11090317156766220734093413)
              ·
                refine ⟨2079434466893666387642515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11090317156766220734093413 2079434466893666387642515)
                ·
                  refine ⟨3119151700340499581463773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2079434466893666387642515 3119151700340499581463773)
                  ·
                    refine ⟨1169681887627687343048915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3119151700340499581463773 1169681887627687343048915)
                    ·
                      rfl

theorem cell22_3416921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 4, 1, 3].length) (baseStart_3416921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3416921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3416921 prefixEnd_3416921 := by exact prefixLift 3416921
  have htrace : WordTrace (prefixWord ++ tailWord_3416921) baseStart_3416921 baseEnd_3416921 := by
    simpa [prefixWord, tailWord_3416921, baseEnd_3416921] using wordTrace_append hprefix tailTrace_3416921
  have hstable : (prefixWord ++ tailWord_3416921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416921).length < 2 ^ (prefixWord ++ tailWord_3416921).sum := by decide
  have hdescent : baseEnd_3416921 < baseStart_3416921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416947 : List Nat := [1, 1, 1, 2, 2, 1, 4, 3, 3, 4]
def baseStart_3416947 : Nat := 118140960795 + 3416947 * 2 ^ 59
def prefixEnd_3416947 : Nat := 4983230072969 + 3 ^ 40 * 3416947 * 2
def baseEnd_3416947 : Nat := 1169690787959031941898835

theorem tailTrace_3416947 : CollatzResearch.WordTrace tailWord_3416947 prefixEnd_3416947 1169690787959031941898835 := by
  unfold tailWord_3416947
  simp only [CollatzResearch.WordTrace]
  refine ⟨124626295551992061932481095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83084197034661374621654063 124626295551992061932481095)
  ·
    refine ⟨186939443327988092898721643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124626295551992061932481095 186939443327988092898721643)
    ·
      refine ⟨280409164991982139348082465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186939443327988092898721643 280409164991982139348082465)
      ·
        refine ⟨210306873743986604511061849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280409164991982139348082465 210306873743986604511061849)
        ·
          refine ⟨157730155307989953383296387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210306873743986604511061849 157730155307989953383296387)
          ·
            refine ⟨236595232961984930074944581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157730155307989953383296387 236595232961984930074944581)
            ·
              refine ⟨44361606180372174389052109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 236595232961984930074944581 44361606180372174389052109)
              ·
                refine ⟨16635602317639565395894541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44361606180372174389052109 16635602317639565395894541)
                ·
                  refine ⟨6238350869114837023460453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16635602317639565395894541 6238350869114837023460453)
                  ·
                    refine ⟨1169690787959031941898835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6238350869114837023460453 1169690787959031941898835)
                    ·
                      rfl

theorem cell22_3416947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 3, 4].length) (baseStart_3416947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3416947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3416947 prefixEnd_3416947 := by exact prefixLift 3416947
  have htrace : WordTrace (prefixWord ++ tailWord_3416947) baseStart_3416947 baseEnd_3416947 := by
    simpa [prefixWord, tailWord_3416947, baseEnd_3416947] using wordTrace_append hprefix tailTrace_3416947
  have hstable : (prefixWord ++ tailWord_3416947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416947).length < 2 ^ (prefixWord ++ tailWord_3416947).sum := by decide
  have hdescent : baseEnd_3416947 < baseStart_3416947 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416992 : List Nat := [2, 1, 1, 4, 1, 1, 2, 1, 3, 6]
def baseStart_3416992 : Nat := 118140960795 + 3416992 * 2 ^ 59
def prefixEnd_3416992 : Nat := 4983230072969 + 3 ^ 40 * 3416992 * 2
def baseEnd_3416992 : Nat := 1169706192378666824523697

theorem tailTrace_3416992 : CollatzResearch.WordTrace tailWord_3416992 prefixEnd_3416992 1169706192378666824523697 := by
  unfold tailWord_3416992
  simp only [CollatzResearch.WordTrace]
  refine ⟨62313968418414517308934615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83085291224552689745246153 62313968418414517308934615)
  ·
    refine ⟨93470952627621775963401923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62313968418414517308934615 93470952627621775963401923)
    ·
      refine ⟨140206428941432663945102885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93470952627621775963401923 140206428941432663945102885)
      ·
        refine ⟨26288705426518624489706791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140206428941432663945102885 26288705426518624489706791)
        ·
          refine ⟨39433058139777936734560187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26288705426518624489706791 39433058139777936734560187)
          ·
            refine ⟨59149587209666905101840281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39433058139777936734560187 59149587209666905101840281)
            ·
              refine ⟨44362190407250178826380211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59149587209666905101840281 44362190407250178826380211)
              ·
                refine ⟨66543285610875268239570317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44362190407250178826380211 66543285610875268239570317)
                ·
                  refine ⟨24953732104078225589838869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66543285610875268239570317 24953732104078225589838869)
                  ·
                    refine ⟨1169706192378666824523697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24953732104078225589838869 1169706192378666824523697)
                    ·
                      rfl

theorem cell22_3416992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 3, 6].length) (baseStart_3416992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3416992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3416992 prefixEnd_3416992 := by exact prefixLift 3416992
  have htrace : WordTrace (prefixWord ++ tailWord_3416992) baseStart_3416992 baseEnd_3416992 := by
    simpa [prefixWord, tailWord_3416992, baseEnd_3416992] using wordTrace_append hprefix tailTrace_3416992
  have hstable : (prefixWord ++ tailWord_3416992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416992).length < 2 ^ (prefixWord ++ tailWord_3416992).sum := by decide
  have hdescent : baseEnd_3416992 < baseStart_3416992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417058 : List Nat := [3, 3, 3, 1, 1, 2, 3, 6]
def baseStart_3417058 : Nat := 118140960795 + 3417058 * 2 ^ 59
def prefixEnd_3417058 : Nat := 4983230072969 + 3 ^ 40 * 3417058 * 2
def baseEnd_3417058 : Nat := 129969865058607183597055

theorem tailTrace_3417058 : CollatzResearch.WordTrace tailWord_3417058 prefixEnd_3417058 129969865058607183597055 := by
  unfold tailWord_3417058
  simp only [CollatzResearch.WordTrace]
  refine ⟨31157586013647481972442957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83086896036393285259847885 31157586013647481972442957)
  ·
    refine ⟨11684094755117805739666109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31157586013647481972442957 11684094755117805739666109)
    ·
      refine ⟨4381535533169177152374791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11684094755117805739666109 4381535533169177152374791)
      ·
        refine ⟨6572303299753765728562187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4381535533169177152374791 6572303299753765728562187)
        ·
          refine ⟨9858454949630648592843281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6572303299753765728562187 9858454949630648592843281)
          ·
            refine ⟨7393841212222986444632461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9858454949630648592843281 7393841212222986444632461)
            ·
              refine ⟨2772690454583619916737173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7393841212222986444632461 2772690454583619916737173)
              ·
                refine ⟨129969865058607183597055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2772690454583619916737173 129969865058607183597055)
                ·
                  rfl

theorem cell22_3417058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 3, 6].length) (baseStart_3417058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3417058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3417058 prefixEnd_3417058 := by exact prefixLift 3417058
  have htrace : WordTrace (prefixWord ++ tailWord_3417058) baseStart_3417058 baseEnd_3417058 := by
    simpa [prefixWord, tailWord_3417058, baseEnd_3417058] using wordTrace_append hprefix tailTrace_3417058
  have hstable : (prefixWord ++ tailWord_3417058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417058).length < 2 ^ (prefixWord ++ tailWord_3417058).sum := by decide
  have hdescent : baseEnd_3417058 < baseStart_3417058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417073 : List Nat := [1, 2, 2, 2, 4, 1, 1, 5, 1, 3]
def baseStart_3417073 : Nat := 118140960795 + 3417073 * 2 ^ 59
def prefixEnd_3417073 : Nat := 4983230072969 + 3 ^ 40 * 3417073 * 2
def baseEnd_3417073 : Nat := 1169733920334009613248449

theorem tailTrace_3417073 : CollatzResearch.WordTrace tailWord_3417073 prefixEnd_3417073 1169733920334009613248449 := by
  unfold tailWord_3417073
  simp only [CollatzResearch.WordTrace]
  refine ⟨124630891149535585451567873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83087260766357056967711915 124630891149535585451567873)
  ·
    refine ⟨93473168362151689088675905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124630891149535585451567873 93473168362151689088675905)
    ·
      refine ⟨70104876271613766816506929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93473168362151689088675905 70104876271613766816506929)
      ·
        refine ⟨52578657203710325112380197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70104876271613766816506929 52578657203710325112380197)
        ·
          refine ⟨9858498225695685958571287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52578657203710325112380197 9858498225695685958571287)
          ·
            refine ⟨14787747338543528937856931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9858498225695685958571287 14787747338543528937856931)
            ·
              refine ⟨22181621007815293406785397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14787747338543528937856931 22181621007815293406785397)
              ·
                refine ⟨2079526969482683756886131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22181621007815293406785397 2079526969482683756886131)
                ·
                  refine ⟨3119290454224025635329197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2079526969482683756886131 3119290454224025635329197)
                  ·
                    refine ⟨1169733920334009613248449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3119290454224025635329197 1169733920334009613248449)
                    ·
                      rfl

theorem cell22_3417073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 5, 1, 3].length) (baseStart_3417073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3417073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3417073 prefixEnd_3417073 := by exact prefixLift 3417073
  have htrace : WordTrace (prefixWord ++ tailWord_3417073) baseStart_3417073 baseEnd_3417073 := by
    simpa [prefixWord, tailWord_3417073, baseEnd_3417073] using wordTrace_append hprefix tailTrace_3417073
  have hstable : (prefixWord ++ tailWord_3417073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417073).length < 2 ^ (prefixWord ++ tailWord_3417073).sum := by decide
  have hdescent : baseEnd_3417073 < baseStart_3417073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417084 : List Nat := [2, 2, 2, 1, 2, 3, 1, 2, 2, 5]
def baseStart_3417084 : Nat := 118140960795 + 3417084 * 2 ^ 59
def prefixEnd_3417084 : Nat := 4983230072969 + 3 ^ 40 * 3417084 * 2
def baseEnd_3417084 : Nat := 1169737685858809251223415

theorem tailTrace_3417084 : CollatzResearch.WordTrace tailWord_3417084 prefixEnd_3417084 1169737685858809251223415 := by
  unfold tailWord_3417084
  simp only [CollatzResearch.WordTrace]
  refine ⟨62315646176247867165109153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83087528234997156220145537 62315646176247867165109153)
  ·
    refine ⟨46736734632185900373831865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62315646176247867165109153 46736734632185900373831865)
    ·
      refine ⟨35052550974139425280373899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46736734632185900373831865 35052550974139425280373899)
      ·
        refine ⟨52578826461209137920560849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35052550974139425280373899 52578826461209137920560849)
        ·
          refine ⟨39434119845906853440420637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52578826461209137920560849 39434119845906853440420637)
          ·
            refine ⟨14787794942215070040157739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39434119845906853440420637 14787794942215070040157739)
            ·
              refine ⟨22181692413322605060236609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14787794942215070040157739 22181692413322605060236609)
              ·
                refine ⟨16636269309991953795177457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22181692413322605060236609 16636269309991953795177457)
                ·
                  refine ⟨12477201982493965346383093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16636269309991953795177457 12477201982493965346383093)
                  ·
                    refine ⟨1169737685858809251223415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12477201982493965346383093 1169737685858809251223415)
                    ·
                      rfl

theorem cell22_3417084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_3417084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3417084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3417084 prefixEnd_3417084 := by exact prefixLift 3417084
  have htrace : WordTrace (prefixWord ++ tailWord_3417084) baseStart_3417084 baseEnd_3417084 := by
    simpa [prefixWord, tailWord_3417084, baseEnd_3417084] using wordTrace_append hprefix tailTrace_3417084
  have hstable : (prefixWord ++ tailWord_3417084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417084).length < 2 ^ (prefixWord ++ tailWord_3417084).sum := by decide
  have hdescent : baseEnd_3417084 < baseStart_3417084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417114 : List Nat := [3, 1, 1, 3, 1, 2, 1, 4, 6]
def baseStart_3417114 : Nat := 118140960795 + 3417114 * 2 ^ 59
def prefixEnd_3417114 : Nat := 4983230072969 + 3 ^ 40 * 3417114 * 2
def baseEnd_3417114 : Nat := 389915985157299724324441

theorem tailTrace_3417114 : CollatzResearch.WordTrace tailWord_3417114 prefixEnd_3417114 389915985157299724324441 := by
  unfold tailWord_3417114
  simp only [CollatzResearch.WordTrace]
  refine ⟨31158096635596762363452599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83088257694924699635873597 31158096635596762363452599)
  ·
    refine ⟨46737144953395143545178899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31158096635596762363452599 46737144953395143545178899)
    ·
      refine ⟨70105717430092715317768349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46737144953395143545178899 70105717430092715317768349)
      ·
        refine ⟨26289644036284768244163131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70105717430092715317768349 26289644036284768244163131)
        ·
          refine ⟨39434466054427152366244697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26289644036284768244163131 39434466054427152366244697)
          ·
            refine ⟨29575849540820364274683523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39434466054427152366244697 29575849540820364274683523)
            ·
              refine ⟨44363774311230546412025285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29575849540820364274683523 44363774311230546412025285)
              ·
                refine ⟨8318207683355727452254741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44363774311230546412025285 8318207683355727452254741)
                ·
                  refine ⟨389915985157299724324441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8318207683355727452254741 389915985157299724324441)
                  ·
                    rfl

theorem cell22_3417114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 4, 6].length) (baseStart_3417114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3417114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3417114 prefixEnd_3417114 := by exact prefixLift 3417114
  have htrace : WordTrace (prefixWord ++ tailWord_3417114) baseStart_3417114 baseEnd_3417114 := by
    simpa [prefixWord, tailWord_3417114, baseEnd_3417114] using wordTrace_append hprefix tailTrace_3417114
  have hstable : (prefixWord ++ tailWord_3417114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417114).length < 2 ^ (prefixWord ++ tailWord_3417114).sum := by decide
  have hdescent : baseEnd_3417114 < baseStart_3417114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417146 : List Nat := [3, 1, 1, 1, 3, 1, 4, 1, 4, 3]
def baseStart_3417146 : Nat := 118140960795 + 3417146 * 2 ^ 59
def prefixEnd_3417146 : Nat := 4983230072969 + 3 ^ 40 * 3417146 * 2
def baseEnd_3417146 : Nat := 1169758909725861756173225

theorem tailTrace_3417146 : CollatzResearch.WordTrace tailWord_3417146 prefixEnd_3417146 1169758909725861756173225 := by
  unfold tailWord_3417146
  simp only [CollatzResearch.WordTrace]
  refine ⟨31158388419567779729743823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83089035785514079279316861 31158388419567779729743823)
  ·
    refine ⟨46737582629351669594615735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31158388419567779729743823 46737582629351669594615735)
    ·
      refine ⟨70106373944027504391923603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46737582629351669594615735 70106373944027504391923603)
      ·
        refine ⟨105159560916041256587885405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70106373944027504391923603 105159560916041256587885405)
        ·
          refine ⟨39434835343515471220457027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105159560916041256587885405 39434835343515471220457027)
          ·
            refine ⟨59152253015273206830685541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39434835343515471220457027 59152253015273206830685541)
            ·
              refine ⟨11091047440363726280753539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59152253015273206830685541 11091047440363726280753539)
              ·
                refine ⟨16636571160545589421130309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11091047440363726280753539 16636571160545589421130309)
                ·
                  refine ⟨3119357092602298016461933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16636571160545589421130309 3119357092602298016461933)
                  ·
                    refine ⟨1169758909725861756173225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3119357092602298016461933 1169758909725861756173225)
                    ·
                      rfl

theorem cell22_3417146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 4, 3].length) (baseStart_3417146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3417146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3417146 prefixEnd_3417146 := by exact prefixLift 3417146
  have htrace : WordTrace (prefixWord ++ tailWord_3417146) baseStart_3417146 baseEnd_3417146 := by
    simpa [prefixWord, tailWord_3417146, baseEnd_3417146] using wordTrace_append hprefix tailTrace_3417146
  have hstable : (prefixWord ++ tailWord_3417146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417146).length < 2 ^ (prefixWord ++ tailWord_3417146).sum := by decide
  have hdescent : baseEnd_3417146 < baseStart_3417146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417159 : List Nat := [1, 1, 4, 1, 3, 2, 1, 9]
def baseStart_3417159 : Nat := 118140960795 + 3417159 * 2 ^ 59
def prefixEnd_3417159 : Nat := 4983230072969 + 3 ^ 40 * 3417159 * 2
def baseEnd_3417159 : Nat := 129973706654614895066465

theorem tailTrace_3417159 : CollatzResearch.WordTrace tailWord_3417159 prefixEnd_3417159 129973706654614895066465 := by
  unfold tailWord_3417159
  simp only [CollatzResearch.WordTrace]
  refine ⟨124634027827224022139198531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83089351884816014759465687 124634027827224022139198531)
  ·
    refine ⟨186951041740836033208797797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124634027827224022139198531 186951041740836033208797797)
    ·
      refine ⟨35053320326406756226649587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 186951041740836033208797797 35053320326406756226649587)
      ·
        refine ⟨52579980489610134339974381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35053320326406756226649587 52579980489610134339974381)
        ·
          refine ⟨19717492683603800377490393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52579980489610134339974381 19717492683603800377490393)
          ·
            refine ⟨14788119512702850283117795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19717492683603800377490393 14788119512702850283117795)
            ·
              refine ⟨22182179269054275424676693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14788119512702850283117795 22182179269054275424676693)
              ·
                refine ⟨129973706654614895066465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22182179269054275424676693 129973706654614895066465)
                ·
                  rfl

theorem cell22_3417159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 9].length) (baseStart_3417159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3417159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3417159 prefixEnd_3417159 := by exact prefixLift 3417159
  have htrace : WordTrace (prefixWord ++ tailWord_3417159) baseStart_3417159 baseEnd_3417159 := by
    simpa [prefixWord, tailWord_3417159, baseEnd_3417159] using wordTrace_append hprefix tailTrace_3417159
  have hstable : (prefixWord ++ tailWord_3417159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417159).length < 2 ^ (prefixWord ++ tailWord_3417159).sum := by decide
  have hdescent : baseEnd_3417159 < baseStart_3417159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417206 : List Nat := [5, 1, 1, 2, 1, 1, 1, 1, 1, 8]
def baseStart_3417206 : Nat := 118140960795 + 3417206 * 2 ^ 59
def prefixEnd_3417206 : Nat := 4983230072969 + 3 ^ 40 * 3417206 * 2
def baseEnd_3417206 : Nat := 1169779448952041599673041

theorem tailTrace_3417206 : CollatzResearch.WordTrace tailWord_3417206 prefixEnd_3417206 1169779448952041599673041 := by
  unfold tailWord_3417206
  simp only [CollatzResearch.WordTrace]
  refine ⟨7789733878628359322884967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83090494705369166110772981 7789733878628359322884967)
  ·
    refine ⟨11684600817942538984327451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7789733878628359322884967 11684600817942538984327451)
    ·
      refine ⟨17526901226913808476491177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11684600817942538984327451 17526901226913808476491177)
      ·
        refine ⟨13145175920185356357368383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17526901226913808476491177 13145175920185356357368383)
        ·
          refine ⟨19717763880278034536052575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13145175920185356357368383 19717763880278034536052575)
          ·
            refine ⟨29576645820417051804078863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19717763880278034536052575 29576645820417051804078863)
            ·
              refine ⟨44364968730625577706118295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29576645820417051804078863 44364968730625577706118295)
              ·
                refine ⟨66547453095938366559177443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44364968730625577706118295 66547453095938366559177443)
                ·
                  refine ⟨99821179643907549838766165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66547453095938366559177443 99821179643907549838766165)
                  ·
                    refine ⟨1169779448952041599673041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 99821179643907549838766165 1169779448952041599673041)
                    ·
                      rfl

theorem cell22_3417206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_3417206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3417206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3417206 prefixEnd_3417206 := by exact prefixLift 3417206
  have htrace : WordTrace (prefixWord ++ tailWord_3417206) baseStart_3417206 baseEnd_3417206 := by
    simpa [prefixWord, tailWord_3417206, baseEnd_3417206] using wordTrace_append hprefix tailTrace_3417206
  have hstable : (prefixWord ++ tailWord_3417206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417206).length < 2 ^ (prefixWord ++ tailWord_3417206).sum := by decide
  have hdescent : baseEnd_3417206 < baseStart_3417206 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417242 : List Nat := [3, 1, 1, 5, 1, 2, 2, 3, 1, 3]
def baseStart_3417242 : Nat := 118140960795 + 3417242 * 2 ^ 59
def prefixEnd_3417242 : Nat := 4983230072969 + 3 ^ 40 * 3417242 * 2
def baseEnd_3417242 : Nat := 1169791772487749505772931

theorem tailTrace_3417242 : CollatzResearch.WordTrace tailWord_3417242 prefixEnd_3417242 1169791772487749505772931 := by
  unfold tailWord_3417242
  simp only [CollatzResearch.WordTrace]
  refine ⟨31159263771480831828617495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83091370057282218209646653 31159263771480831828617495)
  ·
    refine ⟨46738895657221247742926243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31159263771480831828617495 46738895657221247742926243)
    ·
      refine ⟨70108343485831871614389365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46738895657221247742926243 70108343485831871614389365)
      ·
        refine ⟨6572657201796737963849003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70108343485831871614389365 6572657201796737963849003)
        ·
          refine ⟨9858985802695106945773505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6572657201796737963849003 9858985802695106945773505)
          ·
            refine ⟨7394239352021330209330129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9858985802695106945773505 7394239352021330209330129)
            ·
              refine ⟨5545679514015997656997597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7394239352021330209330129 5545679514015997656997597)
              ·
                refine ⟨2079629817755999121374099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5545679514015997656997597 2079629817755999121374099)
                ·
                  refine ⟨3119444726633998682061149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2079629817755999121374099 3119444726633998682061149)
                  ·
                    refine ⟨1169791772487749505772931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3119444726633998682061149 1169791772487749505772931)
                    ·
                      rfl

theorem cell22_3417242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 3, 1, 3].length) (baseStart_3417242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3417242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3417242 prefixEnd_3417242 := by exact prefixLift 3417242
  have htrace : WordTrace (prefixWord ++ tailWord_3417242) baseStart_3417242 baseEnd_3417242 := by
    simpa [prefixWord, tailWord_3417242, baseEnd_3417242] using wordTrace_append hprefix tailTrace_3417242
  have hstable : (prefixWord ++ tailWord_3417242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417242).length < 2 ^ (prefixWord ++ tailWord_3417242).sum := by decide
  have hdescent : baseEnd_3417242 < baseStart_3417242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417255 : List Nat := [1, 1, 6, 2, 1, 3, 1, 2, 5]
def baseStart_3417255 : Nat := 118140960795 + 3417255 * 2 ^ 59
def prefixEnd_3417255 : Nat := 4983230072969 + 3 ^ 40 * 3417255 * 2
def baseEnd_3417255 : Nat := 389932074217807268399297

theorem tailTrace_3417255 : CollatzResearch.WordTrace tailWord_3417255 prefixEnd_3417255 389932074217807268399297 := by
  unfold tailWord_3417255
  simp only [CollatzResearch.WordTrace]
  refine ⟨124637529234876230534693219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83091686156584153689795479 124637529234876230534693219)
  ·
    refine ⟨186956293852314345802039829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124637529234876230534693219 186956293852314345802039829)
    ·
      refine ⟨8763576274327234959470617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 186956293852314345802039829 8763576274327234959470617)
      ·
        refine ⟨6572682205745426219602963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8763576274327234959470617 6572682205745426219602963)
        ·
          refine ⟨9859023308618139329404445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6572682205745426219602963 9859023308618139329404445)
          ·
            refine ⟨3697133740731802248526667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9859023308618139329404445 3697133740731802248526667)
            ·
              refine ⟨5545700611097703372790001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3697133740731802248526667 5545700611097703372790001)
              ·
                refine ⟨4159275458323277529592501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5545700611097703372790001 4159275458323277529592501)
                ·
                  refine ⟨389932074217807268399297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4159275458323277529592501 389932074217807268399297)
                  ·
                    rfl

theorem cell22_3417255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 2, 5].length) (baseStart_3417255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3417255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3417255 prefixEnd_3417255 := by exact prefixLift 3417255
  have htrace : WordTrace (prefixWord ++ tailWord_3417255) baseStart_3417255 baseEnd_3417255 := by
    simpa [prefixWord, tailWord_3417255, baseEnd_3417255] using wordTrace_append hprefix tailTrace_3417255
  have hstable : (prefixWord ++ tailWord_3417255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417255).length < 2 ^ (prefixWord ++ tailWord_3417255).sum := by decide
  have hdescent : baseEnd_3417255 < baseStart_3417255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417266 : List Nat := [3, 2, 1, 1, 1, 4, 1, 3, 6]
def baseStart_3417266 : Nat := 118140960795 + 3417266 * 2 ^ 59
def prefixEnd_3417266 : Nat := 4983230072969 + 3 ^ 40 * 3417266 * 2
def baseEnd_3417266 : Nat := 389933329392740481057619

theorem tailTrace_3417266 : CollatzResearch.WordTrace tailWord_3417266 prefixEnd_3417266 389933329392740481057619 := by
  unfold tailWord_3417266
  simp only [CollatzResearch.WordTrace]
  refine ⟨31159482609459094853335913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83091953625224252942229101 31159482609459094853335913)
  ·
    refine ⟨23369611957094321140001935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31159482609459094853335913 23369611957094321140001935)
    ·
      refine ⟨35054417935641481710002903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23369611957094321140001935 35054417935641481710002903)
      ·
        refine ⟨52581626903462222565004355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35054417935641481710002903 52581626903462222565004355)
        ·
          refine ⟨78872440355193333847506533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52581626903462222565004355 78872440355193333847506533)
          ·
            refine ⟨14788582566598750096407475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78872440355193333847506533 14788582566598750096407475)
            ·
              refine ⟨22182873849898125144611213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14788582566598750096407475 22182873849898125144611213)
              ·
                refine ⟨8318577693711796929229205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22182873849898125144611213 8318577693711796929229205)
                ·
                  refine ⟨389933329392740481057619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8318577693711796929229205 389933329392740481057619)
                  ·
                    rfl

theorem cell22_3417266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 3, 6].length) (baseStart_3417266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3417266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3417266 prefixEnd_3417266 := by exact prefixLift 3417266
  have htrace : WordTrace (prefixWord ++ tailWord_3417266) baseStart_3417266 baseEnd_3417266 := by
    simpa [prefixWord, tailWord_3417266, baseEnd_3417266] using wordTrace_append hprefix tailTrace_3417266
  have hstable : (prefixWord ++ tailWord_3417266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417266).length < 2 ^ (prefixWord ++ tailWord_3417266).sum := by decide
  have hdescent : baseEnd_3417266 < baseStart_3417266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417293 : List Nat := [1, 6, 2, 2, 2, 1, 1, 3, 1, 3]
def baseStart_3417293 : Nat := 118140960795 + 3417293 * 2 ^ 59
def prefixEnd_3417293 : Nat := 4983230072969 + 3 ^ 40 * 3417293 * 2
def baseEnd_3417293 : Nat := 1169809230830002372747775

theorem tailTrace_3417293 : CollatzResearch.WordTrace tailWord_3417293 prefixEnd_3417293 1169809230830002372747775 := by
  unfold tailWord_3417293
  simp only [CollatzResearch.WordTrace]
  refine ⟨124638915208738563024576533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83092610139159042016384355 124638915208738563024576533)
  ·
    refine ⟨5842449150409620141777025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 124638915208738563024576533 5842449150409620141777025)
    ·
      refine ⟨4381836862807215106332769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5842449150409620141777025 4381836862807215106332769)
      ·
        refine ⟨3286377647105411329749577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4381836862807215106332769 3286377647105411329749577)
        ·
          refine ⟨2464783235329058497312183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3286377647105411329749577 2464783235329058497312183)
          ·
            refine ⟨3697174852993587745968275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2464783235329058497312183 3697174852993587745968275)
            ·
              refine ⟨5545762279490381618952413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3697174852993587745968275 5545762279490381618952413)
              ·
                refine ⟨2079660854808893107107155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5545762279490381618952413 2079660854808893107107155)
                ·
                  refine ⟨3119491282213339660660733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2079660854808893107107155 3119491282213339660660733)
                  ·
                    refine ⟨1169809230830002372747775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3119491282213339660660733 1169809230830002372747775)
                    ·
                      rfl

theorem cell22_3417293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_3417293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3417293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3417293 prefixEnd_3417293 := by exact prefixLift 3417293
  have htrace : WordTrace (prefixWord ++ tailWord_3417293) baseStart_3417293 baseEnd_3417293 := by
    simpa [prefixWord, tailWord_3417293, baseEnd_3417293] using wordTrace_append hprefix tailTrace_3417293
  have hstable : (prefixWord ++ tailWord_3417293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417293).length < 2 ^ (prefixWord ++ tailWord_3417293).sum := by decide
  have hdescent : baseEnd_3417293 < baseStart_3417293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417298 : List Nat := [3, 2, 2, 2, 1, 1, 1, 1, 6, 3]
def baseStart_3417298 : Nat := 118140960795 + 3417298 * 2 ^ 59
def prefixEnd_3417298 : Nat := 4983230072969 + 3 ^ 40 * 3417298 * 2
def baseEnd_3417298 : Nat := 1169810942432184026372759

theorem tailTrace_3417298 : CollatzResearch.WordTrace tailWord_3417298 prefixEnd_3417298 1169810942432184026372759 := by
  unfold tailWord_3417298
  simp only [CollatzResearch.WordTrace]
  refine ⟨31159774393430112219627137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83092731715813632585672365 31159774393430112219627137)
  ·
    refine ⟨23369830795072584164720353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31159774393430112219627137 23369830795072584164720353)
    ·
      refine ⟨17527373096304438123540265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23369830795072584164720353 17527373096304438123540265)
      ·
        refine ⟨13145529822228328592655199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17527373096304438123540265 13145529822228328592655199)
        ·
          refine ⟨19718294733342492888982799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13145529822228328592655199 19718294733342492888982799)
          ·
            refine ⟨29577442100013739333474199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19718294733342492888982799 29577442100013739333474199)
            ·
              refine ⟨44366163150020609000211299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29577442100013739333474199 44366163150020609000211299)
              ·
                refine ⟨66549244725030913500316949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44366163150020609000211299 66549244725030913500316949)
                ·
                  refine ⟨3119495846485824070327357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 66549244725030913500316949 3119495846485824070327357)
                  ·
                    refine ⟨1169810942432184026372759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3119495846485824070327357 1169810942432184026372759)
                    ·
                      rfl

theorem cell22_3417298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 6, 3].length) (baseStart_3417298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3417298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3417298 prefixEnd_3417298 := by exact prefixLift 3417298
  have htrace : WordTrace (prefixWord ++ tailWord_3417298) baseStart_3417298 baseEnd_3417298 := by
    simpa [prefixWord, tailWord_3417298, baseEnd_3417298] using wordTrace_append hprefix tailTrace_3417298
  have hstable : (prefixWord ++ tailWord_3417298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417298).length < 2 ^ (prefixWord ++ tailWord_3417298).sum := by decide
  have hdescent : baseEnd_3417298 < baseStart_3417298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417313 : List Nat := [1, 2, 3, 1, 3, 3, 1, 2, 2, 4]
def baseStart_3417313 : Nat := 118140960795 + 3417313 * 2 ^ 59
def prefixEnd_3417313 : Nat := 4983230072969 + 3 ^ 40 * 3417313 * 2
def baseEnd_3417313 : Nat := 1169816077238728987247713

theorem tailTrace_3417313 : CollatzResearch.WordTrace tailWord_3417313 prefixEnd_3417313 1169816077238728987247713 := by
  unfold tailWord_3417313
  simp only [CollatzResearch.WordTrace]
  refine ⟨124639644668666106440304593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83093096445777404293536395 124639644668666106440304593)
  ·
    refine ⟨93479733501499579830228445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124639644668666106440304593 93479733501499579830228445)
    ·
      refine ⟨35054900063062342436335667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93479733501499579830228445 35054900063062342436335667)
      ·
        refine ⟨52582350094593513654503501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35054900063062342436335667 52582350094593513654503501)
        ·
          refine ⟨19718381285472567620438813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52582350094593513654503501 19718381285472567620438813)
          ·
            refine ⟨7394392982052212857664555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19718381285472567620438813 7394392982052212857664555)
            ·
              refine ⟨11091589473078319286496833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7394392982052212857664555 11091589473078319286496833)
              ·
                refine ⟨8318692104808739464872625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11091589473078319286496833 8318692104808739464872625)
                ·
                  refine ⟨6239019078606554598654469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8318692104808739464872625 6239019078606554598654469)
                  ·
                    refine ⟨1169816077238728987247713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6239019078606554598654469 1169816077238728987247713)
                    ·
                      rfl

theorem cell22_3417313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 2, 2, 4].length) (baseStart_3417313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3417313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3417313 prefixEnd_3417313 := by exact prefixLift 3417313
  have htrace : WordTrace (prefixWord ++ tailWord_3417313) baseStart_3417313 baseEnd_3417313 := by
    simpa [prefixWord, tailWord_3417313, baseEnd_3417313] using wordTrace_append hprefix tailTrace_3417313
  have hstable : (prefixWord ++ tailWord_3417313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417313).length < 2 ^ (prefixWord ++ tailWord_3417313).sum := by decide
  have hdescent : baseEnd_3417313 < baseStart_3417313 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417317 : List Nat := [1, 3, 1, 4, 3, 1, 3, 2, 4]
def baseStart_3417317 : Nat := 118140960795 + 3417317 * 2 ^ 59
def prefixEnd_3417317 : Nat := 4983230072969 + 3 ^ 40 * 3417317 * 2
def baseEnd_3417317 : Nat := 389939148840158103382567

theorem tailTrace_3417317 : CollatzResearch.WordTrace tailWord_3417317 prefixEnd_3417317 389939148840158103382567 := by
  unfold tailWord_3417317
  simp only [CollatzResearch.WordTrace]
  refine ⟨124639790560651615123450205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83093193707101076748966803 124639790560651615123450205)
  ·
    refine ⟨46739921460244355671293827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124639790560651615123450205 46739921460244355671293827)
    ·
      refine ⟨70109882190366533506940741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46739921460244355671293827 70109882190366533506940741)
      ·
        refine ⟨13145602910693725032551389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70109882190366533506940741 13145602910693725032551389)
        ·
          refine ⟨4929601091510146887206771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13145602910693725032551389 4929601091510146887206771)
          ·
            refine ⟨7394401637265220330810157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4929601091510146887206771 7394401637265220330810157)
            ·
              refine ⟨2772900613974457624053809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7394401637265220330810157 2772900613974457624053809)
              ·
                refine ⟨2079675460480843218040357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2772900613974457624053809 2079675460480843218040357)
                ·
                  refine ⟨389939148840158103382567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2079675460480843218040357 389939148840158103382567)
                  ·
                    rfl

theorem cell22_3417317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 3, 2, 4].length) (baseStart_3417317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3417317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3417317 prefixEnd_3417317 := by exact prefixLift 3417317
  have htrace : WordTrace (prefixWord ++ tailWord_3417317) baseStart_3417317 baseEnd_3417317 := by
    simpa [prefixWord, tailWord_3417317, baseEnd_3417317] using wordTrace_append hprefix tailTrace_3417317
  have hstable : (prefixWord ++ tailWord_3417317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417317).length < 2 ^ (prefixWord ++ tailWord_3417317).sum := by decide
  have hdescent : baseEnd_3417317 < baseStart_3417317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417371 : List Nat := [1, 1, 1, 1, 1, 1, 5, 4, 2, 5]
def baseStart_3417371 : Nat := 118140960795 + 3417371 * 2 ^ 59
def prefixEnd_3417371 : Nat := 4983230072969 + 3 ^ 40 * 3417371 * 2
def baseEnd_3417371 : Nat := 1169835931824036169297535

theorem tailTrace_3417371 : CollatzResearch.WordTrace tailWord_3417371 prefixEnd_3417371 1169835931824036169297535 := by
  unfold tailWord_3417371
  simp only [CollatzResearch.WordTrace]
  refine ⟨124641760102455982345915967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83094506734970654897277311 124641760102455982345915967)
  ·
    refine ⟨186962640153683973518873951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124641760102455982345915967 186962640153683973518873951)
    ·
      refine ⟨280443960230525960278310927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186962640153683973518873951 280443960230525960278310927)
      ·
        refine ⟨420665940345788940417466391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280443960230525960278310927 420665940345788940417466391)
        ·
          refine ⟨630998910518683410626199587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420665940345788940417466391 630998910518683410626199587)
          ·
            refine ⟨946498365778025115939299381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 630998910518683410626199587 946498365778025115939299381)
            ·
              refine ⟨88734221791689854619309317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 946498365778025115939299381 88734221791689854619309317)
              ·
                refine ⟨16637666585941847741120497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88734221791689854619309317 16637666585941847741120497)
                ·
                  refine ⟨12478249939456385805840373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16637666585941847741120497 12478249939456385805840373)
                  ·
                    refine ⟨1169835931824036169297535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12478249939456385805840373 1169835931824036169297535)
                    ·
                      rfl

theorem cell22_3417371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 2, 5].length) (baseStart_3417371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3417371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3417371 prefixEnd_3417371 := by exact prefixLift 3417371
  have htrace : WordTrace (prefixWord ++ tailWord_3417371) baseStart_3417371 baseEnd_3417371 := by
    simpa [prefixWord, tailWord_3417371, baseEnd_3417371] using wordTrace_append hprefix tailTrace_3417371
  have hstable : (prefixWord ++ tailWord_3417371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417371).length < 2 ^ (prefixWord ++ tailWord_3417371).sum := by decide
  have hdescent : baseEnd_3417371 < baseStart_3417371 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417420 : List Nat := [2, 2, 1, 3, 2, 3, 1, 3, 1, 4]
def baseStart_3417420 : Nat := 118140960795 + 3417420 * 2 ^ 59
def prefixEnd_3417420 : Nat := 4983230072969 + 3 ^ 40 * 3417420 * 2
def baseEnd_3417420 : Nat := 1169852705525416374822385

theorem tailTrace_3417420 : CollatzResearch.WordTrace tailWord_3417420 prefixEnd_3417420 1169852705525416374822385 := by
  unfold tailWord_3417420
  simp only [CollatzResearch.WordTrace]
  refine ⟨62321773639639231857224857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83095698186185642476299809 62321773639639231857224857)
  ·
    refine ⟨46741330229729423892918643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62321773639639231857224857 46741330229729423892918643)
    ·
      refine ⟨70111995344594135839377965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46741330229729423892918643 70111995344594135839377965)
      ·
        refine ⟨26291998254222800939766737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70111995344594135839377965 26291998254222800939766737)
        ·
          refine ⟨19718998690667100704825053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26291998254222800939766737 19718998690667100704825053)
          ·
            refine ⟨7394624509000162764309395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19718998690667100704825053 7394624509000162764309395)
            ·
              refine ⟨11091936763500244146464093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7394624509000162764309395 11091936763500244146464093)
              ·
                refine ⟨4159476286312591554924035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11091936763500244146464093 4159476286312591554924035)
                ·
                  refine ⟨6239214429468887332386053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4159476286312591554924035 6239214429468887332386053)
                  ·
                    refine ⟨1169852705525416374822385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6239214429468887332386053 1169852705525416374822385)
                    ·
                      rfl

theorem cell22_3417420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 3, 1, 4].length) (baseStart_3417420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3417420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3417420 prefixEnd_3417420 := by exact prefixLift 3417420
  have htrace : WordTrace (prefixWord ++ tailWord_3417420) baseStart_3417420 baseEnd_3417420 := by
    simpa [prefixWord, tailWord_3417420, baseEnd_3417420] using wordTrace_append hprefix tailTrace_3417420
  have hstable : (prefixWord ++ tailWord_3417420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417420).length < 2 ^ (prefixWord ++ tailWord_3417420).sum := by decide
  have hdescent : baseEnd_3417420 < baseStart_3417420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417454 : List Nat := [4, 1, 2, 4, 1, 1, 2, 2, 1, 4]
def baseStart_3417454 : Nat := 118140960795 + 3417454 * 2 ^ 59
def prefixEnd_3417454 : Nat := 4983230072969 + 3 ^ 40 * 3417454 * 2
def baseEnd_3417454 : Nat := 1169864344420251619472281

theorem tailTrace_3417454 : CollatzResearch.WordTrace tailWord_3417454 prefixEnd_3417454 1169864344420251619472281 := by
  unfold tailWord_3417454
  simp only [CollatzResearch.WordTrace]
  refine ⟨15580598420144410940148427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83096524907436858347458277 15580598420144410940148427)
  ·
    refine ⟨23370897630216616410222641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15580598420144410940148427 23370897630216616410222641)
    ·
      refine ⟨17528173222662462307666981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23370897630216616410222641 17528173222662462307666981)
      ·
        refine ⟨3286532479249211682687559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17528173222662462307666981 3286532479249211682687559)
        ·
          refine ⟨4929798718873817524031339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3286532479249211682687559 4929798718873817524031339)
          ·
            refine ⟨7394698078310726286047009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4929798718873817524031339 7394698078310726286047009)
            ·
              refine ⟨5546023558733044714535257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7394698078310726286047009 5546023558733044714535257)
              ·
                refine ⟨4159517669049783535901443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5546023558733044714535257 4159517669049783535901443)
                ·
                  refine ⟨6239276503574675303852165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4159517669049783535901443 6239276503574675303852165)
                  ·
                    refine ⟨1169864344420251619472281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6239276503574675303852165 1169864344420251619472281)
                    ·
                      rfl

theorem cell22_3417454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 2, 1, 4].length) (baseStart_3417454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3417454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3417454 prefixEnd_3417454 := by exact prefixLift 3417454
  have htrace : WordTrace (prefixWord ++ tailWord_3417454) baseStart_3417454 baseEnd_3417454 := by
    simpa [prefixWord, tailWord_3417454, baseEnd_3417454] using wordTrace_append hprefix tailTrace_3417454
  have hstable : (prefixWord ++ tailWord_3417454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417454).length < 2 ^ (prefixWord ++ tailWord_3417454).sum := by decide
  have hdescent : baseEnd_3417454 < baseStart_3417454 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417546 : List Nat := [3, 1, 2, 1, 2, 5, 2, 2, 1, 3]
def baseStart_3417546 : Nat := 118140960795 + 3417546 * 2 ^ 59
def prefixEnd_3417546 : Nat := 4983230072969 + 3 ^ 40 * 3417546 * 2
def baseEnd_3417546 : Nat := 1169895837900394046171999

theorem tailTrace_3417546 : CollatzResearch.WordTrace tailWord_3417546 prefixEnd_3417546 1169895837900394046171999 := by
  unfold tailWord_3417546
  simp only [CollatzResearch.WordTrace]
  refine ⟨31162035719205496808384123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83098761917881324822357661 31162035719205496808384123)
  ·
    refine ⟨46743053578808245212576185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31162035719205496808384123 46743053578808245212576185)
    ·
      refine ⟨35057290184106183909432139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46743053578808245212576185 35057290184106183909432139)
      ·
        refine ⟨52585935276159275864148209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35057290184106183909432139 52585935276159275864148209)
        ·
          refine ⟨39439451457119456898111157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52585935276159275864148209 39439451457119456898111157)
          ·
            refine ⟨3697448574104949084197921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39439451457119456898111157 3697448574104949084197921)
            ·
              refine ⟨2773086430578711813148441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3697448574104949084197921 2773086430578711813148441)
              ·
                refine ⟨2079814822934033859861331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2773086430578711813148441 2079814822934033859861331)
                ·
                  refine ⟨3119722234401050789791997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2079814822934033859861331 3119722234401050789791997)
                  ·
                    refine ⟨1169895837900394046171999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3119722234401050789791997 1169895837900394046171999)
                    ·
                      rfl

theorem cell22_3417546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 2, 2, 1, 3].length) (baseStart_3417546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3417546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3417546 prefixEnd_3417546 := by exact prefixLift 3417546
  have htrace : WordTrace (prefixWord ++ tailWord_3417546) baseStart_3417546 baseEnd_3417546 := by
    simpa [prefixWord, tailWord_3417546, baseEnd_3417546] using wordTrace_append hprefix tailTrace_3417546
  have hstable : (prefixWord ++ tailWord_3417546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417546).length < 2 ^ (prefixWord ++ tailWord_3417546).sum := by decide
  have hdescent : baseEnd_3417546 < baseStart_3417546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417585 : List Nat := [1, 2, 2, 2, 3, 2, 2, 2, 1, 5]
def baseStart_3417585 : Nat := 118140960795 + 3417585 * 2 ^ 59
def prefixEnd_3417585 : Nat := 4983230072969 + 3 ^ 40 * 3417585 * 2
def baseEnd_3417585 : Nat := 1169909188397410944446879

theorem tailTrace_3417585 : CollatzResearch.WordTrace tailWord_3417585 prefixEnd_3417585 1169909188397410944446879 := by
  unfold tailWord_3417585
  simp only [CollatzResearch.WordTrace]
  refine ⟨124649565323680696894206209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83099710215787131262804139 124649565323680696894206209)
  ·
    refine ⟨93487173992760522670654657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124649565323680696894206209 93487173992760522670654657)
    ·
      refine ⟨70115380494570392002990993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93487173992760522670654657 70115380494570392002990993)
      ·
        refine ⟨52586535370927794002243245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70115380494570392002990993 52586535370927794002243245)
        ·
          refine ⟨19719950764097922750841217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52586535370927794002243245 19719950764097922750841217)
          ·
            refine ⟨14789963073073442063130913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19719950764097922750841217 14789963073073442063130913)
            ·
              refine ⟨11092472304805081547348185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14789963073073442063130913 11092472304805081547348185)
              ·
                refine ⟨8319354228603811160511139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11092472304805081547348185 8319354228603811160511139)
                ·
                  refine ⟨12479031342905716740766709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8319354228603811160511139 12479031342905716740766709)
                  ·
                    refine ⟨1169909188397410944446879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12479031342905716740766709 1169909188397410944446879)
                    ·
                      rfl

theorem cell22_3417585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 2, 1, 5].length) (baseStart_3417585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3417585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3417585 prefixEnd_3417585 := by exact prefixLift 3417585
  have htrace : WordTrace (prefixWord ++ tailWord_3417585) baseStart_3417585 baseEnd_3417585 := by
    simpa [prefixWord, tailWord_3417585, baseEnd_3417585] using wordTrace_append hprefix tailTrace_3417585
  have hstable : (prefixWord ++ tailWord_3417585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417585).length < 2 ^ (prefixWord ++ tailWord_3417585).sum := by decide
  have hdescent : baseEnd_3417585 < baseStart_3417585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417589 : List Nat := [1, 3, 5, 1, 1, 2, 1, 3, 1, 4]
def baseStart_3417589 : Nat := 118140960795 + 3417589 * 2 ^ 59
def prefixEnd_3417589 : Nat := 4983230072969 + 3 ^ 40 * 3417589 * 2
def baseEnd_3417589 : Nat := 1169910557679156267346867

theorem tailTrace_3417589 : CollatzResearch.WordTrace tailWord_3417589 prefixEnd_3417589 1169910557679156267346867 := by
  unfold tailWord_3417589
  simp only [CollatzResearch.WordTrace]
  refine ⟨124649711215666205577351821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83099807477110803718234547 124649711215666205577351821)
  ·
    refine ⟨46743641705874827091506933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124649711215666205577351821 46743641705874827091506933)
    ·
      refine ⟨4382216409925765039828775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46743641705874827091506933 4382216409925765039828775)
      ·
        refine ⟨6573324614888647559743163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4382216409925765039828775 6573324614888647559743163)
        ·
          refine ⟨9859986922332971339614745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6573324614888647559743163 9859986922332971339614745)
          ·
            refine ⟨7394990191749728504711059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9859986922332971339614745 7394990191749728504711059)
            ·
              refine ⟨11092485287624592757066589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7394990191749728504711059 11092485287624592757066589)
              ·
                refine ⟨4159681982859222283899971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11092485287624592757066589 4159681982859222283899971)
                ·
                  refine ⟨6239522974288833425849957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4159681982859222283899971 6239522974288833425849957)
                  ·
                    refine ⟨1169910557679156267346867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6239522974288833425849957 1169910557679156267346867)
                    ·
                      rfl

theorem cell22_3417589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_3417589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3417589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3417589 prefixEnd_3417589 := by exact prefixLift 3417589
  have htrace : WordTrace (prefixWord ++ tailWord_3417589) baseStart_3417589 baseEnd_3417589 := by
    simpa [prefixWord, tailWord_3417589, baseEnd_3417589] using wordTrace_append hprefix tailTrace_3417589
  have hstable : (prefixWord ++ tailWord_3417589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417589).length < 2 ^ (prefixWord ++ tailWord_3417589).sum := by decide
  have hdescent : baseEnd_3417589 < baseStart_3417589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417619 : List Nat := [1, 1, 1, 2, 1, 7, 3, 1, 2, 3]
def baseStart_3417619 : Nat := 118140960795 + 3417619 * 2 ^ 59
def prefixEnd_3417619 : Nat := 4983230072969 + 3 ^ 40 * 3417619 * 2
def baseEnd_3417619 : Nat := 1169920827292246189096775

theorem tailTrace_3417619 : CollatzResearch.WordTrace tailWord_3417619 prefixEnd_3417619 1169920827292246189096775 := by
  unfold tailWord_3417619
  simp only [CollatzResearch.WordTrace]
  refine ⟨124650805405557520700943911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83100536937038347133962607 124650805405557520700943911)
  ·
    refine ⟨186976208108336281051415867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124650805405557520700943911 186976208108336281051415867)
    ·
      refine ⟨280464312162504421577123801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186976208108336281051415867 280464312162504421577123801)
      ·
        refine ⟨210348234121878316182842851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280464312162504421577123801 210348234121878316182842851)
        ·
          refine ⟨315522351182817474274264277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210348234121878316182842851 315522351182817474274264277)
          ·
            refine ⟨7395055105847284553303069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 315522351182817474274264277 7395055105847284553303069)
            ·
              refine ⟨2773145664692731707488651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7395055105847284553303069 2773145664692731707488651)
              ·
                refine ⟨4159718497039097561232977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2773145664692731707488651 4159718497039097561232977)
                ·
                  refine ⟨3119788872779323170924733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4159718497039097561232977 3119788872779323170924733)
                  ·
                    refine ⟨1169920827292246189096775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3119788872779323170924733 1169920827292246189096775)
                    ·
                      rfl

theorem cell22_3417619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 3, 1, 2, 3].length) (baseStart_3417619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3417619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3417619 prefixEnd_3417619 := by exact prefixLift 3417619
  have htrace : WordTrace (prefixWord ++ tailWord_3417619) baseStart_3417619 baseEnd_3417619 := by
    simpa [prefixWord, tailWord_3417619, baseEnd_3417619] using wordTrace_append hprefix tailTrace_3417619
  have hstable : (prefixWord ++ tailWord_3417619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417619).length < 2 ^ (prefixWord ++ tailWord_3417619).sum := by decide
  have hdescent : baseEnd_3417619 < baseStart_3417619 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417632 : List Nat := [2, 1, 1, 6, 1, 1, 4, 6]
def baseStart_3417632 : Nat := 118140960795 + 3417632 * 2 ^ 59
def prefixEnd_3417632 : Nat := 4983230072969 + 3 ^ 40 * 3417632 * 2
def baseEnd_3417632 : Nat := 129991697495324276502415

theorem tailTrace_3417632 : CollatzResearch.WordTrace tailWord_3417632 prefixEnd_3417632 129991697495324276502415 := by
  unfold tailWord_3417632
  simp only [CollatzResearch.WordTrace]
  refine ⟨62325639777255211960583575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83100853036340282614111433 62325639777255211960583575)
  ·
    refine ⟨93488459665882817940875363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62325639777255211960583575 93488459665882817940875363)
    ·
      refine ⟨140232689498824226911313045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93488459665882817940875363 140232689498824226911313045)
      ·
        refine ⟨6573407320257385636467799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 140232689498824226911313045 6573407320257385636467799)
        ·
          refine ⟨9860110980386078454701699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6573407320257385636467799 9860110980386078454701699)
          ·
            refine ⟨14790166470579117682052549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9860110980386078454701699 14790166470579117682052549)
            ·
              refine ⟨2773156213233584565384853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14790166470579117682052549 2773156213233584565384853)
              ·
                refine ⟨129991697495324276502415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2773156213233584565384853 129991697495324276502415)
                ·
                  rfl

theorem cell22_3417632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 4, 6].length) (baseStart_3417632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3417632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3417632 prefixEnd_3417632 := by exact prefixLift 3417632
  have htrace : WordTrace (prefixWord ++ tailWord_3417632) baseStart_3417632 baseEnd_3417632 := by
    simpa [prefixWord, tailWord_3417632, baseEnd_3417632] using wordTrace_append hprefix tailTrace_3417632
  have hstable : (prefixWord ++ tailWord_3417632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417632).length < 2 ^ (prefixWord ++ tailWord_3417632).sum := by decide
  have hdescent : baseEnd_3417632 < baseStart_3417632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417670 : List Nat := [6, 1, 1, 1, 3, 2, 2, 1, 2, 3]
def baseStart_3417670 : Nat := 118140960795 + 3417670 * 2 ^ 59
def prefixEnd_3417670 : Nat := 4983230072969 + 3 ^ 40 * 3417670 * 2
def baseEnd_3417670 : Nat := 1169938285634499056071619

theorem tailTrace_3417670 : CollatzResearch.WordTrace tailWord_3417670 prefixEnd_3417670 1169938285634499056071619 := by
  unfold tailWord_3417670
  simp only [CollatzResearch.WordTrace]
  refine ⟨3895395797761648637845327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 83101777018915170940700309 3895395797761648637845327)
  ·
    refine ⟨5843093696642472956767991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3895395797761648637845327 5843093696642472956767991)
    ·
      refine ⟨8764640544963709435151987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5843093696642472956767991 8764640544963709435151987)
      ·
        refine ⟨13146960817445564152727981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8764640544963709435151987 13146960817445564152727981)
        ·
          refine ⟨4930110306542086557272993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13146960817445564152727981 4930110306542086557272993)
          ·
            refine ⟨3697582729906564917954745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4930110306542086557272993 3697582729906564917954745)
            ·
              refine ⟨2773187047429923688466059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3697582729906564917954745 2773187047429923688466059)
              ·
                refine ⟨4159780571144885532699089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2773187047429923688466059 4159780571144885532699089)
                ·
                  refine ⟨3119835428358664149524317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4159780571144885532699089 3119835428358664149524317)
                  ·
                    refine ⟨1169938285634499056071619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3119835428358664149524317 1169938285634499056071619)
                    ·
                      rfl

theorem cell22_3417670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_3417670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3417670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3417670 prefixEnd_3417670 := by exact prefixLift 3417670
  have htrace : WordTrace (prefixWord ++ tailWord_3417670) baseStart_3417670 baseEnd_3417670 := by
    simpa [prefixWord, tailWord_3417670, baseEnd_3417670] using wordTrace_append hprefix tailTrace_3417670
  have hstable : (prefixWord ++ tailWord_3417670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417670).length < 2 ^ (prefixWord ++ tailWord_3417670).sum := by decide
  have hdescent : baseEnd_3417670 < baseStart_3417670 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417752 : List Nat := [2, 1, 2, 4, 1, 3, 1, 1, 1, 6]
def baseStart_3417752 : Nat := 118140960795 + 3417752 * 2 ^ 59
def prefixEnd_3417752 : Nat := 4983230072969 + 3 ^ 40 * 3417752 * 2
def baseEnd_3417752 : Nat := 1169966355910278175521367

theorem tailTrace_3417752 : CollatzResearch.WordTrace tailWord_3417752 prefixEnd_3417752 1169966355910278175521367 := by
  unfold tailWord_3417752
  simp only [CollatzResearch.WordTrace]
  refine ⟨62327828157037842207767755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83103770876050456277023673 62327828157037842207767755)
  ·
    refine ⟨93491742235556763311651633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62327828157037842207767755 93491742235556763311651633)
    ·
      refine ⟨70118806676667572483738725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93491742235556763311651633 70118806676667572483738725)
      ·
        refine ⟨13147276251875169840701011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70118806676667572483738725 13147276251875169840701011)
        ·
          refine ⟨19720914377812754761051517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13147276251875169840701011 19720914377812754761051517)
          ·
            refine ⟨7395342891679783035394319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19720914377812754761051517 7395342891679783035394319)
            ·
              refine ⟨11093014337519674553091479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7395342891679783035394319 11093014337519674553091479)
              ·
                refine ⟨16639521506279511829637219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11093014337519674553091479 16639521506279511829637219)
                ·
                  refine ⟨24959282259419267744455829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16639521506279511829637219 24959282259419267744455829)
                  ·
                    refine ⟨1169966355910278175521367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24959282259419267744455829 1169966355910278175521367)
                    ·
                      rfl

theorem cell22_3417752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 1, 6].length) (baseStart_3417752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3417752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3417752 prefixEnd_3417752 := by exact prefixLift 3417752
  have htrace : WordTrace (prefixWord ++ tailWord_3417752) baseStart_3417752 baseEnd_3417752 := by
    simpa [prefixWord, tailWord_3417752, baseEnd_3417752] using wordTrace_append hprefix tailTrace_3417752
  have hstable : (prefixWord ++ tailWord_3417752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417752).length < 2 ^ (prefixWord ++ tailWord_3417752).sum := by decide
  have hdescent : baseEnd_3417752 < baseStart_3417752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417756 : List Nat := [2, 2, 3, 2, 3, 1, 2, 3, 4]
def baseStart_3417756 : Nat := 118140960795 + 3417756 * 2 ^ 59
def prefixEnd_3417756 : Nat := 4983230072969 + 3 ^ 40 * 3417756 * 2
def baseEnd_3417756 : Nat := 389989241730674499473785

theorem tailTrace_3417756 : CollatzResearch.WordTrace tailWord_3417756 prefixEnd_3417756 389989241730674499473785 := by
  unfold tailWord_3417756
  simp only [CollatzResearch.WordTrace]
  refine ⟨62327901103030596549340561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83103868137374128732454081 62327901103030596549340561)
  ·
    refine ⟨46745925827272947412005421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62327901103030596549340561 46745925827272947412005421)
    ·
      refine ⟨17529722185227355279502033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46745925827272947412005421 17529722185227355279502033)
      ·
        refine ⟨13147291638920516459626525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17529722185227355279502033 13147291638920516459626525)
        ·
          refine ⟨4930234364595193672359947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13147291638920516459626525 4930234364595193672359947)
          ·
            refine ⟨7395351546892790508539921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4930234364595193672359947 7395351546892790508539921)
            ·
              refine ⟨5546513660169592881404941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7395351546892790508539921 5546513660169592881404941)
              ·
                refine ⟨2079942622563597330526853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5546513660169592881404941 2079942622563597330526853)
                ·
                  refine ⟨389989241730674499473785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2079942622563597330526853 389989241730674499473785)
                  ·
                    rfl

theorem cell22_3417756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 3, 4].length) (baseStart_3417756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3417756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3417756 prefixEnd_3417756 := by exact prefixLift 3417756
  have htrace : WordTrace (prefixWord ++ tailWord_3417756) baseStart_3417756 baseEnd_3417756 := by
    simpa [prefixWord, tailWord_3417756, baseEnd_3417756] using wordTrace_append hprefix tailTrace_3417756
  have hstable : (prefixWord ++ tailWord_3417756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417756).length < 2 ^ (prefixWord ++ tailWord_3417756).sum := by decide
  have hdescent : baseEnd_3417756 < baseStart_3417756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417758 : List Nat := [4, 3, 1, 1, 1, 4, 2, 1, 1, 4]
def baseStart_3417758 : Nat := 118140960795 + 3417758 * 2 ^ 59
def prefixEnd_3417758 : Nat := 4983230072969 + 3 ^ 40 * 3417758 * 2
def baseEnd_3417758 : Nat := 1169968409832896159871349

theorem tailTrace_3417758 : CollatzResearch.WordTrace tailWord_3417758 prefixEnd_3417758 1169968409832896159871349 := by
  unfold tailWord_3417758
  simp only [CollatzResearch.WordTrace]
  refine ⟨15581984394006743430031741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83103916768035964960169285 15581984394006743430031741)
  ·
    refine ⟨5843244147752528786261903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15581984394006743430031741 5843244147752528786261903)
    ·
      refine ⟨8764866221628793179392855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5843244147752528786261903 8764866221628793179392855)
      ·
        refine ⟨13147299332443189769089283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8764866221628793179392855 13147299332443189769089283)
        ·
          refine ⟨19720948998664784653633925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13147299332443189769089283 19720948998664784653633925)
          ·
            refine ⟨3697677937249647122556361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19720948998664784653633925 3697677937249647122556361)
            ·
              refine ⟨2773258452937235341917271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3697677937249647122556361 2773258452937235341917271)
              ·
                refine ⟨4159887679405853012875907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2773258452937235341917271 4159887679405853012875907)
                ·
                  refine ⟨6239831519108779519313861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4159887679405853012875907 6239831519108779519313861)
                  ·
                    refine ⟨1169968409832896159871349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6239831519108779519313861 1169968409832896159871349)
                    ·
                      rfl

theorem cell22_3417758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_3417758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3417758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3417758 prefixEnd_3417758 := by exact prefixLift 3417758
  have htrace : WordTrace (prefixWord ++ tailWord_3417758) baseStart_3417758 baseEnd_3417758 := by
    simpa [prefixWord, tailWord_3417758, baseEnd_3417758] using wordTrace_append hprefix tailTrace_3417758
  have hstable : (prefixWord ++ tailWord_3417758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417758).length < 2 ^ (prefixWord ++ tailWord_3417758).sum := by decide
  have hdescent : baseEnd_3417758 < baseStart_3417758 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417846 : List Nat := [5, 1, 1, 1, 1, 3, 4, 1, 5]
def baseStart_3417846 : Nat := 118140960795 + 3417846 * 2 ^ 59
def prefixEnd_3417846 : Nat := 4983230072969 + 3 ^ 40 * 3417846 * 2
def baseEnd_3417846 : Nat := 389999511343764421223693

theorem tailTrace_3417846 : CollatzResearch.WordTrace tailWord_3417846 prefixEnd_3417846 389999511343764421223693 := by
  unfold tailWord_3417846
  simp only [CollatzResearch.WordTrace]
  refine ⟨7791192798483446154341087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83106056517156758979638261 7791192798483446154341087)
  ·
    refine ⟨11686789197725169231511631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7791192798483446154341087 11686789197725169231511631)
    ·
      refine ⟨17530183796587753847267447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11686789197725169231511631 17530183796587753847267447)
      ·
        refine ⟨26295275694881630770901171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17530183796587753847267447 26295275694881630770901171)
        ·
          refine ⟨39442913542322446156351757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26295275694881630770901171 39442913542322446156351757)
          ·
            refine ⟨14791092578370917308631909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39442913542322446156351757 14791092578370917308631909)
            ·
              refine ⟨2773329858444546995368483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14791092578370917308631909 2773329858444546995368483)
              ·
                refine ⟨4159994787666820493052725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2773329858444546995368483 4159994787666820493052725)
                ·
                  refine ⟨389999511343764421223693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4159994787666820493052725 389999511343764421223693)
                  ·
                    rfl

theorem cell22_3417846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 4, 1, 5].length) (baseStart_3417846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3417846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3417846 prefixEnd_3417846 := by exact prefixLift 3417846
  have htrace : WordTrace (prefixWord ++ tailWord_3417846) baseStart_3417846 baseEnd_3417846 := by
    simpa [prefixWord, tailWord_3417846, baseEnd_3417846] using wordTrace_append hprefix tailTrace_3417846
  have hstable : (prefixWord ++ tailWord_3417846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417846).length < 2 ^ (prefixWord ++ tailWord_3417846).sum := by decide
  have hdescent : baseEnd_3417846 < baseStart_3417846 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417857 : List Nat := [1, 2, 4, 1, 1, 1, 2, 4, 6]
def baseStart_3417857 : Nat := 118140960795 + 3417857 * 2 ^ 59
def prefixEnd_3417857 : Nat := 4983230072969 + 3 ^ 40 * 3417857 * 2
def baseEnd_3417857 : Nat := 390000766518697633882015

theorem tailTrace_3417857 : CollatzResearch.WordTrace tailWord_3417857 prefixEnd_3417857 390000766518697633882015 := by
  unfold tailWord_3417857
  simp only [CollatzResearch.WordTrace]
  refine ⟨124659485978695287348107825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83106323985796858232071883 124659485978695287348107825)
  ·
    refine ⟨93494614484021465511080869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124659485978695287348107825 93494614484021465511080869)
    ·
      refine ⟨17530240215754024783327663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93494614484021465511080869 17530240215754024783327663)
      ·
        refine ⟨26295360323631037174991495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17530240215754024783327663 26295360323631037174991495)
        ·
          refine ⟨39443040485446555762487243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26295360323631037174991495 39443040485446555762487243)
          ·
            refine ⟨59164560728169833643730865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39443040485446555762487243 59164560728169833643730865)
            ·
              refine ⟨44373420546127375232798149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59164560728169833643730865 44373420546127375232798149)
              ·
                refine ⟨8320016352398882856149653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44373420546127375232798149 8320016352398882856149653)
                ·
                  refine ⟨390000766518697633882015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8320016352398882856149653 390000766518697633882015)
                  ·
                    rfl

theorem cell22_3417857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 4, 6].length) (baseStart_3417857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3417857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3417857 prefixEnd_3417857 := by exact prefixLift 3417857
  have htrace : WordTrace (prefixWord ++ tailWord_3417857) baseStart_3417857 baseEnd_3417857 := by
    simpa [prefixWord, tailWord_3417857, baseEnd_3417857] using wordTrace_append hprefix tailTrace_3417857
  have hstable : (prefixWord ++ tailWord_3417857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417857).length < 2 ^ (prefixWord ++ tailWord_3417857).sum := by decide
  have hdescent : baseEnd_3417857 < baseStart_3417857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417859 : List Nat := [1, 1, 1, 3, 2, 2, 5, 2, 1, 4]
def baseStart_3417859 : Nat := 118140960795 + 3417859 * 2 ^ 59
def prefixEnd_3417859 : Nat := 4983230072969 + 3 ^ 40 * 3417859 * 2
def baseEnd_3417859 : Nat := 1170002984196965563096039

theorem tailTrace_3417859 : CollatzResearch.WordTrace tailWord_3417859 prefixEnd_3417859 1170002984196965563096039 := by
  unfold tailWord_3417859
  simp only [CollatzResearch.WordTrace]
  refine ⟨124659558924688041689680631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83106372616458694459787087 124659558924688041689680631)
  ·
    refine ⟨186989338387032062534520947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124659558924688041689680631 186989338387032062534520947)
    ·
      refine ⟨280484007580548093801781421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186989338387032062534520947 280484007580548093801781421)
      ·
        refine ⟨105181502842705535175668033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 280484007580548093801781421 105181502842705535175668033)
        ·
          refine ⟨78886127132029151381751025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105181502842705535175668033 78886127132029151381751025)
          ·
            refine ⟨59164595349021863536313269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78886127132029151381751025 59164595349021863536313269)
            ·
              refine ⟨5546680813970799706529369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59164595349021863536313269 5546680813970799706529369)
              ·
                refine ⟨4160010610478099779897027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5546680813970799706529369 4160010610478099779897027)
                ·
                  refine ⟨6240015915717149669845541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4160010610478099779897027 6240015915717149669845541)
                  ·
                    refine ⟨1170002984196965563096039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6240015915717149669845541 1170002984196965563096039)
                    ·
                      rfl

theorem cell22_3417859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 2, 1, 4].length) (baseStart_3417859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3417859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3417859 prefixEnd_3417859 := by exact prefixLift 3417859
  have htrace : WordTrace (prefixWord ++ tailWord_3417859) baseStart_3417859 baseEnd_3417859 := by
    simpa [prefixWord, tailWord_3417859, baseEnd_3417859] using wordTrace_append hprefix tailTrace_3417859
  have hstable : (prefixWord ++ tailWord_3417859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417859).length < 2 ^ (prefixWord ++ tailWord_3417859).sum := by decide
  have hdescent : baseEnd_3417859 < baseStart_3417859 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417891 : List Nat := [1, 1, 1, 4, 2, 1, 6, 2, 4]
def baseStart_3417891 : Nat := 118140960795 + 3417891 * 2 ^ 59
def prefixEnd_3417891 : Nat := 4983230072969 + 3 ^ 40 * 3417891 * 2
def baseEnd_3417891 : Nat := 390004646150309382098647

theorem tailTrace_3417891 : CollatzResearch.WordTrace tailWord_3417891 prefixEnd_3417891 390004646150309382098647 := by
  unfold tailWord_3417891
  simp only [CollatzResearch.WordTrace]
  refine ⟨124660726060572111154845527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83107150707048074103230351 124660726060572111154845527)
  ·
    refine ⟨186991089090858166732268291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124660726060572111154845527 186991089090858166732268291)
    ·
      refine ⟨280486633636287250098402437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186991089090858166732268291 280486633636287250098402437)
      ·
        refine ⟨52591243806803859393450457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 280486633636287250098402437 52591243806803859393450457)
        ·
          refine ⟨39443432855102894545087843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52591243806803859393450457 39443432855102894545087843)
          ·
            refine ⟨59165149282654341817631765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39443432855102894545087843 59165149282654341817631765)
            ·
              refine ⟨2773366372624422272701489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 59165149282654341817631765 2773366372624422272701489)
              ·
                refine ⟨2080024779468316704526117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2773366372624422272701489 2080024779468316704526117)
                ·
                  refine ⟨390004646150309382098647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2080024779468316704526117 390004646150309382098647)
                  ·
                    rfl

theorem cell22_3417891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 6, 2, 4].length) (baseStart_3417891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3417891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3417891 prefixEnd_3417891 := by exact prefixLift 3417891
  have htrace : WordTrace (prefixWord ++ tailWord_3417891) baseStart_3417891 baseEnd_3417891 := by
    simpa [prefixWord, tailWord_3417891, baseEnd_3417891] using wordTrace_append hprefix tailTrace_3417891
  have hstable : (prefixWord ++ tailWord_3417891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417891).length < 2 ^ (prefixWord ++ tailWord_3417891).sum := by decide
  have hdescent : baseEnd_3417891 < baseStart_3417891 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417906 : List Nat := [3, 2, 1, 1, 3, 2, 2, 3, 2, 3]
def baseStart_3417906 : Nat := 118140960795 + 3417906 * 2 ^ 59
def prefixEnd_3417906 : Nat := 4983230072969 + 3 ^ 40 * 3417906 * 2
def baseEnd_3417906 : Nat := 1170019073257473107170895

theorem tailTrace_3417906 : CollatzResearch.WordTrace tailWord_3417906 prefixEnd_3417906 1170019073257473107170895 := by
  unfold tailWord_3417906
  simp only [CollatzResearch.WordTrace]
  refine ⟨31165318288879442179160393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83107515437011845811094381 31165318288879442179160393)
  ·
    refine ⟨23373988716659581634370295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31165318288879442179160393 23373988716659581634370295)
    ·
      refine ⟨35060983074989372451555443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23373988716659581634370295 35060983074989372451555443)
      ·
        refine ⟨52591474612484058677333165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35060983074989372451555443 52591474612484058677333165)
        ·
          refine ⟨19721802979681522003999937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52591474612484058677333165 19721802979681522003999937)
          ·
            refine ⟨14791352234761141502999953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19721802979681522003999937 14791352234761141502999953)
            ·
              refine ⟨11093514176070856127249965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14791352234761141502999953 11093514176070856127249965)
              ·
                refine ⟨4160067816026571047718737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11093514176070856127249965 4160067816026571047718737)
                ·
                  refine ⟨3120050862019928285789053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4160067816026571047718737 3120050862019928285789053)
                  ·
                    refine ⟨1170019073257473107170895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3120050862019928285789053 1170019073257473107170895)
                    ·
                      rfl

theorem cell22_3417906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 3, 2, 3].length) (baseStart_3417906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3417906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3417906 prefixEnd_3417906 := by exact prefixLift 3417906
  have htrace : WordTrace (prefixWord ++ tailWord_3417906) baseStart_3417906 baseEnd_3417906 := by
    simpa [prefixWord, tailWord_3417906, baseEnd_3417906] using wordTrace_append hprefix tailTrace_3417906
  have hstable : (prefixWord ++ tailWord_3417906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417906).length < 2 ^ (prefixWord ++ tailWord_3417906).sum := by decide
  have hdescent : baseEnd_3417906 < baseStart_3417906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417951 : List Nat := [1, 1, 2, 3, 1, 5, 2, 1, 3, 3]
def baseStart_3417951 : Nat := 118140960795 + 3417951 * 2 ^ 59
def prefixEnd_3417951 : Nat := 4983230072969 + 3 ^ 40 * 3417951 * 2
def baseEnd_3417951 : Nat := 1170034477677107989795757

theorem tailTrace_3417951 : CollatzResearch.WordTrace tailWord_3417951 prefixEnd_3417951 1170034477677107989795757 := by
  unfold tailWord_3417951
  simp only [CollatzResearch.WordTrace]
  refine ⟨124662914440354741402029707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83108609626903160934686471 124662914440354741402029707)
  ·
    refine ⟨186994371660532112103044561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124662914440354741402029707 186994371660532112103044561)
    ·
      refine ⟨140245778745399084077283421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186994371660532112103044561 140245778745399084077283421)
      ·
        refine ⟨52592167029524656528981283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140245778745399084077283421 52592167029524656528981283)
        ·
          refine ⟨78888250544286984793471925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52592167029524656528981283 78888250544286984793471925)
          ·
            refine ⟨7395773488526904824387993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78888250544286984793471925 7395773488526904824387993)
            ·
              refine ⟨5546830116395178618290995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7395773488526904824387993 5546830116395178618290995)
              ·
                refine ⟨8320245174592767927436493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5546830116395178618290995 8320245174592767927436493)
                ·
                  refine ⟨3120091940472287972788685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8320245174592767927436493 3120091940472287972788685)
                  ·
                    refine ⟨1170034477677107989795757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3120091940472287972788685 1170034477677107989795757)
                    ·
                      rfl

theorem cell22_3417951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 1, 3, 3].length) (baseStart_3417951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3417951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3417951 prefixEnd_3417951 := by exact prefixLift 3417951
  have htrace : WordTrace (prefixWord ++ tailWord_3417951) baseStart_3417951 baseEnd_3417951 := by
    simpa [prefixWord, tailWord_3417951, baseEnd_3417951] using wordTrace_append hprefix tailTrace_3417951
  have hstable : (prefixWord ++ tailWord_3417951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417951).length < 2 ^ (prefixWord ++ tailWord_3417951).sum := by decide
  have hdescent : baseEnd_3417951 < baseStart_3417951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418002 : List Nat := [3, 2, 3, 2, 1, 2, 3, 2, 1, 3]
def baseStart_3418002 : Nat := 118140960795 + 3418002 * 2 ^ 59
def prefixEnd_3418002 : Nat := 4983230072969 + 3 ^ 40 * 3418002 * 2
def baseEnd_3418002 : Nat := 1170051936019360856770601

theorem tailTrace_3418002 : CollatzResearch.WordTrace tailWord_3418002 prefixEnd_3418002 1170051936019360856770601 := by
  unfold tailWord_3418002
  simp only [CollatzResearch.WordTrace]
  refine ⟨31166193640792494278034065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83109849708779984741424173 31166193640792494278034065)
  ·
    refine ⟨23374645230594370708525549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31166193640792494278034065 23374645230594370708525549)
    ·
      refine ⟨8765491961472889015697081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23374645230594370708525549 8765491961472889015697081)
      ·
        refine ⟨6574118971104666761772811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8765491961472889015697081 6574118971104666761772811)
        ·
          refine ⟨9861178456657000142659217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6574118971104666761772811 9861178456657000142659217)
          ·
            refine ⟨7395883842492750106994413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9861178456657000142659217 7395883842492750106994413)
            ·
              refine ⟨2773456440934781290122905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7395883842492750106994413 2773456440934781290122905)
              ·
                refine ⟨2080092330701085967592179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2773456440934781290122905 2080092330701085967592179)
                ·
                  refine ⟨3120138496051628951388269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2080092330701085967592179 3120138496051628951388269)
                  ·
                    refine ⟨1170051936019360856770601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3120138496051628951388269 1170051936019360856770601)
                    ·
                      rfl

theorem cell22_3418002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_3418002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3418002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3418002 prefixEnd_3418002 := by exact prefixLift 3418002
  have htrace : WordTrace (prefixWord ++ tailWord_3418002) baseStart_3418002 baseEnd_3418002 := by
    simpa [prefixWord, tailWord_3418002, baseEnd_3418002] using wordTrace_append hprefix tailTrace_3418002
  have hstable : (prefixWord ++ tailWord_3418002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418002).length < 2 ^ (prefixWord ++ tailWord_3418002).sum := by decide
  have hdescent : baseEnd_3418002 < baseStart_3418002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418009 : List Nat := [1, 2, 1, 2, 1, 3, 5, 1, 6]
def baseStart_3418009 : Nat := 118140960795 + 3418009 * 2 ^ 59
def prefixEnd_3418009 : Nat := 4983230072969 + 3 ^ 40 * 3418009 * 2
def baseEnd_3418009 : Nat := 390018110754138390615193

theorem tailTrace_3418009 : CollatzResearch.WordTrace tailWord_3418009 prefixEnd_3418009 390018110754138390615193 := by
  unfold tailWord_3418009
  simp only [CollatzResearch.WordTrace]
  refine ⟨124665029874144617307641081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83110019916096411538427387 124665029874144617307641081)
  ·
    refine ⟨93498772405608462980730811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124665029874144617307641081 93498772405608462980730811)
    ·
      refine ⟨140248158608412694471096217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93498772405608462980730811 140248158608412694471096217)
      ·
        refine ⟨105186118956309520853322163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140248158608412694471096217 105186118956309520853322163)
        ·
          refine ⟨157779178434464281279983245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105186118956309520853322163 157779178434464281279983245)
          ·
            refine ⟨59167191912924105479993717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157779178434464281279983245 59167191912924105479993717)
            ·
              refine ⟨5546924241836634888749411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59167191912924105479993717 5546924241836634888749411)
              ·
                refine ⟨8320386362754952333124117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5546924241836634888749411 8320386362754952333124117)
                ·
                  refine ⟨390018110754138390615193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8320386362754952333124117 390018110754138390615193)
                  ·
                    rfl

theorem cell22_3418009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 1, 6].length) (baseStart_3418009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3418009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3418009 prefixEnd_3418009 := by exact prefixLift 3418009
  have htrace : WordTrace (prefixWord ++ tailWord_3418009) baseStart_3418009 baseEnd_3418009 := by
    simpa [prefixWord, tailWord_3418009, baseEnd_3418009] using wordTrace_append hprefix tailTrace_3418009
  have hstable : (prefixWord ++ tailWord_3418009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418009).length < 2 ^ (prefixWord ++ tailWord_3418009).sum := by decide
  have hdescent : baseEnd_3418009 < baseStart_3418009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418015 : List Nat := [1, 1, 2, 5, 4, 1, 2, 1, 5]
def baseStart_3418015 : Nat := 118140960795 + 3418015 * 2 ^ 59
def prefixEnd_3418015 : Nat := 4983230072969 + 3 ^ 40 * 3418015 * 2
def baseEnd_3418015 : Nat := 390018795395011052065187

theorem tailTrace_3418015 : CollatzResearch.WordTrace tailWord_3418015 prefixEnd_3418015 390018795395011052065187 := by
  unfold tailWord_3418015
  simp only [CollatzResearch.WordTrace]
  refine ⟨124665248712122880332359499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83110165808081920221572999 124665248712122880332359499)
  ·
    refine ⟨186997873068184320498539249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124665248712122880332359499 186997873068184320498539249)
    ·
      refine ⟨140248404801138240373904437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186997873068184320498539249 140248404801138240373904437)
      ·
        refine ⟨13148287950106710035053541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 140248404801138240373904437 13148287950106710035053541)
        ·
          refine ⟨2465303990645008131572539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13148287950106710035053541 2465303990645008131572539)
          ·
            refine ⟨3697955985967512197358809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2465303990645008131572539 3697955985967512197358809)
            ·
              refine ⟨2773466989475634148019107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3697955985967512197358809 2773466989475634148019107)
              ·
                refine ⟨4160200484213451222028661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2773466989475634148019107 4160200484213451222028661)
                ·
                  refine ⟨390018795395011052065187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4160200484213451222028661 390018795395011052065187)
                  ·
                    rfl

theorem cell22_3418015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 2, 1, 5].length) (baseStart_3418015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3418015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3418015 prefixEnd_3418015 := by exact prefixLift 3418015
  have htrace : WordTrace (prefixWord ++ tailWord_3418015) baseStart_3418015 baseEnd_3418015 := by
    simpa [prefixWord, tailWord_3418015, baseEnd_3418015] using wordTrace_append hprefix tailTrace_3418015
  have hstable : (prefixWord ++ tailWord_3418015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418015).length < 2 ^ (prefixWord ++ tailWord_3418015).sum := by decide
  have hdescent : baseEnd_3418015 < baseStart_3418015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418056 : List Nat := [2, 1, 3, 1, 4, 1, 2, 2, 2, 4]
def baseStart_3418056 : Nat := 118140960795 + 3418056 * 2 ^ 59
def prefixEnd_3418056 : Nat := 4983230072969 + 3 ^ 40 * 3418056 * 2
def baseEnd_3418056 : Nat := 1170070421322922715920435

theorem tailTrace_3418056 : CollatzResearch.WordTrace tailWord_3418056 prefixEnd_3418056 1170070421322922715920435 := by
  unfold tailWord_3418056
  simp only [CollatzResearch.WordTrace]
  refine ⟨62333372052487172167301011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83111162736649562889734681 62333372052487172167301011)
  ·
    refine ⟨93500058078730758250951517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62333372052487172167301011 93500058078730758250951517)
    ·
      refine ⟨35062521779524034344106819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93500058078730758250951517 35062521779524034344106819)
      ·
        refine ⟨52593782669286051516160229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35062521779524034344106819 52593782669286051516160229)
        ·
          refine ⟨9861334250491134659280043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52593782669286051516160229 9861334250491134659280043)
          ·
            refine ⟨14792001375736701988920065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9861334250491134659280043 14792001375736701988920065)
            ·
              refine ⟨11094001031802526491690049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14792001375736701988920065 11094001031802526491690049)
              ·
                refine ⟨8320500773851894868767537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11094001031802526491690049 8320500773851894868767537)
                ·
                  refine ⟨6240375580388921151575653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8320500773851894868767537 6240375580388921151575653)
                  ·
                    refine ⟨1170070421322922715920435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6240375580388921151575653 1170070421322922715920435)
                    ·
                      rfl

theorem cell22_3418056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 2, 2, 4].length) (baseStart_3418056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3418056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3418056 prefixEnd_3418056 := by exact prefixLift 3418056
  have htrace : WordTrace (prefixWord ++ tailWord_3418056) baseStart_3418056 baseEnd_3418056 := by
    simpa [prefixWord, tailWord_3418056, baseEnd_3418056] using wordTrace_append hprefix tailTrace_3418056
  have hstable : (prefixWord ++ tailWord_3418056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418056).length < 2 ^ (prefixWord ++ tailWord_3418056).sum := by decide
  have hdescent : baseEnd_3418056 < baseStart_3418056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418060 : List Nat := [2, 2, 1, 4, 1, 4, 2, 2, 4]
def baseStart_3418060 : Nat := 118140960795 + 3418060 * 2 ^ 59
def prefixEnd_3418060 : Nat := 4983230072969 + 3 ^ 40 * 3418060 * 2
def baseEnd_3418060 : Nat := 390023930201556012940141

theorem tailTrace_3418060 : CollatzResearch.WordTrace tailWord_3418060 prefixEnd_3418060 390023930201556012940141 := by
  unfold tailWord_3418060
  simp only [CollatzResearch.WordTrace]
  refine ⟨62333444998479926508873817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83111259997973235345165089 62333444998479926508873817)
  ·
    refine ⟨46750083748859944881655363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62333444998479926508873817 46750083748859944881655363)
    ·
      refine ⟨70125125623289917322483045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46750083748859944881655363 70125125623289917322483045)
      ·
        refine ⟨13148461054366859497965571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70125125623289917322483045 13148461054366859497965571)
        ·
          refine ⟨19722691581550289246948357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13148461054366859497965571 19722691581550289246948357)
          ·
            refine ⟨3698004671540679233802817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19722691581550289246948357 3698004671540679233802817)
            ·
              refine ⟨2773503503655509425352113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3698004671540679233802817 2773503503655509425352113)
              ·
                refine ⟨2080127627741632069014085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2773503503655509425352113 2080127627741632069014085)
                ·
                  refine ⟨390023930201556012940141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2080127627741632069014085 390023930201556012940141)
                  ·
                    rfl

theorem cell22_3418060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 2, 2, 4].length) (baseStart_3418060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3418060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3418060 prefixEnd_3418060 := by exact prefixLift 3418060
  have htrace : WordTrace (prefixWord ++ tailWord_3418060) baseStart_3418060 baseEnd_3418060 := by
    simpa [prefixWord, tailWord_3418060, baseEnd_3418060] using wordTrace_append hprefix tailTrace_3418060
  have hstable : (prefixWord ++ tailWord_3418060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418060).length < 2 ^ (prefixWord ++ tailWord_3418060).sum := by decide
  have hdescent : baseEnd_3418060 < baseStart_3418060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418084 : List Nat := [2, 3, 1, 1, 1, 1, 3, 2, 2, 6]
def baseStart_3418084 : Nat := 118140960795 + 3418084 * 2 ^ 59
def prefixEnd_3418084 : Nat := 4983230072969 + 3 ^ 40 * 3418084 * 2
def baseEnd_3418084 : Nat := 1170080006295139976220349

theorem tailTrace_3418084 : CollatzResearch.WordTrace tailWord_3418084 prefixEnd_3418084 1170080006295139976220349 := by
  unfold tailWord_3418084
  simp only [CollatzResearch.WordTrace]
  refine ⟨62333882674436452558310653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83111843565915270077747537 62333882674436452558310653)
  ·
    refine ⟨23375206002913669709366495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62333882674436452558310653 23375206002913669709366495)
    ·
      refine ⟨35062809004370504564049743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23375206002913669709366495 35062809004370504564049743)
      ·
        refine ⟨52594213506555756846074615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35062809004370504564049743 52594213506555756846074615)
        ·
          refine ⟨78891320259833635269111923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52594213506555756846074615 78891320259833635269111923)
          ·
            refine ⟨118336980389750452903667885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78891320259833635269111923 118336980389750452903667885)
            ·
              refine ⟨44376367646156419838875457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118336980389750452903667885 44376367646156419838875457)
              ·
                refine ⟨33282275734617314879156593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44376367646156419838875457 33282275734617314879156593)
                ·
                  refine ⟨24961706800962986159367445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33282275734617314879156593 24961706800962986159367445)
                  ·
                    refine ⟨1170080006295139976220349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24961706800962986159367445 1170080006295139976220349)
                    ·
                      rfl

theorem cell22_3418084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_3418084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3418084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3418084 prefixEnd_3418084 := by exact prefixLift 3418084
  have htrace : WordTrace (prefixWord ++ tailWord_3418084) baseStart_3418084 baseEnd_3418084 := by
    simpa [prefixWord, tailWord_3418084, baseEnd_3418084] using wordTrace_append hprefix tailTrace_3418084
  have hstable : (prefixWord ++ tailWord_3418084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418084).length < 2 ^ (prefixWord ++ tailWord_3418084).sum := by decide
  have hdescent : baseEnd_3418084 < baseStart_3418084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418208 : List Nat := [2, 1, 1, 3, 2, 4, 2, 1, 2, 4]
def baseStart_3418208 : Nat := 118140960795 + 3418208 * 2 ^ 59
def prefixEnd_3418208 : Nat := 4983230072969 + 3 ^ 40 * 3418208 * 2
def baseEnd_3418208 : Nat := 1170122454029244986119969

theorem tailTrace_3418208 : CollatzResearch.WordTrace tailWord_3418208 prefixEnd_3418208 1170122454029244986119969 := by
  unfold tailWord_3418208
  simp only [CollatzResearch.WordTrace]
  refine ⟨62336144000211837147067639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83114858666949116196090185 62336144000211837147067639)
  ·
    refine ⟨93504216000317755720601459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62336144000211837147067639 93504216000317755720601459)
    ·
      refine ⟨140256324000476633580902189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93504216000317755720601459 140256324000476633580902189)
      ·
        refine ⟨52596121500178737592838321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140256324000476633580902189 52596121500178737592838321)
        ·
          refine ⟨39447091125134053194628741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52596121500178737592838321 39447091125134053194628741)
          ·
            refine ⟨7396329585962634973992889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39447091125134053194628741 7396329585962634973992889)
            ·
              refine ⟨5547247189471976230494667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7396329585962634973992889 5547247189471976230494667)
              ·
                refine ⟨8320870784207964345742001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5547247189471976230494667 8320870784207964345742001)
                ·
                  refine ⟨6240653088155973259306501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8320870784207964345742001 6240653088155973259306501)
                  ·
                    refine ⟨1170122454029244986119969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6240653088155973259306501 1170122454029244986119969)
                    ·
                      rfl

theorem cell22_3418208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 1, 2, 4].length) (baseStart_3418208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3418208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3418208 prefixEnd_3418208 := by exact prefixLift 3418208
  have htrace : WordTrace (prefixWord ++ tailWord_3418208) baseStart_3418208 baseEnd_3418208 := by
    simpa [prefixWord, tailWord_3418208, baseEnd_3418208] using wordTrace_append hprefix tailTrace_3418208
  have hstable : (prefixWord ++ tailWord_3418208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418208).length < 2 ^ (prefixWord ++ tailWord_3418208).sum := by decide
  have hdescent : baseEnd_3418208 < baseStart_3418208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418210 : List Nat := [3, 3, 2, 2, 2, 1, 1, 2, 1, 5]
def baseStart_3418210 : Nat := 118140960795 + 3418210 * 2 ^ 59
def prefixEnd_3418210 : Nat := 4983230072969 + 3 ^ 40 * 3418210 * 2
def baseEnd_3418210 : Nat := 1170123138670117647569963

theorem tailTrace_3418210 : CollatzResearch.WordTrace tailWord_3418210 prefixEnd_3418210 1170123138670117647569963 := by
  unfold tailWord_3418210
  simp only [CollatzResearch.WordTrace]
  refine ⟨31168090236604107158927021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83114907297610952423805389 31168090236604107158927021)
  ·
    refine ⟨11688033838726540184597633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31168090236604107158927021 11688033838726540184597633)
    ·
      refine ⟨8766025379044905138448225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11688033838726540184597633 8766025379044905138448225)
      ·
        refine ⟨6574519034283678853836169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8766025379044905138448225 6574519034283678853836169)
        ·
          refine ⟨4930889275712759140377127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6574519034283678853836169 4930889275712759140377127)
          ·
            refine ⟨7396333913569138710565691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4930889275712759140377127 7396333913569138710565691)
            ·
              refine ⟨11094500870353708065848537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7396333913569138710565691 11094500870353708065848537)
              ·
                refine ⟨8320875652765281049386403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11094500870353708065848537 8320875652765281049386403)
                ·
                  refine ⟨12481313479147921574079605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8320875652765281049386403 12481313479147921574079605)
                  ·
                    refine ⟨1170123138670117647569963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12481313479147921574079605 1170123138670117647569963)
                    ·
                      rfl

theorem cell22_3418210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_3418210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3418210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3418210 prefixEnd_3418210 := by exact prefixLift 3418210
  have htrace : WordTrace (prefixWord ++ tailWord_3418210) baseStart_3418210 baseEnd_3418210 := by
    simpa [prefixWord, tailWord_3418210, baseEnd_3418210] using wordTrace_append hprefix tailTrace_3418210
  have hstable : (prefixWord ++ tailWord_3418210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418210).length < 2 ^ (prefixWord ++ tailWord_3418210).sum := by decide
  have hdescent : baseEnd_3418210 < baseStart_3418210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418236 : List Nat := [2, 2, 2, 1, 1, 4, 1, 1, 2, 6]
def baseStart_3418236 : Nat := 118140960795 + 3418236 * 2 ^ 59
def prefixEnd_3418236 : Nat := 4983230072969 + 3 ^ 40 * 3418236 * 2
def baseEnd_3418236 : Nat := 1170132039001462246419883

theorem tailTrace_3418236 : CollatzResearch.WordTrace tailWord_3418236 prefixEnd_3418236 1170132039001462246419883 := by
  unfold tailWord_3418236
  simp only [CollatzResearch.WordTrace]
  refine ⟨62336654622161117538077281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83115539496214823384103041 62336654622161117538077281)
  ·
    refine ⟨46752490966620838153557961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62336654622161117538077281 46752490966620838153557961)
    ·
      refine ⟨35064368224965628615168471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46752490966620838153557961 35064368224965628615168471)
      ·
        refine ⟨52596552337448442922752707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35064368224965628615168471 52596552337448442922752707)
        ·
          refine ⟨78894828506172664384129061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52596552337448442922752707 78894828506172664384129061)
          ·
            refine ⟨14792780344907374572024199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78894828506172664384129061 14792780344907374572024199)
            ·
              refine ⟨22189170517361061858036299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14792780344907374572024199 22189170517361061858036299)
              ·
                refine ⟨33283755776041592787054449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22189170517361061858036299 33283755776041592787054449)
                ·
                  refine ⟨24962816832031194590290837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33283755776041592787054449 24962816832031194590290837)
                  ·
                    refine ⟨1170132039001462246419883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24962816832031194590290837 1170132039001462246419883)
                    ·
                      rfl

theorem cell22_3418236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_3418236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3418236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3418236 prefixEnd_3418236 := by exact prefixLift 3418236
  have htrace : WordTrace (prefixWord ++ tailWord_3418236) baseStart_3418236 baseEnd_3418236 := by
    simpa [prefixWord, tailWord_3418236, baseEnd_3418236] using wordTrace_append hprefix tailTrace_3418236
  have hstable : (prefixWord ++ tailWord_3418236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418236).length < 2 ^ (prefixWord ++ tailWord_3418236).sum := by decide
  have hdescent : baseEnd_3418236 < baseStart_3418236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418272 : List Nat := [2, 1, 1, 4, 2, 3, 2, 3, 1, 3]
def baseStart_3418272 : Nat := 118140960795 + 3418272 * 2 ^ 59
def prefixEnd_3418272 : Nat := 4983230072969 + 3 ^ 40 * 3418272 * 2
def baseEnd_3418272 : Nat := 1170144362537170152519773

theorem tailTrace_3418272 : CollatzResearch.WordTrace tailWord_3418272 prefixEnd_3418272 1170144362537170152519773 := by
  unfold tailWord_3418272
  simp only [CollatzResearch.WordTrace]
  refine ⟨62337311136095906612232535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83116414848127875482976713 62337311136095906612232535)
  ·
    refine ⟨93505966704143859918348803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62337311136095906612232535 93505966704143859918348803)
    ·
      refine ⟨140258950056215789877523205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93505966704143859918348803 140258950056215789877523205)
      ·
        refine ⟨26298553135540460602035601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140258950056215789877523205 26298553135540460602035601)
        ·
          refine ⟨19723914851655345451526701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26298553135540460602035601 19723914851655345451526701)
          ·
            refine ⟨7396468069370754544322513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19723914851655345451526701 7396468069370754544322513)
            ·
              refine ⟨5547351052028065908241885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7396468069370754544322513 5547351052028065908241885)
              ·
                refine ⟨2080256644510524715590707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5547351052028065908241885 2080256644510524715590707)
                ·
                  refine ⟨3120384966765787073386061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2080256644510524715590707 3120384966765787073386061)
                  ·
                    refine ⟨1170144362537170152519773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3120384966765787073386061 1170144362537170152519773)
                    ·
                      rfl

theorem cell22_3418272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 3, 1, 3].length) (baseStart_3418272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3418272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3418272 prefixEnd_3418272 := by exact prefixLift 3418272
  have htrace : WordTrace (prefixWord ++ tailWord_3418272) baseStart_3418272 baseEnd_3418272 := by
    simpa [prefixWord, tailWord_3418272, baseEnd_3418272] using wordTrace_append hprefix tailTrace_3418272
  have hstable : (prefixWord ++ tailWord_3418272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418272).length < 2 ^ (prefixWord ++ tailWord_3418272).sum := by decide
  have hdescent : baseEnd_3418272 < baseStart_3418272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418285 : List Nat := [1, 5, 2, 1, 2, 1, 3, 2, 5]
def baseStart_3418285 : Nat := 118140960795 + 3418285 * 2 ^ 59
def prefixEnd_3418285 : Nat := 4983230072969 + 3 ^ 40 * 3418285 * 2
def baseEnd_3418285 : Nat := 390049604234280817314911

theorem tailTrace_3418285 : CollatzResearch.WordTrace tailWord_3418285 prefixEnd_3418285 390049604234280817314911 := by
  unfold tailWord_3418285
  simp only [CollatzResearch.WordTrace]
  refine ⟨124675096421144716444688309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83116730947429810963125539 124675096421144716444688309)
  ·
    refine ⟨11688290289482317166689529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 124675096421144716444688309 11688290289482317166689529)
    ·
      refine ⟨8766217717111737875017147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11688290289482317166689529 8766217717111737875017147)
      ·
        refine ⟨13149326575667606812525721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8766217717111737875017147 13149326575667606812525721)
        ·
          refine ⟨9861994931750705109394291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13149326575667606812525721 9861994931750705109394291)
          ·
            refine ⟨14792992397626057664091437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9861994931750705109394291 14792992397626057664091437)
            ·
              refine ⟨5547372149109771624034289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14792992397626057664091437 5547372149109771624034289)
              ·
                refine ⟨4160529111832328718025717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5547372149109771624034289 4160529111832328718025717)
                ·
                  refine ⟨390049604234280817314911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4160529111832328718025717 390049604234280817314911)
                  ·
                    rfl

theorem cell22_3418285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_3418285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3418285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3418285 prefixEnd_3418285 := by exact prefixLift 3418285
  have htrace : WordTrace (prefixWord ++ tailWord_3418285) baseStart_3418285 baseEnd_3418285 := by
    simpa [prefixWord, tailWord_3418285, baseEnd_3418285] using wordTrace_append hprefix tailTrace_3418285
  have hstable : (prefixWord ++ tailWord_3418285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418285).length < 2 ^ (prefixWord ++ tailWord_3418285).sum := by decide
  have hdescent : baseEnd_3418285 < baseStart_3418285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418302 : List Nat := [4, 2, 1, 1, 4, 1, 3, 1, 5]
def baseStart_3418302 : Nat := 118140960795 + 3418302 * 2 ^ 59
def prefixEnd_3418302 : Nat := 4983230072969 + 3 ^ 40 * 3418302 * 2
def baseEnd_3418302 : Nat := 390051544050086691423227

theorem tailTrace_3418302 : CollatzResearch.WordTrace tailWord_3418302 prefixEnd_3418302 390051544050086691423227 := by
  unfold tailWord_3418302
  simp only [CollatzResearch.WordTrace]
  refine ⟨15584464557760391043507145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83117144308055418898704773 15584464557760391043507145)
  ·
    refine ⟨11688348418320293282630359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15584464557760391043507145 11688348418320293282630359)
    ·
      refine ⟨17532522627480439923945539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11688348418320293282630359 17532522627480439923945539)
      ·
        refine ⟨26298783941220659885918309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17532522627480439923945539 26298783941220659885918309)
        ·
          refine ⟨4931021988978873728609683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26298783941220659885918309 4931021988978873728609683)
          ·
            refine ⟨7396532983468310592914525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4931021988978873728609683 7396532983468310592914525)
            ·
              refine ⟨2773699868800616472342947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7396532983468310592914525 2773699868800616472342947)
              ·
                refine ⟨4160549803200924708514421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2773699868800616472342947 4160549803200924708514421)
                ·
                  refine ⟨390051544050086691423227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4160549803200924708514421 390051544050086691423227)
                  ·
                    rfl

theorem cell22_3418302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 3, 1, 5].length) (baseStart_3418302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3418302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3418302 prefixEnd_3418302 := by exact prefixLift 3418302
  have htrace : WordTrace (prefixWord ++ tailWord_3418302) baseStart_3418302 baseEnd_3418302 := by
    simpa [prefixWord, tailWord_3418302, baseEnd_3418302] using wordTrace_append hprefix tailTrace_3418302
  have hstable : (prefixWord ++ tailWord_3418302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418302).length < 2 ^ (prefixWord ++ tailWord_3418302).sum := by decide
  have hdescent : baseEnd_3418302 < baseStart_3418302 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418330 : List Nat := [3, 1, 1, 2, 2, 1, 5, 3, 4]
def baseStart_3418330 : Nat := 118140960795 + 3418330 * 2 ^ 59
def prefixEnd_3418330 : Nat := 4983230072969 + 3 ^ 40 * 3418330 * 2
def baseEnd_3418330 : Nat := 390054739040825778189865

theorem tailTrace_3418330 : CollatzResearch.WordTrace tailWord_3418330 prefixEnd_3418330 390054739040825778189865 := by
  unfold tailWord_3418330
  simp only [CollatzResearch.WordTrace]
  refine ⟨31169184426495422282519111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83117825137321126086717629 31169184426495422282519111)
  ·
    refine ⟨46753776639743133423778667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31169184426495422282519111 46753776639743133423778667)
    ·
      refine ⟨70130664959614700135668001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46753776639743133423778667 70130664959614700135668001)
      ·
        refine ⟨52597998719711025101751001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70130664959614700135668001 52597998719711025101751001)
        ·
          refine ⟨39448499039783268826313251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52597998719711025101751001 39448499039783268826313251)
          ·
            refine ⟨59172748559674903239469877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39448499039783268826313251 59172748559674903239469877)
            ·
              refine ⟨5547445177469522178700301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59172748559674903239469877 5547445177469522178700301)
              ·
                refine ⟨2080291941551070817012613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5547445177469522178700301 2080291941551070817012613)
                ·
                  refine ⟨390054739040825778189865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2080291941551070817012613 390054739040825778189865)
                  ·
                    rfl

theorem cell22_3418330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 3, 4].length) (baseStart_3418330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3418330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3418330 prefixEnd_3418330 := by exact prefixLift 3418330
  have htrace : WordTrace (prefixWord ++ tailWord_3418330) baseStart_3418330 baseEnd_3418330 := by
    simpa [prefixWord, tailWord_3418330, baseEnd_3418330] using wordTrace_append hprefix tailTrace_3418330
  have hstable : (prefixWord ++ tailWord_3418330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418330).length < 2 ^ (prefixWord ++ tailWord_3418330).sum := by decide
  have hdescent : baseEnd_3418330 < baseStart_3418330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418358 : List Nat := [5, 1, 1, 1, 1, 1, 3, 9]
def baseStart_3418358 : Nat := 118140960795 + 3418358 * 2 ^ 59
def prefixEnd_3418358 : Nat := 4983230072969 + 3 ^ 40 * 3418358 * 2
def baseEnd_3418358 : Nat := 130019311343854954985501

theorem tailTrace_3418358 : CollatzResearch.WordTrace tailWord_3418358 prefixEnd_3418358 130019311343854954985501 := by
  unfold tailWord_3418358
  simp only [CollatzResearch.WordTrace]
  refine ⟨7792359934367515619505983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83118505966586833274730485 7792359934367515619505983)
  ·
    refine ⟨11688539901551273429258975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7792359934367515619505983 11688539901551273429258975)
    ·
      refine ⟨17532809852326910143888463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11688539901551273429258975 17532809852326910143888463)
      ·
        refine ⟨26299214778490365215832695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17532809852326910143888463 26299214778490365215832695)
        ·
          refine ⟨39448822167735547823749043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26299214778490365215832695 39448822167735547823749043)
          ·
            refine ⟨59173233251603321735623565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39448822167735547823749043 59173233251603321735623565)
            ·
              refine ⟨22189962469351245650858837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59173233251603321735623565 22189962469351245650858837)
              ·
                refine ⟨130019311343854954985501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22189962469351245650858837 130019311343854954985501)
                ·
                  rfl

theorem cell22_3418358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 9].length) (baseStart_3418358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3418358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3418358 prefixEnd_3418358 := by exact prefixLift 3418358
  have htrace : WordTrace (prefixWord ++ tailWord_3418358) baseStart_3418358 baseEnd_3418358 := by
    simpa [prefixWord, tailWord_3418358, baseEnd_3418358] using wordTrace_append hprefix tailTrace_3418358
  have hstable : (prefixWord ++ tailWord_3418358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418358).length < 2 ^ (prefixWord ++ tailWord_3418358).sum := by decide
  have hdescent : baseEnd_3418358 < baseStart_3418358 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418362 : List Nat := [3, 1, 1, 1, 1, 5, 4, 1, 2, 3]
def baseStart_3418362 : Nat := 118140960795 + 3418362 * 2 ^ 59
def prefixEnd_3418362 : Nat := 4983230072969 + 3 ^ 40 * 3418362 * 2
def baseEnd_3418362 : Nat := 1170175171376439917769497

theorem tailTrace_3418362 : CollatzResearch.WordTrace tailWord_3418362 prefixEnd_3418362 1170175171376439917769497 := by
  unfold tailWord_3418362
  simp only [CollatzResearch.WordTrace]
  refine ⟨31169476210466439648810335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83118603227910505730160893 31169476210466439648810335)
  ·
    refine ⟨46754214315699659473215503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31169476210466439648810335 46754214315699659473215503)
    ·
      refine ⟨70131321473549489209823255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46754214315699659473215503 70131321473549489209823255)
      ·
        refine ⟨105196982210324233814734883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70131321473549489209823255 105196982210324233814734883)
        ·
          refine ⟨157795473315486350722102325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105196982210324233814734883 157795473315486350722102325)
          ·
            refine ⟨14793325623326845380197093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 157795473315486350722102325 14793325623326845380197093)
            ·
              refine ⟨2773748554373783508786955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14793325623326845380197093 2773748554373783508786955)
              ·
                refine ⟨4160622831560675263180433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2773748554373783508786955 4160622831560675263180433)
                ·
                  refine ⟨3120467123670506447385325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4160622831560675263180433 3120467123670506447385325)
                  ·
                    refine ⟨1170175171376439917769497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3120467123670506447385325 1170175171376439917769497)
                    ·
                      rfl

theorem cell22_3418362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 4, 1, 2, 3].length) (baseStart_3418362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3418362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3418362 prefixEnd_3418362 := by exact prefixLift 3418362
  have htrace : WordTrace (prefixWord ++ tailWord_3418362) baseStart_3418362 baseEnd_3418362 := by
    simpa [prefixWord, tailWord_3418362, baseEnd_3418362] using wordTrace_append hprefix tailTrace_3418362
  have hstable : (prefixWord ++ tailWord_3418362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418362).length < 2 ^ (prefixWord ++ tailWord_3418362).sum := by decide
  have hdescent : baseEnd_3418362 < baseStart_3418362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418463 : List Nat := [1, 1, 2, 3, 1, 2, 2, 2, 3, 5]
def baseStart_3418463 : Nat := 118140960795 + 3418463 * 2 ^ 59
def prefixEnd_3418463 : Nat := 4983230072969 + 3 ^ 40 * 3418463 * 2
def baseEnd_3418463 : Nat := 1170209745740509320994187

theorem tailTrace_3418463 : CollatzResearch.WordTrace tailWord_3418463 prefixEnd_3418463 1170209745740509320994187 := by
  unfold tailWord_3418463
  simp only [CollatzResearch.WordTrace]
  refine ⟨124681588614499852844668043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83121059076333235229778695 124681588614499852844668043)
  ·
    refine ⟨187022382921749779267002065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124681588614499852844668043 187022382921749779267002065)
    ·
      refine ⟨140266787191312334450251549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187022382921749779267002065 140266787191312334450251549)
      ·
        refine ⟨52600045196742125418844331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140266787191312334450251549 52600045196742125418844331)
        ·
          refine ⟨78900067795113188128266497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52600045196742125418844331 78900067795113188128266497)
          ·
            refine ⟨59175050846334891096199873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78900067795113188128266497 59175050846334891096199873)
            ·
              refine ⟨44381288134751168322149905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59175050846334891096199873 44381288134751168322149905)
              ·
                refine ⟨33285966101063376241612429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44381288134751168322149905 33285966101063376241612429)
                ·
                  refine ⟨12482237287898766090604661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33285966101063376241612429 12482237287898766090604661)
                  ·
                    refine ⟨1170209745740509320994187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12482237287898766090604661 1170209745740509320994187)
                    ·
                      rfl

theorem cell22_3418463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 3, 5].length) (baseStart_3418463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3418463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3418463 prefixEnd_3418463 := by exact prefixLift 3418463
  have htrace : WordTrace (prefixWord ++ tailWord_3418463) baseStart_3418463 baseEnd_3418463 := by
    simpa [prefixWord, tailWord_3418463, baseEnd_3418463] using wordTrace_append hprefix tailTrace_3418463
  have hstable : (prefixWord ++ tailWord_3418463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418463).length < 2 ^ (prefixWord ++ tailWord_3418463).sum := by decide
  have hdescent : baseEnd_3418463 < baseStart_3418463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418480 : List Nat := [2, 1, 1, 1, 4, 3, 3, 1, 1, 5]
def baseStart_3418480 : Nat := 118140960795 + 3418480 * 2 ^ 59
def prefixEnd_3418480 : Nat := 4983230072969 + 3 ^ 40 * 3418480 * 2
def baseEnd_3418480 : Nat := 1170215565187926943319135

theorem tailTrace_3418480 : CollatzResearch.WordTrace tailWord_3418480 prefixEnd_3418480 1170215565187926943319135 := by
  unfold tailWord_3418480
  simp only [CollatzResearch.WordTrace]
  refine ⟨62341104327719132374018447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83121472436958843165357929 62341104327719132374018447)
  ·
    refine ⟨93511656491578698561027671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62341104327719132374018447 93511656491578698561027671)
    ·
      refine ⟨140267484737368047841541507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93511656491578698561027671 140267484737368047841541507)
      ·
        refine ⟨210401227106052071762312261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140267484737368047841541507 210401227106052071762312261)
        ·
          refine ⟨39450230082384763455433549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 210401227106052071762312261 39450230082384763455433549)
          ·
            refine ⟨14793836280894286295787581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39450230082384763455433549 14793836280894286295787581)
            ·
              refine ⟨5547688605335357360920343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14793836280894286295787581 5547688605335357360920343)
              ·
                refine ⟨8321532908003036041380515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5547688605335357360920343 8321532908003036041380515)
                ·
                  refine ⟨12482299362004554062070773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8321532908003036041380515 12482299362004554062070773)
                  ·
                    refine ⟨1170215565187926943319135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12482299362004554062070773 1170215565187926943319135)
                    ·
                      rfl

theorem cell22_3418480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 1, 1, 5].length) (baseStart_3418480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3418480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3418480 prefixEnd_3418480 := by exact prefixLift 3418480
  have htrace : WordTrace (prefixWord ++ tailWord_3418480) baseStart_3418480 baseEnd_3418480 := by
    simpa [prefixWord, tailWord_3418480, baseEnd_3418480] using wordTrace_append hprefix tailTrace_3418480
  have hstable : (prefixWord ++ tailWord_3418480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418480).length < 2 ^ (prefixWord ++ tailWord_3418480).sum := by decide
  have hdescent : baseEnd_3418480 < baseStart_3418480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418497 : List Nat := [1, 2, 4, 3, 1, 1, 1, 2, 4, 3]
def baseStart_3418497 : Nat := 118140960795 + 3418497 * 2 ^ 59
def prefixEnd_3418497 : Nat := 4983230072969 + 3 ^ 40 * 3418497 * 2
def baseEnd_3418497 : Nat := 1170221384635344565644083

theorem tailTrace_3418497 : CollatzResearch.WordTrace tailWord_3418497 prefixEnd_3418497 1170221384635344565644083 := by
  unfold tailWord_3418497
  simp only [CollatzResearch.WordTrace]
  refine ⟨124682828696376676651405745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83121885797584451100937163 124682828696376676651405745)
  ·
    refine ⟨93512121522282507488554309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124682828696376676651405745 93512121522282507488554309)
    ·
      refine ⟨17533522785427970154103933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93512121522282507488554309 17533522785427970154103933)
      ·
        refine ⟨6575071044535488807788975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17533522785427970154103933 6575071044535488807788975)
        ·
          refine ⟨9862606566803233211683463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6575071044535488807788975 9862606566803233211683463)
          ·
            refine ⟨14793909850204849817525195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9862606566803233211683463 14793909850204849817525195)
            ·
              refine ⟨22190864775307274726287793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14793909850204849817525195 22190864775307274726287793)
              ·
                refine ⟨16643148581480456044715845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22190864775307274726287793 16643148581480456044715845)
                ·
                  refine ⟨3120590359027585508384221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16643148581480456044715845 3120590359027585508384221)
                  ·
                    refine ⟨1170221384635344565644083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3120590359027585508384221 1170221384635344565644083)
                    ·
                      rfl

theorem cell22_3418497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 4, 3].length) (baseStart_3418497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3418497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3418497 prefixEnd_3418497 := by exact prefixLift 3418497
  have htrace : WordTrace (prefixWord ++ tailWord_3418497) baseStart_3418497 baseEnd_3418497 := by
    simpa [prefixWord, tailWord_3418497, baseEnd_3418497] using wordTrace_append hprefix tailTrace_3418497
  have hstable : (prefixWord ++ tailWord_3418497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418497).length < 2 ^ (prefixWord ++ tailWord_3418497).sum := by decide
  have hdescent : baseEnd_3418497 < baseStart_3418497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418499 : List Nat := [1, 1, 1, 3, 6, 2, 1, 3, 4]
def baseStart_3418499 : Nat := 118140960795 + 3418499 * 2 ^ 59
def prefixEnd_3418499 : Nat := 4983230072969 + 3 ^ 40 * 3418499 * 2
def baseEnd_3418499 : Nat := 390074023092072409031359

theorem tailTrace_3418499 : CollatzResearch.WordTrace tailWord_3418499 prefixEnd_3418499 390074023092072409031359 := by
  unfold tailWord_3418499
  simp only [CollatzResearch.WordTrace]
  refine ⟨124682901642369430992978551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83121934428246287328652367 124682901642369430992978551)
  ·
    refine ⟨187024352463554146489467827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124682901642369430992978551 187024352463554146489467827)
    ·
      refine ⟨280536528695331219734201741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187024352463554146489467827 280536528695331219734201741)
      ·
        refine ⟨105201198260749207400325653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 280536528695331219734201741 105201198260749207400325653)
        ·
          refine ⟨4931306168472619096890265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 105201198260749207400325653 4931306168472619096890265)
          ·
            refine ⟨3698479626354464322667699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4931306168472619096890265 3698479626354464322667699)
            ·
              refine ⟨5547719439531696484001549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3698479626354464322667699 5547719439531696484001549)
              ·
                refine ⟨2080394789824386181500581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5547719439531696484001549 2080394789824386181500581)
                ·
                  refine ⟨390074023092072409031359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2080394789824386181500581 390074023092072409031359)
                  ·
                    rfl

theorem cell22_3418499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 3, 4].length) (baseStart_3418499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3418499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3418499 prefixEnd_3418499 := by exact prefixLift 3418499
  have htrace : WordTrace (prefixWord ++ tailWord_3418499) baseStart_3418499 baseEnd_3418499 := by
    simpa [prefixWord, tailWord_3418499, baseEnd_3418499] using wordTrace_append hprefix tailTrace_3418499
  have hstable : (prefixWord ++ tailWord_3418499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418499).length < 2 ^ (prefixWord ++ tailWord_3418499).sum := by decide
  have hdescent : baseEnd_3418499 < baseStart_3418499 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418510 : List Nat := [4, 1, 1, 4, 1, 1, 10]
def baseStart_3418510 : Nat := 118140960795 + 3418510 * 2 ^ 59
def prefixEnd_3418510 : Nat := 4983230072969 + 3 ^ 40 * 3418510 * 2
def baseEnd_3418510 : Nat := 43341697585222846854409

theorem tailTrace_3418510 : CollatzResearch.WordTrace tailWord_3418510 prefixEnd_3418510 43341697585222846854409 := by
  unfold tailWord_3418510
  simp only [CollatzResearch.WordTrace]
  refine ⟨15585412855666197483953623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83122201896886386581085989 15585412855666197483953623)
  ·
    refine ⟨23378119283499296225930435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15585412855666197483953623 23378119283499296225930435)
    ·
      refine ⟨35067178925248944338895653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23378119283499296225930435 35067178925248944338895653)
      ·
        refine ⟨6575096048484177063542935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35067178925248944338895653 6575096048484177063542935)
        ·
          refine ⟨9862644072726265595314403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6575096048484177063542935 9862644072726265595314403)
          ·
            refine ⟨14793966109089398392971605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9862644072726265595314403 14793966109089398392971605)
            ·
              refine ⟨43341697585222846854409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14793966109089398392971605 43341697585222846854409)
              ·
                rfl

theorem cell22_3418510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 10].length) (baseStart_3418510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3418510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3418510 prefixEnd_3418510 := by exact prefixLift 3418510
  have htrace : WordTrace (prefixWord ++ tailWord_3418510) baseStart_3418510 baseEnd_3418510 := by
    simpa [prefixWord, tailWord_3418510, baseEnd_3418510] using wordTrace_append hprefix tailTrace_3418510
  have hstable : (prefixWord ++ tailWord_3418510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418510).length < 2 ^ (prefixWord ++ tailWord_3418510).sum := by decide
  have hdescent : baseEnd_3418510 < baseStart_3418510 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418516 : List Nat := [2, 4, 2, 1, 3, 1, 3, 2, 4]
def baseStart_3418516 : Nat := 118140960795 + 3418516 * 2 ^ 59
def prefixEnd_3418516 : Nat := 4983230072969 + 3 ^ 40 * 3418516 * 2
def baseEnd_3418516 : Nat := 390075962907878283139675

theorem tailTrace_3418516 : CollatzResearch.WordTrace tailWord_3418516 prefixEnd_3418516 390075962907878283139675 := by
  unfold tailWord_3418516
  simp only [CollatzResearch.WordTrace]
  refine ⟨62341760841653921448173701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83122347788871895264231601 62341760841653921448173701)
  ·
    refine ⟨11689080157810110271532569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62341760841653921448173701 11689080157810110271532569)
    ·
      refine ⟨8766810118357582703649427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11689080157810110271532569 8766810118357582703649427)
      ·
        refine ⟨13150215177536374055474141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8766810118357582703649427 13150215177536374055474141)
        ·
          refine ⟨4931330691576140270802803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13150215177536374055474141 4931330691576140270802803)
          ·
            refine ⟨7396996037364210406204205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4931330691576140270802803 7396996037364210406204205)
            ·
              refine ⟨2773873514011578902326577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7396996037364210406204205 2773873514011578902326577)
              ·
                refine ⟨2080405135508684176744933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2773873514011578902326577 2080405135508684176744933)
                ·
                  refine ⟨390075962907878283139675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2080405135508684176744933 390075962907878283139675)
                  ·
                    rfl

theorem cell22_3418516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 3, 2, 4].length) (baseStart_3418516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3418516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3418516 prefixEnd_3418516 := by exact prefixLift 3418516
  have htrace : WordTrace (prefixWord ++ tailWord_3418516) baseStart_3418516 baseEnd_3418516 := by
    simpa [prefixWord, tailWord_3418516, baseEnd_3418516] using wordTrace_append hprefix tailTrace_3418516
  have hstable : (prefixWord ++ tailWord_3418516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418516).length < 2 ^ (prefixWord ++ tailWord_3418516).sum := by decide
  have hdescent : baseEnd_3418516 < baseStart_3418516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418570 : List Nat := [3, 1, 2, 1, 2, 2, 2, 2, 2, 5]
def baseStart_3418570 : Nat := 118140960795 + 3418570 * 2 ^ 59
def prefixEnd_3418570 : Nat := 4983230072969 + 3 ^ 40 * 3418570 * 2
def baseEnd_3418570 : Nat := 1170246374027196708568859

theorem tailTrace_3418570 : CollatzResearch.WordTrace tailWord_3418570 prefixEnd_3418570 1170246374027196708568859 := by
  unfold tailWord_3418570
  simp only [CollatzResearch.WordTrace]
  refine ⟨31171372806278052529703291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83123660816741473412542109 31171372806278052529703291)
  ·
    refine ⟨46757059209417078794554937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31171372806278052529703291 46757059209417078794554937)
    ·
      refine ⟨35067794407062809095916203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46757059209417078794554937 35067794407062809095916203)
      ·
        refine ⟨52601691610594213643874305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35067794407062809095916203 52601691610594213643874305)
        ·
          refine ⟨39451268707945660232905729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52601691610594213643874305 39451268707945660232905729)
          ·
            refine ⟨29588451530959245174679297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39451268707945660232905729 29588451530959245174679297)
            ·
              refine ⟨22191338648219433881009473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29588451530959245174679297 22191338648219433881009473)
              ·
                refine ⟨16643503986164575410757105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22191338648219433881009473 16643503986164575410757105)
                ·
                  refine ⟨12482627989623431558067829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16643503986164575410757105 12482627989623431558067829)
                  ·
                    refine ⟨1170246374027196708568859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12482627989623431558067829 1170246374027196708568859)
                    ·
                      rfl

theorem cell22_3418570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_3418570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3418570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3418570 prefixEnd_3418570 := by exact prefixLift 3418570
  have htrace : WordTrace (prefixWord ++ tailWord_3418570) baseStart_3418570 baseEnd_3418570 := by
    simpa [prefixWord, tailWord_3418570, baseEnd_3418570] using wordTrace_append hprefix tailTrace_3418570
  have hstable : (prefixWord ++ tailWord_3418570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418570).length < 2 ^ (prefixWord ++ tailWord_3418570).sum := by decide
  have hdescent : baseEnd_3418570 < baseStart_3418570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418585 : List Nat := [1, 2, 1, 2, 4, 1, 1, 1, 5, 4]
def baseStart_3418585 : Nat := 118140960795 + 3418585 * 2 ^ 59
def prefixEnd_3418585 : Nat := 4983230072969 + 3 ^ 40 * 3418585 * 2
def baseEnd_3418585 : Nat := 1170251508833741669443813

theorem tailTrace_3418585 : CollatzResearch.WordTrace tailWord_3418585 prefixEnd_3418585 1170251508833741669443813 := by
  unfold tailWord_3418585
  simp only [CollatzResearch.WordTrace]
  refine ⟨124686038320057867680609209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83124025546705245120406139 124686038320057867680609209)
  ·
    refine ⟨93514528740043400760456907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124686038320057867680609209 93514528740043400760456907)
    ·
      refine ⟨140271793110065101140685361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93514528740043400760456907 140271793110065101140685361)
      ·
        refine ⟨105203844832548825855514021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140271793110065101140685361 105203844832548825855514021)
        ·
          refine ⟨19725720906102904847908879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105203844832548825855514021 19725720906102904847908879)
          ·
            refine ⟨29588581359154357271863319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19725720906102904847908879 29588581359154357271863319)
            ·
              refine ⟨44382872038731535907794979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29588581359154357271863319 44382872038731535907794979)
              ·
                refine ⟨66574308058097303861692469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44382872038731535907794979 66574308058097303861692469)
                ·
                  refine ⟨6241341380446622237033669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66574308058097303861692469 6241341380446622237033669)
                  ·
                    refine ⟨1170251508833741669443813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6241341380446622237033669 1170251508833741669443813)
                    ·
                      rfl

theorem cell22_3418585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 5, 4].length) (baseStart_3418585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3418585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3418585 prefixEnd_3418585 := by exact prefixLift 3418585
  have htrace : WordTrace (prefixWord ++ tailWord_3418585) baseStart_3418585 baseEnd_3418585 := by
    simpa [prefixWord, tailWord_3418585, baseEnd_3418585] using wordTrace_append hprefix tailTrace_3418585
  have hstable : (prefixWord ++ tailWord_3418585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418585).length < 2 ^ (prefixWord ++ tailWord_3418585).sum := by decide
  have hdescent : baseEnd_3418585 < baseStart_3418585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418600 : List Nat := [2, 1, 4, 1, 1, 3, 1, 1, 8]
def baseStart_3418600 : Nat := 118140960795 + 3418600 * 2 ^ 59
def prefixEnd_3418600 : Nat := 4983230072969 + 3 ^ 40 * 3418600 * 2
def baseEnd_3418600 : Nat := 390085547880095543439589

theorem tailTrace_3418600 : CollatzResearch.WordTrace tailWord_3418600 prefixEnd_3418600 390085547880095543439589 := by
  unfold tailWord_3418600
  simp only [CollatzResearch.WordTrace]
  refine ⟨62343292707501762621202627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83124390276669016828270169 62343292707501762621202627)
  ·
    refine ⟨93514939061252643931803941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62343292707501762621202627 93514939061252643931803941)
    ·
      refine ⟨17534051073984870737213239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93514939061252643931803941 17534051073984870737213239)
      ·
        refine ⟨26301076610977306105819859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17534051073984870737213239 26301076610977306105819859)
        ·
          refine ⟨39451614916465959158729789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26301076610977306105819859 39451614916465959158729789)
          ·
            refine ⟨14794355593674734684523671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39451614916465959158729789 14794355593674734684523671)
            ·
              refine ⟨22191533390512102026785507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14794355593674734684523671 22191533390512102026785507)
              ·
                refine ⟨33287300085768153040178261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22191533390512102026785507 33287300085768153040178261)
                ·
                  refine ⟨390085547880095543439589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33287300085768153040178261 390085547880095543439589)
                  ·
                    rfl

theorem cell22_3418600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 8].length) (baseStart_3418600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3418600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3418600 prefixEnd_3418600 := by exact prefixLift 3418600
  have htrace : WordTrace (prefixWord ++ tailWord_3418600) baseStart_3418600 baseEnd_3418600 := by
    simpa [prefixWord, tailWord_3418600, baseEnd_3418600] using wordTrace_append hprefix tailTrace_3418600
  have hstable : (prefixWord ++ tailWord_3418600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418600).length < 2 ^ (prefixWord ++ tailWord_3418600).sum := by decide
  have hdescent : baseEnd_3418600 < baseStart_3418600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418602 : List Nat := [3, 1, 3, 1, 3, 1, 2, 1, 3, 4]
def baseStart_3418602 : Nat := 118140960795 + 3418602 * 2 ^ 59
def prefixEnd_3418602 : Nat := 4983230072969 + 3 ^ 40 * 3418602 * 2
def baseEnd_3418602 : Nat := 1170257328281159291768761

theorem tailTrace_3418602 : CollatzResearch.WordTrace tailWord_3418602 prefixEnd_3418602 1170257328281159291768761 := by
  unfold tailWord_3418602
  simp only [CollatzResearch.WordTrace]
  refine ⟨31171664590249069895994515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83124438907330853055985373 31171664590249069895994515)
  ·
    refine ⟨46757496885373604843991773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31171664590249069895994515 46757496885373604843991773)
    ·
      refine ⟨17534061332015101816496915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46757496885373604843991773 17534061332015101816496915)
      ·
        refine ⟨26301091998022652724745373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17534061332015101816496915 26301091998022652724745373)
        ·
          refine ⟨9862909499258494771779515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26301091998022652724745373 9862909499258494771779515)
          ·
            refine ⟨14794364248887742157669273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9862909499258494771779515 14794364248887742157669273)
            ·
              refine ⟨11095773186665806618251955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14794364248887742157669273 11095773186665806618251955)
              ·
                refine ⟨16643659779998709927377933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11095773186665806618251955 16643659779998709927377933)
                ·
                  refine ⟨6241372417499516222766725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16643659779998709927377933 6241372417499516222766725)
                  ·
                    refine ⟨1170257328281159291768761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6241372417499516222766725 1170257328281159291768761)
                    ·
                      rfl

theorem cell22_3418602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_3418602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3418602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3418602 prefixEnd_3418602 := by exact prefixLift 3418602
  have htrace : WordTrace (prefixWord ++ tailWord_3418602) baseStart_3418602 baseEnd_3418602 := by
    simpa [prefixWord, tailWord_3418602, baseEnd_3418602] using wordTrace_append hprefix tailTrace_3418602
  have hstable : (prefixWord ++ tailWord_3418602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418602).length < 2 ^ (prefixWord ++ tailWord_3418602).sum := by decide
  have hdescent : baseEnd_3418602 < baseStart_3418602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418617 : List Nat := [1, 2, 1, 3, 1, 2, 3, 5, 4]
def baseStart_3418617 : Nat := 118140960795 + 3418617 * 2 ^ 59
def prefixEnd_3418617 : Nat := 4983230072969 + 3 ^ 40 * 3418617 * 2
def baseEnd_3418617 : Nat := 390087487695901417547905

theorem tailTrace_3418617 : CollatzResearch.WordTrace tailWord_3418617 prefixEnd_3418617 390087487695901417547905 := by
  unfold tailWord_3418617
  simp only [CollatzResearch.WordTrace]
  refine ⟨124687205455941937145774105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83124803637294624763849403 124687205455941937145774105)
  ·
    refine ⟨93515404091956452859330579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124687205455941937145774105 93515404091956452859330579)
    ·
      refine ⟨140273106137934679288995869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93515404091956452859330579 140273106137934679288995869)
      ·
        refine ⟨52602414801725504733373451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140273106137934679288995869 52602414801725504733373451)
        ·
          refine ⟨78903622202588257100060177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52602414801725504733373451 78903622202588257100060177)
          ·
            refine ⟨59177716651941192825045133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78903622202588257100060177 59177716651941192825045133)
            ·
              refine ⟨22191643744477947309391925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59177716651941192825045133 22191643744477947309391925)
              ·
                refine ⟨2080466601044807560255493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22191643744477947309391925 2080466601044807560255493)
                ·
                  refine ⟨390087487695901417547905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2080466601044807560255493 390087487695901417547905)
                  ·
                    rfl

theorem cell22_3418617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 5, 4].length) (baseStart_3418617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3418617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3418617 prefixEnd_3418617 := by exact prefixLift 3418617
  have htrace : WordTrace (prefixWord ++ tailWord_3418617) baseStart_3418617 baseEnd_3418617 := by
    simpa [prefixWord, tailWord_3418617, baseEnd_3418617] using wordTrace_append hprefix tailTrace_3418617
  have hstable : (prefixWord ++ tailWord_3418617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418617).length < 2 ^ (prefixWord ++ tailWord_3418617).sum := by decide
  have hdescent : baseEnd_3418617 < baseStart_3418617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418645 : List Nat := [1, 3, 2, 1, 3, 1, 2, 9]
def baseStart_3418645 : Nat := 118140960795 + 3418645 * 2 ^ 59
def prefixEnd_3418645 : Nat := 4983230072969 + 3 ^ 40 * 3418645 * 2
def baseEnd_3418645 : Nat := 130030227562213501438181

theorem tailTrace_3418645 : CollatzResearch.WordTrace tailWord_3418645 prefixEnd_3418645 130030227562213501438181 := by
  unfold tailWord_3418645
  simp only [CollatzResearch.WordTrace]
  refine ⟨124688226699840497927793389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83125484466560331951862259 124688226699840497927793389)
  ·
    refine ⟨46758085012440186722922521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124688226699840497927793389 46758085012440186722922521)
    ·
      refine ⟨35068563759330140042191891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46758085012440186722922521 35068563759330140042191891)
      ·
        refine ⟨52602845638995210063287837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35068563759330140042191891 52602845638995210063287837)
        ·
          refine ⟨19726067114623203773732939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52602845638995210063287837 19726067114623203773732939)
          ·
            refine ⟨29589100671934805660599409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19726067114623203773732939 29589100671934805660599409)
            ·
              refine ⟨22191825503951104245449557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29589100671934805660599409 22191825503951104245449557)
              ·
                refine ⟨130030227562213501438181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22191825503951104245449557 130030227562213501438181)
                ·
                  rfl

theorem cell22_3418645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 9].length) (baseStart_3418645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3418645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3418645 prefixEnd_3418645 := by exact prefixLift 3418645
  have htrace : WordTrace (prefixWord ++ tailWord_3418645) baseStart_3418645 baseEnd_3418645 := by
    simpa [prefixWord, tailWord_3418645, baseEnd_3418645] using wordTrace_append hprefix tailTrace_3418645
  have hstable : (prefixWord ++ tailWord_3418645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418645).length < 2 ^ (prefixWord ++ tailWord_3418645).sum := by decide
  have hdescent : baseEnd_3418645 < baseStart_3418645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418741 : List Nat := [1, 3, 4, 2, 2, 1, 2, 2, 5]
def baseStart_3418741 : Nat := 118140960795 + 3418741 * 2 ^ 59
def prefixEnd_3418741 : Nat := 4983230072969 + 3 ^ 40 * 3418741 * 2
def baseEnd_3418741 : Nat := 390101636940603087514445

theorem tailTrace_3418741 : CollatzResearch.WordTrace tailWord_3418741 prefixEnd_3418741 390101636940603087514445 := by
  unfold tailWord_3418741
  simp only [CollatzResearch.WordTrace]
  refine ⟨124691728107492706323288077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83127818738328470882192051 124691728107492706323288077)
  ·
    refine ⟨46759398040309764871233029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124691728107492706323288077 46759398040309764871233029)
    ·
      refine ⟨8767387132558080913356193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46759398040309764871233029 8767387132558080913356193)
      ·
        refine ⟨6575540349418560685017145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8767387132558080913356193 6575540349418560685017145)
        ·
          refine ⟨4931655262063920513762859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6575540349418560685017145 4931655262063920513762859)
          ·
            refine ⟨7397482893095880770644289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4931655262063920513762859 7397482893095880770644289)
            ·
              refine ⟨5548112169821910577983217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7397482893095880770644289 5548112169821910577983217)
              ·
                refine ⟨4161084127366432933487413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5548112169821910577983217 4161084127366432933487413)
                ·
                  refine ⟨390101636940603087514445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4161084127366432933487413 390101636940603087514445)
                  ·
                    rfl

theorem cell22_3418741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 2, 5].length) (baseStart_3418741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3418741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3418741 prefixEnd_3418741 := by exact prefixLift 3418741
  have htrace : WordTrace (prefixWord ++ tailWord_3418741) baseStart_3418741 baseEnd_3418741 := by
    simpa [prefixWord, tailWord_3418741, baseEnd_3418741] using wordTrace_append hprefix tailTrace_3418741
  have hstable : (prefixWord ++ tailWord_3418741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418741).length < 2 ^ (prefixWord ++ tailWord_3418741).sum := by decide
  have hdescent : baseEnd_3418741 < baseStart_3418741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418842 : List Nat := [3, 1, 1, 2, 2, 2, 1, 1, 9]
def baseStart_3418842 : Nat := 118140960795 + 3418842 * 2 ^ 59
def prefixEnd_3418842 : Nat := 4983230072969 + 3 ^ 40 * 3418842 * 2
def baseEnd_3418842 : Nat := 390113161728626221922675

theorem tailTrace_3418842 : CollatzResearch.WordTrace tailWord_3418842 prefixEnd_3418842 390113161728626221922675 := by
  unfold tailWord_3418842
  simp only [CollatzResearch.WordTrace]
  refine ⟨31173852970031700143178695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83130274586751200381809853 31173852970031700143178695)
  ·
    refine ⟨46760779455047550214768043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31173852970031700143178695 46760779455047550214768043)
    ·
      refine ⟨70141169182571325322152065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46760779455047550214768043 70141169182571325322152065)
      ·
        refine ⟨52605876886928493991614049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70141169182571325322152065 52605876886928493991614049)
        ·
          refine ⟨39454407665196370493710537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52605876886928493991614049 39454407665196370493710537)
          ·
            refine ⟨29590805748897277870282903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39454407665196370493710537 29590805748897277870282903)
            ·
              refine ⟨44386208623345916805424355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29590805748897277870282903 44386208623345916805424355)
              ·
                refine ⟨66579312935018875208136533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44386208623345916805424355 66579312935018875208136533)
                ·
                  refine ⟨390113161728626221922675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 66579312935018875208136533 390113161728626221922675)
                  ·
                    rfl

theorem cell22_3418842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 9].length) (baseStart_3418842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3418842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3418842 prefixEnd_3418842 := by exact prefixLift 3418842
  have htrace : WordTrace (prefixWord ++ tailWord_3418842) baseStart_3418842 baseEnd_3418842 := by
    simpa [prefixWord, tailWord_3418842, baseEnd_3418842] using wordTrace_append hprefix tailTrace_3418842
  have hstable : (prefixWord ++ tailWord_3418842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418842).length < 2 ^ (prefixWord ++ tailWord_3418842).sum := by decide
  have hdescent : baseEnd_3418842 < baseStart_3418842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418857 : List Nat := [1, 2, 1, 1, 1, 2, 4, 1, 4, 5]
def baseStart_3418857 : Nat := 118140960795 + 3418857 * 2 ^ 59
def prefixEnd_3418857 : Nat := 4983230072969 + 3 ^ 40 * 3418857 * 2
def baseEnd_3418857 : Nat := 1170344619992423626642979

theorem tailTrace_3418857 : CollatzResearch.WordTrace tailWord_3418857 prefixEnd_3418857 1170344619992423626642979 := by
  unfold tailWord_3418857
  simp only [CollatzResearch.WordTrace]
  refine ⟨124695958975072458134510825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83130639316714972089673883 124695958975072458134510825)
  ·
    refine ⟨93521969231304343600883119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124695958975072458134510825 93521969231304343600883119)
    ·
      refine ⟨140282953846956515401324679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93521969231304343600883119 140282953846956515401324679)
      ·
        refine ⟨210424430770434773101987019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140282953846956515401324679 210424430770434773101987019)
        ·
          refine ⟨315636646155652159652980529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210424430770434773101987019 315636646155652159652980529)
          ·
            refine ⟨236727484616739119739735397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 315636646155652159652980529 236727484616739119739735397)
            ·
              refine ⟨44386403365638584951200387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 236727484616739119739735397 44386403365638584951200387)
              ·
                refine ⟨66579605048457877426800581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44386403365638584951200387 66579605048457877426800581)
                ·
                  refine ⟨12483675946585852017525109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66579605048457877426800581 12483675946585852017525109)
                  ·
                    refine ⟨1170344619992423626642979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12483675946585852017525109 1170344619992423626642979)
                    ·
                      rfl

theorem cell22_3418857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 4, 5].length) (baseStart_3418857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3418857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3418857 prefixEnd_3418857 := by exact prefixLift 3418857
  have htrace : WordTrace (prefixWord ++ tailWord_3418857) baseStart_3418857 baseEnd_3418857 := by
    simpa [prefixWord, tailWord_3418857, baseEnd_3418857] using wordTrace_append hprefix tailTrace_3418857
  have hstable : (prefixWord ++ tailWord_3418857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418857).length < 2 ^ (prefixWord ++ tailWord_3418857).sum := by decide
  have hdescent : baseEnd_3418857 < baseStart_3418857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418869 : List Nat := [1, 3, 6, 1, 1, 2, 2, 1, 2, 3]
def baseStart_3418869 : Nat := 118140960795 + 3418869 * 2 ^ 59
def prefixEnd_3418869 : Nat := 4983230072969 + 3 ^ 40 * 3418869 * 2
def baseEnd_3418869 : Nat := 1170348727837659595342943

theorem tailTrace_3418869 : CollatzResearch.WordTrace tailWord_3418869 prefixEnd_3418869 1170348727837659595342943 := by
  unfold tailWord_3418869
  simp only [CollatzResearch.WordTrace]
  refine ⟨124696396651028984183947661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83130931100685989455965107 124696396651028984183947661)
  ·
    refine ⟨46761148744135869068980373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124696396651028984183947661 46761148744135869068980373)
    ·
      refine ⟨2191928847381368862608455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 46761148744135869068980373 2191928847381368862608455)
      ·
        refine ⟨3287893271072053293912683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2191928847381368862608455 3287893271072053293912683)
        ·
          refine ⟨4931839906608079940869025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3287893271072053293912683 4931839906608079940869025)
          ·
            refine ⟨3698879929956059955651769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4931839906608079940869025 3698879929956059955651769)
            ·
              refine ⟨2774159947467044966738827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3698879929956059955651769 2774159947467044966738827)
              ·
                refine ⟨4161239921200567450108241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2774159947467044966738827 4161239921200567450108241)
                ·
                  refine ⟨3120929940900425587581181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4161239921200567450108241 3120929940900425587581181)
                  ·
                    refine ⟨1170348727837659595342943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3120929940900425587581181 1170348727837659595342943)
                    ·
                      rfl

theorem cell22_3418869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_3418869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3418869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3418869 prefixEnd_3418869 := by exact prefixLift 3418869
  have htrace : WordTrace (prefixWord ++ tailWord_3418869) baseStart_3418869 baseEnd_3418869 := by
    simpa [prefixWord, tailWord_3418869, baseEnd_3418869] using wordTrace_append hprefix tailTrace_3418869
  have hstable : (prefixWord ++ tailWord_3418869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418869).length < 2 ^ (prefixWord ++ tailWord_3418869).sum := by decide
  have hdescent : baseEnd_3418869 < baseStart_3418869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418876 : List Nat := [2, 2, 2, 1, 3, 2, 4, 1, 5]
def baseStart_3418876 : Nat := 118140960795 + 3418876 * 2 ^ 59
def prefixEnd_3418876 : Nat := 4983230072969 + 3 ^ 40 * 3418876 * 2
def baseEnd_3418876 : Nat := 390117041360237970139307

theorem tailTrace_3418876 : CollatzResearch.WordTrace tailWord_3418876 prefixEnd_3418876 390117041360237970139307 := by
  unfold tailWord_3418876
  simp only [CollatzResearch.WordTrace]
  refine ⟨62348325981001812189726241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83131101308002416252968321 62348325981001812189726241)
  ·
    refine ⟨46761244485751359142294681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62348325981001812189726241 46761244485751359142294681)
    ·
      refine ⟨35070933364313519356721011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46761244485751359142294681 35070933364313519356721011)
      ·
        refine ⟨52606400046470279035081517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35070933364313519356721011 52606400046470279035081517)
        ·
          refine ⟨19727400017426354638155569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52606400046470279035081517 19727400017426354638155569)
          ·
            refine ⟨14795550013069765978616677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19727400017426354638155569 14795550013069765978616677)
            ·
              refine ⟨2774165627450581120990627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14795550013069765978616677 2774165627450581120990627)
              ·
                refine ⟨4161248441175871681485941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2774165627450581120990627 4161248441175871681485941)
                ·
                  refine ⟨390117041360237970139307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4161248441175871681485941 390117041360237970139307)
                  ·
                    rfl

theorem cell22_3418876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 4, 1, 5].length) (baseStart_3418876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3418876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3418876 prefixEnd_3418876 := by exact prefixLift 3418876
  have htrace : WordTrace (prefixWord ++ tailWord_3418876) baseStart_3418876 baseEnd_3418876 := by
    simpa [prefixWord, tailWord_3418876, baseEnd_3418876] using wordTrace_append hprefix tailTrace_3418876
  have hstable : (prefixWord ++ tailWord_3418876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418876).length < 2 ^ (prefixWord ++ tailWord_3418876).sum := by decide
  have hdescent : baseEnd_3418876 < baseStart_3418876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418936 : List Nat := [2, 1, 2, 1, 3, 2, 1, 5, 2, 3]
def baseStart_3418936 : Nat := 118140960795 + 3418936 * 2 ^ 59
def prefixEnd_3418936 : Nat := 4983230072969 + 3 ^ 40 * 3418936 * 2
def baseEnd_3418936 : Nat := 1170371663306893753917737

theorem tailTrace_3418936 : CollatzResearch.WordTrace tailWord_3418936 prefixEnd_3418936 1170371663306893753917737 := by
  unfold tailWord_3418936
  simp only [CollatzResearch.WordTrace]
  refine ⟨62349420170893127313318331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83132560227857503084424441 62349420170893127313318331)
  ·
    refine ⟨93524130256339690969977497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62349420170893127313318331 93524130256339690969977497)
    ·
      refine ⟨70143097692254768227483123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93524130256339690969977497 70143097692254768227483123)
      ·
        refine ⟨105214646538382152341224685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70143097692254768227483123 105214646538382152341224685)
        ·
          refine ⟨39455492451893307127959257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105214646538382152341224685 39455492451893307127959257)
          ·
            refine ⟨29591619338919980345969443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39455492451893307127959257 29591619338919980345969443)
            ·
              refine ⟨44387429008379970518954165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29591619338919980345969443 44387429008379970518954165)
              ·
                refine ⟨4161321469535622236151953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44387429008379970518954165 4161321469535622236151953)
                ·
                  refine ⟨3120991102151716677113965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4161321469535622236151953 3120991102151716677113965)
                  ·
                    refine ⟨1170371663306893753917737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3120991102151716677113965 1170371663306893753917737)
                    ·
                      rfl

theorem cell22_3418936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 5, 2, 3].length) (baseStart_3418936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3418936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3418936 prefixEnd_3418936 := by exact prefixLift 3418936
  have htrace : WordTrace (prefixWord ++ tailWord_3418936) baseStart_3418936 baseEnd_3418936 := by
    simpa [prefixWord, tailWord_3418936, baseEnd_3418936] using wordTrace_append hprefix tailTrace_3418936
  have hstable : (prefixWord ++ tailWord_3418936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418936).length < 2 ^ (prefixWord ++ tailWord_3418936).sum := by decide
  have hdescent : baseEnd_3418936 < baseStart_3418936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418957 : List Nat := [1, 6, 1, 2, 2, 2, 2, 1, 1, 4]
def baseStart_3418957 : Nat := 118140960795 + 3418957 * 2 ^ 59
def prefixEnd_3418957 : Nat := 4983230072969 + 3 ^ 40 * 3418957 * 2
def baseEnd_3418957 : Nat := 1170378852036056699142673

theorem tailTrace_3418957 : CollatzResearch.WordTrace tailWord_3418957 prefixEnd_3418957 1170378852036056699142673 := by
  unfold tailWord_3418957
  simp only [CollatzResearch.WordTrace]
  refine ⟨124699606274710175213151125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83133070849806783475434083 124699606274710175213151125)
  ·
    refine ⟨5845294044127039463116459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 124699606274710175213151125 5845294044127039463116459)
    ·
      refine ⟨8767941066190559194674689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5845294044127039463116459 8767941066190559194674689)
      ·
        refine ⟨6575955799642919396006017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8767941066190559194674689 6575955799642919396006017)
        ·
          refine ⟨4931966849732189547004513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6575955799642919396006017 4931966849732189547004513)
          ·
            refine ⟨3698975137299142160253385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4931966849732189547004513 3698975137299142160253385)
            ·
              refine ⟨2774231352974356620190039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3698975137299142160253385 2774231352974356620190039)
              ·
                refine ⟨4161347029461534930285059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2774231352974356620190039 4161347029461534930285059)
                ·
                  refine ⟨6242020544192302395427589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4161347029461534930285059 6242020544192302395427589)
                  ·
                    refine ⟨1170378852036056699142673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6242020544192302395427589 1170378852036056699142673)
                    ·
                      rfl

theorem cell22_3418957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_3418957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3418957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3418957 prefixEnd_3418957 := by exact prefixLift 3418957
  have htrace : WordTrace (prefixWord ++ tailWord_3418957) baseStart_3418957 baseEnd_3418957 := by
    simpa [prefixWord, tailWord_3418957, baseEnd_3418957] using wordTrace_append hprefix tailTrace_3418957
  have hstable : (prefixWord ++ tailWord_3418957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418957).length < 2 ^ (prefixWord ++ tailWord_3418957).sum := by decide
  have hdescent : baseEnd_3418957 < baseStart_3418957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418981 : List Nat := [1, 3, 1, 3, 1, 1, 3, 3, 3, 3]
def baseStart_3418981 : Nat := 118140960795 + 3418981 * 2 ^ 59
def prefixEnd_3418981 : Nat := 4983230072969 + 3 ^ 40 * 3418981 * 2
def baseEnd_3418981 : Nat := 1170387067726528636542599

theorem tailTrace_3418981 : CollatzResearch.WordTrace tailWord_3418981 prefixEnd_3418981 1170387067726528636542599 := by
  unfold tailWord_3418981
  simp only [CollatzResearch.WordTrace]
  refine ⟨124700481626623227312024797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83133654417748818208016531 124700481626623227312024797)
  ·
    refine ⟨46762680609983710242009299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124700481626623227312024797 46762680609983710242009299)
    ·
      refine ⟨70144020914975565363013949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46762680609983710242009299 70144020914975565363013949)
      ·
        refine ⟨26304007843115837011130231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70144020914975565363013949 26304007843115837011130231)
        ·
          refine ⟨39456011764673755516695347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26304007843115837011130231 39456011764673755516695347)
          ·
            refine ⟨59184017647010633275043021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39456011764673755516695347 59184017647010633275043021)
            ·
              refine ⟨22194006617628987478141133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59184017647010633275043021 22194006617628987478141133)
              ·
                refine ⟨8322752481610870304302925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22194006617628987478141133 8322752481610870304302925)
                ·
                  refine ⟨3121032180604076364113597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8322752481610870304302925 3121032180604076364113597)
                  ·
                    refine ⟨1170387067726528636542599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3121032180604076364113597 1170387067726528636542599)
                    ·
                      rfl

theorem cell22_3418981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 3, 3, 3].length) (baseStart_3418981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3418981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3418981 prefixEnd_3418981 := by exact prefixLift 3418981
  have htrace : WordTrace (prefixWord ++ tailWord_3418981) baseStart_3418981 baseEnd_3418981 := by
    simpa [prefixWord, tailWord_3418981, baseEnd_3418981] using wordTrace_append hprefix tailTrace_3418981
  have hstable : (prefixWord ++ tailWord_3418981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418981).length < 2 ^ (prefixWord ++ tailWord_3418981).sum := by decide
  have hdescent : baseEnd_3418981 < baseStart_3418981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419015 : List Nat := [1, 1, 4, 2, 3, 1, 3, 3, 1, 3]
def baseStart_3419015 : Nat := 118140960795 + 3419015 * 2 ^ 59
def prefixEnd_3419015 : Nat := 4983230072969 + 3 ^ 40 * 3419015 * 2
def baseEnd_3419015 : Nat := 1170398706621363881192495

theorem tailTrace_3419015 : CollatzResearch.WordTrace tailWord_3419015 prefixEnd_3419015 1170398706621363881192495 := by
  unfold tailWord_3419015
  simp only [CollatzResearch.WordTrace]
  refine ⟨124701721708500051118762499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83134481139000034079174999 124701721708500051118762499)
  ·
    refine ⟨187052582562750076678143749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124701721708500051118762499 187052582562750076678143749)
    ·
      refine ⟨35072359230515639377151953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187052582562750076678143749 35072359230515639377151953)
      ·
        refine ⟨26304269422886729532863965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35072359230515639377151953 26304269422886729532863965)
        ·
          refine ⟨9864101033582523574823987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26304269422886729532863965 9864101033582523574823987)
          ·
            refine ⟨14796151550373785362235981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9864101033582523574823987 14796151550373785362235981)
            ·
              refine ⟨5548556831390169510838493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14796151550373785362235981 5548556831390169510838493)
              ·
                refine ⟨2080708811771313566564435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5548556831390169510838493 2080708811771313566564435)
                ·
                  refine ⟨3121063217656970349846653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2080708811771313566564435 3121063217656970349846653)
                  ·
                    refine ⟨1170398706621363881192495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3121063217656970349846653 1170398706621363881192495)
                    ·
                      rfl

theorem cell22_3419015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 3, 1, 3].length) (baseStart_3419015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3419015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3419015 prefixEnd_3419015 := by exact prefixLift 3419015
  have htrace : WordTrace (prefixWord ++ tailWord_3419015) baseStart_3419015 baseEnd_3419015 := by
    simpa [prefixWord, tailWord_3419015, baseEnd_3419015] using wordTrace_append hprefix tailTrace_3419015
  have hstable : (prefixWord ++ tailWord_3419015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419015).length < 2 ^ (prefixWord ++ tailWord_3419015).sum := by decide
  have hdescent : baseEnd_3419015 < baseStart_3419015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419071 : List Nat := [1, 1, 2, 2, 2, 1, 2, 4, 4, 3]
def baseStart_3419071 : Nat := 118140960795 + 3419071 * 2 ^ 59
def prefixEnd_3419071 : Nat := 4983230072969 + 3 ^ 40 * 3419071 * 2
def baseEnd_3419071 : Nat := 1170417876565798401792323

theorem tailTrace_3419071 : CollatzResearch.WordTrace tailWord_3419071 prefixEnd_3419071 1170417876565798401792323 := by
  unfold tailWord_3419071
  simp only [CollatzResearch.WordTrace]
  refine ⟨124703764196297172682801067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83135842797531448455200711 124703764196297172682801067)
  ·
    refine ⟨187055646294445759024201601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124703764196297172682801067 187055646294445759024201601)
    ·
      refine ⟨140291734720834319268151201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187055646294445759024201601 140291734720834319268151201)
      ·
        refine ⟨105218801040625739451113401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140291734720834319268151201 105218801040625739451113401)
        ·
          refine ⟨78914100780469304588335051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105218801040625739451113401 78914100780469304588335051)
          ·
            refine ⟨118371151170703956882502577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78914100780469304588335051 118371151170703956882502577)
            ·
              refine ⟨88778363378027967661876933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118371151170703956882502577 88778363378027967661876933)
              ·
                refine ⟨16645943133380243936601925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88778363378027967661876933 16645943133380243936601925)
                ·
                  refine ⟨3121114337508795738112861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16645943133380243936601925 3121114337508795738112861)
                  ·
                    refine ⟨1170417876565798401792323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3121114337508795738112861 1170417876565798401792323)
                    ·
                      rfl

theorem cell22_3419071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 4, 3].length) (baseStart_3419071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3419071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3419071 prefixEnd_3419071 := by exact prefixLift 3419071
  have htrace : WordTrace (prefixWord ++ tailWord_3419071) baseStart_3419071 baseEnd_3419071 := by
    simpa [prefixWord, tailWord_3419071, baseEnd_3419071] using wordTrace_append hprefix tailTrace_3419071
  have hstable : (prefixWord ++ tailWord_3419071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419071).length < 2 ^ (prefixWord ++ tailWord_3419071).sum := by decide
  have hdescent : baseEnd_3419071 < baseStart_3419071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419090 : List Nat := [3, 2, 2, 3, 1, 2, 1, 4, 4]
def baseStart_3419090 : Nat := 118140960795 + 3419090 * 2 ^ 59
def prefixEnd_3419090 : Nat := 4983230072969 + 3 ^ 40 * 3419090 * 2
def baseEnd_3419090 : Nat := 390141460218029561855755

theorem tailTrace_3419090 : CollatzResearch.WordTrace tailWord_3419090 prefixEnd_3419090 390141460218029561855755 := by
  unfold tailWord_3419090
  simp only [CollatzResearch.WordTrace]
  refine ⟨31176114295807084731935681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83136304788818892618495149 31176114295807084731935681)
  ·
    refine ⟨23382085721855313548951761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31176114295807084731935681 23382085721855313548951761)
    ·
      refine ⟨17536564291391485161713821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23382085721855313548951761 17536564291391485161713821)
      ·
        refine ⟨6576211609271806935642683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17536564291391485161713821 6576211609271806935642683)
        ·
          refine ⟨9864317413907710403464025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6576211609271806935642683 9864317413907710403464025)
          ·
            refine ⟨7398238060430782802598019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9864317413907710403464025 7398238060430782802598019)
            ·
              refine ⟨11097357090646174203897029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7398238060430782802598019 11097357090646174203897029)
              ·
                refine ⟨2080754454496157663230693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11097357090646174203897029 2080754454496157663230693)
                ·
                  refine ⟨390141460218029561855755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2080754454496157663230693 390141460218029561855755)
                  ·
                    rfl

theorem cell22_3419090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 4, 4].length) (baseStart_3419090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3419090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3419090 prefixEnd_3419090 := by exact prefixLift 3419090
  have htrace : WordTrace (prefixWord ++ tailWord_3419090) baseStart_3419090 baseEnd_3419090 := by
    simpa [prefixWord, tailWord_3419090, baseEnd_3419090] using wordTrace_append hprefix tailTrace_3419090
  have hstable : (prefixWord ++ tailWord_3419090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419090).length < 2 ^ (prefixWord ++ tailWord_3419090).sum := by decide
  have hdescent : baseEnd_3419090 < baseStart_3419090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419150 : List Nat := [4, 1, 1, 2, 2, 3, 2, 1, 3, 3]
def baseStart_3419150 : Nat := 118140960795 + 3419150 * 2 ^ 59
def prefixEnd_3419150 : Nat := 4983230072969 + 3 ^ 40 * 3419150 * 2
def baseEnd_3419150 : Nat := 1170444919880268529067081

theorem tailTrace_3419150 : CollatzResearch.WordTrace tailWord_3419150 prefixEnd_3419150 1170444919880268529067081 := by
  unfold tailWord_3419150
  simp only [CollatzResearch.WordTrace]
  refine ⟨15588330695376371146865863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83137763708673979449951269 15588330695376371146865863)
  ·
    refine ⟨23382496043064556720298795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15588330695376371146865863 23382496043064556720298795)
    ·
      refine ⟨35073744064596835080448193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23382496043064556720298795 35073744064596835080448193)
      ·
        refine ⟨26305308048447626310336145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35073744064596835080448193 26305308048447626310336145)
        ·
          refine ⟨19728981036335719732752109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26305308048447626310336145 19728981036335719732752109)
          ·
            refine ⟨7398367888625894899782041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19728981036335719732752109 7398367888625894899782041)
            ·
              refine ⟨5548775916469421174836531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7398367888625894899782041 5548775916469421174836531)
              ·
                refine ⟨8323163874704131762254797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5548775916469421174836531 8323163874704131762254797)
                ·
                  refine ⟨3121186453014049410845549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8323163874704131762254797 3121186453014049410845549)
                  ·
                    refine ⟨1170444919880268529067081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3121186453014049410845549 1170444919880268529067081)
                    ·
                      rfl

theorem cell22_3419150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 1, 3, 3].length) (baseStart_3419150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3419150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3419150 prefixEnd_3419150 := by exact prefixLift 3419150
  have htrace : WordTrace (prefixWord ++ tailWord_3419150) baseStart_3419150 baseEnd_3419150 := by
    simpa [prefixWord, tailWord_3419150, baseEnd_3419150] using wordTrace_append hprefix tailTrace_3419150
  have hstable : (prefixWord ++ tailWord_3419150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419150).length < 2 ^ (prefixWord ++ tailWord_3419150).sum := by decide
  have hdescent : baseEnd_3419150 < baseStart_3419150 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419161 : List Nat := [1, 2, 1, 2, 1, 1, 6, 1, 2, 5]
def baseStart_3419161 : Nat := 118140960795 + 3419161 * 2 ^ 59
def prefixEnd_3419161 : Nat := 4983230072969 + 3 ^ 40 * 3419161 * 2
def baseEnd_3419161 : Nat := 1170448685405068167042047

theorem tailTrace_3419161 : CollatzResearch.WordTrace tailWord_3419161 prefixEnd_3419161 1170448685405068167042047 := by
  unfold tailWord_3419161
  simp only [CollatzResearch.WordTrace]
  refine ⟨124707046765971118053577337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83138031177314078702384891 124707046765971118053577337)
  ·
    refine ⟨93530285074478338540183003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124707046765971118053577337 93530285074478338540183003)
    ·
      refine ⟨140295427611717507810274505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93530285074478338540183003 140295427611717507810274505)
      ·
        refine ⟨105221570708788130857705879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140295427611717507810274505 105221570708788130857705879)
        ·
          refine ⟨157832356063182196286558819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105221570708788130857705879 157832356063182196286558819)
          ·
            refine ⟨236748534094773294429838229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157832356063182196286558819 236748534094773294429838229)
            ·
              refine ⟨11097587535692498176398667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 236748534094773294429838229 11097587535692498176398667)
              ·
                refine ⟨16646381303538747264598001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11097587535692498176398667 16646381303538747264598001)
                ·
                  refine ⟨12484785977654060448448501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16646381303538747264598001 12484785977654060448448501)
                  ·
                    refine ⟨1170448685405068167042047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12484785977654060448448501 1170448685405068167042047)
                    ·
                      rfl

theorem cell22_3419161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 2, 5].length) (baseStart_3419161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3419161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3419161 prefixEnd_3419161 := by exact prefixLift 3419161
  have htrace : WordTrace (prefixWord ++ tailWord_3419161) baseStart_3419161 baseEnd_3419161 := by
    simpa [prefixWord, tailWord_3419161, baseEnd_3419161] using wordTrace_append hprefix tailTrace_3419161
  have hstable : (prefixWord ++ tailWord_3419161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419161).length < 2 ^ (prefixWord ++ tailWord_3419161).sum := by decide
  have hdescent : baseEnd_3419161 < baseStart_3419161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419253 : List Nat := [1, 3, 4, 3, 11]
def baseStart_3419253 : Nat := 118140960795 + 3419253 * 2 ^ 59
def prefixEnd_3419253 : Nat := 4983230072969 + 3 ^ 40 * 3419253 * 2
def baseEnd_3419253 : Nat := 4816790859609920138855

theorem tailTrace_3419253 : CollatzResearch.WordTrace tailWord_3419253 prefixEnd_3419253 4816790859609920138855 := by
  unfold tailWord_3419253
  simp only [CollatzResearch.WordTrace]
  refine ⟨124710402281637817765926413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83140268187758545177284275 124710402281637817765926413)
  ·
    refine ⟨46766400855614181662222405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124710402281637817765926413 46766400855614181662222405)
    ·
      refine ⟨8768700160427659061666701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46766400855614181662222405 8768700160427659061666701)
      ·
        refine ⟨3288262560160372148125013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8768700160427659061666701 3288262560160372148125013)
        ·
          refine ⟨4816790859609920138855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3288262560160372148125013 4816790859609920138855)
          ·
            rfl

theorem cell22_3419253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 11].length) (baseStart_3419253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3419253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3419253 prefixEnd_3419253 := by exact prefixLift 3419253
  have htrace : WordTrace (prefixWord ++ tailWord_3419253) baseStart_3419253 baseEnd_3419253 := by
    simpa [prefixWord, tailWord_3419253, baseEnd_3419253] using wordTrace_append hprefix tailTrace_3419253
  have hstable : (prefixWord ++ tailWord_3419253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419253).length < 2 ^ (prefixWord ++ tailWord_3419253).sum := by decide
  have hdescent : baseEnd_3419253 < baseStart_3419253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419257 : List Nat := [1, 2, 1, 3, 5, 1, 2, 2, 2, 3]
def baseStart_3419257 : Nat := 118140960795 + 3419257 * 2 ^ 59
def prefixEnd_3419257 : Nat := 4983230072969 + 3 ^ 40 * 3419257 * 2
def baseEnd_3419257 : Nat := 1170481548166955916641753

theorem tailTrace_3419257 : CollatzResearch.WordTrace tailWord_3419257 prefixEnd_3419257 1170481548166955916641753 := by
  unfold tailWord_3419257
  simp only [CollatzResearch.WordTrace]
  refine ⟨124710548173623326449072025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83140365449082217632714683 124710548173623326449072025)
  ·
    refine ⟨93532911130217494836804019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124710548173623326449072025 93532911130217494836804019)
    ·
      refine ⟨140299366695326242255206029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93532911130217494836804019 140299366695326242255206029)
      ·
        refine ⟨52612262510747340845702261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140299366695326242255206029 52612262510747340845702261)
        ·
          refine ⟨4932399610382563204284587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52612262510747340845702261 4932399610382563204284587)
          ·
            refine ⟨7398599415573844806426881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4932399610382563204284587 7398599415573844806426881)
            ·
              refine ⟨5548949561680383604820161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7398599415573844806426881 5548949561680383604820161)
              ·
                refine ⟨4161712171260287703615121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5548949561680383604820161 4161712171260287703615121)
                ·
                  refine ⟨3121284128445215777711341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4161712171260287703615121 3121284128445215777711341)
                  ·
                    refine ⟨1170481548166955916641753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3121284128445215777711341 1170481548166955916641753)
                    ·
                      rfl

theorem cell22_3419257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 2, 2, 3].length) (baseStart_3419257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3419257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3419257 prefixEnd_3419257 := by exact prefixLift 3419257
  have htrace : WordTrace (prefixWord ++ tailWord_3419257) baseStart_3419257 baseEnd_3419257 := by
    simpa [prefixWord, tailWord_3419257, baseEnd_3419257] using wordTrace_append hprefix tailTrace_3419257
  have hstable : (prefixWord ++ tailWord_3419257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419257).length < 2 ^ (prefixWord ++ tailWord_3419257).sum := by decide
  have hdescent : baseEnd_3419257 < baseStart_3419257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419422 : List Nat := [4, 3, 2, 1, 2, 10]
def baseStart_3419422 : Nat := 118140960795 + 3419422 * 2 ^ 59
def prefixEnd_3419422 : Nat := 4983230072969 + 3 ^ 40 * 3419422 * 2
def baseEnd_3419422 : Nat := 14451086802950006003287

theorem tailTrace_3419422 : CollatzResearch.WordTrace tailWord_3419422 prefixEnd_3419422 14451086802950006003287 := by
  unfold tailWord_3419422
  simp only [CollatzResearch.WordTrace]
  refine ⟨15589570777253194953603565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83144377478683706419219013 15589570777253194953603565)
  ·
    refine ⟨5846089041469948107601337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15589570777253194953603565 5846089041469948107601337)
    ·
      refine ⟨4384566781102461080701003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5846089041469948107601337 4384566781102461080701003)
      ·
        refine ⟨6576850171653691621051505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4384566781102461080701003 6576850171653691621051505)
        ·
          refine ⟨4932637628740268715788629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6576850171653691621051505 4932637628740268715788629)
          ·
            refine ⟨14451086802950006003287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4932637628740268715788629 14451086802950006003287)
            ·
              rfl

theorem cell22_3419422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 10].length) (baseStart_3419422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3419422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3419422 prefixEnd_3419422 := by exact prefixLift 3419422
  have htrace : WordTrace (prefixWord ++ tailWord_3419422) baseStart_3419422 baseEnd_3419422 := by
    simpa [prefixWord, tailWord_3419422, baseEnd_3419422] using wordTrace_append hprefix tailTrace_3419422
  have hstable : (prefixWord ++ tailWord_3419422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419422).length < 2 ^ (prefixWord ++ tailWord_3419422).sum := by decide
  have hdescent : baseEnd_3419422 < baseStart_3419422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419450 : List Nat := [3, 1, 1, 1, 4, 1, 1, 5, 5]
def baseStart_3419450 : Nat := 118140960795 + 3419450 * 2 ^ 59
def prefixEnd_3419450 : Nat := 4983230072969 + 3 ^ 40 * 3419450 * 2
def baseEnd_3419450 : Nat := 390182538670389248855387

theorem tailTrace_3419450 : CollatzResearch.WordTrace tailWord_3419450 prefixEnd_3419450 390182538670389248855387 := by
  unfold tailWord_3419450
  simp only [CollatzResearch.WordTrace]
  refine ⟨31179396865481030102711951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83145058307949413607231869 31179396865481030102711951)
  ·
    refine ⟨46769095298221545154067927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31179396865481030102711951 46769095298221545154067927)
    ·
      refine ⟨70153642947332317731101891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46769095298221545154067927 70153642947332317731101891)
      ·
        refine ⟨105230464420998476596652837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70153642947332317731101891 105230464420998476596652837)
        ·
          refine ⟨19730712078937214361872407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105230464420998476596652837 19730712078937214361872407)
          ·
            refine ⟨29596068118405821542808611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19730712078937214361872407 29596068118405821542808611)
            ·
              refine ⟨44394102177608732314212917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29596068118405821542808611 44394102177608732314212917)
              ·
                refine ⟨4161947079150818654457461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44394102177608732314212917 4161947079150818654457461)
                ·
                  refine ⟨390182538670389248855387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4161947079150818654457461 390182538670389248855387)
                  ·
                    rfl

theorem cell22_3419450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 5, 5].length) (baseStart_3419450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3419450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3419450 prefixEnd_3419450 := by exact prefixLift 3419450
  have htrace : WordTrace (prefixWord ++ tailWord_3419450) baseStart_3419450 baseEnd_3419450 := by
    simpa [prefixWord, tailWord_3419450, baseEnd_3419450] using wordTrace_append hprefix tailTrace_3419450
  have hstable : (prefixWord ++ tailWord_3419450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419450).length < 2 ^ (prefixWord ++ tailWord_3419450).sum := by decide
  have hdescent : baseEnd_3419450 < baseStart_3419450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419525 : List Nat := [1, 3, 1, 1, 3, 1, 4, 1, 1, 6]
def baseStart_3419525 : Nat := 118140960795 + 3419525 * 2 ^ 59
def prefixEnd_3419525 : Nat := 4983230072969 + 3 ^ 40 * 3419525 * 2
def baseEnd_3419525 : Nat := 1170573290043892550940931

theorem tailTrace_3419525 : CollatzResearch.WordTrace tailWord_3419525 prefixEnd_3419525 1170573290043892550940931 := by
  unfold tailWord_3419525
  simp only [CollatzResearch.WordTrace]
  refine ⟨124720322936652408219828029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83146881957768272146552019 124720322936652408219828029)
  ·
    refine ⟨46770121101244653082435511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124720322936652408219828029 46770121101244653082435511)
    ·
      refine ⟨70155181651866979623653267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46770121101244653082435511 70155181651866979623653267)
      ·
        refine ⟨105232772477800469435479901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70155181651866979623653267 105232772477800469435479901)
        ·
          refine ⟨39462289679175176038304963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105232772477800469435479901 39462289679175176038304963)
          ·
            refine ⟨59193434518762764057457445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39462289679175176038304963 59193434518762764057457445)
            ·
              refine ⟨11098768972268018260773271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59193434518762764057457445 11098768972268018260773271)
              ·
                refine ⟨16648153458402027391159907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11098768972268018260773271 16648153458402027391159907)
                ·
                  refine ⟨24972230187603041086739861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16648153458402027391159907 24972230187603041086739861)
                  ·
                    refine ⟨1170573290043892550940931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24972230187603041086739861 1170573290043892550940931)
                    ·
                      rfl

theorem cell22_3419525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 6].length) (baseStart_3419525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3419525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3419525 prefixEnd_3419525 := by exact prefixLift 3419525
  have htrace : WordTrace (prefixWord ++ tailWord_3419525) baseStart_3419525 baseEnd_3419525 := by
    simpa [prefixWord, tailWord_3419525, baseEnd_3419525] using wordTrace_append hprefix tailTrace_3419525
  have hstable : (prefixWord ++ tailWord_3419525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419525).length < 2 ^ (prefixWord ++ tailWord_3419525).sum := by decide
  have hdescent : baseEnd_3419525 < baseStart_3419525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419527 : List Nat := [1, 1, 4, 2, 2, 2, 1, 2, 4, 3]
def baseStart_3419527 : Nat := 118140960795 + 3419527 * 2 ^ 59
def prefixEnd_3419527 : Nat := 4983230072969 + 3 ^ 40 * 3419527 * 2
def baseEnd_3419527 : Nat := 1170573974684765212390925

theorem tailTrace_3419527 : CollatzResearch.WordTrace tailWord_3419527 prefixEnd_3419527 1170573974684765212390925 := by
  unfold tailWord_3419527
  simp only [CollatzResearch.WordTrace]
  refine ⟨124720395882645162561400835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83146930588430108374267223 124720395882645162561400835)
  ·
    refine ⟨187080593823967743842101253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124720395882645162561400835 187080593823967743842101253)
    ·
      refine ⟨35077611341993951970393985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187080593823967743842101253 35077611341993951970393985)
      ·
        refine ⟨26308208506495463977795489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35077611341993951970393985 26308208506495463977795489)
        ·
          refine ⟨19731156379871597983346617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26308208506495463977795489 19731156379871597983346617)
          ·
            refine ⟨14798367284903698487509963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19731156379871597983346617 14798367284903698487509963)
            ·
              refine ⟨22197550927355547731264945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14798367284903698487509963 22197550927355547731264945)
              ·
                refine ⟨16648163195516660798448709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22197550927355547731264945 16648163195516660798448709)
                ·
                  refine ⟨3121530599159373899709133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16648163195516660798448709 3121530599159373899709133)
                  ·
                    refine ⟨1170573974684765212390925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3121530599159373899709133 1170573974684765212390925)
                    ·
                      rfl

theorem cell22_3419527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 4, 3].length) (baseStart_3419527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3419527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3419527 prefixEnd_3419527 := by exact prefixLift 3419527
  have htrace : WordTrace (prefixWord ++ tailWord_3419527) baseStart_3419527 baseEnd_3419527 := by
    simpa [prefixWord, tailWord_3419527, baseEnd_3419527] using wordTrace_append hprefix tailTrace_3419527
  have hstable : (prefixWord ++ tailWord_3419527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419527).length < 2 ^ (prefixWord ++ tailWord_3419527).sum := by decide
  have hdescent : baseEnd_3419527 < baseStart_3419527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419570 : List Nat := [3, 2, 1, 1, 1, 1, 2, 1, 4, 6]
def baseStart_3419570 : Nat := 118140960795 + 3419570 * 2 ^ 59
def prefixEnd_3419570 : Nat := 4983230072969 + 3 ^ 40 * 3419570 * 2
def baseEnd_3419570 : Nat := 1170588694463527433565793

theorem tailTrace_3419570 : CollatzResearch.WordTrace tailWord_3419570 prefixEnd_3419570 1170588694463527433565793 := by
  unfold tailWord_3419570
  simp only [CollatzResearch.WordTrace]
  refine ⟨31180491055372345226304041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83147976147659587270144109 31180491055372345226304041)
  ·
    refine ⟨23385368291529258919728031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31180491055372345226304041 23385368291529258919728031)
    ·
      refine ⟨35078052437293888379592047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23385368291529258919728031 35078052437293888379592047)
      ·
        refine ⟨52617078655940832569388071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35078052437293888379592047 52617078655940832569388071)
        ·
          refine ⟨78925617983911248854082107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52617078655940832569388071 78925617983911248854082107)
          ·
            refine ⟨118388426975866873281123161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78925617983911248854082107 118388426975866873281123161)
            ·
              refine ⟨88791320231900154960842371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118388426975866873281123161 88791320231900154960842371)
              ·
                refine ⟨133186980347850232441263557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88791320231900154960842371 133186980347850232441263557)
                ·
                  refine ⟨24972558815221918582736917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 133186980347850232441263557 24972558815221918582736917)
                  ·
                    refine ⟨1170588694463527433565793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24972558815221918582736917 1170588694463527433565793)
                    ·
                      rfl

theorem cell22_3419570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_3419570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3419570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3419570 prefixEnd_3419570 := by exact prefixLift 3419570
  have htrace : WordTrace (prefixWord ++ tailWord_3419570) baseStart_3419570 baseEnd_3419570 := by
    simpa [prefixWord, tailWord_3419570, baseEnd_3419570] using wordTrace_append hprefix tailTrace_3419570
  have hstable : (prefixWord ++ tailWord_3419570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419570).length < 2 ^ (prefixWord ++ tailWord_3419570).sum := by decide
  have hdescent : baseEnd_3419570 < baseStart_3419570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419600 : List Nat := [2, 1, 1, 1, 1, 2, 2, 3, 4, 5]
def baseStart_3419600 : Nat := 118140960795 + 3419600 * 2 ^ 59
def prefixEnd_3419600 : Nat := 4983230072969 + 3 ^ 40 * 3419600 * 2
def baseEnd_3419600 : Nat := 1170598964076617355315701

theorem tailTrace_3419600 : CollatzResearch.WordTrace tailWord_3419600 prefixEnd_3419600 1170598964076617355315701 := by
  unfold tailWord_3419600
  simp only [CollatzResearch.WordTrace]
  refine ⟨62361529205690348014404127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83148705607587130685872169 62361529205690348014404127)
  ·
    refine ⟨93542293808535522021606191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62361529205690348014404127 93542293808535522021606191)
    ·
      refine ⟨140313440712803283032409287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93542293808535522021606191 140313440712803283032409287)
      ·
        refine ⟨210470161069204924548613931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140313440712803283032409287 210470161069204924548613931)
        ·
          refine ⟨315705241603807386822920897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210470161069204924548613931 315705241603807386822920897)
          ·
            refine ⟨236778931202855540117190673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 315705241603807386822920897 236778931202855540117190673)
            ·
              refine ⟨177584198402141655087893005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236778931202855540117190673 177584198402141655087893005)
              ·
                refine ⟨66594074400803120657959877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 177584198402141655087893005 66594074400803120657959877)
                ·
                  refine ⟨12486388950150585123367477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66594074400803120657959877 12486388950150585123367477)
                  ·
                    refine ⟨1170598964076617355315701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12486388950150585123367477 1170598964076617355315701)
                    ·
                      rfl

theorem cell22_3419600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 4, 5].length) (baseStart_3419600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3419600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3419600 prefixEnd_3419600 := by exact prefixLift 3419600
  have htrace : WordTrace (prefixWord ++ tailWord_3419600) baseStart_3419600 baseEnd_3419600 := by
    simpa [prefixWord, tailWord_3419600, baseEnd_3419600] using wordTrace_append hprefix tailTrace_3419600
  have hstable : (prefixWord ++ tailWord_3419600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419600).length < 2 ^ (prefixWord ++ tailWord_3419600).sum := by decide
  have hdescent : baseEnd_3419600 < baseStart_3419600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419617 : List Nat := [1, 2, 3, 1, 2, 4, 1, 1, 2, 5]
def baseStart_3419617 : Nat := 118140960795 + 3419617 * 2 ^ 59
def prefixEnd_3419617 : Nat := 4983230072969 + 3 ^ 40 * 3419617 * 2
def baseEnd_3419617 : Nat := 1170604783524034977640649

theorem tailTrace_3419617 : CollatzResearch.WordTrace tailWord_3419617 prefixEnd_3419617 1170604783524034977640649 := by
  unfold tailWord_3419617
  simp only [CollatzResearch.WordTrace]
  refine ⟨124723678452319107932177105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83149118968212738621451403 124723678452319107932177105)
  ·
    refine ⟨93542758839239330949132829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124723678452319107932177105 93542758839239330949132829)
    ·
      refine ⟨35078534564714749105924811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93542758839239330949132829 35078534564714749105924811)
      ·
        refine ⟨52617801847072123658887217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35078534564714749105924811 52617801847072123658887217)
        ·
          refine ⟨39463351385304092744165413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52617801847072123658887217 39463351385304092744165413)
          ·
            refine ⟨7399378384744517389531015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39463351385304092744165413 7399378384744517389531015)
            ·
              refine ⟨11099067577116776084296523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7399378384744517389531015 11099067577116776084296523)
              ·
                refine ⟨16648601365675164126444785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11099067577116776084296523 16648601365675164126444785)
                ·
                  refine ⟨12486451024256373094833589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16648601365675164126444785 12486451024256373094833589)
                  ·
                    refine ⟨1170604783524034977640649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12486451024256373094833589 1170604783524034977640649)
                    ·
                      rfl

theorem cell22_3419617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 2, 5].length) (baseStart_3419617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3419617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3419617 prefixEnd_3419617 := by exact prefixLift 3419617
  have htrace : WordTrace (prefixWord ++ tailWord_3419617) baseStart_3419617 baseEnd_3419617 := by
    simpa [prefixWord, tailWord_3419617, baseEnd_3419617] using wordTrace_append hprefix tailTrace_3419617
  have hstable : (prefixWord ++ tailWord_3419617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419617).length < 2 ^ (prefixWord ++ tailWord_3419617).sum := by decide
  have hdescent : baseEnd_3419617 < baseStart_3419617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419632 : List Nat := [2, 1, 1, 1, 3, 4, 2, 1, 3, 4]
def baseStart_3419632 : Nat := 118140960795 + 3419632 * 2 ^ 59
def prefixEnd_3419632 : Nat := 4983230072969 + 3 ^ 40 * 3419632 * 2
def baseEnd_3419632 : Nat := 1170609918330579938515603

theorem tailTrace_3419632 : CollatzResearch.WordTrace tailWord_3419632 prefixEnd_3419632 1170609918330579938515603 := by
  unfold tailWord_3419632
  simp only [CollatzResearch.WordTrace]
  refine ⟨62362112773632382746986575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83149483698176510329315433 62362112773632382746986575)
  ·
    refine ⟨93543169160448574120479863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62362112773632382746986575 93543169160448574120479863)
    ·
      refine ⟨140314753740672861180719795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93543169160448574120479863 140314753740672861180719795)
      ·
        refine ⟨210472130611009291771079693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140314753740672861180719795 210472130611009291771079693)
        ·
          refine ⟨78927048979128484414154885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210472130611009291771079693 78927048979128484414154885)
          ·
            refine ⟨14798821683586590827654041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78927048979128484414154885 14798821683586590827654041)
            ·
              refine ⟨11099116262689943120740531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14798821683586590827654041 11099116262689943120740531)
              ·
                refine ⟨16648674394034914681110797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11099116262689943120740531 16648674394034914681110797)
                ·
                  refine ⟨6243252897763093005416549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16648674394034914681110797 6243252897763093005416549)
                  ·
                    refine ⟨1170609918330579938515603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6243252897763093005416549 1170609918330579938515603)
                    ·
                      rfl

theorem cell22_3419632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 3, 4].length) (baseStart_3419632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3419632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3419632 prefixEnd_3419632 := by exact prefixLift 3419632
  have htrace : WordTrace (prefixWord ++ tailWord_3419632) baseStart_3419632 baseEnd_3419632 := by
    simpa [prefixWord, tailWord_3419632, baseEnd_3419632] using wordTrace_append hprefix tailTrace_3419632
  have hstable : (prefixWord ++ tailWord_3419632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419632).length < 2 ^ (prefixWord ++ tailWord_3419632).sum := by decide
  have hdescent : baseEnd_3419632 < baseStart_3419632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419677 : List Nat := [1, 4, 2, 2, 1, 1, 1, 1, 3, 6]
def baseStart_3419677 : Nat := 118140960795 + 3419677 * 2 ^ 59
def prefixEnd_3419677 : Nat := 4983230072969 + 3 ^ 40 * 3419677 * 2
def baseEnd_3419677 : Nat := 1170625322750214821140465

theorem tailTrace_3419677 : CollatzResearch.WordTrace tailWord_3419677 prefixEnd_3419677 1170625322750214821140465 := by
  unfold tailWord_3419677
  simp only [CollatzResearch.WordTrace]
  refine ⟨124725866832101738179361285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83150577888067825452907523 124725866832101738179361285)
  ·
    refine ⟨23386100031019075908630241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124725866832101738179361285 23386100031019075908630241)
    ·
      refine ⟨17539575023264306931472681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23386100031019075908630241 17539575023264306931472681)
      ·
        refine ⟨13154681267448230198604511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17539575023264306931472681 13154681267448230198604511)
        ·
          refine ⟨19732021901172345297906767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13154681267448230198604511 19732021901172345297906767)
          ·
            refine ⟨29598032851758517946860151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19732021901172345297906767 29598032851758517946860151)
            ·
              refine ⟨44397049277637776920290227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29598032851758517946860151 44397049277637776920290227)
              ·
                refine ⟨66595573916456665380435341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44397049277637776920290227 66595573916456665380435341)
                ·
                  refine ⟨24973340218671249517663253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66595573916456665380435341 24973340218671249517663253)
                  ·
                    refine ⟨1170625322750214821140465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24973340218671249517663253 1170625322750214821140465)
                    ·
                      rfl

theorem cell22_3419677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_3419677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3419677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3419677 prefixEnd_3419677 := by exact prefixLift 3419677
  have htrace : WordTrace (prefixWord ++ tailWord_3419677) baseStart_3419677 baseEnd_3419677 := by
    simpa [prefixWord, tailWord_3419677, baseEnd_3419677] using wordTrace_append hprefix tailTrace_3419677
  have hstable : (prefixWord ++ tailWord_3419677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419677).length < 2 ^ (prefixWord ++ tailWord_3419677).sum := by decide
  have hdescent : baseEnd_3419677 < baseStart_3419677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419679 : List Nat := [1, 1, 2, 4, 1, 1, 2, 5, 2, 3]
def baseStart_3419679 : Nat := 118140960795 + 3419679 * 2 ^ 59
def prefixEnd_3419679 : Nat := 4983230072969 + 3 ^ 40 * 3419679 * 2
def baseEnd_3419679 : Nat := 1170626007391087482590459

theorem tailTrace_3419679 : CollatzResearch.WordTrace tailWord_3419679 prefixEnd_3419679 1170626007391087482590459 := by
  unfold tailWord_3419679
  simp only [CollatzResearch.WordTrace]
  refine ⟨124725939778094492520934091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83150626518729661680622727 124725939778094492520934091)
  ·
    refine ⟨187088909667141738781401137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124725939778094492520934091 187088909667141738781401137)
    ·
      refine ⟨140316682250356304086050853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187088909667141738781401137 140316682250356304086050853)
      ·
        refine ⟨26309377921941807016134535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140316682250356304086050853 26309377921941807016134535)
        ·
          refine ⟨39464066882912710524201803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26309377921941807016134535 39464066882912710524201803)
          ·
            refine ⟨59196100324369065786302705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39464066882912710524201803 59196100324369065786302705)
            ·
              refine ⟨44397075243276799339727029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59196100324369065786302705 44397075243276799339727029)
              ·
                refine ⟨4162225804057199938099409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44397075243276799339727029 4162225804057199938099409)
                ·
                  refine ⟨3121669353042899953574557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4162225804057199938099409 3121669353042899953574557)
                  ·
                    refine ⟨1170626007391087482590459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3121669353042899953574557 1170626007391087482590459)
                    ·
                      rfl

theorem cell22_3419679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 5, 2, 3].length) (baseStart_3419679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3419679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3419679 prefixEnd_3419679 := by exact prefixLift 3419679
  have htrace : WordTrace (prefixWord ++ tailWord_3419679) baseStart_3419679 baseEnd_3419679 := by
    simpa [prefixWord, tailWord_3419679, baseEnd_3419679] using wordTrace_append hprefix tailTrace_3419679
  have hstable : (prefixWord ++ tailWord_3419679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419679).length < 2 ^ (prefixWord ++ tailWord_3419679).sum := by decide
  have hdescent : baseEnd_3419679 < baseStart_3419679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419694 : List Nat := [4, 1, 3, 1, 2, 1, 2, 1, 1, 6]
def baseStart_3419694 : Nat := 118140960795 + 3419694 * 2 ^ 59
def prefixEnd_3419694 : Nat := 4983230072969 + 3 ^ 40 * 3419694 * 2
def baseEnd_3419694 : Nat := 1170631142197632443465413

theorem tailTrace_3419694 : CollatzResearch.WordTrace tailWord_3419694 prefixEnd_3419694 1170631142197632443465413 := by
  unfold tailWord_3419694
  simp only [CollatzResearch.WordTrace]
  refine ⟨15590810859130018760341267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83150991248693433388486757 15590810859130018760341267)
  ·
    refine ⟨23386216288695028140511901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15590810859130018760341267 23386216288695028140511901)
    ·
      refine ⟨8769831108260635552691963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23386216288695028140511901 8769831108260635552691963)
      ·
        refine ⟨13154746662390953329037945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8769831108260635552691963 13154746662390953329037945)
        ·
          refine ⟨9866059996793214996778459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13154746662390953329037945 9866059996793214996778459)
          ·
            refine ⟨14799089995189822495167689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9866059996793214996778459 14799089995189822495167689)
            ·
              refine ⟨11099317496392366871375767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14799089995189822495167689 11099317496392366871375767)
              ·
                refine ⟨16648976244588550307063651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11099317496392366871375767 16648976244588550307063651)
                ·
                  refine ⟨24973464366882825460595477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16648976244588550307063651 24973464366882825460595477)
                  ·
                    refine ⟨1170631142197632443465413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24973464366882825460595477 1170631142197632443465413)
                    ·
                      rfl

theorem cell22_3419694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_3419694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3419694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3419694 prefixEnd_3419694 := by exact prefixLift 3419694
  have htrace : WordTrace (prefixWord ++ tailWord_3419694) baseStart_3419694 baseEnd_3419694 := by
    simpa [prefixWord, tailWord_3419694, baseEnd_3419694] using wordTrace_append hprefix tailTrace_3419694
  have hstable : (prefixWord ++ tailWord_3419694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419694).length < 2 ^ (prefixWord ++ tailWord_3419694).sum := by decide
  have hdescent : baseEnd_3419694 < baseStart_3419694 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419709 : List Nat := [1, 4, 1, 3, 3, 2, 8]
def baseStart_3419709 : Nat := 118140960795 + 3419709 * 2 ^ 59
def prefixEnd_3419709 : Nat := 4983230072969 + 3 ^ 40 * 3419709 * 2
def baseEnd_3419709 : Nat := 43356899148302866827421

theorem tailTrace_3419709 : CollatzResearch.WordTrace tailWord_3419709 prefixEnd_3419709 43356899148302866827421 := by
  unfold tailWord_3419709
  simp only [CollatzResearch.WordTrace]
  refine ⟨124727033967985807644526181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83151355978657205096350787 124727033967985807644526181)
  ·
    refine ⟨23386318868997338933348659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124727033967985807644526181 23386318868997338933348659)
    ·
      refine ⟨35079478303496008400022989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23386318868997338933348659 35079478303496008400022989)
      ·
        refine ⟨13154804363811003150008621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35079478303496008400022989 13154804363811003150008621)
        ·
          refine ⟨4933051636429126181253233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13154804363811003150008621 4933051636429126181253233)
          ·
            refine ⟨3699788727321844635939925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4933051636429126181253233 3699788727321844635939925)
            ·
              refine ⟨43356899148302866827421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3699788727321844635939925 43356899148302866827421)
              ·
                rfl

theorem cell22_3419709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 8].length) (baseStart_3419709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3419709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3419709 prefixEnd_3419709 := by exact prefixLift 3419709
  have htrace : WordTrace (prefixWord ++ tailWord_3419709) baseStart_3419709 baseEnd_3419709 := by
    simpa [prefixWord, tailWord_3419709, baseEnd_3419709] using wordTrace_append hprefix tailTrace_3419709
  have hstable : (prefixWord ++ tailWord_3419709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419709).length < 2 ^ (prefixWord ++ tailWord_3419709).sum := by decide
  have hdescent : baseEnd_3419709 < baseStart_3419709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419722 : List Nat := [3, 1, 2, 1, 1, 3, 2, 1, 2, 6]
def baseStart_3419722 : Nat := 118140960795 + 3419722 * 2 ^ 59
def prefixEnd_3419722 : Nat := 4983230072969 + 3 ^ 40 * 3419722 * 2
def baseEnd_3419722 : Nat := 1170640727169849703765327

theorem tailTrace_3419722 : CollatzResearch.WordTrace tailWord_3419722 prefixEnd_3419722 1170640727169849703765327 := by
  unfold tailWord_3419722
  simp only [CollatzResearch.WordTrace]
  refine ⟨31181877029234677716187355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83151672077959140576499613 31181877029234677716187355)
  ·
    refine ⟨46772815543852016574281033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31181877029234677716187355 46772815543852016574281033)
    ·
      refine ⟨35079611657889012430710775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46772815543852016574281033 35079611657889012430710775)
      ·
        refine ⟨52619417486833518646066163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35079611657889012430710775 52619417486833518646066163)
        ·
          refine ⟨78929126230250277969099245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52619417486833518646066163 78929126230250277969099245)
          ·
            refine ⟨29598422336343854238412217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78929126230250277969099245 29598422336343854238412217)
            ·
              refine ⟨22198816752257890678809163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29598422336343854238412217 22198816752257890678809163)
              ·
                refine ⟨33298225128386836018213745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22198816752257890678809163 33298225128386836018213745)
                ·
                  refine ⟨24973668846290127013660309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33298225128386836018213745 24973668846290127013660309)
                  ·
                    refine ⟨1170640727169849703765327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24973668846290127013660309 1170640727169849703765327)
                    ·
                      rfl

theorem cell22_3419722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_3419722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3419722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3419722 prefixEnd_3419722 := by exact prefixLift 3419722
  have htrace : WordTrace (prefixWord ++ tailWord_3419722) baseStart_3419722 baseEnd_3419722 := by
    simpa [prefixWord, tailWord_3419722, baseEnd_3419722] using wordTrace_append hprefix tailTrace_3419722
  have hstable : (prefixWord ++ tailWord_3419722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419722).length < 2 ^ (prefixWord ++ tailWord_3419722).sum := by decide
  have hdescent : baseEnd_3419722 < baseStart_3419722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419799 : List Nat := [1, 1, 3, 3, 2, 3, 1, 2, 6]
def baseStart_3419799 : Nat := 118140960795 + 3419799 * 2 ^ 59
def prefixEnd_3419799 : Nat := 4983230072969 + 3 ^ 40 * 3419799 * 2
def baseEnd_3419799 : Nat := 390222361947815723196697

theorem tailTrace_3419799 : CollatzResearch.WordTrace tailWord_3419799 prefixEnd_3419799 390222361947815723196697 := by
  unfold tailWord_3419799
  simp only [CollatzResearch.WordTrace]
  refine ⟨124730316537659753015302451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83153544358439835343534967 124730316537659753015302451)
  ·
    refine ⟨187095474806489629522953677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124730316537659753015302451 187095474806489629522953677)
    ·
      refine ⟨70160803052433611071107629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187095474806489629522953677 70160803052433611071107629)
      ·
        refine ⟨26310301144662604151665361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70160803052433611071107629 26310301144662604151665361)
        ·
          refine ⟨19732725858496953113749021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26310301144662604151665361 19732725858496953113749021)
          ·
            refine ⟨7399772196936357417655883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19732725858496953113749021 7399772196936357417655883)
            ·
              refine ⟨11099658295404536126483825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7399772196936357417655883 11099658295404536126483825)
              ·
                refine ⟨8324743721553402094862869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11099658295404536126483825 8324743721553402094862869)
                ·
                  refine ⟨390222361947815723196697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8324743721553402094862869 390222361947815723196697)
                  ·
                    rfl

theorem cell22_3419799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 2, 6].length) (baseStart_3419799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3419799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3419799 prefixEnd_3419799 := by exact prefixLift 3419799
  have htrace : WordTrace (prefixWord ++ tailWord_3419799) baseStart_3419799 baseEnd_3419799 := by
    simpa [prefixWord, tailWord_3419799, baseEnd_3419799] using wordTrace_append hprefix tailTrace_3419799
  have hstable : (prefixWord ++ tailWord_3419799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419799).length < 2 ^ (prefixWord ++ tailWord_3419799).sum := by decide
  have hdescent : baseEnd_3419799 < baseStart_3419799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419827 : List Nat := [1, 1, 1, 2, 3, 3, 11]
def baseStart_3419827 : Nat := 118140960795 + 3419827 * 2 ^ 59
def prefixEnd_3419827 : Nat := 4983230072969 + 3 ^ 40 * 3419827 * 2
def baseEnd_3419827 : Nat := 43358395215394978884815

theorem tailTrace_3419827 : CollatzResearch.WordTrace tailWord_3419827 prefixEnd_3419827 43358395215394978884815 := by
  unfold tailWord_3419827
  simp only [CollatzResearch.WordTrace]
  refine ⟨124731337781558313797321735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83154225187705542531547823 124731337781558313797321735)
  ·
    refine ⟨187097006672337470695982603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124731337781558313797321735 187097006672337470695982603)
    ·
      refine ⟨280645510008506206043973905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187097006672337470695982603 280645510008506206043973905)
      ·
        refine ⟨210484132506379654532980429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280645510008506206043973905 210484132506379654532980429)
        ·
          refine ⟨78931549689892370449867661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210484132506379654532980429 78931549689892370449867661)
          ·
            refine ⟨29599331133709638918700373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78931549689892370449867661 29599331133709638918700373)
            ·
              refine ⟨43358395215394978884815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 29599331133709638918700373 43358395215394978884815)
              ·
                rfl

theorem cell22_3419827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 11].length) (baseStart_3419827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3419827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3419827 prefixEnd_3419827 := by exact prefixLift 3419827
  have htrace : WordTrace (prefixWord ++ tailWord_3419827) baseStart_3419827 baseEnd_3419827 := by
    simpa [prefixWord, tailWord_3419827, baseEnd_3419827] using wordTrace_append hprefix tailTrace_3419827
  have hstable : (prefixWord ++ tailWord_3419827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419827).length < 2 ^ (prefixWord ++ tailWord_3419827).sum := by decide
  have hdescent : baseEnd_3419827 < baseStart_3419827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419831 : List Nat := [1, 1, 3, 1, 5, 2, 1, 1, 4, 3]
def baseStart_3419831 : Nat := 118140960795 + 3419831 * 2 ^ 59
def prefixEnd_3419831 : Nat := 4983230072969 + 3 ^ 40 * 3419831 * 2
def baseEnd_3419831 : Nat := 1170678040097409752789993

theorem tailTrace_3419831 : CollatzResearch.WordTrace tailWord_3419831 prefixEnd_3419831 1170678040097409752789993 := by
  unfold tailWord_3419831
  simp only [CollatzResearch.WordTrace]
  refine ⟨124731483673543822480467347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83154322449029214986978231 124731483673543822480467347)
  ·
    refine ⟨187097225510315733720701021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124731483673543822480467347 187097225510315733720701021)
    ·
      refine ⟨70161459566368400145262883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187097225510315733720701021 70161459566368400145262883)
      ·
        refine ⟨105242189349552600217894325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70161459566368400145262883 105242189349552600217894325)
        ·
          refine ⟨9866455251520556270427593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 105242189349552600217894325 9866455251520556270427593)
          ·
            refine ⟨7399841438640417202820695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9866455251520556270427593 7399841438640417202820695)
            ·
              refine ⟨11099762157960625804231043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7399841438640417202820695 11099762157960625804231043)
              ·
                refine ⟨16649643236940938706346565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11099762157960625804231043 16649643236940938706346565)
                ·
                  refine ⟨3121808106926426007439981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16649643236940938706346565 3121808106926426007439981)
                  ·
                    refine ⟨1170678040097409752789993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3121808106926426007439981 1170678040097409752789993)
                    ·
                      rfl

theorem cell22_3419831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 4, 3].length) (baseStart_3419831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3419831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3419831 prefixEnd_3419831 := by exact prefixLift 3419831
  have htrace : WordTrace (prefixWord ++ tailWord_3419831) baseStart_3419831 baseEnd_3419831 := by
    simpa [prefixWord, tailWord_3419831, baseEnd_3419831] using wordTrace_append hprefix tailTrace_3419831
  have hstable : (prefixWord ++ tailWord_3419831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419831).length < 2 ^ (prefixWord ++ tailWord_3419831).sum := by decide
  have hdescent : baseEnd_3419831 < baseStart_3419831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419844 : List Nat := [2, 3, 3, 1, 1, 1, 2, 9]
def baseStart_3419844 : Nat := 118140960795 + 3419844 * 2 ^ 59
def prefixEnd_3419844 : Nat := 4983230072969 + 3 ^ 40 * 3419844 * 2
def baseEnd_3419844 : Nat := 130075832251453561357217

theorem tailTrace_3419844 : CollatzResearch.WordTrace tailWord_3419844 prefixEnd_3419844 130075832251453561357217 := by
  unfold tailWord_3419844
  simp only [CollatzResearch.WordTrace]
  refine ⟨62365978911248362850345293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83154638548331150467127057 62365978911248362850345293)
  ·
    refine ⟨23387242091718136068879485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62365978911248362850345293 23387242091718136068879485)
    ·
      refine ⟨8770215784394301025829807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23387242091718136068879485 8770215784394301025829807)
      ·
        refine ⟨13155323676591451538744711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8770215784394301025829807 13155323676591451538744711)
        ·
          refine ⟨19732985514887177308117067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13155323676591451538744711 19732985514887177308117067)
          ·
            refine ⟨29599478272330765962175601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19732985514887177308117067 29599478272330765962175601)
            ·
              refine ⟨22199608704248074471631701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29599478272330765962175601 22199608704248074471631701)
              ·
                refine ⟨130075832251453561357217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22199608704248074471631701 130075832251453561357217)
                ·
                  rfl

theorem cell22_3419844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 9].length) (baseStart_3419844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3419844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3419844 prefixEnd_3419844 := by exact prefixLift 3419844
  have htrace : WordTrace (prefixWord ++ tailWord_3419844) baseStart_3419844 baseEnd_3419844 := by
    simpa [prefixWord, tailWord_3419844, baseEnd_3419844] using wordTrace_append hprefix tailTrace_3419844
  have hstable : (prefixWord ++ tailWord_3419844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419844).length < 2 ^ (prefixWord ++ tailWord_3419844).sum := by decide
  have hdescent : baseEnd_3419844 < baseStart_3419844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419848 : List Nat := [2, 1, 3, 1, 2, 2, 5, 1, 2, 3]
def baseStart_3419848 : Nat := 118140960795 + 3419848 * 2 ^ 59
def prefixEnd_3419848 : Nat := 4983230072969 + 3 ^ 40 * 3419848 * 2
def baseEnd_3419848 : Nat := 1170683859544827375114941

theorem tailTrace_3419848 : CollatzResearch.WordTrace tailWord_3419848 prefixEnd_3419848 1170683859544827375114941 := by
  unfold tailWord_3419848
  simp only [CollatzResearch.WordTrace]
  refine ⟨62366051857241117191918099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83154735809654822922557465 62366051857241117191918099)
  ·
    refine ⟨93549077785861675787877149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62366051857241117191918099 93549077785861675787877149)
    ·
      refine ⟨35080904169698128420453931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93549077785861675787877149 35080904169698128420453931)
      ·
        refine ⟨52621356254547192630680897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35080904169698128420453931 52621356254547192630680897)
        ·
          refine ⟨39466017190910394473010673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52621356254547192630680897 39466017190910394473010673)
          ·
            refine ⟨29599512893182795854758005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39466017190910394473010673 29599512893182795854758005)
            ·
              refine ⟨2774954333735887111383563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29599512893182795854758005 2774954333735887111383563)
              ·
                refine ⟨4162431500603830667075345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2774954333735887111383563 4162431500603830667075345)
                ·
                  refine ⟨3121823625452873000306509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4162431500603830667075345 3121823625452873000306509)
                  ·
                    refine ⟨1170683859544827375114941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3121823625452873000306509 1170683859544827375114941)
                    ·
                      rfl

theorem cell22_3419848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 5, 1, 2, 3].length) (baseStart_3419848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3419848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3419848 prefixEnd_3419848 := by exact prefixLift 3419848
  have htrace : WordTrace (prefixWord ++ tailWord_3419848) baseStart_3419848 baseEnd_3419848 := by
    simpa [prefixWord, tailWord_3419848, baseEnd_3419848] using wordTrace_append hprefix tailTrace_3419848
  have hstable : (prefixWord ++ tailWord_3419848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419848).length < 2 ^ (prefixWord ++ tailWord_3419848).sum := by decide
  have hdescent : baseEnd_3419848 < baseStart_3419848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419859 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 9, 3]
def baseStart_3419859 : Nat := 118140960795 + 3419859 * 2 ^ 59
def prefixEnd_3419859 : Nat := 4983230072969 + 3 ^ 40 * 3419859 * 2
def baseEnd_3419859 : Nat := 1170687625069627013089907

theorem tailTrace_3419859 : CollatzResearch.WordTrace tailWord_3419859 prefixEnd_3419859 1170687625069627013089907 := by
  unfold tailWord_3419859
  simp only [CollatzResearch.WordTrace]
  refine ⟨124732504917442383262486631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83155003278294922174991087 124732504917442383262486631)
  ·
    refine ⟨187098757376163574893729947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124732504917442383262486631 187098757376163574893729947)
    ·
      refine ⟨280648136064245362340594921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187098757376163574893729947 280648136064245362340594921)
      ·
        refine ⟨210486102048184021755446191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280648136064245362340594921 210486102048184021755446191)
        ·
          refine ⟨315729153072276032633169287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210486102048184021755446191 315729153072276032633169287)
          ·
            refine ⟨473593729608414048949753931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315729153072276032633169287 473593729608414048949753931)
            ·
              refine ⟨710390594412621073424630897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 473593729608414048949753931 710390594412621073424630897)
              ·
                refine ⟨532792945809465805068473173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 710390594412621073424630897 532792945809465805068473173)
                ·
                  refine ⟨3121833666852338701573085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 532792945809465805068473173 3121833666852338701573085)
                  ·
                    refine ⟨1170687625069627013089907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3121833666852338701573085 1170687625069627013089907)
                    ·
                      rfl

theorem cell22_3419859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 9, 3].length) (baseStart_3419859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3419859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3419859 prefixEnd_3419859 := by exact prefixLift 3419859
  have htrace : WordTrace (prefixWord ++ tailWord_3419859) baseStart_3419859 baseEnd_3419859 := by
    simpa [prefixWord, tailWord_3419859, baseEnd_3419859] using wordTrace_append hprefix tailTrace_3419859
  have hstable : (prefixWord ++ tailWord_3419859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419859).length < 2 ^ (prefixWord ++ tailWord_3419859).sum := by decide
  have hdescent : baseEnd_3419859 < baseStart_3419859 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419889 : List Nat := [1, 2, 2, 2, 2, 3, 2, 1, 7]
def baseStart_3419889 : Nat := 118140960795 + 3419889 * 2 ^ 59
def prefixEnd_3419889 : Nat := 4983230072969 + 3 ^ 40 * 3419889 * 2
def baseEnd_3419889 : Nat := 390232631560905644946605

theorem tailTrace_3419889 : CollatzResearch.WordTrace tailWord_3419889 prefixEnd_3419889 390232631560905644946605 := by
  unfold tailWord_3419889
  simp only [CollatzResearch.WordTrace]
  refine ⟨124733599107333698386078721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83155732738222465590719147 124733599107333698386078721)
  ·
    refine ⟨93550199330500273789559041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124733599107333698386078721 93550199330500273789559041)
    ·
      refine ⟨70162649497875205342169281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93550199330500273789559041 70162649497875205342169281)
      ·
        refine ⟨52621987123406404006626961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70162649497875205342169281 52621987123406404006626961)
        ·
          refine ⟨39466490342554803004970221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52621987123406404006626961 39466490342554803004970221)
          ·
            refine ⟨14799933878458051126863833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39466490342554803004970221 14799933878458051126863833)
            ·
              refine ⟨11099950408843538345147875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14799933878458051126863833 11099950408843538345147875)
              ·
                refine ⟨16649925613265307517721813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11099950408843538345147875 16649925613265307517721813)
                ·
                  refine ⟨390232631560905644946605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16649925613265307517721813 390232631560905644946605)
                  ·
                    rfl

theorem cell22_3419889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 7].length) (baseStart_3419889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3419889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3419889 prefixEnd_3419889 := by exact prefixLift 3419889
  have htrace : WordTrace (prefixWord ++ tailWord_3419889) baseStart_3419889 baseEnd_3419889 := by
    simpa [prefixWord, tailWord_3419889, baseEnd_3419889] using wordTrace_append hprefix tailTrace_3419889
  have hstable : (prefixWord ++ tailWord_3419889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419889).length < 2 ^ (prefixWord ++ tailWord_3419889).sum := by decide
  have hdescent : baseEnd_3419889 < baseStart_3419889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419951 : List Nat := [1, 1, 2, 1, 2, 1, 2, 8, 4]
def baseStart_3419951 : Nat := 118140960795 + 3419951 * 2 ^ 59
def prefixEnd_3419951 : Nat := 4983230072969 + 3 ^ 40 * 3419951 * 2
def baseEnd_3419951 : Nat := 390239706183256479929875

theorem tailTrace_3419951 : CollatzResearch.WordTrace tailWord_3419951 prefixEnd_3419951 390239706183256479929875 := by
  unfold tailWord_3419951
  simp only [CollatzResearch.WordTrace]
  refine ⟨124735860433109082974835707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83157240288739388649890471 124735860433109082974835707)
  ·
    refine ⟨187103790649663624462253561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124735860433109082974835707 187103790649663624462253561)
    ·
      refine ⟨140327842987247718346690171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187103790649663624462253561 140327842987247718346690171)
      ·
        refine ⟨210491764480871577520035257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140327842987247718346690171 210491764480871577520035257)
        ·
          refine ⟨157868823360653683140026443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210491764480871577520035257 157868823360653683140026443)
          ·
            refine ⟨236803235040980524710039665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157868823360653683140026443 236803235040980524710039665)
            ·
              refine ⟨177602426280735393532529749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236803235040980524710039665 177602426280735393532529749)
              ·
                refine ⟨2081278432977367892959333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 177602426280735393532529749 2081278432977367892959333)
                ·
                  refine ⟨390239706183256479929875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2081278432977367892959333 390239706183256479929875)
                  ·
                    rfl

theorem cell22_3419951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 8, 4].length) (baseStart_3419951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3419951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3419951 prefixEnd_3419951 := by exact prefixLift 3419951
  have htrace : WordTrace (prefixWord ++ tailWord_3419951) baseStart_3419951 baseEnd_3419951 := by
    simpa [prefixWord, tailWord_3419951, baseEnd_3419951] using wordTrace_append hprefix tailTrace_3419951
  have hstable : (prefixWord ++ tailWord_3419951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419951).length < 2 ^ (prefixWord ++ tailWord_3419951).sum := by decide
  have hdescent : baseEnd_3419951 < baseStart_3419951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420000 : List Nat := [2, 1, 1, 3, 3, 4, 1, 2, 2, 3]
def baseStart_3420000 : Nat := 118140960795 + 3420000 * 2 ^ 59
def prefixEnd_3420000 : Nat := 4983230072969 + 3 ^ 40 * 3420000 * 2
def baseEnd_3420000 : Nat := 1170735892251149645314475

theorem tailTrace_3420000 : CollatzResearch.WordTrace tailWord_3420000 prefixEnd_3420000 1170735892251149645314475 := by
  unfold tailWord_3420000
  simp only [CollatzResearch.WordTrace]
  refine ⟨62368823804965782171684727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83158431739954376228912969 62368823804965782171684727)
  ·
    refine ⟨93553235707448673257527091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62368823804965782171684727 93553235707448673257527091)
    ·
      refine ⟨140329853561173009886290637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93553235707448673257527091 140329853561173009886290637)
      ·
        refine ⟨52623695085439878707358989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140329853561173009886290637 52623695085439878707358989)
        ·
          refine ⟨19733885657039954515259621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52623695085439878707358989 19733885657039954515259621)
          ·
            refine ⟨3700103560694991471611179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19733885657039954515259621 3700103560694991471611179)
            ·
              refine ⟨5550155341042487207416769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3700103560694991471611179 5550155341042487207416769)
              ·
                refine ⟨4162616505781865405562577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5550155341042487207416769 4162616505781865405562577)
                ·
                  refine ⟨3121962379336399054171933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4162616505781865405562577 3121962379336399054171933)
                  ·
                    refine ⟨1170735892251149645314475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3121962379336399054171933 1170735892251149645314475)
                    ·
                      rfl

theorem cell22_3420000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 2, 2, 3].length) (baseStart_3420000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3420000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3420000 prefixEnd_3420000 := by exact prefixLift 3420000
  have htrace : WordTrace (prefixWord ++ tailWord_3420000) baseStart_3420000 baseEnd_3420000 := by
    simpa [prefixWord, tailWord_3420000, baseEnd_3420000] using wordTrace_append hprefix tailTrace_3420000
  have hstable : (prefixWord ++ tailWord_3420000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420000).length < 2 ^ (prefixWord ++ tailWord_3420000).sum := by decide
  have hdescent : baseEnd_3420000 < baseStart_3420000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420009 : List Nat := [1, 2, 1, 1, 1, 3, 1, 3, 1, 8]
def baseStart_3420009 : Nat := 118140960795 + 3420009 * 2 ^ 59
def prefixEnd_3420009 : Nat := 4983230072969 + 3 ^ 40 * 3420009 * 2
def baseEnd_3420009 : Nat := 1170738973135076621839447

theorem tailTrace_3420009 : CollatzResearch.WordTrace tailWord_3420009 prefixEnd_3420009 1170738973135076621839447 := by
  unfold tailWord_3420009
  simp only [CollatzResearch.WordTrace]
  refine ⟨124737975866898958880447081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83158650577932639253631387 124737975866898958880447081)
  ·
    refine ⟨93553481900174219160335311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124737975866898958880447081 93553481900174219160335311)
    ·
      refine ⟨140330222850261328740502967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93553481900174219160335311 140330222850261328740502967)
      ·
        refine ⟨210495334275391993110754451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140330222850261328740502967 210495334275391993110754451)
        ·
          refine ⟨315743001413087989666131677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210495334275391993110754451 315743001413087989666131677)
          ·
            refine ⟨118403625529907996124799379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 315743001413087989666131677 118403625529907996124799379)
            ·
              refine ⟨177605438294861994187199069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118403625529907996124799379 177605438294861994187199069)
              ·
                refine ⟨66602039360573247820199651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 177605438294861994187199069 66602039360573247820199651)
                ·
                  refine ⟨99903059040859871730299477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66602039360573247820199651 99903059040859871730299477)
                  ·
                    refine ⟨1170738973135076621839447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 99903059040859871730299477 1170738973135076621839447)
                    ·
                      rfl

theorem cell22_3420009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 8].length) (baseStart_3420009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3420009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3420009 prefixEnd_3420009 := by exact prefixLift 3420009
  have htrace : WordTrace (prefixWord ++ tailWord_3420009) baseStart_3420009 baseEnd_3420009 := by
    simpa [prefixWord, tailWord_3420009, baseEnd_3420009] using wordTrace_append hprefix tailTrace_3420009
  have hstable : (prefixWord ++ tailWord_3420009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420009).length < 2 ^ (prefixWord ++ tailWord_3420009).sum := by decide
  have hdescent : baseEnd_3420009 < baseStart_3420009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420030 : List Nat := [4, 2, 3, 1, 1, 1, 4, 6]
def baseStart_3420030 : Nat := 118140960795 + 3420030 * 2 ^ 59
def prefixEnd_3420030 : Nat := 4983230072969 + 3 ^ 40 * 3420030 * 2
def baseEnd_3420030 : Nat := 130082906873804396340487

theorem tailTrace_3420030 : CollatzResearch.WordTrace tailWord_3420030 prefixEnd_3420030 130082906873804396340487 := by
  unfold tailWord_3420030
  simp only [CollatzResearch.WordTrace]
  refine ⟨15592342724977859933370193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83159161199881919644641029 15592342724977859933370193)
  ·
    refine ⟨11694257043733394950027645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15592342724977859933370193 11694257043733394950027645)
    ·
      refine ⟨4385346391400023106260367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11694257043733394950027645 4385346391400023106260367)
      ·
        refine ⟨6578019587100034659390551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4385346391400023106260367 6578019587100034659390551)
        ·
          refine ⟨9867029380650051989085827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6578019587100034659390551 9867029380650051989085827)
          ·
            refine ⟨14800544070975077983628741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9867029380650051989085827 14800544070975077983628741)
            ·
              refine ⟨2775102013307827121930389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14800544070975077983628741 2775102013307827121930389)
              ·
                refine ⟨130082906873804396340487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2775102013307827121930389 130082906873804396340487)
                ·
                  rfl

theorem cell22_3420030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 4, 6].length) (baseStart_3420030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3420030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3420030 prefixEnd_3420030 := by exact prefixLift 3420030
  have htrace : WordTrace (prefixWord ++ tailWord_3420030) baseStart_3420030 baseEnd_3420030 := by
    simpa [prefixWord, tailWord_3420030, baseEnd_3420030] using wordTrace_append hprefix tailTrace_3420030
  have hstable : (prefixWord ++ tailWord_3420030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420030).length < 2 ^ (prefixWord ++ tailWord_3420030).sum := by decide
  have hdescent : baseEnd_3420030 < baseStart_3420030 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420103 : List Nat := [1, 1, 4, 1, 1, 2, 1, 7, 4]
def baseStart_3420103 : Nat := 118140960795 + 3420103 * 2 ^ 59
def prefixEnd_3420103 : Nat := 4983230072969 + 3 ^ 40 * 3420103 * 2
def baseEnd_3420103 : Nat := 390257050418697236663053

theorem tailTrace_3420103 : CollatzResearch.WordTrace tailWord_3420103 prefixEnd_3420103 390257050418697236663053 := by
  unfold tailWord_3420103
  simp only [CollatzResearch.WordTrace]
  refine ⟨124741404328558412934368963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83160936219038941956245975 124741404328558412934368963)
  ·
    refine ⟨187112106492837619401553445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124741404328558412934368963 187112106492837619401553445)
    ·
      refine ⟨35083519967407053637791271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187112106492837619401553445 35083519967407053637791271)
      ·
        refine ⟨52625279951110580456686907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35083519967407053637791271 52625279951110580456686907)
        ·
          refine ⟨78937919926665870685030361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52625279951110580456686907 78937919926665870685030361)
          ·
            refine ⟨59203439944999403013772771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78937919926665870685030361 59203439944999403013772771)
            ·
              refine ⟨88805159917499104520659157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59203439944999403013772771 88805159917499104520659157)
              ·
                refine ⟨2081370935566385262202949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 88805159917499104520659157 2081370935566385262202949)
                ·
                  refine ⟨390257050418697236663053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2081370935566385262202949 390257050418697236663053)
                  ·
                    rfl

theorem cell22_3420103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 7, 4].length) (baseStart_3420103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3420103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3420103 prefixEnd_3420103 := by exact prefixLift 3420103
  have htrace : WordTrace (prefixWord ++ tailWord_3420103) baseStart_3420103 baseEnd_3420103 := by
    simpa [prefixWord, tailWord_3420103, baseEnd_3420103] using wordTrace_append hprefix tailTrace_3420103
  have hstable : (prefixWord ++ tailWord_3420103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420103).length < 2 ^ (prefixWord ++ tailWord_3420103).sum := by decide
  have hdescent : baseEnd_3420103 < baseStart_3420103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420135 : List Nat := [1, 1, 5, 2, 3, 1, 2, 1, 1, 5]
def baseStart_3420135 : Nat := 118140960795 + 3420135 * 2 ^ 59
def prefixEnd_3420135 : Nat := 4983230072969 + 3 ^ 40 * 3420135 * 2
def baseEnd_3420135 : Nat := 1170782105510054293189061

theorem tailTrace_3420135 : CollatzResearch.WordTrace tailWord_3420135 prefixEnd_3420135 1170782105510054293189061 := by
  unfold tailWord_3420135
  simp only [CollatzResearch.WordTrace]
  refine ⟨124742571464442482399533859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83161714309628321599689239 124742571464442482399533859)
  ·
    refine ⟨187113857196663723599300789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124742571464442482399533859 187113857196663723599300789)
    ·
      refine ⟨17541924112187224087434449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 187113857196663723599300789 17541924112187224087434449)
      ·
        refine ⟨13156443084140418065575837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17541924112187224087434449 13156443084140418065575837)
        ·
          refine ⟨4933666156552656774590939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13156443084140418065575837 4933666156552656774590939)
          ·
            refine ⟨7400499234828985161886409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4933666156552656774590939 7400499234828985161886409)
            ·
              refine ⟨5550374426121738871414807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7400499234828985161886409 5550374426121738871414807)
              ·
                refine ⟨8325561639182608307122211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5550374426121738871414807 8325561639182608307122211)
                ·
                  refine ⟨12488342458773912460683317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8325561639182608307122211 12488342458773912460683317)
                  ·
                    refine ⟨1170782105510054293189061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12488342458773912460683317 1170782105510054293189061)
                    ·
                      rfl

theorem cell22_3420135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_3420135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3420135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3420135 prefixEnd_3420135 := by exact prefixLift 3420135
  have htrace : WordTrace (prefixWord ++ tailWord_3420135) baseStart_3420135 baseEnd_3420135 := by
    simpa [prefixWord, tailWord_3420135, baseEnd_3420135] using wordTrace_append hprefix tailTrace_3420135
  have hstable : (prefixWord ++ tailWord_3420135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420135).length < 2 ^ (prefixWord ++ tailWord_3420135).sum := by decide
  have hdescent : baseEnd_3420135 < baseStart_3420135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420150 : List Nat := [5, 1, 1, 1, 4, 1, 1, 1, 1, 6]
def baseStart_3420150 : Nat := 118140960795 + 3420150 * 2 ^ 59
def prefixEnd_3420150 : Nat := 4983230072969 + 3 ^ 40 * 3420150 * 2
def baseEnd_3420150 : Nat := 1170787240316599254064015

theorem tailTrace_3420150 : CollatzResearch.WordTrace tailWord_3420150 prefixEnd_3420150 1170787240316599254064015 := by
  unfold tailWord_3420150
  simp only [CollatzResearch.WordTrace]
  refine ⟨7796444909961758747583119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83162079039592093307553269 7796444909961758747583119)
  ·
    refine ⟨11694667364942638121374679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7796444909961758747583119 11694667364942638121374679)
    ·
      refine ⟨17542001047413957182062019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11694667364942638121374679 17542001047413957182062019)
      ·
        refine ⟨26313001571120935773093029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17542001047413957182062019 26313001571120935773093029)
        ·
          refine ⟨4933687794585175457454943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26313001571120935773093029 4933687794585175457454943)
          ·
            refine ⟨7400531691877763186182415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4933687794585175457454943 7400531691877763186182415)
            ·
              refine ⟨11100797537816644779273623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7400531691877763186182415 11100797537816644779273623)
              ·
                refine ⟨16651196306724967168910435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11100797537816644779273623 16651196306724967168910435)
                ·
                  refine ⟨24976794460087450753365653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16651196306724967168910435 24976794460087450753365653)
                  ·
                    refine ⟨1170787240316599254064015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24976794460087450753365653 1170787240316599254064015)
                    ·
                      rfl

theorem cell22_3420150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_3420150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3420150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3420150 prefixEnd_3420150 := by exact prefixLift 3420150
  have htrace : WordTrace (prefixWord ++ tailWord_3420150) baseStart_3420150 baseEnd_3420150 := by
    simpa [prefixWord, tailWord_3420150, baseEnd_3420150] using wordTrace_append hprefix tailTrace_3420150
  have hstable : (prefixWord ++ tailWord_3420150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420150).length < 2 ^ (prefixWord ++ tailWord_3420150).sum := by decide
  have hdescent : baseEnd_3420150 < baseStart_3420150 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420176 : List Nat := [2, 1, 1, 1, 1, 1, 1, 7, 7]
def baseStart_3420176 : Nat := 118140960795 + 3420176 * 2 ^ 59
def prefixEnd_3420176 : Nat := 4983230072969 + 3 ^ 40 * 3420176 * 2
def baseEnd_3420176 : Nat := 390265380215981284304645

theorem tailTrace_3420176 : CollatzResearch.WordTrace tailWord_3420176 prefixEnd_3420176 390265380215981284304645 := by
  unfold tailWord_3420176
  simp only [CollatzResearch.WordTrace]
  refine ⟨62372033428646973200888191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83162711238195964267850921 62372033428646973200888191)
  ·
    refine ⟨93558050142970459801332287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62372033428646973200888191 93558050142970459801332287)
    ·
      refine ⟨140337075214455689701998431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93558050142970459801332287 140337075214455689701998431)
      ·
        refine ⟨210505612821683534552997647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140337075214455689701998431 210505612821683534552997647)
        ·
          refine ⟨315758419232525301829496471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210505612821683534552997647 315758419232525301829496471)
          ·
            refine ⟨473637628848787952744244707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315758419232525301829496471 473637628848787952744244707)
            ·
              refine ⟨710456443273181929116367061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 473637628848787952744244707 710456443273181929116367061)
              ·
                refine ⟨16651322889215201463664853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 710456443273181929116367061 16651322889215201463664853)
                ·
                  refine ⟨390265380215981284304645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16651322889215201463664853 390265380215981284304645)
                  ·
                    rfl

theorem cell22_3420176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 7].length) (baseStart_3420176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3420176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3420176 prefixEnd_3420176 := by exact prefixLift 3420176
  have htrace : WordTrace (prefixWord ++ tailWord_3420176) baseStart_3420176 baseEnd_3420176 := by
    simpa [prefixWord, tailWord_3420176, baseEnd_3420176] using wordTrace_append hprefix tailTrace_3420176
  have hstable : (prefixWord ++ tailWord_3420176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420176).length < 2 ^ (prefixWord ++ tailWord_3420176).sum := by decide
  have hdescent : baseEnd_3420176 < baseStart_3420176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420199 : List Nat := [1, 1, 7, 1, 3, 1, 2, 6]
def baseStart_3420199 : Nat := 118140960795 + 3420199 * 2 ^ 59
def prefixEnd_3420199 : Nat := 4983230072969 + 3 ^ 40 * 3420199 * 2
def baseEnd_3420199 : Nat := 130089334890886606620985

theorem tailTrace_3420199 : CollatzResearch.WordTrace tailWord_3420199 prefixEnd_3420199 130089334890886606620985 := by
  unfold tailWord_3420199
  simp only [CollatzResearch.WordTrace]
  refine ⟨124744905736210621329863651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83163270490807080886575767 124744905736210621329863651)
  ·
    refine ⟨187117358604315931994795477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124744905736210621329863651 187117358604315931994795477)
    ·
      refine ⟨4385563092288654656128019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 187117358604315931994795477 4385563092288654656128019)
      ·
        refine ⟨6578344638432981984192029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4385563092288654656128019 6578344638432981984192029)
        ·
          refine ⟨2466879239412368244072011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6578344638432981984192029 2466879239412368244072011)
          ·
            refine ⟨3700318859118552366108017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2466879239412368244072011 3700318859118552366108017)
            ·
              refine ⟨2775239144338914274581013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3700318859118552366108017 2775239144338914274581013)
              ·
                refine ⟨130089334890886606620985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2775239144338914274581013 130089334890886606620985)
                ·
                  rfl

theorem cell22_3420199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 2, 6].length) (baseStart_3420199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3420199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3420199 prefixEnd_3420199 := by exact prefixLift 3420199
  have htrace : WordTrace (prefixWord ++ tailWord_3420199) baseStart_3420199 baseEnd_3420199 := by
    simpa [prefixWord, tailWord_3420199, baseEnd_3420199] using wordTrace_append hprefix tailTrace_3420199
  have hstable : (prefixWord ++ tailWord_3420199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420199).length < 2 ^ (prefixWord ++ tailWord_3420199).sum := by decide
  have hdescent : baseEnd_3420199 < baseStart_3420199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420270 : List Nat := [4, 1, 2, 2, 1, 1, 3, 2, 1, 5]
def baseStart_3420270 : Nat := 118140960795 + 3420270 * 2 ^ 59
def prefixEnd_3420270 : Nat := 4983230072969 + 3 ^ 40 * 3420270 * 2
def baseEnd_3420270 : Nat := 1170828318768958941063647

theorem tailTrace_3420270 : CollatzResearch.WordTrace tailWord_3420270 prefixEnd_3420270 1170828318768958941063647 := by
  unfold tailWord_3420270
  simp only [CollatzResearch.WordTrace]
  refine ⟨15593436914869175056962283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83164996879302266970465509 15593436914869175056962283)
  ·
    refine ⟨23390155372303762585443425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15593436914869175056962283 23390155372303762585443425)
    ·
      refine ⟨17542616529227821939082569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23390155372303762585443425 17542616529227821939082569)
      ·
        refine ⟨13156962396920866454311927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17542616529227821939082569 13156962396920866454311927)
        ·
          refine ⟨19735443595381299681467891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13156962396920866454311927 19735443595381299681467891)
          ·
            refine ⟨29603165393071949522201837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19735443595381299681467891 29603165393071949522201837)
            ·
              refine ⟨11101187022401981070825689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29603165393071949522201837 11101187022401981070825689)
              ·
                refine ⟨8325890266801485803119267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11101187022401981070825689 8325890266801485803119267)
                ·
                  refine ⟨12488835400202228704678901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8325890266801485803119267 12488835400202228704678901)
                  ·
                    refine ⟨1170828318768958941063647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12488835400202228704678901 1170828318768958941063647)
                    ·
                      rfl

theorem cell22_3420270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_3420270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3420270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3420270 prefixEnd_3420270 := by exact prefixLift 3420270
  have htrace : WordTrace (prefixWord ++ tailWord_3420270) baseStart_3420270 baseEnd_3420270 := by
    simpa [prefixWord, tailWord_3420270, baseEnd_3420270] using wordTrace_append hprefix tailTrace_3420270
  have hstable : (prefixWord ++ tailWord_3420270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420270).length < 2 ^ (prefixWord ++ tailWord_3420270).sum := by decide
  have hdescent : baseEnd_3420270 < baseStart_3420270 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420285 : List Nat := [1, 4, 1, 1, 3, 2, 2, 2, 2, 4]
def baseStart_3420285 : Nat := 118140960795 + 3420285 * 2 ^ 59
def prefixEnd_3420285 : Nat := 4983230072969 + 3 ^ 40 * 3420285 * 2
def baseEnd_3420285 : Nat := 1170833453575503901938601

theorem tailTrace_3420285 : CollatzResearch.WordTrace tailWord_3420285 prefixEnd_3420285 1170833453575503901938601 := by
  unfold tailWord_3420285
  simp only [CollatzResearch.WordTrace]
  refine ⟨124748042413899058017494309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83165361609266038678329539 124748042413899058017494309)
  ·
    refine ⟨23390257952606073378280183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124748042413899058017494309 23390257952606073378280183)
    ·
      refine ⟨35085386928909110067420275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23390257952606073378280183 35085386928909110067420275)
      ·
        refine ⟨52628080393363665101130413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35085386928909110067420275 52628080393363665101130413)
        ·
          refine ⟨19735530147511374412923905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52628080393363665101130413 19735530147511374412923905)
          ·
            refine ⟨14801647610633530809692929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19735530147511374412923905 14801647610633530809692929)
            ·
              refine ⟨11101235707975148107269697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14801647610633530809692929 11101235707975148107269697)
              ·
                refine ⟨8325926780981361080452273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11101235707975148107269697 8325926780981361080452273)
                ·
                  refine ⟨6244445085736020810339205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8325926780981361080452273 6244445085736020810339205)
                  ·
                    refine ⟨1170833453575503901938601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6244445085736020810339205 1170833453575503901938601)
                    ·
                      rfl

theorem cell22_3420285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 2, 2, 4].length) (baseStart_3420285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3420285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3420285 prefixEnd_3420285 := by exact prefixLift 3420285
  have htrace : WordTrace (prefixWord ++ tailWord_3420285) baseStart_3420285 baseEnd_3420285 := by
    simpa [prefixWord, tailWord_3420285, baseEnd_3420285] using wordTrace_append hprefix tailTrace_3420285
  have hstable : (prefixWord ++ tailWord_3420285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420285).length < 2 ^ (prefixWord ++ tailWord_3420285).sum := by decide
  have hdescent : baseEnd_3420285 < baseStart_3420285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420362 : List Nat := [3, 1, 2, 1, 3, 1, 5, 1, 5]
def baseStart_3420362 : Nat := 118140960795 + 3420362 * 2 ^ 59
def prefixEnd_3420362 : Nat := 4983230072969 + 3 ^ 40 * 3420362 * 2
def baseEnd_3420362 : Nat := 390286604083033789254455

theorem tailTrace_3420362 : CollatzResearch.WordTrace tailWord_3420362 prefixEnd_3420362 390286604083033789254455 := by
  unfold tailWord_3420362
  simp only [CollatzResearch.WordTrace]
  refine ⟨31187712708655025042011835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83167233889746733445364893 31187712708655025042011835)
  ·
    refine ⟨46781569062982537563017753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31187712708655025042011835 46781569062982537563017753)
    ·
      refine ⟨35086176797236903172263315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46781569062982537563017753 35086176797236903172263315)
      ·
        refine ⟨52629265195855354758394973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35086176797236903172263315 52629265195855354758394973)
        ·
          refine ⟨19735974448445758034398115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52629265195855354758394973 19735974448445758034398115)
          ·
            refine ⟨29603961672668637051597173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19735974448445758034398115 29603961672668637051597173)
            ·
              refine ⟨2775371406812684723587235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29603961672668637051597173 2775371406812684723587235)
              ·
                refine ⟨4163057110219027085380853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2775371406812684723587235 4163057110219027085380853)
                ·
                  refine ⟨390286604083033789254455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4163057110219027085380853 390286604083033789254455)
                  ·
                    rfl

theorem cell22_3420362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 5, 1, 5].length) (baseStart_3420362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3420362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3420362 prefixEnd_3420362 := by exact prefixLift 3420362
  have htrace : WordTrace (prefixWord ++ tailWord_3420362) baseStart_3420362 baseEnd_3420362 := by
    simpa [prefixWord, tailWord_3420362, baseEnd_3420362] using wordTrace_append hprefix tailTrace_3420362
  have hstable : (prefixWord ++ tailWord_3420362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420362).length < 2 ^ (prefixWord ++ tailWord_3420362).sum := by decide
  have hdescent : baseEnd_3420362 < baseStart_3420362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420392 : List Nat := [2, 1, 4, 1, 2, 2, 2, 3, 1, 4]
def baseStart_3420392 : Nat := 118140960795 + 3420392 * 2 ^ 59
def prefixEnd_3420392 : Nat := 4983230072969 + 3 ^ 40 * 3420392 * 2
def baseEnd_3420392 : Nat := 1170870081862191289513273

theorem tailTrace_3420392 : CollatzResearch.WordTrace tailWord_3420392 prefixEnd_3420392 1170870081862191289513273 := by
  unfold tailWord_3420392
  simp only [CollatzResearch.WordTrace]
  refine ⟨62375972512255707645819715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83167963349674276861092953 62375972512255707645819715)
  ·
    refine ⟨93563958768383561468729573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62375972512255707645819715 93563958768383561468729573)
    ·
      refine ⟨17543242269071917775386795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93563958768383561468729573 17543242269071917775386795)
      ·
        refine ⟨26314863403607876663080193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17543242269071917775386795 26314863403607876663080193)
        ·
          refine ⟨19736147552705907497310145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26314863403607876663080193 19736147552705907497310145)
          ·
            refine ⟨14802110664529430622982609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19736147552705907497310145 14802110664529430622982609)
            ·
              refine ⟨11101582998397072967236957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14802110664529430622982609 11101582998397072967236957)
              ·
                refine ⟨4163093624398902362713859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11101582998397072967236957 4163093624398902362713859)
                ·
                  refine ⟨6244640436598353544070789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4163093624398902362713859 6244640436598353544070789)
                  ·
                    refine ⟨1170870081862191289513273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6244640436598353544070789 1170870081862191289513273)
                    ·
                      rfl

theorem cell22_3420392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_3420392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3420392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3420392 prefixEnd_3420392 := by exact prefixLift 3420392
  have htrace : WordTrace (prefixWord ++ tailWord_3420392) baseStart_3420392 baseEnd_3420392 := by
    simpa [prefixWord, tailWord_3420392, baseEnd_3420392] using wordTrace_append hprefix tailTrace_3420392
  have hstable : (prefixWord ++ tailWord_3420392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420392).length < 2 ^ (prefixWord ++ tailWord_3420392).sum := by decide
  have hdescent : baseEnd_3420392 < baseStart_3420392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420456 : List Nat := [2, 1, 5, 1, 3, 1, 2, 2, 2, 3]
def baseStart_3420456 : Nat := 118140960795 + 3420456 * 2 ^ 59
def prefixEnd_3420456 : Nat := 4983230072969 + 3 ^ 40 * 3420456 * 2
def baseEnd_3420456 : Nat := 1170891990370116455913077

theorem tailTrace_3420456 : CollatzResearch.WordTrace tailWord_3420456 prefixEnd_3420456 1170891990370116455913077 := by
  unfold tailWord_3420456
  simp only [CollatzResearch.WordTrace]
  refine ⟨62377139648139777110984611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83169519530853036147979481 62377139648139777110984611)
  ·
    refine ⟨93565709472209665666476917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62377139648139777110984611 93565709472209665666476917)
    ·
      refine ⟨8771785263019656156232211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 93565709472209665666476917 8771785263019656156232211)
      ·
        refine ⟨13157677894529484234348317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8771785263019656156232211 13157677894529484234348317)
        ·
          refine ⟨4934129210448556587880619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13157677894529484234348317 4934129210448556587880619)
          ·
            refine ⟨7401193815672834881820929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4934129210448556587880619 7401193815672834881820929)
            ·
              refine ⟨5550895361754626161365697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7401193815672834881820929 5550895361754626161365697)
              ·
                refine ⟨4163171521315969621024273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5550895361754626161365697 4163171521315969621024273)
                ·
                  refine ⟨3122378640986977215768205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4163171521315969621024273 3122378640986977215768205)
                  ·
                    refine ⟨1170891990370116455913077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3122378640986977215768205 1170891990370116455913077)
                    ·
                      rfl

theorem cell22_3420456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_3420456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3420456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3420456 prefixEnd_3420456 := by exact prefixLift 3420456
  have htrace : WordTrace (prefixWord ++ tailWord_3420456) baseStart_3420456 baseEnd_3420456 := by
    simpa [prefixWord, tailWord_3420456, baseEnd_3420456] using wordTrace_append hprefix tailTrace_3420456
  have hstable : (prefixWord ++ tailWord_3420456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420456).length < 2 ^ (prefixWord ++ tailWord_3420456).sum := by decide
  have hdescent : baseEnd_3420456 < baseStart_3420456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420458 : List Nat := [3, 1, 4, 2, 2, 2, 2, 2, 4]
def baseStart_3420458 : Nat := 118140960795 + 3420458 * 2 ^ 59
def prefixEnd_3420458 : Nat := 4983230072969 + 3 ^ 40 * 3420458 * 2
def baseEnd_3420458 : Nat := 390297558336996372454357

theorem tailTrace_3420458 : CollatzResearch.WordTrace tailWord_3420458 prefixEnd_3420458 390297558336996372454357 := by
  unfold tailWord_3420458
  simp only [CollatzResearch.WordTrace]
  refine ⟨31188588060568077140885507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83169568161514872375694685 31188588060568077140885507)
  ·
    refine ⟨46782882090852115711328261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31188588060568077140885507 46782882090852115711328261)
    ·
      refine ⟨8771790392034771695874049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46782882090852115711328261 8771790392034771695874049)
      ·
        refine ⟨6578842794026078771905537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8771790392034771695874049 6578842794026078771905537)
        ·
          refine ⟨4934132095519559078929153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6578842794026078771905537 4934132095519559078929153)
          ·
            refine ⟨3700599071639669309196865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4934132095519559078929153 3700599071639669309196865)
            ·
              refine ⟨2775449303729751981897649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3700599071639669309196865 2775449303729751981897649)
              ·
                refine ⟨2081586977797313986423237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2775449303729751981897649 2081586977797313986423237)
                ·
                  refine ⟨390297558336996372454357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2081586977797313986423237 390297558336996372454357)
                  ·
                    rfl

theorem cell22_3420458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 2, 2, 4].length) (baseStart_3420458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3420458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3420458 prefixEnd_3420458 := by exact prefixLift 3420458
  have htrace : WordTrace (prefixWord ++ tailWord_3420458) baseStart_3420458 baseEnd_3420458 := by
    simpa [prefixWord, tailWord_3420458, baseEnd_3420458] using wordTrace_append hprefix tailTrace_3420458
  have hstable : (prefixWord ++ tailWord_3420458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420458).length < 2 ^ (prefixWord ++ tailWord_3420458).sum := by decide
  have hdescent : baseEnd_3420458 < baseStart_3420458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420467 : List Nat := [1, 1, 1, 2, 5, 1, 2, 3, 3, 3]
def baseStart_3420467 : Nat := 118140960795 + 3420467 * 2 ^ 59
def prefixEnd_3420467 : Nat := 4983230072969 + 3 ^ 40 * 3420467 * 2
def baseEnd_3420467 : Nat := 1170895755894916093888043

theorem tailTrace_3420467 : CollatzResearch.WordTrace tailWord_3420467 prefixEnd_3420467 1170895755894916093888043 := by
  unfold tailWord_3420467
  simp only [CollatzResearch.WordTrace]
  refine ⟨124754680499239703100619655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83169786999493135400413103 124754680499239703100619655)
  ·
    refine ⟨187132020748859554650929483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124754680499239703100619655 187132020748859554650929483)
    ·
      refine ⟨280698031123289331976394225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187132020748859554650929483 280698031123289331976394225)
      ·
        refine ⟨210523523342466998982295669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280698031123289331976394225 210523523342466998982295669)
        ·
          refine ⟨19736580313356281154590219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 210523523342466998982295669 19736580313356281154590219)
          ·
            refine ⟨29604870470034421731885329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19736580313356281154590219 29604870470034421731885329)
            ·
              refine ⟨22203652852525816298913997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29604870470034421731885329 22203652852525816298913997)
              ·
                refine ⟨8326369819697181112092749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22203652852525816298913997 8326369819697181112092749)
                ·
                  refine ⟨3122388682386442917034781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8326369819697181112092749 3122388682386442917034781)
                  ·
                    refine ⟨1170895755894916093888043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3122388682386442917034781 1170895755894916093888043)
                    ·
                      rfl

theorem cell22_3420467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 3, 3, 3].length) (baseStart_3420467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3420467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3420467 prefixEnd_3420467 := by exact prefixLift 3420467
  have htrace : WordTrace (prefixWord ++ tailWord_3420467) baseStart_3420467 baseEnd_3420467 := by
    simpa [prefixWord, tailWord_3420467, baseEnd_3420467] using wordTrace_append hprefix tailTrace_3420467
  have hstable : (prefixWord ++ tailWord_3420467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420467).length < 2 ^ (prefixWord ++ tailWord_3420467).sum := by decide
  have hdescent : baseEnd_3420467 < baseStart_3420467 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420514 : List Nat := [3, 3, 2, 1, 1, 2, 3, 2, 5]
def baseStart_3420514 : Nat := 118140960795 + 3420514 * 2 ^ 59
def prefixEnd_3420514 : Nat := 4983230072969 + 3 ^ 40 * 3420514 * 2
def baseEnd_3420514 : Nat := 390303948318474545987633

theorem tailTrace_3420514 : CollatzResearch.WordTrace tailWord_3420514 prefixEnd_3420514 390303948318474545987633 := by
  unfold tailWord_3420514
  simp only [CollatzResearch.WordTrace]
  refine ⟨31189098682517357531895149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83170929820046286751720397 31189098682517357531895149)
  ·
    refine ⟨11695912005944009074460681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31189098682517357531895149 11695912005944009074460681)
    ·
      refine ⟨8771934004458006805845511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11695912005944009074460681 8771934004458006805845511)
      ·
        refine ⟨13157901006687010208768267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8771934004458006805845511 13157901006687010208768267)
        ·
          refine ⟨19736851510030515313152401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13157901006687010208768267 19736851510030515313152401)
          ·
            refine ⟨14802638632522886484864301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19736851510030515313152401 14802638632522886484864301)
            ·
              refine ⟨5550989487196082431824113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14802638632522886484864301 5550989487196082431824113)
              ·
                refine ⟨4163242115397061823868085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5550989487196082431824113 4163242115397061823868085)
                ·
                  refine ⟨390303948318474545987633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4163242115397061823868085 390303948318474545987633)
                  ·
                    rfl

theorem cell22_3420514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_3420514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3420514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3420514 prefixEnd_3420514 := by exact prefixLift 3420514
  have htrace : WordTrace (prefixWord ++ tailWord_3420514) baseStart_3420514 baseEnd_3420514 := by
    simpa [prefixWord, tailWord_3420514, baseEnd_3420514] using wordTrace_append hprefix tailTrace_3420514
  have hstable : (prefixWord ++ tailWord_3420514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420514).length < 2 ^ (prefixWord ++ tailWord_3420514).sum := by decide
  have hdescent : baseEnd_3420514 < baseStart_3420514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420576 : List Nat := [2, 1, 1, 4, 1, 4, 3, 2, 4]
def baseStart_3420576 : Nat := 118140960795 + 3420576 * 2 ^ 59
def prefixEnd_3420576 : Nat := 4983230072969 + 3 ^ 40 * 3420576 * 2
def baseEnd_3420576 : Nat := 390311022940825380970903

theorem tailTrace_3420576 : CollatzResearch.WordTrace tailWord_3420576 prefixEnd_3420576 390311022940825380970903 := by
  unfold tailWord_3420576
  simp only [CollatzResearch.WordTrace]
  refine ⟨62379328027922407358168791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83172437370563209810891721 62379328027922407358168791)
  ·
    refine ⟨93568992041883611037253187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62379328027922407358168791 93568992041883611037253187)
    ·
      refine ⟨140353488062825416555879781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93568992041883611037253187 140353488062825416555879781)
      ·
        refine ⟨26316279011779765604227459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140353488062825416555879781 26316279011779765604227459)
        ·
          refine ⟨39474418517669648406341189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26316279011779765604227459 39474418517669648406341189)
          ·
            refine ⟨7401453472063059076188973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39474418517669648406341189 7401453472063059076188973)
            ·
              refine ⟨2775545052023647153570865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7401453472063059076188973 2775545052023647153570865)
              ·
                refine ⟨2081658789017735365178149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2775545052023647153570865 2081658789017735365178149)
                ·
                  refine ⟨390311022940825380970903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2081658789017735365178149 390311022940825380970903)
                  ·
                    rfl

theorem cell22_3420576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 3, 2, 4].length) (baseStart_3420576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3420576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3420576 prefixEnd_3420576 := by exact prefixLift 3420576
  have htrace : WordTrace (prefixWord ++ tailWord_3420576) baseStart_3420576 baseEnd_3420576 := by
    simpa [prefixWord, tailWord_3420576, baseEnd_3420576] using wordTrace_append hprefix tailTrace_3420576
  have hstable : (prefixWord ++ tailWord_3420576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420576).length < 2 ^ (prefixWord ++ tailWord_3420576).sum := by decide
  have hdescent : baseEnd_3420576 < baseStart_3420576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420709 : List Nat := [1, 3, 1, 2, 2, 1, 5, 1, 1, 5]
def baseStart_3420709 : Nat := 118140960795 + 3420709 * 2 ^ 59
def prefixEnd_3420709 : Nat := 4983230072969 + 3 ^ 40 * 3420709 * 2
def baseEnd_3420709 : Nat := 1170978597440508129337301

theorem tailTrace_3420709 : CollatzResearch.WordTrace tailWord_3420709 prefixEnd_3420709 1170978597440508129337301 := by
  unfold tailWord_3420709
  simp only [CollatzResearch.WordTrace]
  refine ⟨124763506964362978430929181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83175671309575318953952787 124763506964362978430929181)
  ·
    refine ⟨46786315111636116911598443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124763506964362978430929181 46786315111636116911598443)
    ·
      refine ⟨70179472667454175367397665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46786315111636116911598443 70179472667454175367397665)
      ·
        refine ⟨52634604500590631525548249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70179472667454175367397665 52634604500590631525548249)
        ·
          refine ⟨39475953375442973644161187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52634604500590631525548249 39475953375442973644161187)
          ·
            refine ⟨59213930063164460466241781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39475953375442973644161187 59213930063164460466241781)
            ·
              refine ⟨5551305943421668168710167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59213930063164460466241781 5551305943421668168710167)
              ·
                refine ⟨8326958915132502253065251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5551305943421668168710167 8326958915132502253065251)
                ·
                  refine ⟨12490438372698753379597877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8326958915132502253065251 12490438372698753379597877)
                  ·
                    refine ⟨1170978597440508129337301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12490438372698753379597877 1170978597440508129337301)
                    ·
                      rfl

theorem cell22_3420709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 1, 1, 5].length) (baseStart_3420709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3420709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3420709 prefixEnd_3420709 := by exact prefixLift 3420709
  have htrace : WordTrace (prefixWord ++ tailWord_3420709) baseStart_3420709 baseEnd_3420709 := by
    simpa [prefixWord, tailWord_3420709, baseEnd_3420709] using wordTrace_append hprefix tailTrace_3420709
  have hstable : (prefixWord ++ tailWord_3420709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420709).length < 2 ^ (prefixWord ++ tailWord_3420709).sum := by decide
  have hdescent : baseEnd_3420709 < baseStart_3420709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420801 : List Nat := [1, 2, 4, 2, 1, 1, 4, 2, 5]
def baseStart_3420801 : Nat := 118140960795 + 3420801 * 2 ^ 59
def prefixEnd_3420801 : Nat := 4983230072969 + 3 ^ 40 * 3420801 * 2
def baseEnd_3420801 : Nat := 390336696973550185345673

theorem tailTrace_3420801 : CollatzResearch.WordTrace tailWord_3420801 prefixEnd_3420801 390336696973550185345673 := by
  unfold tailWord_3420801
  simp only [CollatzResearch.WordTrace]
  refine ⟨124766862480029678143278257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83177908320019785428852171 124766862480029678143278257)
  ·
    refine ⟨93575146860022258607458693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124766862480029678143278257 93575146860022258607458693)
    ·
      refine ⟨17545340036254173488898505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93575146860022258607458693 17545340036254173488898505)
      ·
        refine ⟨13159005027190630116673879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17545340036254173488898505 13159005027190630116673879)
        ·
          refine ⟨19738507540785945175010819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13159005027190630116673879 19738507540785945175010819)
          ·
            refine ⟨29607761311178917762516229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19738507540785945175010819 29607761311178917762516229)
            ·
              refine ⟨5551455245846047080471793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29607761311178917762516229 5551455245846047080471793)
              ·
                refine ⟨4163591434384535310353845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5551455245846047080471793 4163591434384535310353845)
                ·
                  refine ⟨390336696973550185345673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4163591434384535310353845 390336696973550185345673)
                  ·
                    rfl

theorem cell22_3420801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 2, 5].length) (baseStart_3420801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3420801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3420801 prefixEnd_3420801 := by exact prefixLift 3420801
  have htrace : WordTrace (prefixWord ++ tailWord_3420801) baseStart_3420801 baseEnd_3420801 := by
    simpa [prefixWord, tailWord_3420801, baseEnd_3420801] using wordTrace_append hprefix tailTrace_3420801
  have hstable : (prefixWord ++ tailWord_3420801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420801).length < 2 ^ (prefixWord ++ tailWord_3420801).sum := by decide
  have hdescent : baseEnd_3420801 < baseStart_3420801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420805 : List Nat := [1, 3, 1, 1, 4, 2, 4, 2, 1, 3]
def baseStart_3420805 : Nat := 118140960795 + 3420805 * 2 ^ 59
def prefixEnd_3420805 : Nat := 4983230072969 + 3 ^ 40 * 3420805 * 2
def baseEnd_3420805 : Nat := 1171011460202395878937007

theorem tailTrace_3420805 : CollatzResearch.WordTrace tailWord_3420805 prefixEnd_3420805 1171011460202395878937007 := by
  unfold tailWord_3420805
  simp only [CollatzResearch.WordTrace]
  refine ⟨124767008372015186826423869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83178005581343457884282579 124767008372015186826423869)
  ·
    refine ⟨46787628139505695059908951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124767008372015186826423869 46787628139505695059908951)
    ·
      refine ⟨70181442209258542589863427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46787628139505695059908951 70181442209258542589863427)
      ·
        refine ⟨105272163313887813884795141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70181442209258542589863427 105272163313887813884795141)
        ·
          refine ⟨19738530621353965103399089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105272163313887813884795141 19738530621353965103399089)
          ·
            refine ⟨14803897966015473827549317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19738530621353965103399089 14803897966015473827549317)
            ·
              refine ⟨2775730868627901342665497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14803897966015473827549317 2775730868627901342665497)
              ·
                refine ⟨2081798151470926006999123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2775730868627901342665497 2081798151470926006999123)
                ·
                  refine ⟨3122697227206389010498685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2081798151470926006999123 3122697227206389010498685)
                  ·
                    refine ⟨1171011460202395878937007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3122697227206389010498685 1171011460202395878937007)
                    ·
                      rfl

theorem cell22_3420805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 4, 2, 1, 3].length) (baseStart_3420805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3420805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3420805 prefixEnd_3420805 := by exact prefixLift 3420805
  have htrace : WordTrace (prefixWord ++ tailWord_3420805) baseStart_3420805 baseEnd_3420805 := by
    simpa [prefixWord, tailWord_3420805, baseEnd_3420805] using wordTrace_append hprefix tailTrace_3420805
  have hstable : (prefixWord ++ tailWord_3420805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420805).length < 2 ^ (prefixWord ++ tailWord_3420805).sum := by decide
  have hdescent : baseEnd_3420805 < baseStart_3420805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420829 : List Nat := [1, 4, 2, 1, 1, 1, 3, 1, 8]
def baseStart_3420829 : Nat := 118140960795 + 3420829 * 2 ^ 59
def prefixEnd_3420829 : Nat := 4983230072969 + 3 ^ 40 * 3420829 * 2
def baseEnd_3420829 : Nat := 390339891964289272112311

theorem tailTrace_3420829 : CollatzResearch.WordTrace tailWord_3420829 prefixEnd_3420829 390339891964289272112311 := by
  unfold tailWord_3420829
  simp only [CollatzResearch.WordTrace]
  refine ⟨124767883723928238925297541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83178589149285492616865027 124767883723928238925297541)
  ·
    refine ⟨23393978198236544798493289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124767883723928238925297541 23393978198236544798493289)
    ·
      refine ⟨17545483648677408598869967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23393978198236544798493289 17545483648677408598869967)
      ·
        refine ⟨26318225473016112898304951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17545483648677408598869967 26318225473016112898304951)
        ·
          refine ⟨39477338209524169347457427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26318225473016112898304951 39477338209524169347457427)
          ·
            refine ⟨59216007314286254021186141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39477338209524169347457427 59216007314286254021186141)
            ·
              refine ⟨22206002742857345257944803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59216007314286254021186141 22206002742857345257944803)
              ·
                refine ⟨33309004114286017886917205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22206002742857345257944803 33309004114286017886917205)
                ·
                  refine ⟨390339891964289272112311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33309004114286017886917205 390339891964289272112311)
                  ·
                    rfl

theorem cell22_3420829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 8].length) (baseStart_3420829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3420829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3420829 prefixEnd_3420829 := by exact prefixLift 3420829
  have htrace : WordTrace (prefixWord ++ tailWord_3420829) baseStart_3420829 baseEnd_3420829 := by
    simpa [prefixWord, tailWord_3420829, baseEnd_3420829] using wordTrace_append hprefix tailTrace_3420829
  have hstable : (prefixWord ++ tailWord_3420829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420829).length < 2 ^ (prefixWord ++ tailWord_3420829).sum := by decide
  have hdescent : baseEnd_3420829 < baseStart_3420829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420876 : List Nat := [2, 2, 1, 5, 1, 1, 1, 2, 1, 6]
def baseStart_3420876 : Nat := 118140960795 + 3420876 * 2 ^ 59
def prefixEnd_3420876 : Nat := 4983230072969 + 3 ^ 40 * 3420876 * 2
def baseEnd_3420876 : Nat := 1171035764953375360411789

theorem tailTrace_3420876 : CollatzResearch.WordTrace tailWord_3420876 prefixEnd_3420876 1171035764953375360411789 := by
  unfold tailWord_3420876
  simp only [CollatzResearch.WordTrace]
  refine ⟨62384798977378982976129241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83179731969838643968172321 62384798977378982976129241)
  ·
    refine ⟨46788599233034237232096931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62384798977378982976129241 46788599233034237232096931)
    ·
      refine ⟨70182898849551355848145397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46788599233034237232096931 70182898849551355848145397)
      ·
        refine ⟨6579646767145439610763631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70182898849551355848145397 6579646767145439610763631)
        ·
          refine ⟨9869470150718159416145447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6579646767145439610763631 9869470150718159416145447)
          ·
            refine ⟨14804205226077239124218171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9869470150718159416145447 14804205226077239124218171)
            ·
              refine ⟨22206307839115858686327257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14804205226077239124218171 22206307839115858686327257)
              ·
                refine ⟨16654730879336894014745443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22206307839115858686327257 16654730879336894014745443)
                ·
                  refine ⟨24982096319005341022118165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16654730879336894014745443 24982096319005341022118165)
                  ·
                    refine ⟨1171035764953375360411789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24982096319005341022118165 1171035764953375360411789)
                    ·
                      rfl

theorem cell22_3420876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 1, 6].length) (baseStart_3420876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3420876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3420876 prefixEnd_3420876 := by exact prefixLift 3420876
  have htrace : WordTrace (prefixWord ++ tailWord_3420876) baseStart_3420876 baseEnd_3420876 := by
    simpa [prefixWord, tailWord_3420876, baseEnd_3420876] using wordTrace_append hprefix tailTrace_3420876
  have hstable : (prefixWord ++ tailWord_3420876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420876).length < 2 ^ (prefixWord ++ tailWord_3420876).sum := by decide
  have hdescent : baseEnd_3420876 < baseStart_3420876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420878 : List Nat := [4, 1, 1, 1, 3, 4, 1, 1, 1, 5]
def baseStart_3420878 : Nat := 118140960795 + 3420878 * 2 ^ 59
def prefixEnd_3420878 : Nat := 4983230072969 + 3 ^ 40 * 3420878 * 2
def baseEnd_3420878 : Nat := 1171036449594248021861783

theorem tailTrace_3420878 : CollatzResearch.WordTrace tailWord_3420878 prefixEnd_3420878 1171036449594248021861783 := by
  unfold tailWord_3420878
  simp only [CollatzResearch.WordTrace]
  refine ⟨15596208862593840036728911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83179780600500480195887525 15596208862593840036728911)
  ·
    refine ⟨23394313293890760055093367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15596208862593840036728911 23394313293890760055093367)
    ·
      refine ⟨35091469940836140082640051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23394313293890760055093367 35091469940836140082640051)
      ·
        refine ⟨52637204911254210123960077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35091469940836140082640051 52637204911254210123960077)
        ·
          refine ⟨19738951841720328796485029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52637204911254210123960077 19738951841720328796485029)
          ·
            refine ⟨3701053470322561649340943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19738951841720328796485029 3701053470322561649340943)
            ·
              refine ⟨5551580205483842474011415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3701053470322561649340943 5551580205483842474011415)
              ·
                refine ⟨8327370308225763711017123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5551580205483842474011415 8327370308225763711017123)
                ·
                  refine ⟨12491055462338645566525685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8327370308225763711017123 12491055462338645566525685)
                  ·
                    refine ⟨1171036449594248021861783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12491055462338645566525685 1171036449594248021861783)
                    ·
                      rfl

theorem cell22_3420878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 1, 1, 5].length) (baseStart_3420878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3420878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3420878 prefixEnd_3420878 := by exact prefixLift 3420878
  have htrace : WordTrace (prefixWord ++ tailWord_3420878) baseStart_3420878 baseEnd_3420878 := by
    simpa [prefixWord, tailWord_3420878, baseEnd_3420878] using wordTrace_append hprefix tailTrace_3420878
  have hstable : (prefixWord ++ tailWord_3420878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420878).length < 2 ^ (prefixWord ++ tailWord_3420878).sum := by decide
  have hdescent : baseEnd_3420878 < baseStart_3420878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420889 : List Nat := [1, 2, 1, 2, 3, 2, 1, 1, 2, 7]
def baseStart_3420889 : Nat := 118140960795 + 3420889 * 2 ^ 59
def prefixEnd_3420889 : Nat := 4983230072969 + 3 ^ 40 * 3420889 * 2
def baseEnd_3420889 : Nat := 1171040215119047659836749

theorem tailTrace_3420889 : CollatzResearch.WordTrace tailWord_3420889 prefixEnd_3420889 1171040215119047659836749 := by
  unfold tailWord_3420889
  simp only [CollatzResearch.WordTrace]
  refine ⟨124770072103710869172481721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83180048069140579448321147 124770072103710869172481721)
  ·
    refine ⟨93577554077783151879361291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124770072103710869172481721 93577554077783151879361291)
    ·
      refine ⟨140366331116674727819041937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93577554077783151879361291 140366331116674727819041937)
      ·
        refine ⟨105274748337506045864281453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140366331116674727819041937 105274748337506045864281453)
        ·
          refine ⟨39478030626564767199105545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105274748337506045864281453 39478030626564767199105545)
          ·
            refine ⟨29608522969923575399329159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39478030626564767199105545 29608522969923575399329159)
            ·
              refine ⟨44412784454885363098993739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29608522969923575399329159 44412784454885363098993739)
              ·
                refine ⟨66619176682328044648490609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44412784454885363098993739 66619176682328044648490609)
                ·
                  refine ⟨49964382511746033486367957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66619176682328044648490609 49964382511746033486367957)
                  ·
                    refine ⟨1171040215119047659836749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49964382511746033486367957 1171040215119047659836749)
                    ·
                      rfl

theorem cell22_3420889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 7].length) (baseStart_3420889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3420889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3420889 prefixEnd_3420889 := by exact prefixLift 3420889
  have htrace : WordTrace (prefixWord ++ tailWord_3420889) baseStart_3420889 baseEnd_3420889 := by
    simpa [prefixWord, tailWord_3420889, baseEnd_3420889] using wordTrace_append hprefix tailTrace_3420889
  have hstable : (prefixWord ++ tailWord_3420889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420889).length < 2 ^ (prefixWord ++ tailWord_3420889).sum := by decide
  have hdescent : baseEnd_3420889 < baseStart_3420889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420974 : List Nat := [4, 1, 3, 2, 1, 1, 4, 2, 1, 3]
def baseStart_3420974 : Nat := 118140960795 + 3420974 * 2 ^ 59
def prefixEnd_3420974 : Nat := 4983230072969 + 3 ^ 40 * 3420974 * 2
def baseEnd_3420974 : Nat := 1171069312356135771461489

theorem tailTrace_3420974 : CollatzResearch.WordTrace tailWord_3420974 prefixEnd_3420974 1171069312356135771461489 := by
  unfold tailWord_3420974
  simp only [CollatzResearch.WordTrace]
  refine ⟨15596646538550366086165747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83182114872268619126217317 15596646538550366086165747)
  ·
    refine ⟨23394969807825549129248621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15596646538550366086165747 23394969807825549129248621)
    ·
      refine ⟨8773113677934580923468233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23394969807825549129248621 8773113677934580923468233)
      ·
        refine ⟨6579835258450935692601175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8773113677934580923468233 6579835258450935692601175)
        ·
          refine ⟨9869752887676403538901763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6579835258450935692601175 9869752887676403538901763)
          ·
            refine ⟨14804629331514605308352645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9869752887676403538901763 14804629331514605308352645)
            ·
              refine ⟨2775867999658988495316121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14804629331514605308352645 2775867999658988495316121)
              ·
                refine ⟨2081900999744241371487091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2775867999658988495316121 2081900999744241371487091)
                ·
                  refine ⟨3122851499616362057230637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2081900999744241371487091 3122851499616362057230637)
                  ·
                    refine ⟨1171069312356135771461489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3122851499616362057230637 1171069312356135771461489)
                    ·
                      rfl

theorem cell22_3420974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_3420974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3420974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3420974 prefixEnd_3420974 := by exact prefixLift 3420974
  have htrace : WordTrace (prefixWord ++ tailWord_3420974) baseStart_3420974 baseEnd_3420974 := by
    simpa [prefixWord, tailWord_3420974, baseEnd_3420974] using wordTrace_append hprefix tailTrace_3420974
  have hstable : (prefixWord ++ tailWord_3420974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420974).length < 2 ^ (prefixWord ++ tailWord_3420974).sum := by decide
  have hdescent : baseEnd_3420974 < baseStart_3420974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421013 : List Nat := [1, 3, 2, 2, 2, 1, 2, 2, 4, 3]
def baseStart_3421013 : Nat := 118140960795 + 3421013 * 2 ^ 59
def prefixEnd_3421013 : Nat := 4983230072969 + 3 ^ 40 * 3421013 * 2
def baseEnd_3421013 : Nat := 1171082662853152669736369

theorem tailTrace_3421013 : CollatzResearch.WordTrace tailWord_3421013 prefixEnd_3421013 1171082662853152669736369 := by
  unfold tailWord_3421013
  simp only [CollatzResearch.WordTrace]
  refine ⟨124774594755261638349995693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83183063170174425566663795 124774594755261638349995693)
  ·
    refine ⟨46790473033223114381248385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124774594755261638349995693 46790473033223114381248385)
    ·
      refine ⟨35092854774917335785936289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46790473033223114381248385 35092854774917335785936289)
      ·
        refine ⟨26319641081188001839452217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35092854774917335785936289 26319641081188001839452217)
        ·
          refine ⟨19739730810891001379589163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26319641081188001839452217 19739730810891001379589163)
          ·
            refine ⟨29609596216336502069383745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19739730810891001379589163 29609596216336502069383745)
            ·
              refine ⟨22207197162252376552037809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29609596216336502069383745 22207197162252376552037809)
              ·
                refine ⟨16655397871689282414028357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22207197162252376552037809 16655397871689282414028357)
                ·
                  refine ⟨3122887100941740452630317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16655397871689282414028357 3122887100941740452630317)
                  ·
                    refine ⟨1171082662853152669736369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3122887100941740452630317 1171082662853152669736369)
                    ·
                      rfl

theorem cell22_3421013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 4, 3].length) (baseStart_3421013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3421013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3421013 prefixEnd_3421013 := by exact prefixLift 3421013
  have htrace : WordTrace (prefixWord ++ tailWord_3421013) baseStart_3421013 baseEnd_3421013 := by
    simpa [prefixWord, tailWord_3421013, baseEnd_3421013] using wordTrace_append hprefix tailTrace_3421013
  have hstable : (prefixWord ++ tailWord_3421013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421013).length < 2 ^ (prefixWord ++ tailWord_3421013).sum := by decide
  have hdescent : baseEnd_3421013 < baseStart_3421013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421015 : List Nat := [1, 1, 3, 2, 4, 2, 2, 3, 4]
def baseStart_3421015 : Nat := 118140960795 + 3421015 * 2 ^ 59
def prefixEnd_3421015 : Nat := 4983230072969 + 3 ^ 40 * 3421015 * 2
def baseEnd_3421015 : Nat := 390361115831341777062121

theorem tailTrace_3421015 : CollatzResearch.WordTrace tailWord_3421015 prefixEnd_3421015 390361115831341777062121 := by
  unfold tailWord_3421015
  simp only [CollatzResearch.WordTrace]
  refine ⟨124774667701254392691568499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83183111800836261794378999 124774667701254392691568499)
  ·
    refine ⟨187162001551881589037352749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124774667701254392691568499 187162001551881589037352749)
    ·
      refine ⟨70185750581955595889007281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187162001551881589037352749 70185750581955595889007281)
      ·
        refine ⟨52639312936466696916755461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70185750581955595889007281 52639312936466696916755461)
        ·
          refine ⟨9869871175587505671891649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52639312936466696916755461 9869871175587505671891649)
          ·
            refine ⟨7402403381690629253918737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9869871175587505671891649 7402403381690629253918737)
            ·
              refine ⟨5551802536267971940439053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7402403381690629253918737 5551802536267971940439053)
              ·
                refine ⟨2081925951100489477664645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5551802536267971940439053 2081925951100489477664645)
                ·
                  refine ⟨390361115831341777062121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2081925951100489477664645 390361115831341777062121)
                  ·
                    rfl

theorem cell22_3421015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 3, 4].length) (baseStart_3421015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3421015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3421015 prefixEnd_3421015 := by exact prefixLift 3421015
  have htrace : WordTrace (prefixWord ++ tailWord_3421015) baseStart_3421015 baseEnd_3421015 := by
    simpa [prefixWord, tailWord_3421015, baseEnd_3421015] using wordTrace_append hprefix tailTrace_3421015
  have hstable : (prefixWord ++ tailWord_3421015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421015).length < 2 ^ (prefixWord ++ tailWord_3421015).sum := by decide
  have hdescent : baseEnd_3421015 < baseStart_3421015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421075 : List Nat := [1, 1, 1, 2, 1, 2, 1, 9, 1, 3]
def baseStart_3421075 : Nat := 118140960795 + 3421075 * 2 ^ 59
def prefixEnd_3421075 : Nat := 4983230072969 + 3 ^ 40 * 3421075 * 2
def baseEnd_3421075 : Nat := 1171103886720205174686179

theorem tailTrace_3421075 : CollatzResearch.WordTrace tailWord_3421075 prefixEnd_3421075 1171103886720205174686179 := by
  unfold tailWord_3421075
  simp only [CollatzResearch.WordTrace]
  refine ⟨124776856081037022938752679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83184570720691348625835119 124776856081037022938752679)
  ·
    refine ⟨187165284121555534408129019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124776856081037022938752679 187165284121555534408129019)
    ·
      refine ⟨280747926182333301612193529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187165284121555534408129019 280747926182333301612193529)
      ·
        refine ⟨210560944636749976209145147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280747926182333301612193529 210560944636749976209145147)
        ·
          refine ⟨315841416955124964313717721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210560944636749976209145147 315841416955124964313717721)
          ·
            refine ⟨236881062716343723235288291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 315841416955124964313717721 236881062716343723235288291)
            ·
              refine ⟨355321594074515584852932437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236881062716343723235288291 355321594074515584852932437)
              ·
                refine ⟨2081962465280364754997651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 355321594074515584852932437 2081962465280364754997651)
                ·
                  refine ⟨3122943697920547132496477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2081962465280364754997651 3122943697920547132496477)
                  ·
                    refine ⟨1171103886720205174686179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3122943697920547132496477 1171103886720205174686179)
                    ·
                      rfl

theorem cell22_3421075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 9, 1, 3].length) (baseStart_3421075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3421075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3421075 prefixEnd_3421075 := by exact prefixLift 3421075
  have htrace : WordTrace (prefixWord ++ tailWord_3421075) baseStart_3421075 baseEnd_3421075 := by
    simpa [prefixWord, tailWord_3421075, baseEnd_3421075] using wordTrace_append hprefix tailTrace_3421075
  have hstable : (prefixWord ++ tailWord_3421075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421075).length < 2 ^ (prefixWord ++ tailWord_3421075).sum := by decide
  have hdescent : baseEnd_3421075 < baseStart_3421075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421105 : List Nat := [1, 2, 2, 4, 3, 1, 1, 3, 5]
def baseStart_3421105 : Nat := 118140960795 + 3421105 * 2 ^ 59
def prefixEnd_3421105 : Nat := 4983230072969 + 3 ^ 40 * 3421105 * 2
def baseEnd_3421105 : Nat := 390371385444431698812029

theorem tailTrace_3421105 : CollatzResearch.WordTrace tailWord_3421105 prefixEnd_3421105 390371385444431698812029 := by
  unfold tailWord_3421105
  simp only [CollatzResearch.WordTrace]
  refine ⟨124777950270928338062344769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83185300180618892041563179 124777950270928338062344769)
  ·
    refine ⟨93583462703196253546758577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124777950270928338062344769 93583462703196253546758577)
    ·
      refine ⟨70187597027397190160068933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93583462703196253546758577 70187597027397190160068933)
      ·
        refine ⟨13160174442636973155012925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70187597027397190160068933 13160174442636973155012925)
        ·
          refine ⟨4935065415988864933129847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13160174442636973155012925 4935065415988864933129847)
          ·
            refine ⟨7402598123983297399694771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4935065415988864933129847 7402598123983297399694771)
            ·
              refine ⟨11103897185974946099542157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7402598123983297399694771 11103897185974946099542157)
              ·
                refine ⟨4163961444740604787328309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11103897185974946099542157 4163961444740604787328309)
                ·
                  refine ⟨390371385444431698812029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4163961444740604787328309 390371385444431698812029)
                  ·
                    rfl

theorem cell22_3421105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 3, 5].length) (baseStart_3421105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3421105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3421105 prefixEnd_3421105 := by exact prefixLift 3421105
  have htrace : WordTrace (prefixWord ++ tailWord_3421105) baseStart_3421105 baseEnd_3421105 := by
    simpa [prefixWord, tailWord_3421105, baseEnd_3421105] using wordTrace_append hprefix tailTrace_3421105
  have hstable : (prefixWord ++ tailWord_3421105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421105).length < 2 ^ (prefixWord ++ tailWord_3421105).sum := by decide
  have hdescent : baseEnd_3421105 < baseStart_3421105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421180 : List Nat := [2, 2, 2, 1, 2, 3, 3, 1, 2, 4]
def baseStart_3421180 : Nat := 118140960795 + 3421180 * 2 ^ 59
def prefixEnd_3421180 : Nat := 4983230072969 + 3 ^ 40 * 3421180 * 2
def baseEnd_3421180 : Nat := 1171139830366019900810857

theorem tailTrace_3421180 : CollatzResearch.WordTrace tailWord_3421180 prefixEnd_3421180 1171139830366019900810857 := by
  unfold tailWord_3421180
  simp only [CollatzResearch.WordTrace]
  refine ⟨62390342872828312935662497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83187123830437750580883329 62390342872828312935662497)
  ·
    refine ⟨46792757154621234701746873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62390342872828312935662497 46792757154621234701746873)
    ·
      refine ⟨35094567865965926026310155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46792757154621234701746873 35094567865965926026310155)
      ·
        refine ⟨52641851798948889039465233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35094567865965926026310155 52641851798948889039465233)
        ·
          refine ⟨39481388849211666779598925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52641851798948889039465233 39481388849211666779598925)
          ·
            refine ⟨14805520818454375042349597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39481388849211666779598925 14805520818454375042349597)
            ·
              refine ⟨5552070306920390640881099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14805520818454375042349597 5552070306920390640881099)
              ·
                refine ⟨8328105460380585961321649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5552070306920390640881099 8328105460380585961321649)
                ·
                  refine ⟨6246079095285439470991237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8328105460380585961321649 6246079095285439470991237)
                  ·
                    refine ⟨1171139830366019900810857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6246079095285439470991237 1171139830366019900810857)
                    ·
                      rfl

theorem cell22_3421180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 1, 2, 4].length) (baseStart_3421180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3421180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3421180 prefixEnd_3421180 := by exact prefixLift 3421180
  have htrace : WordTrace (prefixWord ++ tailWord_3421180) baseStart_3421180 baseEnd_3421180 := by
    simpa [prefixWord, tailWord_3421180, baseEnd_3421180] using wordTrace_append hprefix tailTrace_3421180
  have hstable : (prefixWord ++ tailWord_3421180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421180).length < 2 ^ (prefixWord ++ tailWord_3421180).sum := by decide
  have hdescent : baseEnd_3421180 < baseStart_3421180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421216 : List Nat := [2, 1, 1, 7, 1, 1, 3, 1, 2, 3]
def baseStart_3421216 : Nat := 118140960795 + 3421216 * 2 ^ 59
def prefixEnd_3421216 : Nat := 4983230072969 + 3 ^ 40 * 3421216 * 2
def baseEnd_3421216 : Nat := 1171152153901727806910747

theorem tailTrace_3421216 : CollatzResearch.WordTrace tailWord_3421216 prefixEnd_3421216 1171152153901727806910747 := by
  unfold tailWord_3421216
  simp only [CollatzResearch.WordTrace]
  refine ⟨62390999386763102009817751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83187999182350802679757001 62390999386763102009817751)
  ·
    refine ⟨93586499080144653014726627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62390999386763102009817751 93586499080144653014726627)
    ·
      refine ⟨140379748620216979522089941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93586499080144653014726627 140379748620216979522089941)
      ·
        refine ⟨3290150358286335457548983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 140379748620216979522089941 3290150358286335457548983)
        ·
          refine ⟨4935225537429503186323475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3290150358286335457548983 4935225537429503186323475)
          ·
            refine ⟨7402838306144254779485213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4935225537429503186323475 7402838306144254779485213)
            ·
              refine ⟨2776064364804095542306955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7402838306144254779485213 2776064364804095542306955)
              ·
                refine ⟨4164096547206143313460433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2776064364804095542306955 4164096547206143313460433)
                ·
                  refine ⟨3123072410404607485095325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4164096547206143313460433 3123072410404607485095325)
                  ·
                    refine ⟨1171152153901727806910747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3123072410404607485095325 1171152153901727806910747)
                    ·
                      rfl

theorem cell22_3421216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 3, 1, 2, 3].length) (baseStart_3421216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3421216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3421216 prefixEnd_3421216 := by exact prefixLift 3421216
  have htrace : WordTrace (prefixWord ++ tailWord_3421216) baseStart_3421216 baseEnd_3421216 := by
    simpa [prefixWord, tailWord_3421216, baseEnd_3421216] using wordTrace_append hprefix tailTrace_3421216
  have hstable : (prefixWord ++ tailWord_3421216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421216).length < 2 ^ (prefixWord ++ tailWord_3421216).sum := by decide
  have hdescent : baseEnd_3421216 < baseStart_3421216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421244 : List Nat := [2, 2, 2, 2, 2, 2, 3, 3, 1, 3]
def baseStart_3421244 : Nat := 118140960795 + 3421244 * 2 ^ 59
def prefixEnd_3421244 : Nat := 4983230072969 + 3 ^ 40 * 3421244 * 2
def baseEnd_3421244 : Nat := 1171161738873945067210661

theorem tailTrace_3421244 : CollatzResearch.WordTrace tailWord_3421244 prefixEnd_3421244 1171161738873945067210661 := by
  unfold tailWord_3421244
  simp only [CollatzResearch.WordTrace]
  refine ⟨62391510008712382400827393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83188680011616509867769857 62391510008712382400827393)
  ·
    refine ⟨46793632506534286800620545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62391510008712382400827393 46793632506534286800620545)
    ·
      refine ⟨35095224379900715100465409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46793632506534286800620545 35095224379900715100465409)
      ·
        refine ⟨26321418284925536325349057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35095224379900715100465409 26321418284925536325349057)
        ·
          refine ⟨19741063713694152244011793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26321418284925536325349057 19741063713694152244011793)
          ·
            refine ⟨14805797785270614183008845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19741063713694152244011793 14805797785270614183008845)
            ·
              refine ⟨5552174169476480318628317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14805797785270614183008845 5552174169476480318628317)
              ·
                refine ⟨2082065313553680119485619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5552174169476480318628317 2082065313553680119485619)
                ·
                  refine ⟨3123097970330520179228429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2082065313553680119485619 3123097970330520179228429)
                  ·
                    refine ⟨1171161738873945067210661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3123097970330520179228429 1171161738873945067210661)
                    ·
                      rfl

theorem cell22_3421244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 1, 3].length) (baseStart_3421244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3421244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3421244 prefixEnd_3421244 := by exact prefixLift 3421244
  have htrace : WordTrace (prefixWord ++ tailWord_3421244) baseStart_3421244 baseEnd_3421244 := by
    simpa [prefixWord, tailWord_3421244, baseEnd_3421244] using wordTrace_append hprefix tailTrace_3421244
  have hstable : (prefixWord ++ tailWord_3421244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421244).length < 2 ^ (prefixWord ++ tailWord_3421244).sum := by decide
  have hdescent : baseEnd_3421244 < baseStart_3421244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421287 : List Nat := [1, 1, 5, 1, 1, 3, 3, 2, 1, 4]
def baseStart_3421287 : Nat := 118140960795 + 3421287 * 2 ^ 59
def prefixEnd_3421287 : Nat := 4983230072969 + 3 ^ 40 * 3421287 * 2
def baseEnd_3421287 : Nat := 1171176458652707288385529

theorem tailTrace_3421287 : CollatzResearch.WordTrace tailWord_3421287 prefixEnd_3421287 1171176458652707288385529 := by
  unfold tailWord_3421287
  simp only [CollatzResearch.WordTrace]
  refine ⟨124784588356268983145470115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83189725570845988763646743 124784588356268983145470115)
  ·
    refine ⟨187176882534403474718205173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124784588356268983145470115 187176882534403474718205173)
    ·
      refine ⟨17547832737600325754831735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 187176882534403474718205173 17547832737600325754831735)
      ·
        refine ⟨26321749106400488632247603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17547832737600325754831735 26321749106400488632247603)
        ·
          refine ⟨39482623659600732948371405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26321749106400488632247603 39482623659600732948371405)
          ·
            refine ⟨14805983872350274855639277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39482623659600732948371405 14805983872350274855639277)
            ·
              refine ⟨5552243952131353070864729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14805983872350274855639277 5552243952131353070864729)
              ·
                refine ⟨4164182964098514803148547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5552243952131353070864729 4164182964098514803148547)
                ·
                  refine ⟨6246274446147772204722821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4164182964098514803148547 6246274446147772204722821)
                  ·
                    refine ⟨1171176458652707288385529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6246274446147772204722821 1171176458652707288385529)
                    ·
                      rfl

theorem cell22_3421287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_3421287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3421287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3421287 prefixEnd_3421287 := by exact prefixLift 3421287
  have htrace : WordTrace (prefixWord ++ tailWord_3421287) baseStart_3421287 baseEnd_3421287 := by
    simpa [prefixWord, tailWord_3421287, baseEnd_3421287] using wordTrace_append hprefix tailTrace_3421287
  have hstable : (prefixWord ++ tailWord_3421287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421287).length < 2 ^ (prefixWord ++ tailWord_3421287).sum := by decide
  have hdescent : baseEnd_3421287 < baseStart_3421287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421315 : List Nat := [1, 1, 1, 3, 3, 2, 1, 4, 2, 4]
def baseStart_3421315 : Nat := 118140960795 + 3421315 * 2 ^ 59
def prefixEnd_3421315 : Nat := 4983230072969 + 3 ^ 40 * 3421315 * 2
def baseEnd_3421315 : Nat := 1171186043624924548685443

theorem tailTrace_3421315 : CollatzResearch.WordTrace tailWord_3421315 prefixEnd_3421315 1171186043624924548685443 := by
  unfold tailWord_3421315
  simp only [CollatzResearch.WordTrace]
  refine ⟨124785609600167543927489399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83190406400111695951659599 124785609600167543927489399)
  ·
    refine ⟨187178414400251315891234099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124785609600167543927489399 187178414400251315891234099)
    ·
      refine ⟨280767621600376973836851149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187178414400251315891234099 280767621600376973836851149)
      ·
        refine ⟨105287858100141365188819181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 280767621600376973836851149 105287858100141365188819181)
        ·
          refine ⟨39482946787553011945807193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105287858100141365188819181 39482946787553011945807193)
          ·
            refine ⟨29612210090664758959355395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39482946787553011945807193 29612210090664758959355395)
            ·
              refine ⟨44418315135997138439033093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29612210090664758959355395 44418315135997138439033093)
              ·
                refine ⟨8328434087999463457318705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44418315135997138439033093 8328434087999463457318705)
                ·
                  refine ⟨6246325565999597592989029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8328434087999463457318705 6246325565999597592989029)
                  ·
                    refine ⟨1171186043624924548685443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6246325565999597592989029 1171186043624924548685443)
                    ·
                      rfl

theorem cell22_3421315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 4, 2, 4].length) (baseStart_3421315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3421315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3421315 prefixEnd_3421315 := by exact prefixLift 3421315
  have htrace : WordTrace (prefixWord ++ tailWord_3421315) baseStart_3421315 baseEnd_3421315 := by
    simpa [prefixWord, tailWord_3421315, baseEnd_3421315] using wordTrace_append hprefix tailTrace_3421315
  have hstable : (prefixWord ++ tailWord_3421315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421315).length < 2 ^ (prefixWord ++ tailWord_3421315).sum := by decide
  have hdescent : baseEnd_3421315 < baseStart_3421315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421398 : List Nat := [5, 2, 1, 2, 3, 1, 2, 6]
def baseStart_3421398 : Nat := 118140960795 + 3421398 * 2 ^ 59
def prefixEnd_3421398 : Nat := 4983230072969 + 3 ^ 40 * 3421398 * 2
def baseEnd_3421398 : Nat := 130134939580126666540021

theorem tailTrace_3421398 : CollatzResearch.WordTrace tailWord_3421398 prefixEnd_3421398 130134939580126666540021 := by
  unfold tailWord_3421398
  simp only [CollatzResearch.WordTrace]
  refine ⟨7799289803679178068922553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83192424572577899401840565 7799289803679178068922553)
  ·
    refine ⟨5849467352759383551691915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7799289803679178068922553 5849467352759383551691915)
    ·
      refine ⟨8774201029139075327537873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5849467352759383551691915 8774201029139075327537873)
      ·
        refine ⟨6580650771854306495653405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8774201029139075327537873 6580650771854306495653405)
        ·
          refine ⟨2467744039445364935870027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6580650771854306495653405 2467744039445364935870027)
          ·
            refine ⟨3701616059168047403805041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2467744039445364935870027 3701616059168047403805041)
            ·
              refine ⟨2776212044376035552853781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3701616059168047403805041 2776212044376035552853781)
              ·
                refine ⟨130134939580126666540021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2776212044376035552853781 130134939580126666540021)
                ·
                  rfl

theorem cell22_3421398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 2, 6].length) (baseStart_3421398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3421398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3421398 prefixEnd_3421398 := by exact prefixLift 3421398
  have htrace : WordTrace (prefixWord ++ tailWord_3421398) baseStart_3421398 baseEnd_3421398 := by
    simpa [prefixWord, tailWord_3421398, baseEnd_3421398] using wordTrace_append hprefix tailTrace_3421398
  have hstable : (prefixWord ++ tailWord_3421398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421398).length < 2 ^ (prefixWord ++ tailWord_3421398).sum := by decide
  have hdescent : baseEnd_3421398 < baseStart_3421398 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421413 : List Nat := [1, 3, 1, 4, 3, 2, 1, 3, 1, 3]
def baseStart_3421413 : Nat := 118140960795 + 3421413 * 2 ^ 59
def prefixEnd_3421413 : Nat := 4983230072969 + 3 ^ 40 * 3421413 * 2
def baseEnd_3421413 : Nat := 1171219591027684959735143

theorem tailTrace_3421413 : CollatzResearch.WordTrace tailWord_3421413 prefixEnd_3421413 1171219591027684959735143 := by
  unfold tailWord_3421413
  simp only [CollatzResearch.WordTrace]
  refine ⟨124789183953812506664556893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83192789302541671109704595 124789183953812506664556893)
  ·
    refine ⟨46795943982679689999208835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124789183953812506664556893 46795943982679689999208835)
    ·
      refine ⟨70193915974019534998813253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46795943982679689999208835 70193915974019534998813253)
      ·
        refine ⟨13161359245128662812277485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70193915974019534998813253 13161359245128662812277485)
        ·
          refine ⟨4935509716923248554604057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13161359245128662812277485 4935509716923248554604057)
          ·
            refine ⟨3701632287692436415953043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4935509716923248554604057 3701632287692436415953043)
            ·
              refine ⟨5552448431538654623929565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3701632287692436415953043 5552448431538654623929565)
              ·
                refine ⟨2082168161826995483973587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5552448431538654623929565 2082168161826995483973587)
                ·
                  refine ⟨3123252242740493225960381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2082168161826995483973587 3123252242740493225960381)
                  ·
                    refine ⟨1171219591027684959735143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3123252242740493225960381 1171219591027684959735143)
                    ·
                      rfl

theorem cell22_3421413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 3, 1, 3].length) (baseStart_3421413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3421413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3421413 prefixEnd_3421413 := by exact prefixLift 3421413
  have htrace : WordTrace (prefixWord ++ tailWord_3421413) baseStart_3421413 baseEnd_3421413 := by
    simpa [prefixWord, tailWord_3421413, baseEnd_3421413] using wordTrace_append hprefix tailTrace_3421413
  have hstable : (prefixWord ++ tailWord_3421413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421413).length < 2 ^ (prefixWord ++ tailWord_3421413).sum := by decide
  have hdescent : baseEnd_3421413 < baseStart_3421413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421469 : List Nat := [1, 4, 2, 3, 1, 2, 1, 2, 1, 5]
def baseStart_3421469 : Nat := 118140960795 + 3421469 * 2 ^ 59
def prefixEnd_3421469 : Nat := 4983230072969 + 3 ^ 40 * 3421469 * 2
def baseEnd_3421469 : Nat := 1171238760972119480334971

theorem tailTrace_3421469 : CollatzResearch.WordTrace tailWord_3421469 prefixEnd_3421469 1171238760972119480334971 := by
  unfold tailWord_3421469
  simp only [CollatzResearch.WordTrace]
  refine ⟨124791226441609628228595461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83194150961073085485730307 124791226441609628228595461)
  ·
    refine ⟨23398354957801805292861649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124791226441609628228595461 23398354957801805292861649)
    ·
      refine ⟨17548766218351353969646237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23398354957801805292861649 17548766218351353969646237)
      ·
        refine ⟨6580787331881757738617339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17548766218351353969646237 6580787331881757738617339)
        ·
          refine ⟨9871180997822636607926009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6580787331881757738617339 9871180997822636607926009)
          ·
            refine ⟨7403385748366977455944507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9871180997822636607926009 7403385748366977455944507)
            ·
              refine ⟨11105078622550466183916761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7403385748366977455944507 11105078622550466183916761)
              ·
                refine ⟨8328808966912849637937571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11105078622550466183916761 8328808966912849637937571)
                ·
                  refine ⟨12493213450369274456906357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8328808966912849637937571 12493213450369274456906357)
                  ·
                    refine ⟨1171238760972119480334971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12493213450369274456906357 1171238760972119480334971)
                    ·
                      rfl

theorem cell22_3421469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_3421469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3421469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3421469 prefixEnd_3421469 := by exact prefixLift 3421469
  have htrace : WordTrace (prefixWord ++ tailWord_3421469) baseStart_3421469 baseEnd_3421469 := by
    simpa [prefixWord, tailWord_3421469, baseEnd_3421469] using wordTrace_append hprefix tailTrace_3421469
  have hstable : (prefixWord ++ tailWord_3421469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421469).length < 2 ^ (prefixWord ++ tailWord_3421469).sum := by decide
  have hdescent : baseEnd_3421469 < baseStart_3421469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421482 : List Nat := [3, 1, 4, 2, 1, 11]
def baseStart_3421482 : Nat := 118140960795 + 3421482 * 2 ^ 59
def prefixEnd_3421482 : Nat := 4983230072969 + 3 ^ 40 * 3421482 * 2
def baseEnd_3421482 : Nat := 14459792730096194811851

theorem tailTrace_3421482 : CollatzResearch.WordTrace tailWord_3421482 prefixEnd_3421482 14459792730096194811851 := by
  unfold tailWord_3421482
  simp only [CollatzResearch.WordTrace]
  refine ⟨31197925147640632862204675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83194467060375020965879133 31197925147640632862204675)
  ·
    refine ⟨46796887721460949293307013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31197925147640632862204675 46796887721460949293307013)
    ·
      refine ⟨8774416447773927992495065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46796887721460949293307013 8774416447773927992495065)
      ·
        refine ⟨6580812335830445994371299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8774416447773927992495065 6580812335830445994371299)
        ·
          refine ⟨9871218503745668991556949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6580812335830445994371299 9871218503745668991556949)
          ·
            refine ⟨14459792730096194811851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9871218503745668991556949 14459792730096194811851)
            ·
              rfl

theorem cell22_3421482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 11].length) (baseStart_3421482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3421482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3421482 prefixEnd_3421482 := by exact prefixLift 3421482
  have htrace : WordTrace (prefixWord ++ tailWord_3421482) baseStart_3421482 baseEnd_3421482 := by
    simpa [prefixWord, tailWord_3421482, baseEnd_3421482] using wordTrace_append hprefix tailTrace_3421482
  have hstable : (prefixWord ++ tailWord_3421482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421482).length < 2 ^ (prefixWord ++ tailWord_3421482).sum := by decide
  have hdescent : baseEnd_3421482 < baseStart_3421482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421544 : List Nat := [2, 1, 4, 2, 3, 1, 1, 1, 7]
def baseStart_3421544 : Nat := 118140960795 + 3421544 * 2 ^ 59
def prefixEnd_3421544 : Nat := 4983230072969 + 3 ^ 40 * 3421544 * 2
def baseEnd_3421544 : Nat := 390421478334948094903247

theorem tailTrace_3421544 : CollatzResearch.WordTrace tailWord_3421544 prefixEnd_3421544 390421478334948094903247 := by
  unfold tailWord_3421544
  simp only [CollatzResearch.WordTrace]
  refine ⟨62396980958168958018787843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83195974610891944025050457 62396980958168958018787843)
  ·
    refine ⟨93595471437253437028181765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62396980958168958018787843 93595471437253437028181765)
    ·
      refine ⟨17549150894485019442784081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93595471437253437028181765 17549150894485019442784081)
      ·
        refine ⟨13161863170863764582088061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17549150894485019442784081 13161863170863764582088061)
        ·
          refine ⟨4935698689073911718283023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13161863170863764582088061 4935698689073911718283023)
          ·
            refine ⟨7403548033610867577424535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4935698689073911718283023 7403548033610867577424535)
            ·
              refine ⟨11105322050416301366136803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7403548033610867577424535 11105322050416301366136803)
              ·
                refine ⟨16657983075624452049205205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11105322050416301366136803 16657983075624452049205205)
                ·
                  refine ⟨390421478334948094903247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16657983075624452049205205 390421478334948094903247)
                  ·
                    rfl

theorem cell22_3421544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 7].length) (baseStart_3421544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3421544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3421544 prefixEnd_3421544 := by exact prefixLift 3421544
  have htrace : WordTrace (prefixWord ++ tailWord_3421544) baseStart_3421544 baseEnd_3421544 := by
    simpa [prefixWord, tailWord_3421544, baseEnd_3421544] using wordTrace_append hprefix tailTrace_3421544
  have hstable : (prefixWord ++ tailWord_3421544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421544).length < 2 ^ (prefixWord ++ tailWord_3421544).sum := by decide
  have hdescent : baseEnd_3421544 < baseStart_3421544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421582 : List Nat := [4, 1, 1, 4, 3, 1, 1, 3, 1, 3]
def baseStart_3421582 : Nat := 118140960795 + 3421582 * 2 ^ 59
def prefixEnd_3421582 : Nat := 4983230072969 + 3 ^ 40 * 3421582 * 2
def baseEnd_3421582 : Nat := 1171277443181424852259625

theorem tailTrace_3421582 : CollatzResearch.WordTrace tailWord_3421582 prefixEnd_3421582 1171277443181424852259625 := by
  unfold tailWord_3421582
  simp only [CollatzResearch.WordTrace]
  refine ⟨15599418486275031065932375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83196898593466832351639333 15599418486275031065932375)
  ·
    refine ⟨23399127729412546598898563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15599418486275031065932375 23399127729412546598898563)
    ·
      refine ⟨35098691594118819898347845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23399127729412546598898563 35098691594118819898347845)
      ·
        refine ⟨6581004673897278730940221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35098691594118819898347845 6581004673897278730940221)
        ·
          refine ⟨2467876752711479524102583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6581004673897278730940221 2467876752711479524102583)
          ·
            refine ⟨3701815129067219286153875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2467876752711479524102583 3701815129067219286153875)
            ·
              refine ⟨5552722693600828929230813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3701815129067219286153875 5552722693600828929230813)
              ·
                refine ⟨2082271010100310848461555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5552722693600828929230813 2082271010100310848461555)
                ·
                  refine ⟨3123406515150466272692333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2082271010100310848461555 3123406515150466272692333)
                  ·
                    refine ⟨1171277443181424852259625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3123406515150466272692333 1171277443181424852259625)
                    ·
                      rfl

theorem cell22_3421582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 3, 1, 3].length) (baseStart_3421582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3421582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3421582 prefixEnd_3421582 := by exact prefixLift 3421582
  have htrace : WordTrace (prefixWord ++ tailWord_3421582) baseStart_3421582 baseEnd_3421582 := by
    simpa [prefixWord, tailWord_3421582, baseEnd_3421582] using wordTrace_append hprefix tailTrace_3421582
  have hstable : (prefixWord ++ tailWord_3421582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421582).length < 2 ^ (prefixWord ++ tailWord_3421582).sum := by decide
  have hdescent : baseEnd_3421582 < baseStart_3421582 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421632 : List Nat := [2, 1, 1, 2, 3, 1, 2, 1, 2, 7]
def baseStart_3421632 : Nat := 118140960795 + 3421632 * 2 ^ 59
def prefixEnd_3421632 : Nat := 4983230072969 + 3 ^ 40 * 3421632 * 2
def baseEnd_3421632 : Nat := 1171294559203241388509471

theorem tailTrace_3421632 : CollatzResearch.WordTrace tailWord_3421632 prefixEnd_3421632 1171294559203241388509471 := by
  unfold tailWord_3421632
  simp only [CollatzResearch.WordTrace]
  refine ⟨62398585770009553533389575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83198114360012738044519433 62398585770009553533389575)
  ·
    refine ⟨93597878655014330300084363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62398585770009553533389575 93597878655014330300084363)
    ·
      refine ⟨140396817982521495450126545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93597878655014330300084363 140396817982521495450126545)
      ·
        refine ⟨105297613486891121587594909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140396817982521495450126545 105297613486891121587594909)
        ·
          refine ⟨39486605057584170595348091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105297613486891121587594909 39486605057584170595348091)
          ·
            refine ⟨59229907586376255893022137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39486605057584170595348091 59229907586376255893022137)
            ·
              refine ⟨44422430689782191919766603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59229907586376255893022137 44422430689782191919766603)
              ·
                refine ⟨66633646034673287879649905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44422430689782191919766603 66633646034673287879649905)
                ·
                  refine ⟨49975234526004965909737429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66633646034673287879649905 49975234526004965909737429)
                  ·
                    refine ⟨1171294559203241388509471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49975234526004965909737429 1171294559203241388509471)
                    ·
                      rfl

theorem cell22_3421632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 2, 7].length) (baseStart_3421632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3421632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3421632 prefixEnd_3421632 := by exact prefixLift 3421632
  have htrace : WordTrace (prefixWord ++ tailWord_3421632) baseStart_3421632 baseEnd_3421632 := by
    simpa [prefixWord, tailWord_3421632, baseEnd_3421632] using wordTrace_append hprefix tailTrace_3421632
  have hstable : (prefixWord ++ tailWord_3421632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421632).length < 2 ^ (prefixWord ++ tailWord_3421632).sum := by decide
  have hdescent : baseEnd_3421632 < baseStart_3421632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421636 : List Nat := [2, 3, 3, 2, 1, 1, 1, 3, 2, 4]
def baseStart_3421636 : Nat := 118140960795 + 3421636 * 2 ^ 59
def prefixEnd_3421636 : Nat := 4983230072969 + 3 ^ 40 * 3421636 * 2
def baseEnd_3421636 : Nat := 1171295928484986711409459

theorem tailTrace_3421636 : CollatzResearch.WordTrace tailWord_3421636 prefixEnd_3421636 1171295928484986711409459 := by
  unfold tailWord_3421636
  simp only [CollatzResearch.WordTrace]
  refine ⟨62398658716002307874962381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83198211621336410499949841 62398658716002307874962381)
  ·
    refine ⟨23399497018500865453110893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62398658716002307874962381 23399497018500865453110893)
    ·
      refine ⟨8774811381937824544916585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23399497018500865453110893 8774811381937824544916585)
      ·
        refine ⟨6581108536453368408687439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8774811381937824544916585 6581108536453368408687439)
        ·
          refine ⟨9871662804680052613031159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6581108536453368408687439 9871662804680052613031159)
          ·
            refine ⟨14807494207020078919546739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9871662804680052613031159 14807494207020078919546739)
            ·
              refine ⟨22211241310530118379320109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14807494207020078919546739 22211241310530118379320109)
              ·
                refine ⟨8329215491448794392245041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22211241310530118379320109 8329215491448794392245041)
                ·
                  refine ⟨6246911618586595794183781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8329215491448794392245041 6246911618586595794183781)
                  ·
                    refine ⟨1171295928484986711409459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6246911618586595794183781 1171295928484986711409459)
                    ·
                      rfl

theorem cell22_3421636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_3421636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3421636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3421636 prefixEnd_3421636 := by exact prefixLift 3421636
  have htrace : WordTrace (prefixWord ++ tailWord_3421636) baseStart_3421636 baseEnd_3421636 := by
    simpa [prefixWord, tailWord_3421636, baseEnd_3421636] using wordTrace_append hprefix tailTrace_3421636
  have hstable : (prefixWord ++ tailWord_3421636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421636).length < 2 ^ (prefixWord ++ tailWord_3421636).sum := by decide
  have hdescent : baseEnd_3421636 < baseStart_3421636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421679 : List Nat := [1, 1, 2, 1, 4, 1, 4, 3, 5]
def baseStart_3421679 : Nat := 118140960795 + 3421679 * 2 ^ 59
def prefixEnd_3421679 : Nat := 4983230072969 + 3 ^ 40 * 3421679 * 2
def baseEnd_3421679 : Nat := 390436882754582977528109

theorem tailTrace_3421679 : CollatzResearch.WordTrace tailWord_3421679 prefixEnd_3421679 390436882754582977528109 := by
  unfold tailWord_3421679
  simp only [CollatzResearch.WordTrace]
  refine ⟨124798885770848834093740091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83199257180565889395826727 124798885770848834093740091)
  ·
    refine ⟨187198328656273251140610137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124798885770848834093740091 187198328656273251140610137)
    ·
      refine ⟨140398746492204938355457603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187198328656273251140610137 140398746492204938355457603)
      ·
        refine ⟨210598119738307407533186405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140398746492204938355457603 210598119738307407533186405)
        ·
          refine ⟨39487147450932638912472451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 210598119738307407533186405 39487147450932638912472451)
          ·
            refine ⟨59230721176398958368708677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39487147450932638912472451 59230721176398958368708677)
            ·
              refine ⟨11105760220574804694132877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59230721176398958368708677 11105760220574804694132877)
              ·
                refine ⟨4164660082715551760299829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11105760220574804694132877 4164660082715551760299829)
                ·
                  refine ⟨390436882754582977528109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4164660082715551760299829 390436882754582977528109)
                  ·
                    rfl

theorem cell22_3421679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 3, 5].length) (baseStart_3421679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3421679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3421679 prefixEnd_3421679 := by exact prefixLift 3421679
  have htrace : WordTrace (prefixWord ++ tailWord_3421679) baseStart_3421679 baseEnd_3421679 := by
    simpa [prefixWord, tailWord_3421679, baseEnd_3421679] using wordTrace_append hprefix tailTrace_3421679
  have hstable : (prefixWord ++ tailWord_3421679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421679).length < 2 ^ (prefixWord ++ tailWord_3421679).sum := by decide
  have hdescent : baseEnd_3421679 < baseStart_3421679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421754 : List Nat := [3, 1, 1, 1, 3, 2, 1, 3, 1, 6]
def baseStart_3421754 : Nat := 118140960795 + 3421754 * 2 ^ 59
def prefixEnd_3421754 : Nat := 4983230072969 + 3 ^ 40 * 3421754 * 2
def baseEnd_3421754 : Nat := 1171336322296473736959097

theorem tailTrace_3421754 : CollatzResearch.WordTrace tailWord_3421754 prefixEnd_3421754 1171336322296473736959097 := by
  unfold tailWord_3421754
  simp only [CollatzResearch.WordTrace]
  refine ⟨31200405311394280475680079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83201080830384747935146877 31200405311394280475680079)
  ·
    refine ⟨46800607967091420713520119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31200405311394280475680079 46800607967091420713520119)
    ·
      refine ⟨70200911950637131070280179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46800607967091420713520119 70200911950637131070280179)
      ·
        refine ⟨105301367925955696605420269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70200911950637131070280179 105301367925955696605420269)
        ·
          refine ⟨39488012972233386227032601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105301367925955696605420269 39488012972233386227032601)
          ·
            refine ⟨29616009729175039670274451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39488012972233386227032601 29616009729175039670274451)
            ·
              refine ⟨44424014593762559505411677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29616009729175039670274451 44424014593762559505411677)
              ·
                refine ⟨16659005472660959814529379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44424014593762559505411677 16659005472660959814529379)
                ·
                  refine ⟨24988508208991439721794069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16659005472660959814529379 24988508208991439721794069)
                  ·
                    refine ⟨1171336322296473736959097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24988508208991439721794069 1171336322296473736959097)
                    ·
                      rfl

theorem cell22_3421754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 1, 6].length) (baseStart_3421754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3421754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3421754 prefixEnd_3421754 := by exact prefixLift 3421754
  have htrace : WordTrace (prefixWord ++ tailWord_3421754) baseStart_3421754 baseEnd_3421754 := by
    simpa [prefixWord, tailWord_3421754, baseEnd_3421754] using wordTrace_append hprefix tailTrace_3421754
  have hstable : (prefixWord ++ tailWord_3421754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421754).length < 2 ^ (prefixWord ++ tailWord_3421754).sum := by decide
  have hdescent : baseEnd_3421754 < baseStart_3421754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421801 : List Nat := [1, 2, 1, 1, 1, 4, 2, 4, 3, 3]
def baseStart_3421801 : Nat := 118140960795 + 3421801 * 2 ^ 59
def prefixEnd_3421801 : Nat := 4983230072969 + 3 ^ 40 * 3421801 * 2
def baseEnd_3421801 : Nat := 1171352411356981281033953

theorem tailTrace_3421801 : CollatzResearch.WordTrace tailWord_3421801 prefixEnd_3421801 1171352411356981281033953 := by
  unfold tailWord_3421801
  simp only [CollatzResearch.WordTrace]
  refine ⟨124803335476406848929681257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83202223650937899286454171 124803335476406848929681257)
  ·
    refine ⟨93602501607305136697260943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124803335476406848929681257 93602501607305136697260943)
    ·
      refine ⟨140403752410957705045891415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93602501607305136697260943 140403752410957705045891415)
      ·
        refine ⟨210605628616436557568837123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140403752410957705045891415 210605628616436557568837123)
        ·
          refine ⟨315908442924654836353255685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210605628616436557568837123 315908442924654836353255685)
          ·
            refine ⟨59232833048372781816235441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 315908442924654836353255685 59232833048372781816235441)
            ·
              refine ⟨44424624786279586362176581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59232833048372781816235441 44424624786279586362176581)
              ·
                refine ⟨8329617147427422442908109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44424624786279586362176581 8329617147427422442908109)
                ·
                  refine ⟨3123606430285283416090541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8329617147427422442908109 3123606430285283416090541)
                  ·
                    refine ⟨1171352411356981281033953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3123606430285283416090541 1171352411356981281033953)
                    ·
                      rfl

theorem cell22_3421801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 4, 3, 3].length) (baseStart_3421801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3421801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3421801 prefixEnd_3421801 := by exact prefixLift 3421801
  have htrace : WordTrace (prefixWord ++ tailWord_3421801) baseStart_3421801 baseEnd_3421801 := by
    simpa [prefixWord, tailWord_3421801, baseEnd_3421801] using wordTrace_append hprefix tailTrace_3421801
  have hstable : (prefixWord ++ tailWord_3421801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421801).length < 2 ^ (prefixWord ++ tailWord_3421801).sum := by decide
  have hdescent : baseEnd_3421801 < baseStart_3421801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421831 : List Nat := [1, 1, 4, 2, 1, 3, 1, 4, 5]
def baseStart_3421831 : Nat := 118140960795 + 3421831 * 2 ^ 59
def prefixEnd_3421831 : Nat := 4983230072969 + 3 ^ 40 * 3421831 * 2
def baseEnd_3421831 : Nat := 390454226990023734261287

theorem tailTrace_3421831 : CollatzResearch.WordTrace tailWord_3421831 prefixEnd_3421831 390454226990023734261287 := by
  unfold tailWord_3421831
  simp only [CollatzResearch.WordTrace]
  refine ⟨124804429666298164053273347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83202953110865442702182231 124804429666298164053273347)
  ·
    refine ⟨187206644499447246079910021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124804429666298164053273347 187206644499447246079910021)
    ·
      refine ⟨35101245843646358639983129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187206644499447246079910021 35101245843646358639983129)
      ·
        refine ⟨26325934382734768979987347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35101245843646358639983129 26325934382734768979987347)
        ·
          refine ⟨39488901574102153469981021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26325934382734768979987347 39488901574102153469981021)
          ·
            refine ⟨14808338090288307551242883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39488901574102153469981021 14808338090288307551242883)
            ·
              refine ⟨22212507135432461326864325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14808338090288307551242883 22212507135432461326864325)
              ·
                refine ⟨4164845087893586498787061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22212507135432461326864325 4164845087893586498787061)
                ·
                  refine ⟨390454226990023734261287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4164845087893586498787061 390454226990023734261287)
                  ·
                    rfl

theorem cell22_3421831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 4, 5].length) (baseStart_3421831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3421831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3421831 prefixEnd_3421831 := by exact prefixLift 3421831
  have htrace : WordTrace (prefixWord ++ tailWord_3421831) baseStart_3421831 baseEnd_3421831 := by
    simpa [prefixWord, tailWord_3421831, baseEnd_3421831] using wordTrace_append hprefix tailTrace_3421831
  have hstable : (prefixWord ++ tailWord_3421831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421831).length < 2 ^ (prefixWord ++ tailWord_3421831).sum := by decide
  have hdescent : baseEnd_3421831 < baseStart_3421831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421861 : List Nat := [1, 3, 1, 2, 1, 2, 4, 1, 3, 4]
def baseStart_3421861 : Nat := 118140960795 + 3421861 * 2 ^ 59
def prefixEnd_3421861 : Nat := 4983230072969 + 3 ^ 40 * 3421861 * 2
def baseEnd_3421861 : Nat := 1171372950583161124533769

theorem tailTrace_3421861 : CollatzResearch.WordTrace tailWord_3421861 prefixEnd_3421861 1171372950583161124533769 := by
  unfold tailWord_3421861
  simp only [CollatzResearch.WordTrace]
  refine ⟨124805523856189479176865437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83203682570792986117910291 124805523856189479176865437)
  ·
    refine ⟨46802071446071054691324539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124805523856189479176865437 46802071446071054691324539)
    ·
      refine ⟨70203107169106582036986809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46802071446071054691324539 70203107169106582036986809)
      ·
        refine ⟨52652330376829936527740107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70203107169106582036986809 52652330376829936527740107)
        ·
          refine ⟨78978495565244904791610161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52652330376829936527740107 78978495565244904791610161)
          ·
            refine ⟨59233871673933678593707621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78978495565244904791610161 59233871673933678593707621)
            ·
              refine ⟨11106350938862564736320179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59233871673933678593707621 11106350938862564736320179)
              ·
                refine ⟨16659526408293847104480269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11106350938862564736320179 16659526408293847104480269)
                ·
                  refine ⟨6247322403110192664180101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16659526408293847104480269 6247322403110192664180101)
                  ·
                    refine ⟨1171372950583161124533769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6247322403110192664180101 1171372950583161124533769)
                    ·
                      rfl

theorem cell22_3421861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 3, 4].length) (baseStart_3421861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3421861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3421861 prefixEnd_3421861 := by exact prefixLift 3421861
  have htrace : WordTrace (prefixWord ++ tailWord_3421861) baseStart_3421861 baseEnd_3421861 := by
    simpa [prefixWord, tailWord_3421861, baseEnd_3421861] using wordTrace_append hprefix tailTrace_3421861
  have hstable : (prefixWord ++ tailWord_3421861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421861).length < 2 ^ (prefixWord ++ tailWord_3421861).sum := by decide
  have hdescent : baseEnd_3421861 < baseStart_3421861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421959 : List Nat := [1, 1, 4, 4, 2, 2, 2, 1, 2, 3]
def baseStart_3421959 : Nat := 118140960795 + 3421959 * 2 ^ 59
def prefixEnd_3421959 : Nat := 4983230072969 + 3 ^ 40 * 3421959 * 2
def baseEnd_3421959 : Nat := 1171406497985921535583469

theorem tailTrace_3421959 : CollatzResearch.WordTrace tailWord_3421959 prefixEnd_3421959 1171406497985921535583469 := by
  unfold tailWord_3421959
  simp only [CollatzResearch.WordTrace]
  refine ⟨124809098209834441913932931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83206065473222961275955287 124809098209834441913932931)
  ·
    refine ⟨187213647314751662870899397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124809098209834441913932931 187213647314751662870899397)
    ·
      refine ⟨35102558871515936788293637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187213647314751662870899397 35102558871515936788293637)
      ·
        refine ⟨6581729788409238147805057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35102558871515936788293637 6581729788409238147805057)
        ·
          refine ⟨4936297341306928610853793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6581729788409238147805057 4936297341306928610853793)
          ·
            refine ⟨3702223005980196458140345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4936297341306928610853793 3702223005980196458140345)
            ·
              refine ⟨2776667254485147343605259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3702223005980196458140345 2776667254485147343605259)
              ·
                refine ⟨4165000881727721015407889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2776667254485147343605259 4165000881727721015407889)
                ·
                  refine ⟨3123750661295790761555917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4165000881727721015407889 3123750661295790761555917)
                  ·
                    refine ⟨1171406497985921535583469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3123750661295790761555917 1171406497985921535583469)
                    ·
                      rfl

theorem cell22_3421959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 2, 1, 2, 3].length) (baseStart_3421959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3421959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3421959 prefixEnd_3421959 := by exact prefixLift 3421959
  have htrace : WordTrace (prefixWord ++ tailWord_3421959) baseStart_3421959 baseEnd_3421959 := by
    simpa [prefixWord, tailWord_3421959, baseEnd_3421959] using wordTrace_append hprefix tailTrace_3421959
  have hstable : (prefixWord ++ tailWord_3421959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421959).length < 2 ^ (prefixWord ++ tailWord_3421959).sum := by decide
  have hdescent : baseEnd_3421959 < baseStart_3421959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422004 : List Nat := [2, 5, 1, 1, 2, 2, 1, 4, 1, 3]
def baseStart_3422004 : Nat := 118140960795 + 3422004 * 2 ^ 59
def prefixEnd_3422004 : Nat := 4983230072969 + 3 ^ 40 * 3422004 * 2
def baseEnd_3422004 : Nat := 1171421902405556418208331

theorem tailTrace_3422004 : CollatzResearch.WordTrace tailWord_3422004 prefixEnd_3422004 1171421902405556418208331 := by
  unfold tailWord_3422004
  simp only [CollatzResearch.WordTrace]
  refine ⟨62405369747335707299660533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83207159663114276399547377 62405369747335707299660533)
  ·
    refine ⟨5850503413812722559343175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62405369747335707299660533 5850503413812722559343175)
    ·
      refine ⟨8775755120719083839014763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5850503413812722559343175 8775755120719083839014763)
      ·
        refine ⟨13163632681078625758522145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8775755120719083839014763 13163632681078625758522145)
        ·
          refine ⟨9872724510808969318891609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13163632681078625758522145 9872724510808969318891609)
          ·
            refine ⟨7404543383106726989168707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9872724510808969318891609 7404543383106726989168707)
            ·
              refine ⟨11106815074660090483753061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7404543383106726989168707 11106815074660090483753061)
              ·
                refine ⟨2082527826498766965703699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11106815074660090483753061 2082527826498766965703699)
                ·
                  refine ⟨3123791739748150448555549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2082527826498766965703699 3123791739748150448555549)
                  ·
                    refine ⟨1171421902405556418208331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3123791739748150448555549 1171421902405556418208331)
                    ·
                      rfl

theorem cell22_3422004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_3422004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3422004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3422004 prefixEnd_3422004 := by exact prefixLift 3422004
  have htrace : WordTrace (prefixWord ++ tailWord_3422004) baseStart_3422004 baseEnd_3422004 := by
    simpa [prefixWord, tailWord_3422004, baseEnd_3422004] using wordTrace_append hprefix tailTrace_3422004
  have hstable : (prefixWord ++ tailWord_3422004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422004).length < 2 ^ (prefixWord ++ tailWord_3422004).sum := by decide
  have hdescent : baseEnd_3422004 < baseStart_3422004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422047 : List Nat := [1, 1, 2, 3, 1, 6, 2, 1, 1, 4]
def baseStart_3422047 : Nat := 118140960795 + 3422047 * 2 ^ 59
def prefixEnd_3422047 : Nat := 4983230072969 + 3 ^ 40 * 3422047 * 2
def baseEnd_3422047 : Nat := 1171436622184318639383199

theorem tailTrace_3422047 : CollatzResearch.WordTrace tailWord_3422047 prefixEnd_3422047 1171436622184318639383199 := by
  unfold tailWord_3422047
  simp only [CollatzResearch.WordTrace]
  refine ⟨124812307833515632943136395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83208205222343755295424263 124812307833515632943136395)
  ·
    refine ⟨187218461750273449414704593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124812307833515632943136395 187218461750273449414704593)
    ·
      refine ⟨140413846312705087061028445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187218461750273449414704593 140413846312705087061028445)
      ·
        refine ⟨52655192367264407647885667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140413846312705087061028445 52655192367264407647885667)
        ·
          refine ⟨78982788550896611471828501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52655192367264407647885667 78982788550896611471828501)
          ·
            refine ⟨3702318213323278662741961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 78982788550896611471828501 3702318213323278662741961)
            ·
              refine ⟨2776738659992458997056471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3702318213323278662741961 2776738659992458997056471)
              ·
                refine ⟨4165107989988688495584707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2776738659992458997056471 4165107989988688495584707)
                ·
                  refine ⟨6247661984983032743377061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4165107989988688495584707 6247661984983032743377061)
                  ·
                    refine ⟨1171436622184318639383199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6247661984983032743377061 1171436622184318639383199)
                    ·
                      rfl

theorem cell22_3422047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 2, 1, 1, 4].length) (baseStart_3422047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3422047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3422047 prefixEnd_3422047 := by exact prefixLift 3422047
  have htrace : WordTrace (prefixWord ++ tailWord_3422047) baseStart_3422047 baseEnd_3422047 := by
    simpa [prefixWord, tailWord_3422047, baseEnd_3422047] using wordTrace_append hprefix tailTrace_3422047
  have hstable : (prefixWord ++ tailWord_3422047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422047).length < 2 ^ (prefixWord ++ tailWord_3422047).sum := by decide
  have hdescent : baseEnd_3422047 < baseStart_3422047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422060 : List Nat := [2, 2, 1, 1, 4, 3, 1, 1, 4, 3]
def baseStart_3422060 : Nat := 118140960795 + 3422060 * 2 ^ 59
def prefixEnd_3422060 : Nat := 4983230072969 + 3 ^ 40 * 3422060 * 2
def baseEnd_3422060 : Nat := 1171441072349990938808159

theorem tailTrace_3422060 : CollatzResearch.WordTrace tailWord_3422060 prefixEnd_3422060 1171441072349990938808159 := by
  unfold tailWord_3422060
  simp only [CollatzResearch.WordTrace]
  refine ⟨62406390991234268081679817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83208521321645690775573089 62406390991234268081679817)
  ·
    refine ⟨46804793243425701061259863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62406390991234268081679817 46804793243425701061259863)
    ·
      refine ⟨70207189865138551591889795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46804793243425701061259863 70207189865138551591889795)
      ·
        refine ⟨105310784797707827387834693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70207189865138551591889795 105310784797707827387834693)
        ·
          refine ⟨19745772149570217635219005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105310784797707827387834693 19745772149570217635219005)
          ·
            refine ⟨7404664556088831613207127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19745772149570217635219005 7404664556088831613207127)
            ·
              refine ⟨11106996834133247419810691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7404664556088831613207127 11106996834133247419810691)
              ·
                refine ⟨16660495251199871129716037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11106996834133247419810691 16660495251199871129716037)
                ·
                  refine ⟨3123842859599975836821757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16660495251199871129716037 3123842859599975836821757)
                  ·
                    refine ⟨1171441072349990938808159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3123842859599975836821757 1171441072349990938808159)
                    ·
                      rfl

theorem cell22_3422060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 3].length) (baseStart_3422060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3422060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3422060 prefixEnd_3422060 := by exact prefixLift 3422060
  have htrace : WordTrace (prefixWord ++ tailWord_3422060) baseStart_3422060 baseEnd_3422060 := by
    simpa [prefixWord, tailWord_3422060, baseEnd_3422060] using wordTrace_append hprefix tailTrace_3422060
  have hstable : (prefixWord ++ tailWord_3422060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422060).length < 2 ^ (prefixWord ++ tailWord_3422060).sum := by decide
  have hdescent : baseEnd_3422060 < baseStart_3422060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422062 : List Nat := [4, 1, 2, 3, 1, 1, 2, 4, 4]
def baseStart_3422062 : Nat := 118140960795 + 3422062 * 2 ^ 59
def prefixEnd_3422062 : Nat := 4983230072969 + 3 ^ 40 * 3422062 * 2
def baseEnd_3422062 : Nat := 390480585663621200086051

theorem tailTrace_3422062 : CollatzResearch.WordTrace tailWord_3422062 prefixEnd_3422062 390480585663621200086051 := by
  unfold tailWord_3422062
  simp only [CollatzResearch.WordTrace]
  refine ⟨15601606866057661313116555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83208569952307527003288293 15601606866057661313116555)
  ·
    refine ⟨23402410299086491969674833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15601606866057661313116555 23402410299086491969674833)
    ·
      refine ⟨17551807724314868977256125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23402410299086491969674833 17551807724314868977256125)
      ·
        refine ⟨6581927896618075866471047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17551807724314868977256125 6581927896618075866471047)
        ·
          refine ⟨9872891844927113799706571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6581927896618075866471047 9872891844927113799706571)
          ·
            refine ⟨14809337767390670699559857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9872891844927113799706571 14809337767390670699559857)
            ·
              refine ⟨11107003325543003024669893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14809337767390670699559857 11107003325543003024669893)
              ·
                refine ⟨2082563123539313067125605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11107003325543003024669893 2082563123539313067125605)
                ·
                  refine ⟨390480585663621200086051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2082563123539313067125605 390480585663621200086051)
                  ·
                    rfl

theorem cell22_3422062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 4, 4].length) (baseStart_3422062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3422062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3422062 prefixEnd_3422062 := by exact prefixLift 3422062
  have htrace : WordTrace (prefixWord ++ tailWord_3422062) baseStart_3422062 baseEnd_3422062 := by
    simpa [prefixWord, tailWord_3422062, baseEnd_3422062] using wordTrace_append hprefix tailTrace_3422062
  have hstable : (prefixWord ++ tailWord_3422062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422062).length < 2 ^ (prefixWord ++ tailWord_3422062).sum := by decide
  have hdescent : baseEnd_3422062 < baseStart_3422062 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422090 : List Nat := [3, 1, 2, 4, 2, 1, 1, 8]
def baseStart_3422090 : Nat := 118140960795 + 3422090 * 2 ^ 59
def prefixEnd_3422090 : Nat := 4983230072969 + 3 ^ 40 * 3422090 * 2
def baseEnd_3422090 : Nat := 130161260218120095617563

theorem tailTrace_3422090 : CollatzResearch.WordTrace tailWord_3422090 prefixEnd_3422090 130161260218120095617563 := by
  unfold tailWord_3422090
  simp only [CollatzResearch.WordTrace]
  refine ⟨31203469043089962821737931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83209250781573234191301149 31203469043089962821737931)
  ·
    refine ⟨46805203564634944232606897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31203469043089962821737931 46805203564634944232606897)
    ·
      refine ⟨35103902673476208174455173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46805203564634944232606897 35103902673476208174455173)
      ·
        refine ⟨6581981751276789032710345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35103902673476208174455173 6581981751276789032710345)
        ·
          refine ⟨4936486313457591774532759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6581981751276789032710345 4936486313457591774532759)
          ·
            refine ⟨7404729470186387661799139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4936486313457591774532759 7404729470186387661799139)
            ·
              refine ⟨11107094205279581492698709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7404729470186387661799139 11107094205279581492698709)
              ·
                refine ⟨130161260218120095617563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11107094205279581492698709 130161260218120095617563)
                ·
                  rfl

theorem cell22_3422090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 8].length) (baseStart_3422090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3422090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3422090 prefixEnd_3422090 := by exact prefixLift 3422090
  have htrace : WordTrace (prefixWord ++ tailWord_3422090) baseStart_3422090 baseEnd_3422090 := by
    simpa [prefixWord, tailWord_3422090, baseEnd_3422090] using wordTrace_append hprefix tailTrace_3422090
  have hstable : (prefixWord ++ tailWord_3422090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422090).length < 2 ^ (prefixWord ++ tailWord_3422090).sum := by decide
  have hdescent : baseEnd_3422090 < baseStart_3422090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422173 : List Nat := [1, 4, 3, 1, 3, 2, 2, 2, 1, 3]
def baseStart_3422173 : Nat := 118140960795 + 3422173 * 2 ^ 59
def prefixEnd_3422173 : Nat := 4983230072969 + 3 ^ 40 * 3422173 * 2
def baseEnd_3422173 : Nat := 1171479754559296310732813

theorem tailTrace_3422173 : CollatzResearch.WordTrace tailWord_3422173 prefixEnd_3422173 1171479754559296310732813 := by
  unfold tailWord_3422173
  simp only [CollatzResearch.WordTrace]
  refine ⟨124816903431059156462223173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83211268954039437641482115 124816903431059156462223173)
  ·
    refine ⟨23403169393323591836666845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124816903431059156462223173 23403169393323591836666845)
    ·
      refine ⟨8776188522496346938750067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23403169393323591836666845 8776188522496346938750067)
      ·
        refine ⟨13164282783744520408125101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8776188522496346938750067 13164282783744520408125101)
        ·
          refine ⟨4936606043904195153046913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13164282783744520408125101 4936606043904195153046913)
          ·
            refine ⟨3702454532928146364785185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4936606043904195153046913 3702454532928146364785185)
            ·
              refine ⟨2776840899696109773588889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3702454532928146364785185 2776840899696109773588889)
              ·
                refine ⟨2082630674772082330191667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2776840899696109773588889 2082630674772082330191667)
                ·
                  refine ⟨3123946012158123495287501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2082630674772082330191667 3123946012158123495287501)
                  ·
                    refine ⟨1171479754559296310732813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3123946012158123495287501 1171479754559296310732813)
                    ·
                      rfl

theorem cell22_3422173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_3422173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3422173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3422173 prefixEnd_3422173 := by exact prefixLift 3422173
  have htrace : WordTrace (prefixWord ++ tailWord_3422173) baseStart_3422173 baseEnd_3422173 := by
    simpa [prefixWord, tailWord_3422173, baseEnd_3422173] using wordTrace_append hprefix tailTrace_3422173
  have hstable : (prefixWord ++ tailWord_3422173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422173).length < 2 ^ (prefixWord ++ tailWord_3422173).sum := by decide
  have hdescent : baseEnd_3422173 < baseStart_3422173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422257 : List Nat := [1, 2, 2, 3, 1, 3, 2, 2, 3, 3]
def baseStart_3422257 : Nat := 118140960795 + 3422257 * 2 ^ 59
def prefixEnd_3422257 : Nat := 4983230072969 + 3 ^ 40 * 3422257 * 2
def baseEnd_3422257 : Nat := 1171508509475948091632555

theorem tailTrace_3422257 : CollatzResearch.WordTrace tailWord_3422257 prefixEnd_3422257 1171508509475948091632555 := by
  unfold tailWord_3422257
  simp only [CollatzResearch.WordTrace]
  refine ⟨124819967162754838808281025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83213311441836559205520683 124819967162754838808281025)
  ·
    refine ⟨93614975372066129106210769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124819967162754838808281025 93614975372066129106210769)
    ·
      refine ⟨70211231529049596829658077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93614975372066129106210769 70211231529049596829658077)
      ·
        refine ⟨26329211823393598811121779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70211231529049596829658077 26329211823393598811121779)
        ·
          refine ⟨39493817735090398216682669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26329211823393598811121779 39493817735090398216682669)
          ·
            refine ⟨14810181650658899331256001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39493817735090398216682669 14810181650658899331256001)
            ·
              refine ⟨11107636237994174498442001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14810181650658899331256001 11107636237994174498442001)
              ·
                refine ⟨8330727178495630873831501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11107636237994174498442001 8330727178495630873831501)
                ·
                  refine ⟨3124022691935861577686813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8330727178495630873831501 3124022691935861577686813)
                  ·
                    refine ⟨1171508509475948091632555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3124022691935861577686813 1171508509475948091632555)
                    ·
                      rfl

theorem cell22_3422257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 2, 3, 3].length) (baseStart_3422257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3422257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3422257 prefixEnd_3422257 := by exact prefixLift 3422257
  have htrace : WordTrace (prefixWord ++ tailWord_3422257) baseStart_3422257 baseEnd_3422257 := by
    simpa [prefixWord, tailWord_3422257, baseEnd_3422257] using wordTrace_append hprefix tailTrace_3422257
  have hstable : (prefixWord ++ tailWord_3422257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422257).length < 2 ^ (prefixWord ++ tailWord_3422257).sum := by decide
  have hdescent : baseEnd_3422257 < baseStart_3422257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422304 : List Nat := [2, 1, 1, 3, 2, 5, 2, 1, 5]
def baseStart_3422304 : Nat := 118140960795 + 3422304 * 2 ^ 59
def prefixEnd_3422304 : Nat := 4983230072969 + 3 ^ 40 * 3422304 * 2
def baseEnd_3422304 : Nat := 390508199512151878569137

theorem tailTrace_3422304 : CollatzResearch.WordTrace tailWord_3422304 prefixEnd_3422304 390508199512151878569137 := by
  unfold tailWord_3422304
  simp only [CollatzResearch.WordTrace]
  refine ⟨62410840696792282917620983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83214454262389710556827977 62410840696792282917620983)
  ·
    refine ⟨93616261045188424376431475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62410840696792282917620983 93616261045188424376431475)
    ·
      refine ⟨140424391567782636564647213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93616261045188424376431475 140424391567782636564647213)
      ·
        refine ⟨52659146837918488711742705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140424391567782636564647213 52659146837918488711742705)
        ·
          refine ⟨39494360128438866533807029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52659146837918488711742705 39494360128438866533807029)
          ·
            refine ⟨3702596262041143737544409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39494360128438866533807029 3702596262041143737544409)
            ·
              refine ⟨2776947196530857803158307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3702596262041143737544409 2776947196530857803158307)
              ·
                refine ⟨4165420794796286704737461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2776947196530857803158307 4165420794796286704737461)
                ·
                  refine ⟨390508199512151878569137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4165420794796286704737461 390508199512151878569137)
                  ·
                    rfl

theorem cell22_3422304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 2, 1, 5].length) (baseStart_3422304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3422304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3422304 prefixEnd_3422304 := by exact prefixLift 3422304
  have htrace : WordTrace (prefixWord ++ tailWord_3422304) baseStart_3422304 baseEnd_3422304 := by
    simpa [prefixWord, tailWord_3422304, baseEnd_3422304] using wordTrace_append hprefix tailTrace_3422304
  have hstable : (prefixWord ++ tailWord_3422304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422304).length < 2 ^ (prefixWord ++ tailWord_3422304).sum := by decide
  have hdescent : baseEnd_3422304 < baseStart_3422304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422317 : List Nat := [1, 5, 1, 1, 2, 1, 3, 1, 3, 4]
def baseStart_3422317 : Nat := 118140960795 + 3422317 * 2 ^ 59
def prefixEnd_3422317 : Nat := 4983230072969 + 3 ^ 40 * 3422317 * 2
def baseEnd_3422317 : Nat := 1171529048702127935132371

theorem tailTrace_3422317 : CollatzResearch.WordTrace tailWord_3422317 prefixEnd_3422317 1171529048702127935132371 := by
  unfold tailWord_3422317
  simp only [CollatzResearch.WordTrace]
  refine ⟨124822155542537469055465205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83214770361691646036976803 124822155542537469055465205)
  ·
    refine ⟨11702077082112887723949863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 124822155542537469055465205 11702077082112887723949863)
    ·
      refine ⟨17553115623169331585924795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11702077082112887723949863 17553115623169331585924795)
      ·
        refine ⟨26329673434753997378887193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17553115623169331585924795 26329673434753997378887193)
        ·
          refine ⟨19747255076065498034165395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26329673434753997378887193 19747255076065498034165395)
          ·
            refine ⟨29620882614098247051248093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19747255076065498034165395 29620882614098247051248093)
            ·
              refine ⟨11107830980286842644218035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29620882614098247051248093 11107830980286842644218035)
              ·
                refine ⟨16661746470430263966327053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11107830980286842644218035 16661746470430263966327053)
                ·
                  refine ⟨6248154926411348987372645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16661746470430263966327053 6248154926411348987372645)
                  ·
                    refine ⟨1171529048702127935132371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6248154926411348987372645 1171529048702127935132371)
                    ·
                      rfl

theorem cell22_3422317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_3422317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3422317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3422317 prefixEnd_3422317 := by exact prefixLift 3422317
  have htrace : WordTrace (prefixWord ++ tailWord_3422317) baseStart_3422317 baseEnd_3422317 := by
    simpa [prefixWord, tailWord_3422317, baseEnd_3422317] using wordTrace_append hprefix tailTrace_3422317
  have hstable : (prefixWord ++ tailWord_3422317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422317).length < 2 ^ (prefixWord ++ tailWord_3422317).sum := by decide
  have hdescent : baseEnd_3422317 < baseStart_3422317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422364 : List Nat := [2, 2, 3, 2, 1, 1, 1, 5, 2, 3]
def baseStart_3422364 : Nat := 118140960795 + 3422364 * 2 ^ 59
def prefixEnd_3422364 : Nat := 4983230072969 + 3 ^ 40 * 3422364 * 2
def baseEnd_3422364 : Nat := 1171545137762635479207227

theorem tailTrace_3422364 : CollatzResearch.WordTrace tailWord_3422364 prefixEnd_3422364 1171545137762635479207227 := by
  unfold tailWord_3422364
  simp only [CollatzResearch.WordTrace]
  refine ⟨62411934886683598041213073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83215913182244797388284097 62411934886683598041213073)
  ·
    refine ⟨46808951165012698530909805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62411934886683598041213073 46808951165012698530909805)
    ·
      refine ⟨17553356686879761949091177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46808951165012698530909805 17553356686879761949091177)
      ·
        refine ⟨13165017515159821461818383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17553356686879761949091177 13165017515159821461818383)
        ·
          refine ⟨19747526272739732192727575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13165017515159821461818383 19747526272739732192727575)
          ·
            refine ⟨29621289409109598289091363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19747526272739732192727575 29621289409109598289091363)
            ·
              refine ⟨44431934113664397433637045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29621289409109598289091363 44431934113664397433637045)
              ·
                refine ⟨4165493823156037259403473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44431934113664397433637045 4165493823156037259403473)
                ·
                  refine ⟨3124120367367027944552605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4165493823156037259403473 3124120367367027944552605)
                  ·
                    refine ⟨1171545137762635479207227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3124120367367027944552605 1171545137762635479207227)
                    ·
                      rfl

theorem cell22_3422364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 5, 2, 3].length) (baseStart_3422364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3422364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3422364 prefixEnd_3422364 := by exact prefixLift 3422364
  have htrace : WordTrace (prefixWord ++ tailWord_3422364) baseStart_3422364 baseEnd_3422364 := by
    simpa [prefixWord, tailWord_3422364, baseEnd_3422364] using wordTrace_append hprefix tailTrace_3422364
  have hstable : (prefixWord ++ tailWord_3422364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422364).length < 2 ^ (prefixWord ++ tailWord_3422364).sum := by decide
  have hdescent : baseEnd_3422364 < baseStart_3422364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422392 : List Nat := [2, 1, 2, 1, 2, 1, 3, 2, 5, 3]
def baseStart_3422392 : Nat := 118140960795 + 3422392 * 2 ^ 59
def prefixEnd_3422392 : Nat := 4983230072969 + 3 ^ 40 * 3422392 * 2
def baseEnd_3422392 : Nat := 1171554722734852739507141

theorem tailTrace_3422392 : CollatzResearch.WordTrace tailWord_3422392 prefixEnd_3422392 1171554722734852739507141 := by
  unfold tailWord_3422392
  simp only [CollatzResearch.WordTrace]
  refine ⟨62412445508632878432222715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83216594011510504576296953 62412445508632878432222715)
  ·
    refine ⟨93618668262949317648334073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62412445508632878432222715 93618668262949317648334073)
    ·
      refine ⟨70214001197211988236250555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93618668262949317648334073 70214001197211988236250555)
      ·
        refine ⟨105321001795817982354375833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70214001197211988236250555 105321001795817982354375833)
        ·
          refine ⟨78990751346863486765781875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105321001795817982354375833 78990751346863486765781875)
          ·
            refine ⟨118486127020295230148672813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78990751346863486765781875 118486127020295230148672813)
            ·
              refine ⟨44432297632610711305752305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118486127020295230148672813 44432297632610711305752305)
              ·
                refine ⟨33324223224458033479314229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44432297632610711305752305 33324223224458033479314229)
                ·
                  refine ⟨3124145927292940638685709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33324223224458033479314229 3124145927292940638685709)
                  ·
                    refine ⟨1171554722734852739507141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3124145927292940638685709 1171554722734852739507141)
                    ·
                      rfl

theorem cell22_3422392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 5, 3].length) (baseStart_3422392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3422392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3422392 prefixEnd_3422392 := by exact prefixLift 3422392
  have htrace : WordTrace (prefixWord ++ tailWord_3422392) baseStart_3422392 baseEnd_3422392 := by
    simpa [prefixWord, tailWord_3422392, baseEnd_3422392] using wordTrace_append hprefix tailTrace_3422392
  have hstable : (prefixWord ++ tailWord_3422392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422392).length < 2 ^ (prefixWord ++ tailWord_3422392).sum := by decide
  have hdescent : baseEnd_3422392 < baseStart_3422392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422398 : List Nat := [4, 2, 1, 1, 4, 2, 1, 2, 2, 3]
def baseStart_3422398 : Nat := 118140960795 + 3422398 * 2 ^ 59
def prefixEnd_3422398 : Nat := 4983230072969 + 3 ^ 40 * 3422398 * 2
def baseEnd_3422398 : Nat := 1171556776657470723857123

theorem tailTrace_3422398 : CollatzResearch.WordTrace tailWord_3422398 prefixEnd_3422398 1171556776657470723857123 := by
  unfold tailWord_3422398
  simp only [CollatzResearch.WordTrace]
  refine ⟨15603138731905502486145481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83216739903496013259442565 15603138731905502486145481)
  ·
    refine ⟨11702354048929126864609111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15603138731905502486145481 11702354048929126864609111)
    ·
      refine ⟨17553531073393690296913667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11702354048929126864609111 17553531073393690296913667)
      ·
        refine ⟨26330296610090535445370501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17553531073393690296913667 26330296610090535445370501)
        ·
          refine ⟨4936930614391975396006969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26330296610090535445370501 4936930614391975396006969)
          ·
            refine ⟨3702697960793981547005227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4936930614391975396006969 3702697960793981547005227)
            ·
              refine ⟨5554046941190972320507841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3702697960793981547005227 5554046941190972320507841)
              ·
                refine ⟨4165535205893229240380881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5554046941190972320507841 4165535205893229240380881)
                ·
                  refine ⟨3124151404419921930285661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4165535205893229240380881 3124151404419921930285661)
                  ·
                    refine ⟨1171556776657470723857123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3124151404419921930285661 1171556776657470723857123)
                    ·
                      rfl

theorem cell22_3422398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 2, 2, 3].length) (baseStart_3422398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3422398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3422398 prefixEnd_3422398 := by exact prefixLift 3422398
  have htrace : WordTrace (prefixWord ++ tailWord_3422398) baseStart_3422398 baseEnd_3422398 := by
    simpa [prefixWord, tailWord_3422398, baseEnd_3422398] using wordTrace_append hprefix tailTrace_3422398
  have hstable : (prefixWord ++ tailWord_3422398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422398).length < 2 ^ (prefixWord ++ tailWord_3422398).sum := by decide
  have hdescent : baseEnd_3422398 < baseStart_3422398 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422428 : List Nat := [2, 2, 5, 2, 1, 2, 2, 6]
def baseStart_3422428 : Nat := 118140960795 + 3422428 * 2 ^ 59
def prefixEnd_3422428 : Nat := 4983230072969 + 3 ^ 40 * 3422428 * 2
def baseEnd_3422428 : Nat := 130174116252284516178559

theorem tailTrace_3422428 : CollatzResearch.WordTrace tailWord_3422428 prefixEnd_3422428 130174116252284516178559 := by
  unfold tailWord_3422428
  simp only [CollatzResearch.WordTrace]
  refine ⟨62413102022567667506377969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83217469363423556675170625 62413102022567667506377969)
  ·
    refine ⟨46809826516925750629783477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62413102022567667506377969 46809826516925750629783477)
    ·
      refine ⟨4388421235961789121542201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46809826516925750629783477 4388421235961789121542201)
      ·
        refine ⟨3291315926971341841156651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4388421235961789121542201 3291315926971341841156651)
        ·
          refine ⟨4936973890457012761734977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3291315926971341841156651 4936973890457012761734977)
          ·
            refine ⟨3702730417842759571301233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4936973890457012761734977 3702730417842759571301233)
            ·
              refine ⟨2777047813382069678475925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3702730417842759571301233 2777047813382069678475925)
              ·
                refine ⟨130174116252284516178559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2777047813382069678475925 130174116252284516178559)
                ·
                  rfl

theorem cell22_3422428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 2, 6].length) (baseStart_3422428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3422428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3422428 prefixEnd_3422428 := by exact prefixLift 3422428
  have htrace : WordTrace (prefixWord ++ tailWord_3422428) baseStart_3422428 baseEnd_3422428 := by
    simpa [prefixWord, tailWord_3422428, baseEnd_3422428] using wordTrace_append hprefix tailTrace_3422428
  have hstable : (prefixWord ++ tailWord_3422428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422428).length < 2 ^ (prefixWord ++ tailWord_3422428).sum := by decide
  have hdescent : baseEnd_3422428 < baseStart_3422428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422497 : List Nat := [1, 2, 3, 2, 1, 1, 2, 3, 1, 6]
def baseStart_3422497 : Nat := 118140960795 + 3422497 * 2 ^ 59
def prefixEnd_3422497 : Nat := 4983230072969 + 3 ^ 40 * 3422497 * 2
def baseEnd_3422497 : Nat := 1171590666380667465631819

theorem tailTrace_3422497 : CollatzResearch.WordTrace tailWord_3422497 prefixEnd_3422497 1171590666380667465631819 := by
  unfold tailWord_3422497
  simp only [CollatzResearch.WordTrace]
  refine ⟨124828720681885359797017745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83219147121256906531345163 124828720681885359797017745)
  ·
    refine ⟨93621540511414019847763309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124828720681885359797017745 93621540511414019847763309)
    ·
      refine ⟨35108077691780257442911241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93621540511414019847763309 35108077691780257442911241)
      ·
        refine ⟨26331058268835193082183431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35108077691780257442911241 26331058268835193082183431)
        ·
          refine ⟨39496587403252789623275147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26331058268835193082183431 39496587403252789623275147)
          ·
            refine ⟨59244881104879184434912721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39496587403252789623275147 59244881104879184434912721)
            ·
              refine ⟨44433660828659388326184541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59244881104879184434912721 44433660828659388326184541)
              ·
                refine ⟨16662622810747270622319203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44433660828659388326184541 16662622810747270622319203)
                ·
                  refine ⟨24993934216120905933478805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16662622810747270622319203 24993934216120905933478805)
                  ·
                    refine ⟨1171590666380667465631819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24993934216120905933478805 1171590666380667465631819)
                    ·
                      rfl

theorem cell22_3422497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_3422497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3422497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3422497 prefixEnd_3422497 := by exact prefixLift 3422497
  have htrace : WordTrace (prefixWord ++ tailWord_3422497) baseStart_3422497 baseEnd_3422497 := by
    simpa [prefixWord, tailWord_3422497, baseEnd_3422497] using wordTrace_append hprefix tailTrace_3422497
  have hstable : (prefixWord ++ tailWord_3422497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422497).length < 2 ^ (prefixWord ++ tailWord_3422497).sum := by decide
  have hdescent : baseEnd_3422497 < baseStart_3422497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422544 : List Nat := [2, 1, 1, 1, 1, 6, 1, 1, 5, 3]
def baseStart_3422544 : Nat := 118140960795 + 3422544 * 2 ^ 59
def prefixEnd_3422544 : Nat := 4983230072969 + 3 ^ 40 * 3422544 * 2
def baseEnd_3422544 : Nat := 1171606755441175009706675

theorem tailTrace_3422544 : CollatzResearch.WordTrace tailWord_3422544 prefixEnd_3422544 1171606755441175009706675 := by
  unfold tailWord_3422544
  simp only [CollatzResearch.WordTrace]
  refine ⟨62415217456357543411989343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83220289941810057882652457 62415217456357543411989343)
  ·
    refine ⟨93622826184536315117984015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62415217456357543411989343 93622826184536315117984015)
    ·
      refine ⟨140434239276804472676976023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93622826184536315117984015 140434239276804472676976023)
      ·
        refine ⟨210651358915206709015464035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140434239276804472676976023 210651358915206709015464035)
        ·
          refine ⟨315977038372810063523196053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210651358915206709015464035 315977038372810063523196053)
          ·
            refine ⟨14811423673725471727649815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 315977038372810063523196053 14811423673725471727649815)
            ·
              refine ⟨22217135510588207591474723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14811423673725471727649815 22217135510588207591474723)
              ·
                refine ⟨33325703265882311387212085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22217135510588207591474723 33325703265882311387212085)
                ·
                  refine ⟨3124284681176466692551133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33325703265882311387212085 3124284681176466692551133)
                  ·
                    refine ⟨1171606755441175009706675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3124284681176466692551133 1171606755441175009706675)
                    ·
                      rfl

theorem cell22_3422544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 5, 3].length) (baseStart_3422544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3422544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3422544 prefixEnd_3422544 := by exact prefixLift 3422544
  have htrace : WordTrace (prefixWord ++ tailWord_3422544) baseStart_3422544 baseEnd_3422544 := by
    simpa [prefixWord, tailWord_3422544, baseEnd_3422544] using wordTrace_append hprefix tailTrace_3422544
  have hstable : (prefixWord ++ tailWord_3422544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422544).length < 2 ^ (prefixWord ++ tailWord_3422544).sum := by decide
  have hdescent : baseEnd_3422544 < baseStart_3422544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422578 : List Nat := [3, 2, 1, 2, 1, 3, 2, 4, 1, 3]
def baseStart_3422578 : Nat := 118140960795 + 3422578 * 2 ^ 59
def prefixEnd_3422578 : Nat := 4983230072969 + 3 ^ 40 * 3422578 * 2
def baseEnd_3422578 : Nat := 1171618394336010254356571

theorem tailTrace_3422578 : CollatzResearch.WordTrace tailWord_3422578 prefixEnd_3422578 1171618394336010254356571 := by
  unfold tailWord_3422578
  simp only [CollatzResearch.WordTrace]
  refine ⟨31207918748647977657679097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83221116663061273753810925 31207918748647977657679097)
  ·
    refine ⟨23405939061485983243259323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31207918748647977657679097 23405939061485983243259323)
    ·
      refine ⟨35108908592228974864888985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23405939061485983243259323 35108908592228974864888985)
      ·
        refine ⟨26331681444171731148666739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35108908592228974864888985 26331681444171731148666739)
        ·
          refine ⟨39497522166257596723000109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26331681444171731148666739 39497522166257596723000109)
          ·
            refine ⟨14811570812346598771125041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39497522166257596723000109 14811570812346598771125041)
            ·
              refine ⟨11108678109259949078343781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14811570812346598771125041 11108678109259949078343781)
              ·
                refine ⟨2082877145486240452189459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11108678109259949078343781 2082877145486240452189459)
                ·
                  refine ⟨3124315718229360678284189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2082877145486240452189459 3124315718229360678284189)
                  ·
                    refine ⟨1171618394336010254356571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3124315718229360678284189 1171618394336010254356571)
                    ·
                      rfl

theorem cell22_3422578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 4, 1, 3].length) (baseStart_3422578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3422578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3422578 prefixEnd_3422578 := by exact prefixLift 3422578
  have htrace : WordTrace (prefixWord ++ tailWord_3422578) baseStart_3422578 baseEnd_3422578 := by
    simpa [prefixWord, tailWord_3422578, baseEnd_3422578] using wordTrace_append hprefix tailTrace_3422578
  have hstable : (prefixWord ++ tailWord_3422578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422578).length < 2 ^ (prefixWord ++ tailWord_3422578).sum := by decide
  have hdescent : baseEnd_3422578 < baseStart_3422578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422589 : List Nat := [1, 4, 1, 1, 2, 3, 2, 1, 2, 5]
def baseStart_3422589 : Nat := 118140960795 + 3422589 * 2 ^ 59
def prefixEnd_3422589 : Nat := 4983230072969 + 3 ^ 40 * 3422589 * 2
def baseEnd_3422589 : Nat := 1171622159860809892331537

theorem tailTrace_3422589 : CollatzResearch.WordTrace tailWord_3422589 prefixEnd_3422589 1171622159860809892331537 := by
  unfold tailWord_3422589
  simp only [CollatzResearch.WordTrace]
  refine ⟨124832076197552059509366821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83221384131701373006244547 124832076197552059509366821)
  ·
    refine ⟨23406014287041011158006279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124832076197552059509366821 23406014287041011158006279)
    ·
      refine ⟨35109021430561516737009419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23406014287041011158006279 35109021430561516737009419)
      ·
        refine ⟨52663532145842275105514129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35109021430561516737009419 52663532145842275105514129)
        ·
          refine ⟨39497649109381706329135597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52663532145842275105514129 39497649109381706329135597)
          ·
            refine ⟨14811618416018139873425849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39497649109381706329135597 14811618416018139873425849)
            ·
              refine ⟨11108713812013604905069387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14811618416018139873425849 11108713812013604905069387)
              ·
                refine ⟨16663070718020407357604081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11108713812013604905069387 16663070718020407357604081)
                ·
                  refine ⟨12497303038515305518203061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16663070718020407357604081 12497303038515305518203061)
                  ·
                    refine ⟨1171622159860809892331537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12497303038515305518203061 1171622159860809892331537)
                    ·
                      rfl

theorem cell22_3422589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 2, 5].length) (baseStart_3422589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3422589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3422589 prefixEnd_3422589 := by exact prefixLift 3422589
  have htrace : WordTrace (prefixWord ++ tailWord_3422589) baseStart_3422589 baseEnd_3422589 := by
    simpa [prefixWord, tailWord_3422589, baseEnd_3422589] using wordTrace_append hprefix tailTrace_3422589
  have hstable : (prefixWord ++ tailWord_3422589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422589).length < 2 ^ (prefixWord ++ tailWord_3422589).sum := by decide
  have hdescent : baseEnd_3422589 < baseStart_3422589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422612 : List Nat := [2, 4, 2, 1, 3, 2, 1, 3, 1, 3]
def baseStart_3422612 : Nat := 118140960795 + 3422612 * 2 ^ 59
def prefixEnd_3422612 : Nat := 4983230072969 + 3 ^ 40 * 3422612 * 2
def baseEnd_3422612 : Nat := 1171630033230845499006467

theorem tailTrace_3422612 : CollatzResearch.WordTrace tailWord_3422612 prefixEnd_3422612 1171630033230845499006467 := by
  unfold tailWord_3422612
  simp only [CollatzResearch.WordTrace]
  refine ⟨62416457538234367218727045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83221943384312489624969393 62416457538234367218727045)
  ·
    refine ⟨11703085788418943853511321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62416457538234367218727045 11703085788418943853511321)
    ·
      refine ⟨8777314341314207890133491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11703085788418943853511321 8777314341314207890133491)
      ·
        refine ⟨13165971511971311835200237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8777314341314207890133491 13165971511971311835200237)
        ·
          refine ⟨4937239316989241938200089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13165971511971311835200237 4937239316989241938200089)
          ·
            refine ⟨3702929487741931453650067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4937239316989241938200089 3702929487741931453650067)
            ·
              refine ⟨5554394231612897180475101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3702929487741931453650067 5554394231612897180475101)
              ·
                refine ⟨2082897836854836442678163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5554394231612897180475101 2082897836854836442678163)
                ·
                  refine ⟨3124346755282254664017245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2082897836854836442678163 3124346755282254664017245)
                  ·
                    refine ⟨1171630033230845499006467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3124346755282254664017245 1171630033230845499006467)
                    ·
                      rfl

theorem cell22_3422612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_3422612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3422612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3422612 prefixEnd_3422612 := by exact prefixLift 3422612
  have htrace : WordTrace (prefixWord ++ tailWord_3422612) baseStart_3422612 baseEnd_3422612 := by
    simpa [prefixWord, tailWord_3422612, baseEnd_3422612] using wordTrace_append hprefix tailTrace_3422612
  have hstable : (prefixWord ++ tailWord_3422612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422612).length < 2 ^ (prefixWord ++ tailWord_3422612).sum := by decide
  have hdescent : baseEnd_3422612 < baseStart_3422612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422664 : List Nat := [2, 1, 3, 1, 3, 2, 2, 8]
def baseStart_3422664 : Nat := 118140960795 + 3422664 * 2 ^ 59
def prefixEnd_3422664 : Nat := 4983230072969 + 3 ^ 40 * 3422664 * 2
def baseEnd_3422664 : Nat := 130183092654837188522923

theorem tailTrace_3422664 : CollatzResearch.WordTrace tailWord_3422664 prefixEnd_3422664 130183092654837188522923 := by
  unfold tailWord_3422664
  simp only [CollatzResearch.WordTrace]
  refine ⟨62417405836140173659173523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83223207781520231545564697 62417405836140173659173523)
  ·
    refine ⟨93626108754210260488760285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62417405836140173659173523 93626108754210260488760285)
    ·
      refine ⟨35109790782828847683285107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93626108754210260488760285 35109790782828847683285107)
      ·
        refine ⟨52664686174243271524927661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35109790782828847683285107 52664686174243271524927661)
        ·
          refine ⟨19749257315341226821847873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52664686174243271524927661 19749257315341226821847873)
          ·
            refine ⟨14811942986505920116385905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19749257315341226821847873 14811942986505920116385905)
            ·
              refine ⟨11108957239879440087289429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14811942986505920116385905 11108957239879440087289429)
              ·
                refine ⟨130183092654837188522923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11108957239879440087289429 130183092654837188522923)
                ·
                  rfl

theorem cell22_3422664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 8].length) (baseStart_3422664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3422664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3422664 prefixEnd_3422664 := by exact prefixLift 3422664
  have htrace : WordTrace (prefixWord ++ tailWord_3422664) baseStart_3422664 baseEnd_3422664 := by
    simpa [prefixWord, tailWord_3422664, baseEnd_3422664] using wordTrace_append hprefix tailTrace_3422664
  have hstable : (prefixWord ++ tailWord_3422664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422664).length < 2 ^ (prefixWord ++ tailWord_3422664).sum := by decide
  have hdescent : baseEnd_3422664 < baseStart_3422664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422666 : List Nat := [3, 1, 2, 1, 2, 2, 4, 1, 2, 4]
def baseStart_3422666 : Nat := 118140960795 + 3422666 * 2 ^ 59
def prefixEnd_3422666 : Nat := 4983230072969 + 3 ^ 40 * 3422666 * 2
def baseEnd_3422666 : Nat := 1171648518534407358156301

theorem tailTrace_3422666 : CollatzResearch.WordTrace tailWord_3422666 prefixEnd_3422666 1171648518534407358156301 := by
  unfold tailWord_3422666
  simp only [CollatzResearch.WordTrace]
  refine ⟨31208721154568275414979963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83223256412182067773279901 31208721154568275414979963)
  ·
    refine ⟨46813081731852413122469945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31208721154568275414979963 46813081731852413122469945)
    ·
      refine ⟨35109811298889309841852459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46813081731852413122469945 35109811298889309841852459)
      ·
        refine ⟨52664716948333964762778689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35109811298889309841852459 52664716948333964762778689)
        ·
          refine ⟨39498537711250473572084017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52664716948333964762778689 39498537711250473572084017)
          ·
            refine ⟨29623903283437855179063013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39498537711250473572084017 29623903283437855179063013)
            ·
              refine ⟨5554481865644597846074315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29623903283437855179063013 5554481865644597846074315)
              ·
                refine ⟨8331722798466896769111473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5554481865644597846074315 8331722798466896769111473)
                ·
                  refine ⟨6248792098850172576833605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8331722798466896769111473 6248792098850172576833605)
                  ·
                    refine ⟨1171648518534407358156301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6248792098850172576833605 1171648518534407358156301)
                    ·
                      rfl

theorem cell22_3422666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 1, 2, 4].length) (baseStart_3422666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3422666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3422666 prefixEnd_3422666 := by exact prefixLift 3422666
  have htrace : WordTrace (prefixWord ++ tailWord_3422666) baseStart_3422666 baseEnd_3422666 := by
    simpa [prefixWord, tailWord_3422666, baseEnd_3422666] using wordTrace_append hprefix tailTrace_3422666
  have hstable : (prefixWord ++ tailWord_3422666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422666).length < 2 ^ (prefixWord ++ tailWord_3422666).sum := by decide
  have hdescent : baseEnd_3422666 < baseStart_3422666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422730 : List Nat := [3, 1, 2, 2, 2, 1, 4, 3, 1, 3]
def baseStart_3422730 : Nat := 118140960795 + 3422730 * 2 ^ 59
def prefixEnd_3422730 : Nat := 4983230072969 + 3 ^ 40 * 3422730 * 2
def baseEnd_3422730 : Nat := 1171670427042332524556105

theorem tailTrace_3422730 : CollatzResearch.WordTrace tailWord_3422730 prefixEnd_3422730 1171670427042332524556105 := by
  unfold tailWord_3422730
  simp only [CollatzResearch.WordTrace]
  refine ⟨31209304722510310147562411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83224812593360827060166429 31209304722510310147562411)
  ·
    refine ⟨46813957083765465221343617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31209304722510310147562411 46813957083765465221343617)
    ·
      refine ⟨35110467812824098916007713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46813957083765465221343617 35110467812824098916007713)
      ·
        refine ⟨26332850859618074187005785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35110467812824098916007713 26332850859618074187005785)
        ·
          refine ⟨19749638144713555640254339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26332850859618074187005785 19749638144713555640254339)
          ·
            refine ⟨29624457217070333460381509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19749638144713555640254339 29624457217070333460381509)
            ·
              refine ⟨5554585728200687523821533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29624457217070333460381509 5554585728200687523821533)
              ·
                refine ⟨2082969648075257821433075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5554585728200687523821533 2082969648075257821433075)
                ·
                  refine ⟨3124454472112886732149613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2082969648075257821433075 3124454472112886732149613)
                  ·
                    refine ⟨1171670427042332524556105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3124454472112886732149613 1171670427042332524556105)
                    ·
                      rfl

theorem cell22_3422730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 3, 1, 3].length) (baseStart_3422730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3422730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3422730 prefixEnd_3422730 := by exact prefixLift 3422730
  have htrace : WordTrace (prefixWord ++ tailWord_3422730) baseStart_3422730 baseEnd_3422730 := by
    simpa [prefixWord, tailWord_3422730, baseEnd_3422730] using wordTrace_append hprefix tailTrace_3422730
  have hstable : (prefixWord ++ tailWord_3422730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422730).length < 2 ^ (prefixWord ++ tailWord_3422730).sum := by decide
  have hdescent : baseEnd_3422730 < baseStart_3422730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422743 : List Nat := [1, 1, 3, 6, 1, 1, 1, 1, 7]
def baseStart_3422743 : Nat := 118140960795 + 3422743 * 2 ^ 59
def prefixEnd_3422743 : Nat := 4983230072969 + 3 ^ 40 * 3422743 * 2
def baseEnd_3422743 : Nat := 390558292402668274660355

theorem tailTrace_3422743 : CollatzResearch.WordTrace tailWord_3422743 prefixEnd_3422743 390558292402668274660355 := by
  unfold tailWord_3422743
  simp only [CollatzResearch.WordTrace]
  refine ⟨124837693038994143810472883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83225128692662762540315255 124837693038994143810472883)
  ·
    refine ⟨187256539558491215715709325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124837693038994143810472883 187256539558491215715709325)
    ·
      refine ⟨70221202334434205893390997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187256539558491215715709325 70221202334434205893390997)
      ·
        refine ⟨3291618859426603401252703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 70221202334434205893390997 3291618859426603401252703)
        ·
          refine ⟨4937428289139905101879055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3291618859426603401252703 4937428289139905101879055)
          ·
            refine ⟨7406142433709857652818583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4937428289139905101879055 7406142433709857652818583)
            ·
              refine ⟨11109213650564786479227875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7406142433709857652818583 11109213650564786479227875)
              ·
                refine ⟨16663820475847179718841813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11109213650564786479227875 16663820475847179718841813)
                ·
                  refine ⟨390558292402668274660355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16663820475847179718841813 390558292402668274660355)
                  ·
                    rfl

theorem cell22_3422743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 7].length) (baseStart_3422743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3422743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3422743 prefixEnd_3422743 := by exact prefixLift 3422743
  have htrace : WordTrace (prefixWord ++ tailWord_3422743) baseStart_3422743 baseEnd_3422743 := by
    simpa [prefixWord, tailWord_3422743, baseEnd_3422743] using wordTrace_append hprefix tailTrace_3422743
  have hstable : (prefixWord ++ tailWord_3422743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422743).length < 2 ^ (prefixWord ++ tailWord_3422743).sum := by decide
  have hdescent : baseEnd_3422743 < baseStart_3422743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422760 : List Nat := [2, 1, 5, 2, 1, 2, 3, 1, 5]
def baseStart_3422760 : Nat := 118140960795 + 3422760 * 2 ^ 59
def prefixEnd_3422760 : Nat := 4983230072969 + 3 ^ 40 * 3422760 * 2
def baseEnd_3422760 : Nat := 390560232218474148768671

theorem tailTrace_3422760 : CollatzResearch.WordTrace tailWord_3422760 prefixEnd_3422760 390560232218474148768671 := by
  unfold tailWord_3422760
  simp only [CollatzResearch.WordTrace]
  refine ⟨62419156539966277856920867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83225542053288370475894489 62419156539966277856920867)
  ·
    refine ⟨93628734809949416785381301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62419156539966277856920867 93628734809949416785381301)
    ·
      refine ⟨8777693888432757823629497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 93628734809949416785381301 8777693888432757823629497)
      ·
        refine ⟨6583270416324568367722123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8777693888432757823629497 6583270416324568367722123)
        ·
          refine ⟨9874905624486852551583185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6583270416324568367722123 9874905624486852551583185)
          ·
            refine ⟨7406179218365139413687389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9874905624486852551583185 7406179218365139413687389)
            ·
              refine ⟨2777317206886927280132771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7406179218365139413687389 2777317206886927280132771)
              ·
                refine ⟨4165975810330390920199157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2777317206886927280132771 4165975810330390920199157)
                ·
                  refine ⟨390560232218474148768671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4165975810330390920199157 390560232218474148768671)
                  ·
                    rfl

theorem cell22_3422760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 3, 1, 5].length) (baseStart_3422760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3422760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3422760 prefixEnd_3422760 := by exact prefixLift 3422760
  have htrace : WordTrace (prefixWord ++ tailWord_3422760) baseStart_3422760 baseEnd_3422760 := by
    simpa [prefixWord, tailWord_3422760, baseEnd_3422760] using wordTrace_append hprefix tailTrace_3422760
  have hstable : (prefixWord ++ tailWord_3422760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422760).length < 2 ^ (prefixWord ++ tailWord_3422760).sum := by decide
  have hdescent : baseEnd_3422760 < baseStart_3422760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422773 : List Nat := [1, 3, 3, 1, 1, 2, 4, 2, 1, 4]
def baseStart_3422773 : Nat := 118140960795 + 3422773 * 2 ^ 59
def prefixEnd_3422773 : Nat := 4983230072969 + 3 ^ 40 * 3422773 * 2
def baseEnd_3422773 : Nat := 1171685146821094745730973

theorem tailTrace_3422773 : CollatzResearch.WordTrace tailWord_3422773 prefixEnd_3422773 1171685146821094745730973 := by
  unfold tailWord_3422773
  simp only [CollatzResearch.WordTrace]
  refine ⟨124838787228885458934064973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83225858152590305956043315 124838787228885458934064973)
  ·
    refine ⟨46814545210832047100274365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124838787228885458934064973 46814545210832047100274365)
    ·
      refine ⟨17555454454062017662602887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46814545210832047100274365 17555454454062017662602887)
      ·
        refine ⟨26333181681093026493904331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17555454454062017662602887 26333181681093026493904331)
        ·
          refine ⟨39499772521639539740856497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26333181681093026493904331 39499772521639539740856497)
          ·
            refine ⟨29624829391229654805642373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39499772521639539740856497 29624829391229654805642373)
            ·
              refine ⟨5554655510855560276057945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29624829391229654805642373 5554655510855560276057945)
              ·
                refine ⟨4165991633141670207043459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5554655510855560276057945 4165991633141670207043459)
                ·
                  refine ⟨6248987449712505310565189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4165991633141670207043459 6248987449712505310565189)
                  ·
                    refine ⟨1171685146821094745730973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6248987449712505310565189 1171685146821094745730973)
                    ·
                      rfl

theorem cell22_3422773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_3422773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3422773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3422773 prefixEnd_3422773 := by exact prefixLift 3422773
  have htrace : WordTrace (prefixWord ++ tailWord_3422773) baseStart_3422773 baseEnd_3422773 := by
    simpa [prefixWord, tailWord_3422773, baseEnd_3422773] using wordTrace_append hprefix tailTrace_3422773
  have hstable : (prefixWord ++ tailWord_3422773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422773).length < 2 ^ (prefixWord ++ tailWord_3422773).sum := by decide
  have hdescent : baseEnd_3422773 < baseStart_3422773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422799 : List Nat := [1, 1, 2, 1, 1, 2, 14]
def baseStart_3422799 : Nat := 118140960795 + 3422799 * 2 ^ 59
def prefixEnd_3422799 : Nat := 4983230072969 + 3 ^ 40 * 3422799 * 2
def baseEnd_3422799 : Nat := 43396075820460716465959

theorem tailTrace_3422799 : CollatzResearch.WordTrace tailWord_3422799 prefixEnd_3422799 43396075820460716465959 := by
  unfold tailWord_3422799
  simp only [CollatzResearch.WordTrace]
  refine ⟨124839735526791265374511451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83226490351194176916340967 124839735526791265374511451)
  ·
    refine ⟨187259603290186898061767177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124839735526791265374511451 187259603290186898061767177)
    ·
      refine ⟨140444702467640173546325383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187259603290186898061767177 140444702467640173546325383)
      ·
        refine ⟨210667053701460260319488075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140444702467640173546325383 210667053701460260319488075)
        ·
          refine ⟨316000580552190390479232113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210667053701460260319488075 316000580552190390479232113)
          ·
            refine ⟨237000435414142792859424085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 316000580552190390479232113 237000435414142792859424085)
            ·
              refine ⟨43396075820460716465959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 237000435414142792859424085 43396075820460716465959)
              ·
                rfl

theorem cell22_3422799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 14].length) (baseStart_3422799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3422799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3422799 prefixEnd_3422799 := by exact prefixLift 3422799
  have htrace : WordTrace (prefixWord ++ tailWord_3422799) baseStart_3422799 baseEnd_3422799 := by
    simpa [prefixWord, tailWord_3422799, baseEnd_3422799] using wordTrace_append hprefix tailTrace_3422799
  have hstable : (prefixWord ++ tailWord_3422799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422799).length < 2 ^ (prefixWord ++ tailWord_3422799).sum := by decide
  have hdescent : baseEnd_3422799 < baseStart_3422799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422801 : List Nat := [1, 2, 2, 1, 3, 3, 1, 1, 4, 4]
def baseStart_3422801 : Nat := 118140960795 + 3422801 * 2 ^ 59
def prefixEnd_3422801 : Nat := 4983230072969 + 3 ^ 40 * 3422801 * 2
def baseEnd_3422801 : Nat := 1171694731793312006030887

theorem tailTrace_3422801 : CollatzResearch.WordTrace tailWord_3422801 prefixEnd_3422801 1171694731793312006030887 := by
  unfold tailWord_3422801
  simp only [CollatzResearch.WordTrace]
  refine ⟨124839808472784019716084257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83226538981856013144056171 124839808472784019716084257)
  ·
    refine ⟨93629856354588014787063193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124839808472784019716084257 93629856354588014787063193)
    ·
      refine ⟨70222392265941011090297395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93629856354588014787063193 70222392265941011090297395)
      ·
        refine ⟨105333588398911516635446093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70222392265941011090297395 105333588398911516635446093)
        ·
          refine ⟨39500095649591818738292285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105333588398911516635446093 39500095649591818738292285)
          ·
            refine ⟨14812535868596932026859607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39500095649591818738292285 14812535868596932026859607)
            ·
              refine ⟨22218803802895398040289411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14812535868596932026859607 22218803802895398040289411)
              ·
                refine ⟨33328205704343097060434117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22218803802895398040289411 33328205704343097060434117)
                ·
                  refine ⟨6249038569564330698831397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33328205704343097060434117 6249038569564330698831397)
                  ·
                    refine ⟨1171694731793312006030887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6249038569564330698831397 1171694731793312006030887)
                    ·
                      rfl

theorem cell22_3422801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 4, 4].length) (baseStart_3422801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3422801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3422801 prefixEnd_3422801 := by exact prefixLift 3422801
  have htrace : WordTrace (prefixWord ++ tailWord_3422801) baseStart_3422801 baseEnd_3422801 := by
    simpa [prefixWord, tailWord_3422801, baseEnd_3422801] using wordTrace_append hprefix tailTrace_3422801
  have hstable : (prefixWord ++ tailWord_3422801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422801).length < 2 ^ (prefixWord ++ tailWord_3422801).sum := by decide
  have hdescent : baseEnd_3422801 < baseStart_3422801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422850 : List Nat := [3, 4, 3, 1, 11]
def baseStart_3422850 : Nat := 118140960795 + 3422850 * 2 ^ 59
def prefixEnd_3422850 : Nat := 4983230072969 + 3 ^ 40 * 3422850 * 2
def baseEnd_3422850 : Nat := 4821858047303260129859

theorem tailTrace_3422850 : CollatzResearch.WordTrace tailWord_3422850 prefixEnd_3422850 4821858047303260129859 := by
  unfold tailWord_3422850
  simp only [CollatzResearch.WordTrace]
  refine ⟨31210398912401625271154501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83227730433071000723078669 31210398912401625271154501)
  ·
    refine ⟨5851949796075304738341469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31210398912401625271154501 5851949796075304738341469)
    ·
      refine ⟨2194481173528239276878051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5851949796075304738341469 2194481173528239276878051)
      ·
        refine ⟨3291721760292358915317077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2194481173528239276878051 3291721760292358915317077)
        ·
          refine ⟨4821858047303260129859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3291721760292358915317077 4821858047303260129859)
          ·
            rfl

theorem cell22_3422850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 11].length) (baseStart_3422850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3422850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3422850 prefixEnd_3422850 := by exact prefixLift 3422850
  have htrace : WordTrace (prefixWord ++ tailWord_3422850) baseStart_3422850 baseEnd_3422850 := by
    simpa [prefixWord, tailWord_3422850, baseEnd_3422850] using wordTrace_append hprefix tailTrace_3422850
  have hstable : (prefixWord ++ tailWord_3422850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422850).length < 2 ^ (prefixWord ++ tailWord_3422850).sum := by decide
  have hdescent : baseEnd_3422850 < baseStart_3422850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422906 : List Nat := [3, 1, 1, 1, 2, 3, 1, 2, 8]
def baseStart_3422906 : Nat := 118140960795 + 3422906 * 2 ^ 59
def prefixEnd_3422906 : Nat := 4983230072969 + 3 ^ 40 * 3422906 * 2
def baseEnd_3422906 : Nat := 390576891813042244051855

theorem tailTrace_3422906 : CollatzResearch.WordTrace tailWord_3422906 prefixEnd_3422906 390576891813042244051855 := by
  unfold tailWord_3422906
  simp only [CollatzResearch.WordTrace]
  refine ⟨31210909534350905662164143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83229092091602415099104381 31210909534350905662164143)
  ·
    refine ⟨46816364301526358493246215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31210909534350905662164143 46816364301526358493246215)
    ·
      refine ⟨70224546452289537739869323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46816364301526358493246215 70224546452289537739869323)
      ·
        refine ⟨105336819678434306609803985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70224546452289537739869323 105336819678434306609803985)
        ·
          refine ⟨79002614758825729957352989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105336819678434306609803985 79002614758825729957352989)
          ·
            refine ⟨29625980534559648734007371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79002614758825729957352989 29625980534559648734007371)
            ·
              refine ⟨44438970801839473101011057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29625980534559648734007371 44438970801839473101011057)
              ·
                refine ⟨33329228101379604825758293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44438970801839473101011057 33329228101379604825758293)
                ·
                  refine ⟨390576891813042244051855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33329228101379604825758293 390576891813042244051855)
                  ·
                    rfl

theorem cell22_3422906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 8].length) (baseStart_3422906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3422906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3422906 prefixEnd_3422906 := by exact prefixLift 3422906
  have htrace : WordTrace (prefixWord ++ tailWord_3422906) baseStart_3422906 baseEnd_3422906 := by
    simpa [prefixWord, tailWord_3422906, baseEnd_3422906] using wordTrace_append hprefix tailTrace_3422906
  have hstable : (prefixWord ++ tailWord_3422906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422906).length < 2 ^ (prefixWord ++ tailWord_3422906).sum := by decide
  have hdescent : baseEnd_3422906 < baseStart_3422906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422940 : List Nat := [2, 2, 5, 1, 1, 1, 2, 2, 6]
def baseStart_3422940 : Nat := 118140960795 + 3422940 * 2 ^ 59
def prefixEnd_3422940 : Nat := 4983230072969 + 3 ^ 40 * 3422940 * 2
def baseEnd_3422940 : Nat := 390580771444653992268487

theorem tailTrace_3422940 : CollatzResearch.WordTrace tailWord_3422940 prefixEnd_3422940 390580771444653992268487 := by
  unfold tailWord_3422940
  simp only [CollatzResearch.WordTrace]
  refine ⟨62422439109640223227697137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83229918812853630970262849 62422439109640223227697137)
  ·
    refine ⟨46816829332230167420772853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62422439109640223227697137 46816829332230167420772853)
    ·
      refine ⟨4389077749896578195697455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46816829332230167420772853 4389077749896578195697455)
      ·
        refine ⟨6583616624844867293546183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4389077749896578195697455 6583616624844867293546183)
        ·
          refine ⟨9875424937267300940319275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6583616624844867293546183 9875424937267300940319275)
          ·
            refine ⟨14813137405900951410478913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9875424937267300940319275 14813137405900951410478913)
            ·
              refine ⟨11109853054425713557859185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14813137405900951410478913 11109853054425713557859185)
              ·
                refine ⟨8332389790819285168394389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11109853054425713557859185 8332389790819285168394389)
                ·
                  refine ⟨390580771444653992268487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8332389790819285168394389 390580771444653992268487)
                  ·
                    rfl

theorem cell22_3422940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 2, 6].length) (baseStart_3422940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3422940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3422940 prefixEnd_3422940 := by exact prefixLift 3422940
  have htrace : WordTrace (prefixWord ++ tailWord_3422940) baseStart_3422940 baseEnd_3422940 := by
    simpa [prefixWord, tailWord_3422940, baseEnd_3422940] using wordTrace_append hprefix tailTrace_3422940
  have hstable : (prefixWord ++ tailWord_3422940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422940).length < 2 ^ (prefixWord ++ tailWord_3422940).sum := by decide
  have hdescent : baseEnd_3422940 < baseStart_3422940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422974 : List Nat := [4, 2, 2, 1, 2, 2, 3, 2, 4]
def baseStart_3422974 : Nat := 118140960795 + 3422974 * 2 ^ 59
def prefixEnd_3422974 : Nat := 4983230072969 + 3 ^ 40 * 3422974 * 2
def baseEnd_3422974 : Nat := 390584651076265740485119

theorem tailTrace_3422974 : CollatzResearch.WordTrace tailWord_3422974 prefixEnd_3422974 390584651076265740485119 := by
  unfold tailWord_3422974
  simp only [CollatzResearch.WordTrace]
  refine ⟨15605764787644658782766497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83230745534104846841421317 15605764787644658782766497)
  ·
    refine ⟨11704323590733494087074873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15605764787644658782766497 11704323590733494087074873)
    ·
      refine ⟨8778242693050120565306155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11704323590733494087074873 8778242693050120565306155)
      ·
        refine ⟨13167364039575180847959233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8778242693050120565306155 13167364039575180847959233)
        ·
          refine ⟨9875523029681385635969425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13167364039575180847959233 9875523029681385635969425)
          ·
            refine ⟨7406642272261039226977069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9875523029681385635969425 7406642272261039226977069)
            ·
              refine ⟨2777490852097889710116401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7406642272261039226977069 2777490852097889710116401)
              ·
                refine ⟨2083118139073417282587301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2777490852097889710116401 2083118139073417282587301)
                ·
                  refine ⟨390584651076265740485119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2083118139073417282587301 390584651076265740485119)
                  ·
                    rfl

theorem cell22_3422974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 3, 2, 4].length) (baseStart_3422974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3422974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3422974 prefixEnd_3422974 := by exact prefixLift 3422974
  have htrace : WordTrace (prefixWord ++ tailWord_3422974) baseStart_3422974 baseEnd_3422974 := by
    simpa [prefixWord, tailWord_3422974, baseEnd_3422974] using wordTrace_append hprefix tailTrace_3422974
  have hstable : (prefixWord ++ tailWord_3422974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422974).length < 2 ^ (prefixWord ++ tailWord_3422974).sum := by decide
  have hdescent : baseEnd_3422974 < baseStart_3422974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423034 : List Nat := [3, 1, 1, 1, 6, 1, 1, 4, 1, 3]
def baseStart_3423034 : Nat := 118140960795 + 3423034 * 2 ^ 59
def prefixEnd_3423034 : Nat := 4983230072969 + 3 ^ 40 * 3423034 * 2
def baseEnd_3423034 : Nat := 1171774492454977064955173

theorem tailTrace_3423034 : CollatzResearch.WordTrace tailWord_3423034 prefixEnd_3423034 1171774492454977064955173 := by
  unfold tailWord_3423034
  simp only [CollatzResearch.WordTrace]
  refine ⟨31212076670234975127329039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83232204453959933672877437 31212076670234975127329039)
  ·
    refine ⟨46818115005352462690993559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31212076670234975127329039 46818115005352462690993559)
    ·
      refine ⟨70227172508028694036490339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46818115005352462690993559 70227172508028694036490339)
      ·
        refine ⟨105340758762043041054735509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70227172508028694036490339 105340758762043041054735509)
        ·
          refine ⟨4937848066970767549440727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 105340758762043041054735509 4937848066970767549440727)
          ·
            refine ⟨7406772100456151324161091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4937848066970767549440727 7406772100456151324161091)
            ·
              refine ⟨11110158150684226986241637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7406772100456151324161091 11110158150684226986241637)
              ·
                refine ⟨2083154653253292559920307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11110158150684226986241637 2083154653253292559920307)
                ·
                  refine ⟨3124731979879938839880461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2083154653253292559920307 3124731979879938839880461)
                  ·
                    refine ⟨1171774492454977064955173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3124731979879938839880461 1171774492454977064955173)
                    ·
                      rfl

theorem cell22_3423034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 4, 1, 3].length) (baseStart_3423034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3423034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3423034 prefixEnd_3423034 := by exact prefixLift 3423034
  have htrace : WordTrace (prefixWord ++ tailWord_3423034) baseStart_3423034 baseEnd_3423034 := by
    simpa [prefixWord, tailWord_3423034, baseEnd_3423034] using wordTrace_append hprefix tailTrace_3423034
  have hstable : (prefixWord ++ tailWord_3423034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423034).length < 2 ^ (prefixWord ++ tailWord_3423034).sum := by decide
  have hdescent : baseEnd_3423034 < baseStart_3423034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423043 : List Nat := [1, 1, 1, 3, 1, 4, 1, 1, 5, 4]
def baseStart_3423043 : Nat := 118140960795 + 3423043 * 2 ^ 59
def prefixEnd_3423043 : Nat := 4983230072969 + 3 ^ 40 * 3423043 * 2
def baseEnd_3423043 : Nat := 1171777573338904041480145

theorem tailTrace_3423043 : CollatzResearch.WordTrace tailWord_3423043 prefixEnd_3423043 1171777573338904041480145 := by
  unfold tailWord_3423043
  simp only [CollatzResearch.WordTrace]
  refine ⟨124848634937907295046393783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83232423291938196697595855 124848634937907295046393783)
  ·
    refine ⟨187272952406860942569590675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124848634937907295046393783 187272952406860942569590675)
    ·
      refine ⟨280909428610291413854386013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187272952406860942569590675 280909428610291413854386013)
      ·
        refine ⟨105341035728859280195394755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 280909428610291413854386013 105341035728859280195394755)
        ·
          refine ⟨158011553593288920293092133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105341035728859280195394755 158011553593288920293092133)
          ·
            refine ⟨29627166298741672554954775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 158011553593288920293092133 29627166298741672554954775)
            ·
              refine ⟨44440749448112508832432163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29627166298741672554954775 44440749448112508832432163)
              ·
                refine ⟨66661124172168763248648245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44440749448112508832432163 66661124172168763248648245)
                ·
                  refine ⟨6249480391140821554560773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66661124172168763248648245 6249480391140821554560773)
                  ·
                    refine ⟨1171777573338904041480145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6249480391140821554560773 1171777573338904041480145)
                    ·
                      rfl

theorem cell22_3423043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 5, 4].length) (baseStart_3423043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3423043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3423043 prefixEnd_3423043 := by exact prefixLift 3423043
  have htrace : WordTrace (prefixWord ++ tailWord_3423043) baseStart_3423043 baseEnd_3423043 := by
    simpa [prefixWord, tailWord_3423043, baseEnd_3423043] using wordTrace_append hprefix tailTrace_3423043
  have hstable : (prefixWord ++ tailWord_3423043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423043).length < 2 ^ (prefixWord ++ tailWord_3423043).sum := by decide
  have hdescent : baseEnd_3423043 < baseStart_3423043 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423073 : List Nat := [1, 2, 3, 1, 1, 1, 2, 3, 3, 5]
def baseStart_3423073 : Nat := 118140960795 + 3423073 * 2 ^ 59
def prefixEnd_3423073 : Nat := 4983230072969 + 3 ^ 40 * 3423073 * 2
def baseEnd_3423073 : Nat := 1171787842951993963230053

theorem tailTrace_3423073 : CollatzResearch.WordTrace tailWord_3423073 prefixEnd_3423073 1171787842951993963230053 := by
  unfold tailWord_3423073
  simp only [CollatzResearch.WordTrace]
  refine ⟨124849729127798610169985873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83233152751865740113323915 124849729127798610169985873)
  ·
    refine ⟨93637296845848957627489405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124849729127798610169985873 93637296845848957627489405)
    ·
      refine ⟨35113986317193359110308527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93637296845848957627489405 35113986317193359110308527)
      ·
        refine ⟨52670979475790038665462791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35113986317193359110308527 52670979475790038665462791)
        ·
          refine ⟨79006469213685057998194187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52670979475790038665462791 79006469213685057998194187)
          ·
            refine ⟨118509703820527586997291281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79006469213685057998194187 118509703820527586997291281)
            ·
              refine ⟨88882277865395690247968461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118509703820527586997291281 88882277865395690247968461)
              ·
                refine ⟨33330854199523383842988173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88882277865395690247968461 33330854199523383842988173)
                ·
                  refine ⟨12499070324821268941120565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33330854199523383842988173 12499070324821268941120565)
                  ·
                    refine ⟨1171787842951993963230053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12499070324821268941120565 1171787842951993963230053)
                    ·
                      rfl

theorem cell22_3423073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_3423073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3423073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3423073 prefixEnd_3423073 := by exact prefixLift 3423073
  have htrace : WordTrace (prefixWord ++ tailWord_3423073) baseStart_3423073 baseEnd_3423073 := by
    simpa [prefixWord, tailWord_3423073, baseEnd_3423073] using wordTrace_append hprefix tailTrace_3423073
  have hstable : (prefixWord ++ tailWord_3423073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423073).length < 2 ^ (prefixWord ++ tailWord_3423073).sum := by decide
  have hdescent : baseEnd_3423073 < baseStart_3423073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423077 : List Nat := [1, 3, 1, 3, 1, 1, 6, 1, 1, 4]
def baseStart_3423077 : Nat := 118140960795 + 3423077 * 2 ^ 59
def prefixEnd_3423077 : Nat := 4983230072969 + 3 ^ 40 * 3423077 * 2
def baseEnd_3423077 : Nat := 1171789212233739286130041

theorem tailTrace_3423077 : CollatzResearch.WordTrace tailWord_3423077 prefixEnd_3423077 1171789212233739286130041 := by
  unfold tailWord_3423077
  simp only [CollatzResearch.WordTrace]
  refine ⟨124849875019784118853131485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83233250013189412568754323 124849875019784118853131485)
  ·
    refine ⟨46818703132419044569924307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124849875019784118853131485 46818703132419044569924307)
    ·
      refine ⟨70228054698628566854886461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46818703132419044569924307 70228054698628566854886461)
      ·
        refine ⟨26335520511985712570582423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70228054698628566854886461 26335520511985712570582423)
        ·
          refine ⟨39503280767978568855873635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26335520511985712570582423 39503280767978568855873635)
          ·
            refine ⟨59254921151967853283810453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39503280767978568855873635 59254921151967853283810453)
            ·
              refine ⟨2777574428998493122678615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 59254921151967853283810453 2777574428998493122678615)
              ·
                refine ⟨4166361643497739684017923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2777574428998493122678615 4166361643497739684017923)
                ·
                  refine ⟨6249542465246609526026885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4166361643497739684017923 6249542465246609526026885)
                  ·
                    refine ⟨1171789212233739286130041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6249542465246609526026885 1171789212233739286130041)
                    ·
                      rfl

theorem cell22_3423077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 6, 1, 1, 4].length) (baseStart_3423077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3423077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3423077 prefixEnd_3423077 := by exact prefixLift 3423077
  have htrace : WordTrace (prefixWord ++ tailWord_3423077) baseStart_3423077 baseEnd_3423077 := by
    simpa [prefixWord, tailWord_3423077, baseEnd_3423077] using wordTrace_append hprefix tailTrace_3423077
  have hstable : (prefixWord ++ tailWord_3423077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423077).length < 2 ^ (prefixWord ++ tailWord_3423077).sum := by decide
  have hdescent : baseEnd_3423077 < baseStart_3423077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423220 : List Nat := [2, 6, 2, 1, 1, 1, 1, 2, 3, 3]
def baseStart_3423220 : Nat := 118140960795 + 3423220 * 2 ^ 59
def prefixEnd_3423220 : Nat := 4983230072969 + 3 ^ 40 * 3423220 * 2
def baseEnd_3423220 : Nat := 1171838164056134579804603

theorem tailTrace_3423220 : CollatzResearch.WordTrace tailWord_3423220 prefixEnd_3423220 1171838164056134579804603 := by
  unfold tailWord_3423220
  simp only [CollatzResearch.WordTrace]
  refine ⟨62427545329133027137793557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83236727105510702850391409 62427545329133027137793557)
  ·
    refine ⟨2926291187303110647084073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 62427545329133027137793557 2926291187303110647084073)
    ·
      refine ⟨2194718390477332985313055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2926291187303110647084073 2194718390477332985313055)
      ·
        refine ⟨3292077585715999477969583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2194718390477332985313055 3292077585715999477969583)
        ·
          refine ⟨4938116378573999216954375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3292077585715999477969583 4938116378573999216954375)
          ·
            refine ⟨7407174567860998825431563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4938116378573999216954375 7407174567860998825431563)
            ·
              refine ⟨11110761851791498238147345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7407174567860998825431563 11110761851791498238147345)
              ·
                refine ⟨8333071388843623678610509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11110761851791498238147345 8333071388843623678610509)
                ·
                  refine ⟨3124901770816358879478941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8333071388843623678610509 3124901770816358879478941)
                  ·
                    refine ⟨1171838164056134579804603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3124901770816358879478941 1171838164056134579804603)
                    ·
                      rfl

theorem cell22_3423220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_3423220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3423220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3423220 prefixEnd_3423220 := by exact prefixLift 3423220
  have htrace : WordTrace (prefixWord ++ tailWord_3423220) baseStart_3423220 baseEnd_3423220 := by
    simpa [prefixWord, tailWord_3423220, baseEnd_3423220] using wordTrace_append hprefix tailTrace_3423220
  have hstable : (prefixWord ++ tailWord_3423220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423220).length < 2 ^ (prefixWord ++ tailWord_3423220).sum := by decide
  have hdescent : baseEnd_3423220 < baseStart_3423220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423242 : List Nat := [3, 1, 2, 2, 3, 1, 2, 2, 1, 5]
def baseStart_3423242 : Nat := 118140960795 + 3423242 * 2 ^ 59
def prefixEnd_3423242 : Nat := 4983230072969 + 3 ^ 40 * 3423242 * 2
def baseEnd_3423242 : Nat := 1171845695105733855754535

theorem tailTrace_3423242 : CollatzResearch.WordTrace tailWord_3423242 prefixEnd_3423242 1171845695105733855754535 := by
  unfold tailWord_3423242
  simp only [CollatzResearch.WordTrace]
  refine ⟨31213973266046588008221995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83237262042790901355258653 31213973266046588008221995)
  ·
    refine ⟨46820959899069882012332993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31213973266046588008221995 46820959899069882012332993)
    ·
      refine ⟨35115719924302411509249745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46820959899069882012332993 35115719924302411509249745)
      ·
        refine ⟨26336789943226808631937309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35115719924302411509249745 26336789943226808631937309)
        ·
          refine ⟨9876296228710053236976491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26336789943226808631937309 9876296228710053236976491)
          ·
            refine ⟨14814444343065079855464737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9876296228710053236976491 14814444343065079855464737)
            ·
              refine ⟨11110833257298809891598553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14814444343065079855464737 11110833257298809891598553)
              ·
                refine ⟨8333124942974107418698915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11110833257298809891598553 8333124942974107418698915)
                ·
                  refine ⟨12499687414461161128048373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8333124942974107418698915 12499687414461161128048373)
                  ·
                    refine ⟨1171845695105733855754535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12499687414461161128048373 1171845695105733855754535)
                    ·
                      rfl

theorem cell22_3423242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 2, 1, 5].length) (baseStart_3423242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3423242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3423242 prefixEnd_3423242 := by exact prefixLift 3423242
  have htrace : WordTrace (prefixWord ++ tailWord_3423242) baseStart_3423242 baseEnd_3423242 := by
    simpa [prefixWord, tailWord_3423242, baseEnd_3423242] using wordTrace_append hprefix tailTrace_3423242
  have hstable : (prefixWord ++ tailWord_3423242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423242).length < 2 ^ (prefixWord ++ tailWord_3423242).sum := by decide
  have hdescent : baseEnd_3423242 < baseStart_3423242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423244 : List Nat := [2, 2, 1, 2, 3, 3, 2, 3, 4]
def baseStart_3423244 : Nat := 118140960795 + 3423244 * 2 ^ 59
def prefixEnd_3423244 : Nat := 4983230072969 + 3 ^ 40 * 3423244 * 2
def baseEnd_3423244 : Nat := 390615459915535505734843

theorem tailTrace_3423244 : CollatzResearch.WordTrace tailWord_3423244 prefixEnd_3423244 390615459915535505734843 := by
  unfold tailWord_3423244
  simp only [CollatzResearch.WordTrace]
  refine ⟨62427983005089553187230393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83237310673452737582973857 62427983005089553187230393)
  ·
    refine ⟨46820987253817164890422795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62427983005089553187230393 46820987253817164890422795)
    ·
      refine ⟨70231480880725747335634193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46820987253817164890422795 70231480880725747335634193)
      ·
        refine ⟨52673610660544310501725645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70231480880725747335634193 52673610660544310501725645)
        ·
          refine ⟨19752603997704116438147117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52673610660544310501725645 19752603997704116438147117)
          ·
            refine ⟨7407226499139043664305169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19752603997704116438147117 7407226499139043664305169)
            ·
              refine ⟨5555419874354282748228877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7407226499139043664305169 5555419874354282748228877)
              ·
                refine ⟨2083282452882856030585829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5555419874354282748228877 2083282452882856030585829)
                ·
                  refine ⟨390615459915535505734843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2083282452882856030585829 390615459915535505734843)
                  ·
                    rfl

theorem cell22_3423244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 3, 4].length) (baseStart_3423244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3423244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3423244 prefixEnd_3423244 := by exact prefixLift 3423244
  have htrace : WordTrace (prefixWord ++ tailWord_3423244) baseStart_3423244 baseEnd_3423244 := by
    simpa [prefixWord, tailWord_3423244, baseEnd_3423244] using wordTrace_append hprefix tailTrace_3423244
  have hstable : (prefixWord ++ tailWord_3423244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423244).length < 2 ^ (prefixWord ++ tailWord_3423244).sum := by decide
  have hdescent : baseEnd_3423244 < baseStart_3423244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423246 : List Nat := [4, 1, 1, 2, 2, 4, 2, 1, 1, 4]
def baseStart_3423246 : Nat := 118140960795 + 3423246 * 2 ^ 59
def prefixEnd_3423246 : Nat := 4983230072969 + 3 ^ 40 * 3423246 * 2
def baseEnd_3423246 : Nat := 1171847064387479178654523

theorem tailTrace_3423246 : CollatzResearch.WordTrace tailWord_3423246 prefixEnd_3423246 1171847064387479178654523 := by
  unfold tailWord_3423246
  simp only [CollatzResearch.WordTrace]
  refine ⟨15607004869521482589504199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83237359304114573810689061 15607004869521482589504199)
  ·
    refine ⟨23410507304282223884256299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15607004869521482589504199 23410507304282223884256299)
    ·
      refine ⟨35115760956423335826384449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23410507304282223884256299 35115760956423335826384449)
      ·
        refine ⟨26336820717317501869788337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35115760956423335826384449 26336820717317501869788337)
        ·
          refine ⟨19752615537988126402341253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26336820717317501869788337 19752615537988126402341253)
          ·
            refine ⟨3703615413372773700438985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19752615537988126402341253 3703615413372773700438985)
            ·
              refine ⟨2777711560029580275329239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3703615413372773700438985 2777711560029580275329239)
              ·
                refine ⟨4166567340044370412993859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2777711560029580275329239 4166567340044370412993859)
                ·
                  refine ⟨6249851010066555619490789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4166567340044370412993859 6249851010066555619490789)
                  ·
                    refine ⟨1171847064387479178654523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6249851010066555619490789 1171847064387479178654523)
                    ·
                      rfl

theorem cell22_3423246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 2, 1, 1, 4].length) (baseStart_3423246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3423246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3423246 prefixEnd_3423246 := by exact prefixLift 3423246
  have htrace : WordTrace (prefixWord ++ tailWord_3423246) baseStart_3423246 baseEnd_3423246 := by
    simpa [prefixWord, tailWord_3423246, baseEnd_3423246] using wordTrace_append hprefix tailTrace_3423246
  have hstable : (prefixWord ++ tailWord_3423246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423246).length < 2 ^ (prefixWord ++ tailWord_3423246).sum := by decide
  have hdescent : baseEnd_3423246 < baseStart_3423246 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423250 : List Nat := [3, 2, 5, 1, 2, 1, 1, 2, 5]
def baseStart_3423250 : Nat := 118140960795 + 3423250 * 2 ^ 59
def prefixEnd_3423250 : Nat := 4983230072969 + 3 ^ 40 * 3423250 * 2
def baseEnd_3423250 : Nat := 390616144556408167184837

theorem tailTrace_3423250 : CollatzResearch.WordTrace tailWord_3423250 prefixEnd_3423250 390616144556408167184837 := by
  unfold tailWord_3423250
  simp only [CollatzResearch.WordTrace]
  refine ⟨31214046212039342349794801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83237456565438246266119469 31214046212039342349794801)
  ·
    refine ⟨23410534659029506762346101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31214046212039342349794801 23410534659029506762346101)
    ·
      refine ⟨2194737624284016258969947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23410534659029506762346101 2194737624284016258969947)
      ·
        refine ⟨3292106436426024388454921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2194737624284016258969947 3292106436426024388454921)
        ·
          refine ⟨2469079827319518291341191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3292106436426024388454921 2469079827319518291341191)
          ·
            refine ⟨3703619740979277437011787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2469079827319518291341191 3703619740979277437011787)
            ·
              refine ⟨5555429611468916155517681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3703619740979277437011787 5555429611468916155517681)
              ·
                refine ⟨4166572208601687116638261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5555429611468916155517681 4166572208601687116638261)
                ·
                  refine ⟨390616144556408167184837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4166572208601687116638261 390616144556408167184837)
                  ·
                    rfl

theorem cell22_3423250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 2, 5].length) (baseStart_3423250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3423250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3423250 prefixEnd_3423250 := by exact prefixLift 3423250
  have htrace : WordTrace (prefixWord ++ tailWord_3423250) baseStart_3423250 baseEnd_3423250 := by
    simpa [prefixWord, tailWord_3423250, baseEnd_3423250] using wordTrace_append hprefix tailTrace_3423250
  have hstable : (prefixWord ++ tailWord_3423250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423250).length < 2 ^ (prefixWord ++ tailWord_3423250).sum := by decide
  have hdescent : baseEnd_3423250 < baseStart_3423250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423289 : List Nat := [1, 2, 1, 5, 2, 3, 2, 6]
def baseStart_3423289 : Nat := 118140960795 + 3423289 * 2 ^ 59
def prefixEnd_3423289 : Nat := 4983230072969 + 3 ^ 40 * 3423289 * 2
def baseEnd_3423289 : Nat := 130206864907360155536599

theorem tailTrace_3423289 : CollatzResearch.WordTrace tailWord_3423289 prefixEnd_3423289 130206864907360155536599 := by
  unfold tailWord_3423289
  simp only [CollatzResearch.WordTrace]
  refine ⟨124857607295016079059848921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83238404863344052706565947 124857607295016079059848921)
  ·
    refine ⟨93643205471262059294886691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124857607295016079059848921 93643205471262059294886691)
    ·
      refine ⟨140464808206893088942330037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93643205471262059294886691 140464808206893088942330037)
      ·
        refine ⟨13168575769396227088343441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 140464808206893088942330037 13168575769396227088343441)
        ·
          refine ⟨9876431827047170316257581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13168575769396227088343441 9876431827047170316257581)
          ·
            refine ⟨3703661935142688868596593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9876431827047170316257581 3703661935142688868596593)
            ·
              refine ⟨2777746451357016651447445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3703661935142688868596593 2777746451357016651447445)
              ·
                refine ⟨130206864907360155536599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2777746451357016651447445 130206864907360155536599)
                ·
                  rfl

theorem cell22_3423289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 2, 6].length) (baseStart_3423289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3423289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3423289 prefixEnd_3423289 := by exact prefixLift 3423289
  have htrace : WordTrace (prefixWord ++ tailWord_3423289) baseStart_3423289 baseEnd_3423289 := by
    simpa [prefixWord, tailWord_3423289, baseEnd_3423289] using wordTrace_append hprefix tailTrace_3423289
  have hstable : (prefixWord ++ tailWord_3423289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423289).length < 2 ^ (prefixWord ++ tailWord_3423289).sum := by decide
  have hdescent : baseEnd_3423289 < baseStart_3423289 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423317 : List Nat := [1, 3, 2, 2, 1, 2, 2, 4, 5]
def baseStart_3423317 : Nat := 118140960795 + 3423317 * 2 ^ 59
def prefixEnd_3423317 : Nat := 4983230072969 + 3 ^ 40 * 3423317 * 2
def baseEnd_3423317 : Nat := 390623789712819553376435

theorem tailTrace_3423317 : CollatzResearch.WordTrace tailWord_3423317 prefixEnd_3423317 390623789712819553376435 := by
  unfold tailWord_3423317
  simp only [CollatzResearch.WordTrace]
  refine ⟨124858628538914639841868205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83239085692609759894578803 124858628538914639841868205)
  ·
    refine ⟨46821985702092989940700577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124858628538914639841868205 46821985702092989940700577)
    ·
      refine ⟨35116489276569742455525433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46821985702092989940700577 35116489276569742455525433)
      ·
        refine ⟨26337366957427306841644075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35116489276569742455525433 26337366957427306841644075)
        ·
          refine ⟨39506050436140960262466113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26337366957427306841644075 39506050436140960262466113)
          ·
            refine ⟨29629537827105720196849585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39506050436140960262466113 29629537827105720196849585)
            ·
              refine ⟨22222153370329290147637189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29629537827105720196849585 22222153370329290147637189)
              ·
                refine ⟨4166653756936741902681973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22222153370329290147637189 4166653756936741902681973)
                ·
                  refine ⟨390623789712819553376435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4166653756936741902681973 390623789712819553376435)
                  ·
                    rfl

theorem cell22_3423317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 4, 5].length) (baseStart_3423317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3423317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3423317 prefixEnd_3423317 := by exact prefixLift 3423317
  have htrace : WordTrace (prefixWord ++ tailWord_3423317) baseStart_3423317 baseEnd_3423317 := by
    simpa [prefixWord, tailWord_3423317, baseEnd_3423317] using wordTrace_append hprefix tailTrace_3423317
  have hstable : (prefixWord ++ tailWord_3423317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423317).length < 2 ^ (prefixWord ++ tailWord_3423317).sum := by decide
  have hdescent : baseEnd_3423317 < baseStart_3423317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423392 : List Nat := [2, 1, 1, 4, 2, 1, 2, 2, 1, 6]
def baseStart_3423392 : Nat := 118140960795 + 3423392 * 2 ^ 59
def prefixEnd_3423392 : Nat := 4983230072969 + 3 ^ 40 * 3423392 * 2
def baseEnd_3423392 : Nat := 1171897043171183464504075

theorem tailTrace_3423392 : CollatzResearch.WordTrace tailWord_3423392 prefixEnd_3423392 1171897043171183464504075 := by
  unfold tailWord_3423392
  simp only [CollatzResearch.WordTrace]
  refine ⟨62430682006821463825424215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83240909342428618433898953 62430682006821463825424215)
  ·
    refine ⟨93646023010232195738136323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62430682006821463825424215 93646023010232195738136323)
    ·
      refine ⟨140469034515348293607204485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93646023010232195738136323 140469034515348293607204485)
      ·
        refine ⟨26337943971627805051350841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140469034515348293607204485 26337943971627805051350841)
        ·
          refine ⟨19753457978720853788513131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26337943971627805051350841 19753457978720853788513131)
          ·
            refine ⟨29630186968081280682769697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19753457978720853788513131 29630186968081280682769697)
            ·
              refine ⟨22222640226060960512077273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29630186968081280682769697 22222640226060960512077273)
              ·
                refine ⟨16666980169545720384057955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22222640226060960512077273 16666980169545720384057955)
                ·
                  refine ⟨25000470254318580576086933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16666980169545720384057955 25000470254318580576086933)
                  ·
                    refine ⟨1171897043171183464504075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25000470254318580576086933 1171897043171183464504075)
                    ·
                      rfl

theorem cell22_3423392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 1, 6].length) (baseStart_3423392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3423392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3423392 prefixEnd_3423392 := by exact prefixLift 3423392
  have htrace : WordTrace (prefixWord ++ tailWord_3423392) baseStart_3423392 baseEnd_3423392 := by
    simpa [prefixWord, tailWord_3423392, baseEnd_3423392] using wordTrace_append hprefix tailTrace_3423392
  have hstable : (prefixWord ++ tailWord_3423392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423392).length < 2 ^ (prefixWord ++ tailWord_3423392).sum := by decide
  have hdescent : baseEnd_3423392 < baseStart_3423392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423409 : List Nat := [1, 2, 2, 5, 1, 2, 1, 1, 1, 6]
def baseStart_3423409 : Nat := 118140960795 + 3423409 * 2 ^ 59
def prefixEnd_3423409 : Nat := 4983230072969 + 3 ^ 40 * 3423409 * 2
def baseEnd_3423409 : Nat := 1171902862618601086829023

theorem tailTrace_3423409 : CollatzResearch.WordTrace tailWord_3423409 prefixEnd_3423409 1171902862618601086829023 := by
  unfold tailWord_3423409
  simp only [CollatzResearch.WordTrace]
  refine ⟨124861984054581339554217281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83241322703054226369478187 124861984054581339554217281)
  ·
    refine ⟨93646488040936004665662961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124861984054581339554217281 93646488040936004665662961)
    ·
      refine ⟨70234866030702003499247221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93646488040936004665662961 70234866030702003499247221)
      ·
        refine ⟨6584518690378312828054427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70234866030702003499247221 6584518690378312828054427)
        ·
          refine ⟨9876778035567469242081641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6584518690378312828054427 9876778035567469242081641)
          ·
            refine ⟨7407583526675601931561231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9876778035567469242081641 7407583526675601931561231)
            ·
              refine ⟨11111375290013402897341847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7407583526675601931561231 11111375290013402897341847)
              ·
                refine ⟨16667062935020104346012771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11111375290013402897341847 16667062935020104346012771)
                ·
                  refine ⟨25000594402530156519019157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16667062935020104346012771 25000594402530156519019157)
                  ·
                    refine ⟨1171902862618601086829023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25000594402530156519019157 1171902862618601086829023)
                    ·
                      rfl

theorem cell22_3423409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 6].length) (baseStart_3423409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3423409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3423409 prefixEnd_3423409 := by exact prefixLift 3423409
  have htrace : WordTrace (prefixWord ++ tailWord_3423409) baseStart_3423409 baseEnd_3423409 := by
    simpa [prefixWord, tailWord_3423409, baseEnd_3423409] using wordTrace_append hprefix tailTrace_3423409
  have hstable : (prefixWord ++ tailWord_3423409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423409).length < 2 ^ (prefixWord ++ tailWord_3423409).sum := by decide
  have hdescent : baseEnd_3423409 < baseStart_3423409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423430 : List Nat := [6, 1, 2, 2, 1, 1, 2, 1, 6]
def baseStart_3423430 : Nat := 118140960795 + 3423430 * 2 ^ 59
def prefixEnd_3423430 : Nat := 4983230072969 + 3 ^ 40 * 3423430 * 2
def baseEnd_3423430 : Nat := 390636683782588010684653

theorem tailTrace_3423430 : CollatzResearch.WordTrace tailWord_3423430 prefixEnd_3423430 390636683782588010684653 := by
  unfold tailWord_3423430
  simp only [CollatzResearch.WordTrace]
  refine ⟨3901960937109539379397867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 83241833325003506760487829 3901960937109539379397867)
  ·
    refine ⟨5852941405664309069096801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3901960937109539379397867 5852941405664309069096801)
    ·
      refine ⟨4389706054248231801822601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5852941405664309069096801 4389706054248231801822601)
      ·
        refine ⟨3292279540686173851366951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4389706054248231801822601 3292279540686173851366951)
        ·
          refine ⟨4938419311029260777050427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3292279540686173851366951 4938419311029260777050427)
          ·
            refine ⟨7407628966543891165575641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4938419311029260777050427 7407628966543891165575641)
            ·
              refine ⟨5555721724907918374181731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7407628966543891165575641 5555721724907918374181731)
              ·
                refine ⟨8333582587361877561272597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5555721724907918374181731 8333582587361877561272597)
                ·
                  refine ⟨390636683782588010684653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8333582587361877561272597 390636683782588010684653)
                  ·
                    rfl

theorem cell22_3423430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_3423430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3423430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3423430 prefixEnd_3423430 := by exact prefixLift 3423430
  have htrace : WordTrace (prefixWord ++ tailWord_3423430) baseStart_3423430 baseEnd_3423430 := by
    simpa [prefixWord, tailWord_3423430, baseEnd_3423430] using wordTrace_append hprefix tailTrace_3423430
  have hstable : (prefixWord ++ tailWord_3423430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423430).length < 2 ^ (prefixWord ++ tailWord_3423430).sum := by decide
  have hdescent : baseEnd_3423430 < baseStart_3423430 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423469 : List Nat := [1, 5, 1, 2, 2, 1, 1, 2, 7]
def baseStart_3423469 : Nat := 118140960795 + 3423469 * 2 ^ 59
def prefixEnd_3423469 : Nat := 4983230072969 + 3 ^ 40 * 3423469 * 2
def baseEnd_3423469 : Nat := 390641133948260310109613

theorem tailTrace_3423469 : CollatzResearch.WordTrace tailWord_3423469 prefixEnd_3423469 390641133948260310109613 := by
  unfold tailWord_3423469
  simp only [CollatzResearch.WordTrace]
  refine ⟨124864172434363969801401461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83242781622909313200934307 124864172434363969801401461)
  ·
    refine ⟨11706016165721622168881387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 124864172434363969801401461 11706016165721622168881387)
    ·
      refine ⟨17559024248582433253322081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11706016165721622168881387 17559024248582433253322081)
      ·
        refine ⟨13169268186436824939991561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17559024248582433253322081 13169268186436824939991561)
        ·
          refine ⟨9876951139827618704993671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13169268186436824939991561 9876951139827618704993671)
          ·
            refine ⟨14815426709741428057490507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9876951139827618704993671 14815426709741428057490507)
            ·
              refine ⟨22223140064612142086235761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14815426709741428057490507 22223140064612142086235761)
              ·
                refine ⟨16667355048459106564676821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22223140064612142086235761 16667355048459106564676821)
                ·
                  refine ⟨390641133948260310109613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16667355048459106564676821 390641133948260310109613)
                  ·
                    rfl

theorem cell22_3423469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_3423469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3423469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3423469 prefixEnd_3423469 := by exact prefixLift 3423469
  have htrace : WordTrace (prefixWord ++ tailWord_3423469) baseStart_3423469 baseEnd_3423469 := by
    simpa [prefixWord, tailWord_3423469, baseEnd_3423469] using wordTrace_append hprefix tailTrace_3423469
  have hstable : (prefixWord ++ tailWord_3423469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423469).length < 2 ^ (prefixWord ++ tailWord_3423469).sum := by decide
  have hdescent : baseEnd_3423469 < baseStart_3423469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423490 : List Nat := [3, 4, 1, 1, 3, 2, 1, 1, 3, 3]
def baseStart_3423490 : Nat := 118140960795 + 3423490 * 2 ^ 59
def prefixEnd_3423490 : Nat := 4983230072969 + 3 ^ 40 * 3423490 * 2
def baseEnd_3423490 : Nat := 1171930590573943875553775

theorem tailTrace_3423490 : CollatzResearch.WordTrace tailWord_3423490 prefixEnd_3423490 1171930590573943875553775 := by
  unfold tailWord_3423490
  simp only [CollatzResearch.WordTrace]
  refine ⟨31216234591821972596978981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83243292244858593591943949 31216234591821972596978981)
  ·
    refine ⟨5853043985966619861933559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31216234591821972596978981 5853043985966619861933559)
    ·
      refine ⟨8779565978949929792900339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5853043985966619861933559 8779565978949929792900339)
      ·
        refine ⟨13169348968424894689350509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8779565978949929792900339 13169348968424894689350509)
        ·
          refine ⟨4938505863159335508506441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13169348968424894689350509 4938505863159335508506441)
          ·
            refine ⟨3703879397369501631379831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4938505863159335508506441 3703879397369501631379831)
            ·
              refine ⟨5555819096054252447069747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3703879397369501631379831 5555819096054252447069747)
              ·
                refine ⟨8333728644081378670604621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5555819096054252447069747 8333728644081378670604621)
                ·
                  refine ⟨3125148241530517001476733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8333728644081378670604621 3125148241530517001476733)
                  ·
                    refine ⟨1171930590573943875553775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3125148241530517001476733 1171930590573943875553775)
                    ·
                      rfl

theorem cell22_3423490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_3423490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3423490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3423490 prefixEnd_3423490 := by exact prefixLift 3423490
  have htrace : WordTrace (prefixWord ++ tailWord_3423490) baseStart_3423490 baseEnd_3423490 := by
    simpa [prefixWord, tailWord_3423490, baseEnd_3423490] using wordTrace_append hprefix tailTrace_3423490
  have hstable : (prefixWord ++ tailWord_3423490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423490).length < 2 ^ (prefixWord ++ tailWord_3423490).sum := by decide
  have hdescent : baseEnd_3423490 < baseStart_3423490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423516 : List Nat := [2, 2, 3, 1, 1, 1, 5, 2, 1, 4]
def baseStart_3423516 : Nat := 118140960795 + 3423516 * 2 ^ 59
def prefixEnd_3423516 : Nat := 4983230072969 + 3 ^ 40 * 3423516 * 2
def baseEnd_3423516 : Nat := 1171939490905288474403695

theorem tailTrace_3423516 : CollatzResearch.WordTrace tailWord_3423516 prefixEnd_3423516 1171939490905288474403695 := by
  unfold tailWord_3423516
  simp only [CollatzResearch.WordTrace]
  refine ⟨62432943332596848414181201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83243924443462464552241601 62432943332596848414181201)
  ·
    refine ⟨46824707499447636310635901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62432943332596848414181201 46824707499447636310635901)
    ·
      refine ⟨17559265312292863616488463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46824707499447636310635901 17559265312292863616488463)
      ·
        refine ⟨26338897968439295424732695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17559265312292863616488463 26338897968439295424732695)
        ·
          refine ⟨39508346952658943137099043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26338897968439295424732695 39508346952658943137099043)
          ·
            refine ⟨59262520428988414705648565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39508346952658943137099043 59262520428988414705648565)
            ·
              refine ⟨5555861290217663878654553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59262520428988414705648565 5555861290217663878654553)
              ·
                refine ⟨4166895967663247908990915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5555861290217663878654553 4166895967663247908990915)
                ·
                  refine ⟨6250343951494871863486373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4166895967663247908990915 6250343951494871863486373)
                  ·
                    refine ⟨1171939490905288474403695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6250343951494871863486373 1171939490905288474403695)
                    ·
                      rfl

theorem cell22_3423516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_3423516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3423516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3423516 prefixEnd_3423516 := by exact prefixLift 3423516
  have htrace : WordTrace (prefixWord ++ tailWord_3423516) baseStart_3423516 baseEnd_3423516 := by
    simpa [prefixWord, tailWord_3423516, baseEnd_3423516] using wordTrace_append hprefix tailTrace_3423516
  have hstable : (prefixWord ++ tailWord_3423516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423516).length < 2 ^ (prefixWord ++ tailWord_3423516).sum := by decide
  have hdescent : baseEnd_3423516 < baseStart_3423516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423548 : List Nat := [2, 2, 2, 2, 1, 3, 4, 2, 4]
def baseStart_3423548 : Nat := 118140960795 + 3423548 * 2 ^ 59
def prefixEnd_3423548 : Nat := 4983230072969 + 3 ^ 40 * 3423548 * 2
def baseEnd_3423548 : Nat := 390650148386417019201199

theorem tailTrace_3423548 : CollatzResearch.WordTrace tailWord_3423548 prefixEnd_3423548 390650148386417019201199 := by
  unfold tailWord_3423548
  simp only [CollatzResearch.WordTrace]
  refine ⟨62433526900538883146763649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83244702534051844195684865 62433526900538883146763649)
  ·
    refine ⟨46825145175404162360072737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62433526900538883146763649 46825145175404162360072737)
    ·
      refine ⟨35118858881553121770054553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46825145175404162360072737 35118858881553121770054553)
      ·
        refine ⟨26339144161164841327540915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35118858881553121770054553 26339144161164841327540915)
        ·
          refine ⟨39508716241747261991311373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26339144161164841327540915 39508716241747261991311373)
          ·
            refine ⟨14815768590655223246741765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39508716241747261991311373 14815768590655223246741765)
            ·
              refine ⟨2777956610747854358764081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14815768590655223246741765 2777956610747854358764081)
              ·
                refine ⟨2083467458060890769073061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2777956610747854358764081 2083467458060890769073061)
                ·
                  refine ⟨390650148386417019201199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2083467458060890769073061 390650148386417019201199)
                  ·
                    rfl

theorem cell22_3423548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 4, 2, 4].length) (baseStart_3423548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3423548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3423548 prefixEnd_3423548 := by exact prefixLift 3423548
  have htrace : WordTrace (prefixWord ++ tailWord_3423548) baseStart_3423548 baseEnd_3423548 := by
    simpa [prefixWord, tailWord_3423548, baseEnd_3423548] using wordTrace_append hprefix tailTrace_3423548
  have hstable : (prefixWord ++ tailWord_3423548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423548).length < 2 ^ (prefixWord ++ tailWord_3423548).sum := by decide
  have hdescent : baseEnd_3423548 < baseStart_3423548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423559 : List Nat := [1, 1, 4, 1, 2, 3, 3, 7]
def baseStart_3423559 : Nat := 118140960795 + 3423559 * 2 ^ 59
def prefixEnd_3423559 : Nat := 4983230072969 + 3 ^ 40 * 3423559 * 2
def baseEnd_3423559 : Nat := 130217134520450077286507

theorem tailTrace_3423559 : CollatzResearch.WordTrace tailWord_3423559 prefixEnd_3423559 130217134520450077286507 := by
  unfold tailWord_3423559
  simp only [CollatzResearch.WordTrace]
  refine ⟨124867455004037915172177731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83244970002691943448118487 124867455004037915172177731)
  ·
    refine ⟨187301182506056872758266597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124867455004037915172177731 187301182506056872758266597)
    ·
      refine ⟨35118971719885663642174987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187301182506056872758266597 35118971719885663642174987)
      ·
        refine ⟨52678457579828495463262481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35118971719885663642174987 52678457579828495463262481)
        ·
          refine ⟨39508843184871371597446861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52678457579828495463262481 39508843184871371597446861)
          ·
            refine ⟨14815816194326764349042573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39508843184871371597446861 14815816194326764349042573)
            ·
              refine ⟨5555931072872536630890965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14815816194326764349042573 5555931072872536630890965)
              ·
                refine ⟨130217134520450077286507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5555931072872536630890965 130217134520450077286507)
                ·
                  rfl

theorem cell22_3423559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 7].length) (baseStart_3423559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3423559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3423559 prefixEnd_3423559 := by exact prefixLift 3423559
  have htrace : WordTrace (prefixWord ++ tailWord_3423559) baseStart_3423559 baseEnd_3423559 := by
    simpa [prefixWord, tailWord_3423559, baseEnd_3423559] using wordTrace_append hprefix tailTrace_3423559
  have hstable : (prefixWord ++ tailWord_3423559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423559).length < 2 ^ (prefixWord ++ tailWord_3423559).sum := by decide
  have hdescent : baseEnd_3423559 < baseStart_3423559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423614 : List Nat := [4, 2, 3, 2, 1, 1, 3, 1, 2, 3]
def baseStart_3423614 : Nat := 118140960795 + 3423614 * 2 ^ 59
def prefixEnd_3423614 : Nat := 4983230072969 + 3 ^ 40 * 3423614 * 2
def baseEnd_3423614 : Nat := 1171973038308048885453395

theorem tailTrace_3423614 : CollatzResearch.WordTrace tailWord_3423614 prefixEnd_3423614 1171973038308048885453395 := by
  unfold tailWord_3423614
  simp only [CollatzResearch.WordTrace]
  refine ⟨15608682627354832445678737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83246307345892439710286597 15608682627354832445678737)
  ·
    refine ⟨11706511970516124334259053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15608682627354832445678737 11706511970516124334259053)
    ·
      refine ⟨4389941988943546625347145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11706511970516124334259053 4389941988943546625347145)
      ·
        refine ⟨3292456491707659969010359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4389941988943546625347145 3292456491707659969010359)
        ·
          refine ⟨4938684737561489953515539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3292456491707659969010359 4938684737561489953515539)
          ·
            refine ⟨7408027106342234930273309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4938684737561489953515539 7408027106342234930273309)
            ·
              refine ⟨2778010164878338098852491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7408027106342234930273309 2778010164878338098852491)
              ·
                refine ⟨4167015247317507148278737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2778010164878338098852491 4167015247317507148278737)
                ·
                  refine ⟨3125261435488130361209053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4167015247317507148278737 3125261435488130361209053)
                  ·
                    refine ⟨1171973038308048885453395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3125261435488130361209053 1171973038308048885453395)
                    ·
                      rfl

theorem cell22_3423614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_3423614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3423614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3423614 prefixEnd_3423614 := by exact prefixLift 3423614
  have htrace : WordTrace (prefixWord ++ tailWord_3423614) baseStart_3423614 baseEnd_3423614 := by
    simpa [prefixWord, tailWord_3423614, baseEnd_3423614] using wordTrace_append hprefix tailTrace_3423614
  have hstable : (prefixWord ++ tailWord_3423614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423614).length < 2 ^ (prefixWord ++ tailWord_3423614).sum := by decide
  have hdescent : baseEnd_3423614 < baseStart_3423614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423651 : List Nat := [1, 1, 1, 4, 1, 3, 1, 5, 1, 4]
def baseStart_3423651 : Nat := 118140960795 + 3423651 * 2 ^ 59
def prefixEnd_3423651 : Nat := 4983230072969 + 3 ^ 40 * 3423651 * 2
def baseEnd_3423651 : Nat := 1171985704164193122278281

theorem tailTrace_3423651 : CollatzResearch.WordTrace tailWord_3423651 prefixEnd_3423651 1171985704164193122278281 := by
  unfold tailWord_3423651
  simp only [CollatzResearch.WordTrace]
  refine ⟨124870810519704614884526807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83247207013136409923017871 124870810519704614884526807)
  ·
    refine ⟨187306215779556922326790211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124870810519704614884526807 187306215779556922326790211)
    ·
      refine ⟨280959323669335383490185317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187306215779556922326790211 280959323669335383490185317)
      ·
        refine ⟨52679873188000384404409747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 280959323669335383490185317 52679873188000384404409747)
        ·
          refine ⟨79019809782000576606614621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52679873188000384404409747 79019809782000576606614621)
          ·
            refine ⟨29632428668250216227480483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79019809782000576606614621 29632428668250216227480483)
            ·
              refine ⟨44448643002375324341220725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29632428668250216227480483 44448643002375324341220725)
              ·
                refine ⟨4167060281472686656989443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44448643002375324341220725 4167060281472686656989443)
                ·
                  refine ⟨6250590422209029985484165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4167060281472686656989443 6250590422209029985484165)
                  ·
                    refine ⟨1171985704164193122278281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6250590422209029985484165 1171985704164193122278281)
                    ·
                      rfl

theorem cell22_3423651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 5, 1, 4].length) (baseStart_3423651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3423651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3423651 prefixEnd_3423651 := by exact prefixLift 3423651
  have htrace : WordTrace (prefixWord ++ tailWord_3423651) baseStart_3423651 baseEnd_3423651 := by
    simpa [prefixWord, tailWord_3423651, baseEnd_3423651] using wordTrace_append hprefix tailTrace_3423651
  have hstable : (prefixWord ++ tailWord_3423651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423651).length < 2 ^ (prefixWord ++ tailWord_3423651).sum := by decide
  have hdescent : baseEnd_3423651 < baseStart_3423651 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423664 : List Nat := [2, 1, 1, 1, 2, 1, 1, 3, 5, 5]
def baseStart_3423664 : Nat := 118140960795 + 3423664 * 2 ^ 59
def prefixEnd_3423664 : Nat := 4983230072969 + 3 ^ 40 * 3423664 * 2
def baseEnd_3423664 : Nat := 1171990154329865421703241

theorem tailTrace_3423664 : CollatzResearch.WordTrace tailWord_3423664 prefixEnd_3423664 1171990154329865421703241 := by
  unfold tailWord_3423664
  simp only [CollatzResearch.WordTrace]
  refine ⟨62435642334328759052375023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83247523112438345403166697 62435642334328759052375023)
  ·
    refine ⟨93653463501493138578562535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62435642334328759052375023 93653463501493138578562535)
    ·
      refine ⟨140480195252239707867843803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93653463501493138578562535 140480195252239707867843803)
      ·
        refine ⟨210720292878359561801765705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140480195252239707867843803 210720292878359561801765705)
        ·
          refine ⟨158040219658769671351324279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210720292878359561801765705 158040219658769671351324279)
          ·
            refine ⟨237060329488154507026986419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158040219658769671351324279 237060329488154507026986419)
            ·
              refine ⟨355590494232231760540479629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237060329488154507026986419 355590494232231760540479629)
              ·
                refine ⟨133346435337086910202679861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 355590494232231760540479629 133346435337086910202679861)
                ·
                  refine ⟨12501228312851897831501237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 133346435337086910202679861 12501228312851897831501237)
                  ·
                    refine ⟨1171990154329865421703241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12501228312851897831501237 1171990154329865421703241)
                    ·
                      rfl

theorem cell22_3423664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 5, 5].length) (baseStart_3423664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3423664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3423664 prefixEnd_3423664 := by exact prefixLift 3423664
  have htrace : WordTrace (prefixWord ++ tailWord_3423664) baseStart_3423664 baseEnd_3423664 := by
    simpa [prefixWord, tailWord_3423664, baseEnd_3423664] using wordTrace_append hprefix tailTrace_3423664
  have hstable : (prefixWord ++ tailWord_3423664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423664).length < 2 ^ (prefixWord ++ tailWord_3423664).sum := by decide
  have hdescent : baseEnd_3423664 < baseStart_3423664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423679 : List Nat := [1, 1, 2, 2, 2, 1, 1, 3, 3, 6]
def baseStart_3423679 : Nat := 118140960795 + 3423679 * 2 ^ 59
def prefixEnd_3423679 : Nat := 4983230072969 + 3 ^ 40 * 3423679 * 2
def baseEnd_3423679 : Nat := 1171995289136410382578195

theorem tailTrace_3423679 : CollatzResearch.WordTrace tailWord_3423679 prefixEnd_3423679 1171995289136410382578195 := by
  unfold tailWord_3423679
  simp only [CollatzResearch.WordTrace]
  refine ⟨124871831763603175666546091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83247887842402117111030727 124871831763603175666546091)
  ·
    refine ⟨187307747645404763499819137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124871831763603175666546091 187307747645404763499819137)
    ·
      refine ⟨140480810734053572624864353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187307747645404763499819137 140480810734053572624864353)
      ·
        refine ⟨105360608050540179468648265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140480810734053572624864353 105360608050540179468648265)
        ·
          refine ⟨79020456037905134601486199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105360608050540179468648265 79020456037905134601486199)
          ·
            refine ⟨118530684056857701902229299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79020456037905134601486199 118530684056857701902229299)
            ·
              refine ⟨177796026085286552853343949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118530684056857701902229299 177796026085286552853343949)
              ·
                refine ⟨66673509781982457320003981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 177796026085286552853343949 66673509781982457320003981)
                ·
                  refine ⟨25002566168243421495001493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66673509781982457320003981 25002566168243421495001493)
                  ·
                    refine ⟨1171995289136410382578195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25002566168243421495001493 1171995289136410382578195)
                    ·
                      rfl

theorem cell22_3423679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 6].length) (baseStart_3423679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3423679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3423679 prefixEnd_3423679 := by exact prefixLift 3423679
  have htrace : WordTrace (prefixWord ++ tailWord_3423679) baseStart_3423679 baseEnd_3423679 := by
    simpa [prefixWord, tailWord_3423679, baseEnd_3423679] using wordTrace_append hprefix tailTrace_3423679
  have hstable : (prefixWord ++ tailWord_3423679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423679).length < 2 ^ (prefixWord ++ tailWord_3423679).sum := by decide
  have hdescent : baseEnd_3423679 < baseStart_3423679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423702 : List Nat := [5, 2, 1, 1, 1, 3, 3, 1, 1, 4]
def baseStart_3423702 : Nat := 118140960795 + 3423702 * 2 ^ 59
def prefixEnd_3423702 : Nat := 4983230072969 + 3 ^ 40 * 3423702 * 2
def baseEnd_3423702 : Nat := 1172003162506445989253125

theorem tailTrace_3423702 : CollatzResearch.WordTrace tailWord_3423702 prefixEnd_3423702 1172003162506445989253125 := by
  unfold tailWord_3423702
  simp only [CollatzResearch.WordTrace]
  refine ⟨7804541915157490662164585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83248447095013233729755573 7804541915157490662164585)
  ·
    refine ⟨5853406436368117996623439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7804541915157490662164585 5853406436368117996623439)
    ·
      refine ⟨8780109654552176994935159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5853406436368117996623439 8780109654552176994935159)
      ·
        refine ⟨13170164481828265492402739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8780109654552176994935159 13170164481828265492402739)
        ·
          refine ⟨19755246722742398238604109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13170164481828265492402739 19755246722742398238604109)
          ·
            refine ⟨7408217521028399339476541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19755246722742398238604109 7408217521028399339476541)
            ·
              refine ⟨2778081570385649752303703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7408217521028399339476541 2778081570385649752303703)
              ·
                refine ⟨4167122355578474628455555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2778081570385649752303703 4167122355578474628455555)
                ·
                  refine ⟨6250683533367711942683333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4167122355578474628455555 6250683533367711942683333)
                  ·
                    refine ⟨1172003162506445989253125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6250683533367711942683333 1172003162506445989253125)
                    ·
                      rfl

theorem cell22_3423702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_3423702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3423702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3423702 prefixEnd_3423702 := by exact prefixLift 3423702
  have htrace : WordTrace (prefixWord ++ tailWord_3423702) baseStart_3423702 baseEnd_3423702 := by
    simpa [prefixWord, tailWord_3423702, baseEnd_3423702] using wordTrace_append hprefix tailTrace_3423702
  have hstable : (prefixWord ++ tailWord_3423702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423702).length < 2 ^ (prefixWord ++ tailWord_3423702).sum := by decide
  have hdescent : baseEnd_3423702 < baseStart_3423702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423715 : List Nat := [1, 1, 1, 6, 2, 2, 2, 2, 2, 3]
def baseStart_3423715 : Nat := 118140960795 + 3423715 * 2 ^ 59
def prefixEnd_3423715 : Nat := 4983230072969 + 3 ^ 40 * 3423715 * 2
def baseEnd_3423715 : Nat := 1172007612672118288678085

theorem tailTrace_3423715 : CollatzResearch.WordTrace tailWord_3423715 prefixEnd_3423715 1172007612672118288678085 := by
  unfold tailWord_3423715
  simp only [CollatzResearch.WordTrace]
  refine ⟨124873144791472753814856599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83248763194315169209904399 124873144791472753814856599)
  ·
    refine ⟨187309717187209130722284899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124873144791472753814856599 187309717187209130722284899)
    ·
      refine ⟨280964575780813696083427349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187309717187209130722284899 280964575780813696083427349)
      ·
        refine ⟨13170214489725642003910657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 280964575780813696083427349 13170214489725642003910657)
        ·
          refine ⟨9877660867294231502932993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13170214489725642003910657 9877660867294231502932993)
          ·
            refine ⟨7408245650470673627199745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9877660867294231502932993 7408245650470673627199745)
            ·
              refine ⟨5556184237853005220399809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7408245650470673627199745 5556184237853005220399809)
              ·
                refine ⟨4167138178389753915299857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5556184237853005220399809 4167138178389753915299857)
                ·
                  refine ⟨3125353633792315436474893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4167138178389753915299857 3125353633792315436474893)
                  ·
                    refine ⟨1172007612672118288678085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3125353633792315436474893 1172007612672118288678085)
                    ·
                      rfl

theorem cell22_3423715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 2, 2, 3].length) (baseStart_3423715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3423715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3423715 prefixEnd_3423715 := by exact prefixLift 3423715
  have htrace : WordTrace (prefixWord ++ tailWord_3423715) baseStart_3423715 baseEnd_3423715 := by
    simpa [prefixWord, tailWord_3423715, baseEnd_3423715] using wordTrace_append hprefix tailTrace_3423715
  have hstable : (prefixWord ++ tailWord_3423715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423715).length < 2 ^ (prefixWord ++ tailWord_3423715).sum := by decide
  have hdescent : baseEnd_3423715 < baseStart_3423715 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423717 : List Nat := [1, 3, 1, 5, 1, 3, 2, 2, 4]
def baseStart_3423717 : Nat := 118140960795 + 3423717 * 2 ^ 59
def prefixEnd_3423717 : Nat := 4983230072969 + 3 ^ 40 * 3423717 * 2
def baseEnd_3423717 : Nat := 390669432437663650042693

theorem tailTrace_3423717 : CollatzResearch.WordTrace tailWord_3423717 prefixEnd_3423717 390669432437663650042693 := by
  unfold tailWord_3423717
  simp only [CollatzResearch.WordTrace]
  refine ⟨124873217737465508156429405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83248811824977005437619603 124873217737465508156429405)
  ·
    refine ⟨46827456651549565558661027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124873217737465508156429405 46827456651549565558661027)
    ·
      refine ⟨70241184977324348337991541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46827456651549565558661027 70241184977324348337991541)
      ·
        refine ⟨6585111091624157656686707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70241184977324348337991541 6585111091624157656686707)
        ·
          refine ⟨9877666637436236485030061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6585111091624157656686707 9877666637436236485030061)
          ·
            refine ⟨3704124989038588681886273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9877666637436236485030061 3704124989038588681886273)
            ·
              refine ⟨2778093741778941511414705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3704124989038588681886273 2778093741778941511414705)
              ·
                refine ⟨2083570306334206133561029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2778093741778941511414705 2083570306334206133561029)
                ·
                  refine ⟨390669432437663650042693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2083570306334206133561029 390669432437663650042693)
                  ·
                    rfl

theorem cell22_3423717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 2, 2, 4].length) (baseStart_3423717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3423717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3423717 prefixEnd_3423717 := by exact prefixLift 3423717
  have htrace : WordTrace (prefixWord ++ tailWord_3423717) baseStart_3423717 baseEnd_3423717 := by
    simpa [prefixWord, tailWord_3423717, baseEnd_3423717] using wordTrace_append hprefix tailTrace_3423717
  have hstable : (prefixWord ++ tailWord_3423717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423717).length < 2 ^ (prefixWord ++ tailWord_3423717).sum := by decide
  have hdescent : baseEnd_3423717 < baseStart_3423717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423854 : List Nat := [4, 1, 2, 2, 4, 1, 1, 2, 1, 4]
def baseStart_3423854 : Nat := 118140960795 + 3423854 * 2 ^ 59
def prefixEnd_3423854 : Nat := 4983230072969 + 3 ^ 40 * 3423854 * 2
def baseEnd_3423854 : Nat := 1172055195212768259452659

theorem tailTrace_3423854 : CollatzResearch.WordTrace tailWord_3423854 prefixEnd_3423854 1172055195212768259452659 := by
  unfold tailWord_3423854
  simp only [CollatzResearch.WordTrace]
  refine ⟨15609776817246147569270827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83252143025312787036111077 15609776817246147569270827)
  ·
    refine ⟨23414665225869221353906241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15609776817246147569270827 23414665225869221353906241)
    ·
      refine ⟨17560998919401916015429681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23414665225869221353906241 17560998919401916015429681)
      ·
        refine ⟨13170749189551437011572261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17560998919401916015429681 13170749189551437011572261)
        ·
          refine ⟨2469515473040894439669799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13170749189551437011572261 2469515473040894439669799)
          ·
            refine ⟨3704273209561341659504699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2469515473040894439669799 3704273209561341659504699)
            ·
              refine ⟨5556409814342012489257049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3704273209561341659504699 5556409814342012489257049)
              ·
                refine ⟨4167307360756509366942787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5556409814342012489257049 4167307360756509366942787)
                ·
                  refine ⟨6250961041134764050414181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4167307360756509366942787 6250961041134764050414181)
                  ·
                    refine ⟨1172055195212768259452659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6250961041134764050414181 1172055195212768259452659)
                    ·
                      rfl

theorem cell22_3423854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 2, 1, 4].length) (baseStart_3423854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3423854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3423854 prefixEnd_3423854 := by exact prefixLift 3423854
  have htrace : WordTrace (prefixWord ++ tailWord_3423854) baseStart_3423854 baseEnd_3423854 := by
    simpa [prefixWord, tailWord_3423854, baseEnd_3423854] using wordTrace_append hprefix tailTrace_3423854
  have hstable : (prefixWord ++ tailWord_3423854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423854).length < 2 ^ (prefixWord ++ tailWord_3423854).sum := by decide
  have hdescent : baseEnd_3423854 < baseStart_3423854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423880 : List Nat := [2, 1, 3, 5, 2, 9]
def baseStart_3423880 : Nat := 118140960795 + 3423880 * 2 ^ 59
def prefixEnd_3423880 : Nat := 4983230072969 + 3 ^ 40 * 3423880 * 2
def baseEnd_3423880 : Nat := 14469927105482874793859

theorem tailTrace_3423880 : CollatzResearch.WordTrace tailWord_3423880 prefixEnd_3423880 14469927105482874793859 := by
  unfold tailWord_3423880
  simp only [CollatzResearch.WordTrace]
  refine ⟨62439581417937493497306547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83252775223916657996408729 62439581417937493497306547)
  ·
    refine ⟨93659372126906240245959821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62439581417937493497306547 93659372126906240245959821)
    ·
      refine ⟨35122264547589840092234933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93659372126906240245959821 35122264547589840092234933)
      ·
        refine ⟨3292712301336547508647025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35122264547589840092234933 3292712301336547508647025)
        ·
          refine ⟨2469534226002410631485269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3292712301336547508647025 2469534226002410631485269)
          ·
            refine ⟨14469927105482874793859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2469534226002410631485269 14469927105482874793859)
            ·
              rfl

theorem cell22_3423880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 9].length) (baseStart_3423880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3423880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3423880 prefixEnd_3423880 := by exact prefixLift 3423880
  have htrace : WordTrace (prefixWord ++ tailWord_3423880) baseStart_3423880 baseEnd_3423880 := by
    simpa [prefixWord, tailWord_3423880, baseEnd_3423880] using wordTrace_append hprefix tailTrace_3423880
  have hstable : (prefixWord ++ tailWord_3423880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423880).length < 2 ^ (prefixWord ++ tailWord_3423880).sum := by decide
  have hdescent : baseEnd_3423880 < baseStart_3423880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423953 : List Nat := [1, 2, 2, 1, 2, 4, 1, 3, 6]
def baseStart_3423953 : Nat := 118140960795 + 3423953 * 2 ^ 59
def prefixEnd_3423953 : Nat := 4983230072969 + 3 ^ 40 * 3423953 * 2
def baseEnd_3423953 : Nat := 390696361645321667075785

theorem tailTrace_3423953 : CollatzResearch.WordTrace tailWord_3423953 prefixEnd_3423953 390696361645321667075785 := by
  unfold tailWord_3423953
  simp only [CollatzResearch.WordTrace]
  refine ⟨124881825364610520462020513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83254550243073680308013675 124881825364610520462020513)
  ·
    refine ⟨93661369023457890346515385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124881825364610520462020513 93661369023457890346515385)
    ·
      refine ⟨70246026767593417759886539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93661369023457890346515385 70246026767593417759886539)
      ·
        refine ⟨105369040151390126639829809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70246026767593417759886539 105369040151390126639829809)
        ·
          refine ⟨79026780113542594979872357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105369040151390126639829809 79026780113542594979872357)
          ·
            refine ⟨14817521271289236558726067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79026780113542594979872357 14817521271289236558726067)
            ·
              refine ⟨22226281906933854838089101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14817521271289236558726067 22226281906933854838089101)
              ·
                refine ⟨8334855715100195564283413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22226281906933854838089101 8334855715100195564283413)
                ·
                  refine ⟨390696361645321667075785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8334855715100195564283413 390696361645321667075785)
                  ·
                    rfl

theorem cell22_3423953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 3, 6].length) (baseStart_3423953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3423953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3423953 prefixEnd_3423953 := by exact prefixLift 3423953
  have htrace : WordTrace (prefixWord ++ tailWord_3423953) baseStart_3423953 baseEnd_3423953 := by
    simpa [prefixWord, tailWord_3423953, baseEnd_3423953] using wordTrace_append hprefix tailTrace_3423953
  have hstable : (prefixWord ++ tailWord_3423953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423953).length < 2 ^ (prefixWord ++ tailWord_3423953).sum := by decide
  have hdescent : baseEnd_3423953 < baseStart_3423953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423983 : List Nat := [1, 1, 2, 1, 5, 1, 1, 3, 1, 6]
def baseStart_3423983 : Nat := 118140960795 + 3423983 * 2 ^ 59
def prefixEnd_3423983 : Nat := 4983230072969 + 3 ^ 40 * 3423983 * 2
def baseEnd_3423983 : Nat := 1172099354549054922977263

theorem tailTrace_3423983 : CollatzResearch.WordTrace tailWord_3423983 prefixEnd_3423983 1172099354549054922977263 := by
  unfold tailWord_3423983
  simp only [CollatzResearch.WordTrace]
  refine ⟨124882919554501835585612603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83255279703001223723741735 124882919554501835585612603)
  ·
    refine ⟨187324379331752753378418905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124882919554501835585612603 187324379331752753378418905)
    ·
      refine ⟨140493284498814565033814179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187324379331752753378418905 140493284498814565033814179)
      ·
        refine ⟨210739926748221847550721269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140493284498814565033814179 210739926748221847550721269)
        ·
          refine ⟨19756868132645798207880119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 210739926748221847550721269 19756868132645798207880119)
          ·
            refine ⟨29635302198968697311820179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19756868132645798207880119 29635302198968697311820179)
            ·
              refine ⟨44452953298453045967730269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29635302198968697311820179 44452953298453045967730269)
              ·
                refine ⟨16669857486919892237898851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44452953298453045967730269 16669857486919892237898851)
                ·
                  refine ⟨25004786230379838356848277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16669857486919892237898851 25004786230379838356848277)
                  ·
                    refine ⟨1172099354549054922977263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25004786230379838356848277 1172099354549054922977263)
                    ·
                      rfl

theorem cell22_3423983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 6].length) (baseStart_3423983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3423983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3423983 prefixEnd_3423983 := by exact prefixLift 3423983
  have htrace : WordTrace (prefixWord ++ tailWord_3423983) baseStart_3423983 baseEnd_3423983 := by
    simpa [prefixWord, tailWord_3423983, baseEnd_3423983] using wordTrace_append hprefix tailTrace_3423983
  have hstable : (prefixWord ++ tailWord_3423983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423983).length < 2 ^ (prefixWord ++ tailWord_3423983).sum := by decide
  have hdescent : baseEnd_3423983 < baseStart_3423983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423985 : List Nat := [1, 2, 2, 2, 2, 3, 1, 2, 4, 3]
def baseStart_3423985 : Nat := 118140960795 + 3423985 * 2 ^ 59
def prefixEnd_3423985 : Nat := 4983230072969 + 3 ^ 40 * 3423985 * 2
def baseEnd_3423985 : Nat := 1172100039189927584427257

theorem tailTrace_3423985 : CollatzResearch.WordTrace tailWord_3423985 prefixEnd_3423985 1172100039189927584427257 := by
  unfold tailWord_3423985
  simp only [CollatzResearch.WordTrace]
  refine ⟨124882992500494589927185409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83255328333663059951456939 124882992500494589927185409)
  ·
    refine ⟨93662244375370942445389057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124882992500494589927185409 93662244375370942445389057)
    ·
      refine ⟨70246683281528206834041793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93662244375370942445389057 70246683281528206834041793)
      ·
        refine ⟨52685012461146155125531345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70246683281528206834041793 52685012461146155125531345)
        ·
          refine ⟨39513759345859616344148509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52685012461146155125531345 39513759345859616344148509)
          ·
            refine ⟨14817659754697356129055691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39513759345859616344148509 14817659754697356129055691)
            ·
              refine ⟨22226489632046034193583537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14817659754697356129055691 22226489632046034193583537)
              ·
                refine ⟨16669867224034525645187653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22226489632046034193583537 16669867224034525645187653)
                ·
                  refine ⟨3125600104506473558472685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16669867224034525645187653 3125600104506473558472685)
                  ·
                    refine ⟨1172100039189927584427257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3125600104506473558472685 1172100039189927584427257)
                    ·
                      rfl

theorem cell22_3423985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 4, 3].length) (baseStart_3423985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3423985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3423985 prefixEnd_3423985 := by exact prefixLift 3423985
  have htrace : WordTrace (prefixWord ++ tailWord_3423985) baseStart_3423985 baseEnd_3423985 := by
    simpa [prefixWord, tailWord_3423985, baseEnd_3423985] using wordTrace_append hprefix tailTrace_3423985
  have hstable : (prefixWord ++ tailWord_3423985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423985).length < 2 ^ (prefixWord ++ tailWord_3423985).sum := by decide
  have hdescent : baseEnd_3423985 < baseStart_3423985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424002 : List Nat := [3, 4, 1, 1, 1, 1, 1, 3, 4, 3]
def baseStart_3424002 : Nat := 118140960795 + 3424002 * 2 ^ 59
def prefixEnd_3424002 : Nat := 4983230072969 + 3 ^ 40 * 3424002 * 2
def baseEnd_3424002 : Nat := 1172105858637345206752205

theorem tailTrace_3424002 : CollatzResearch.WordTrace tailWord_3424002 prefixEnd_3424002 1172105858637345206752205 := by
  unfold tailWord_3424002
  simp only [CollatzResearch.WordTrace]
  refine ⟨31220903135358250457638565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83255741694288667887036173 31220903135358250457638565)
  ·
    refine ⟨5853919337879671960807231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31220903135358250457638565 5853919337879671960807231)
    ·
      refine ⟨8780879006819507941210847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5853919337879671960807231 8780879006819507941210847)
      ·
        refine ⟨13171318510229261911816271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8780879006819507941210847 13171318510229261911816271)
        ·
          refine ⟨19756977765343892867724407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13171318510229261911816271 19756977765343892867724407)
          ·
            refine ⟨29635466648015839301586611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19756977765343892867724407 29635466648015839301586611)
            ·
              refine ⟨44453199972023758952379917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29635466648015839301586611 44453199972023758952379917)
              ·
                refine ⟨16669949989508909607142469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44453199972023758952379917 16669949989508909607142469)
                ·
                  refine ⟨3125615623032920551339213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16669949989508909607142469 3125615623032920551339213)
                  ·
                    refine ⟨1172105858637345206752205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3125615623032920551339213 1172105858637345206752205)
                    ·
                      rfl

theorem cell22_3424002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_3424002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3424002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3424002 prefixEnd_3424002 := by exact prefixLift 3424002
  have htrace : WordTrace (prefixWord ++ tailWord_3424002) baseStart_3424002 baseEnd_3424002 := by
    simpa [prefixWord, tailWord_3424002, baseEnd_3424002] using wordTrace_append hprefix tailTrace_3424002
  have hstable : (prefixWord ++ tailWord_3424002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424002).length < 2 ^ (prefixWord ++ tailWord_3424002).sum := by decide
  have hdescent : baseEnd_3424002 < baseStart_3424002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424004 : List Nat := [2, 3, 2, 2, 1, 3, 3, 2, 4]
def baseStart_3424004 : Nat := 118140960795 + 3424004 * 2 ^ 59
def prefixEnd_3424004 : Nat := 4983230072969 + 3 ^ 40 * 3424004 * 2
def baseEnd_3424004 : Nat := 390702181092739289400733

theorem tailTrace_3424004 : CollatzResearch.WordTrace tailWord_3424004 prefixEnd_3424004 390702181092739289400733 := by
  unfold tailWord_3424004
  simp only [CollatzResearch.WordTrace]
  refine ⟨62441842743712878086063533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83255790324950504114751377 62441842743712878086063533)
  ·
    refine ⟨23415691028892329282273825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62441842743712878086063533 23415691028892329282273825)
    ·
      refine ⟨17561768271669246961705369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23415691028892329282273825 17561768271669246961705369)
      ·
        refine ⟨13171326203751935221279027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17561768271669246961705369 13171326203751935221279027)
        ·
          refine ⟨19756989305627902831918541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13171326203751935221279027 19756989305627902831918541)
          ·
            refine ⟨7408870989610463561969453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19756989305627902831918541 7408870989610463561969453)
            ·
              refine ⟨2778326621103923835738545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7408870989610463561969453 2778326621103923835738545)
              ·
                refine ⟨2083744965827942876803909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2778326621103923835738545 2083744965827942876803909)
                ·
                  refine ⟨390702181092739289400733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2083744965827942876803909 390702181092739289400733)
                  ·
                    rfl

theorem cell22_3424004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 3, 2, 4].length) (baseStart_3424004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3424004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3424004 prefixEnd_3424004 := by exact prefixLift 3424004
  have htrace : WordTrace (prefixWord ++ tailWord_3424004) baseStart_3424004 baseEnd_3424004 := by
    simpa [prefixWord, tailWord_3424004, baseEnd_3424004] using wordTrace_append hprefix tailTrace_3424004
  have hstable : (prefixWord ++ tailWord_3424004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424004).length < 2 ^ (prefixWord ++ tailWord_3424004).sum := by decide
  have hdescent : baseEnd_3424004 < baseStart_3424004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
