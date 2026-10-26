import V185TrunkScan23Chunk0098

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_586695 : List Nat := [1, 1, 4, 1, 1, 2, 5, 3, 1, 4]
def baseStart_586695 : Nat := 118140960795 + 586695 * 2 ^ 59
def prefixEnd_586695 : Nat := 4983230072969 + 3 ^ 40 * 586695 * 2
def baseEnd_586695 : Nat := 100418844196562428938115

theorem tailTrace_586695 : CollatzResearch.WordTrace tailWord_586695 prefixEnd_586695 100418844196562428938115 := by
  unfold tailWord_586695
  simp only [CollatzResearch.WordTrace]
  refine ⟨21398524609511689373817539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14265683073007792915878359 21398524609511689373817539)
  ·
    refine ⟨32097786914267534060726309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21398524609511689373817539 32097786914267534060726309)
    ·
      refine ⟨6018335046425162636386183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32097786914267534060726309 6018335046425162636386183)
      ·
        refine ⟨9027502569637743954579275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6018335046425162636386183 9027502569637743954579275)
        ·
          refine ⟨13541253854456615931868913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9027502569637743954579275 13541253854456615931868913)
          ·
            refine ⟨10155940390842461948901685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13541253854456615931868913 10155940390842461948901685)
            ·
              refine ⟨952119411641480807709533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10155940390842461948901685 952119411641480807709533)
              ·
                refine ⟨357044779365555302891075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 952119411641480807709533 357044779365555302891075)
                ·
                  refine ⟨535567169048332954336613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 357044779365555302891075 535567169048332954336613)
                  ·
                    refine ⟨100418844196562428938115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 535567169048332954336613 100418844196562428938115)
                    ·
                      rfl

theorem cell23_586695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 3, 1, 4].length) (baseStart_586695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_586695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_586695 prefixEnd_586695 := by exact prefixLift 586695
  have htrace : WordTrace (prefixWord ++ tailWord_586695) baseStart_586695 baseEnd_586695 := by
    simpa [prefixWord, tailWord_586695, baseEnd_586695] using wordTrace_append hprefix tailTrace_586695
  have hstable : (prefixWord ++ tailWord_586695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586695).length < 2 ^ (prefixWord ++ tailWord_586695).sum := by decide
  have hdescent : baseEnd_586695 < baseStart_586695 := by decide
  rcases family_descends (prefixWord ++ tailWord_586695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586712 : List Nat := [2, 1, 2, 2, 2, 4, 3, 2, 1, 4]
def baseStart_586712 : Nat := 118140960795 + 586712 * 2 ^ 59
def prefixEnd_586712 : Nat := 4983230072969 + 3 ^ 40 * 586712 * 2
def baseEnd_586712 : Nat := 100421753920271240100589

theorem tailTrace_586712 : CollatzResearch.WordTrace tailWord_586712 prefixEnd_586712 100421753920271240100589 := by
  unfold tailWord_586712
  simp only [CollatzResearch.WordTrace]
  refine ⟨10699572325225050638593195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14266096433633400851457593 10699572325225050638593195)
  ·
    refine ⟨16049358487837575957889793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10699572325225050638593195 16049358487837575957889793)
    ·
      refine ⟨12037018865878181968417345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16049358487837575957889793 12037018865878181968417345)
      ·
        refine ⟨9027764149408636476313009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12037018865878181968417345 9027764149408636476313009)
        ·
          refine ⟨6770823112056477357234757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9027764149408636476313009 6770823112056477357234757)
          ·
            refine ⟨1269529333510589504481517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6770823112056477357234757 1269529333510589504481517)
            ·
              refine ⟨476073500066471064180569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1269529333510589504481517 476073500066471064180569)
              ·
                refine ⟨357055125049853298135427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 476073500066471064180569 357055125049853298135427)
                ·
                  refine ⟨535582687574779947203141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 357055125049853298135427 535582687574779947203141)
                  ·
                    refine ⟨100421753920271240100589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 535582687574779947203141 100421753920271240100589)
                    ·
                      rfl

theorem cell23_586712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 3, 2, 1, 4].length) (baseStart_586712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_586712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_586712 prefixEnd_586712 := by exact prefixLift 586712
  have htrace : WordTrace (prefixWord ++ tailWord_586712) baseStart_586712 baseEnd_586712 := by
    simpa [prefixWord, tailWord_586712, baseEnd_586712] using wordTrace_append hprefix tailTrace_586712
  have hstable : (prefixWord ++ tailWord_586712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586712).length < 2 ^ (prefixWord ++ tailWord_586712).sum := by decide
  have hdescent : baseEnd_586712 < baseStart_586712 := by decide
  rcases family_descends (prefixWord ++ tailWord_586712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586721 : List Nat := [1, 2, 3, 1, 2, 1, 1, 4, 3, 5]
def baseStart_586721 : Nat := 118140960795 + 586721 * 2 ^ 59
def prefixEnd_586721 : Nat := 4983230072969 + 3 ^ 40 * 586721 * 2
def baseEnd_586721 : Nat := 100423294362234728363075

theorem tailTrace_586721 : CollatzResearch.WordTrace tailWord_586721 prefixEnd_586721 100423294362234728363075 := by
  unfold tailWord_586721
  simp only [CollatzResearch.WordTrace]
  refine ⟨21399472907417495814264017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14266315271611663876176011 21399472907417495814264017)
  ·
    refine ⟨16049604680563121860698013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21399472907417495814264017 16049604680563121860698013)
    ·
      refine ⟨6018601755211170697761755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16049604680563121860698013 6018601755211170697761755)
      ·
        refine ⟨9027902632816756046642633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6018601755211170697761755 9027902632816756046642633)
        ·
          refine ⟨6770926974612567034981975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9027902632816756046642633 6770926974612567034981975)
          ·
            refine ⟨10156390461918850552472963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6770926974612567034981975 10156390461918850552472963)
            ·
              refine ⟨15234585692878275828709445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10156390461918850552472963 15234585692878275828709445)
              ·
                refine ⟨2856484817414676717883021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15234585692878275828709445 2856484817414676717883021)
                ·
                  refine ⟨1071181806530503769206133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2856484817414676717883021 1071181806530503769206133)
                  ·
                    refine ⟨100423294362234728363075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1071181806530503769206133 100423294362234728363075)
                    ·
                      rfl

theorem cell23_586721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 3, 5].length) (baseStart_586721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_586721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_586721 prefixEnd_586721 := by exact prefixLift 586721
  have htrace : WordTrace (prefixWord ++ tailWord_586721) baseStart_586721 baseEnd_586721 := by
    simpa [prefixWord, tailWord_586721, baseEnd_586721] using wordTrace_append hprefix tailTrace_586721
  have hstable : (prefixWord ++ tailWord_586721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586721).length < 2 ^ (prefixWord ++ tailWord_586721).sum := by decide
  have hdescent : baseEnd_586721 < baseStart_586721 := by decide
  rcases family_descends (prefixWord ++ tailWord_586721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586725 : List Nat := [1, 3, 1, 6, 1, 1, 1, 3, 6]
def baseStart_586725 : Nat := 118140960795 + 586725 * 2 ^ 59
def prefixEnd_586725 : Nat := 4983230072969 + 3 ^ 40 * 586725 * 2
def baseEnd_586725 : Nat := 33474659667702463271023

theorem tailTrace_586725 : CollatzResearch.WordTrace tailWord_586725 prefixEnd_586725 33474659667702463271023 := by
  unfold tailWord_586725
  simp only [CollatzResearch.WordTrace]
  refine ⟨21399618799403004497409629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14266412532935336331606419 21399618799403004497409629)
  ·
    refine ⟨8024857049776126686528611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21399618799403004497409629 8024857049776126686528611)
    ·
      refine ⟨12037285574664190029792917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8024857049776126686528611 12037285574664190029792917)
      ·
        refine ⟨564247761312383907646543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 12037285574664190029792917 564247761312383907646543)
        ·
          refine ⟨846371641968575861469815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 564247761312383907646543 846371641968575861469815)
          ·
            refine ⟨1269557462952863792204723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 846371641968575861469815 1269557462952863792204723)
            ·
              refine ⟨1904336194429295688307085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1269557462952863792204723 1904336194429295688307085)
              ·
                refine ⟨714126072910985883115157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1904336194429295688307085 714126072910985883115157)
                ·
                  refine ⟨33474659667702463271023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 714126072910985883115157 33474659667702463271023)
                  ·
                    rfl

theorem cell23_586725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 3, 6].length) (baseStart_586725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_586725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_586725 prefixEnd_586725 := by exact prefixLift 586725
  have htrace : WordTrace (prefixWord ++ tailWord_586725) baseStart_586725 baseEnd_586725 := by
    simpa [prefixWord, tailWord_586725, baseEnd_586725] using wordTrace_append hprefix tailTrace_586725
  have hstable : (prefixWord ++ tailWord_586725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586725).length < 2 ^ (prefixWord ++ tailWord_586725).sum := by decide
  have hdescent : baseEnd_586725 < baseStart_586725 := by decide
  rcases family_descends (prefixWord ++ tailWord_586725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586728 : List Nat := [2, 1, 4, 1, 1, 1, 2, 1, 3, 5, 2]
def baseStart_586728 : Nat := 118140960795 + 586728 * 2 ^ 59
def prefixEnd_586728 : Nat := 4983230072969 + 3 ^ 40 * 586728 * 2
def baseEnd_586728 : Nat := 301273477451285657701693

theorem tailTrace_586728 : CollatzResearch.WordTrace tailWord_586728 prefixEnd_586728 301273477451285657701693 := by
  unfold tailWord_586728
  simp only [CollatzResearch.WordTrace]
  refine ⟨10699864109196068004884419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14266485478928090673179225 10699864109196068004884419)
  ·
    refine ⟨16049796163794102007326629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10699864109196068004884419 16049796163794102007326629)
    ·
      refine ⟨3009336780711394126373743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16049796163794102007326629 3009336780711394126373743)
      ·
        refine ⟨4514005171067091189560615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3009336780711394126373743 4514005171067091189560615)
        ·
          refine ⟨6771007756600636784340923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4514005171067091189560615 6771007756600636784340923)
          ·
            refine ⟨10156511634900955176511385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6771007756600636784340923 10156511634900955176511385)
            ·
              refine ⟨7617383726175716382383539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10156511634900955176511385 7617383726175716382383539)
              ·
                refine ⟨11426075589263574573575309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7617383726175716382383539 11426075589263574573575309)
                ·
                  refine ⟨4284778345973840465090741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11426075589263574573575309 4284778345973840465090741)
                  ·
                    refine ⟨401697969935047543602257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4284778345973840465090741 401697969935047543602257)
                    ·
                      refine ⟨301273477451285657701693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 401697969935047543602257 301273477451285657701693)
                      ·
                        rfl

theorem cell23_586728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 3, 5, 2].length) (baseStart_586728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_586728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_586728 prefixEnd_586728 := by exact prefixLift 586728
  have htrace : WordTrace (prefixWord ++ tailWord_586728) baseStart_586728 baseEnd_586728 := by
    simpa [prefixWord, tailWord_586728, baseEnd_586728] using wordTrace_append hprefix tailTrace_586728
  have hstable : (prefixWord ++ tailWord_586728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586728).length < 2 ^ (prefixWord ++ tailWord_586728).sum := by decide
  have hdescent : baseEnd_586728 < baseStart_586728 := by decide
  rcases family_descends (prefixWord ++ tailWord_586728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586745 : List Nat := [1, 2, 1, 3, 1, 3, 4, 1, 2, 3, 2]
def baseStart_586745 : Nat := 118140960795 + 586745 * 2 ^ 59
def prefixEnd_586745 : Nat := 4983230072969 + 3 ^ 40 * 586745 * 2
def baseEnd_586745 : Nat := 301282206622412091189115

theorem tailTrace_586745 : CollatzResearch.WordTrace tailWord_586745 prefixEnd_586745 301282206622412091189115 := by
  unfold tailWord_586745
  simp only [CollatzResearch.WordTrace]
  refine ⟨21400348259330547913137689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14266898839553698608758459 21400348259330547913137689)
  ·
    refine ⟨16050261194497910934853267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21400348259330547913137689 16050261194497910934853267)
    ·
      refine ⟨24075391791746866402279901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16050261194497910934853267 24075391791746866402279901)
      ·
        refine ⟨9028271921905074900854963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24075391791746866402279901 9028271921905074900854963)
        ·
          refine ⟨13542407882857612351282445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9028271921905074900854963 13542407882857612351282445)
          ·
            refine ⟨5078402956071604631730917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13542407882857612351282445 5078402956071604631730917)
            ·
              refine ⟨952200554263425868449547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5078402956071604631730917 952200554263425868449547)
              ·
                refine ⟨1428300831395138802674321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 952200554263425868449547 1428300831395138802674321)
                ·
                  refine ⟨1071225623546354102005741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1428300831395138802674321 1071225623546354102005741)
                  ·
                    refine ⟨401709608829882788252153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1071225623546354102005741 401709608829882788252153)
                    ·
                      refine ⟨301282206622412091189115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 401709608829882788252153 301282206622412091189115)
                      ·
                        rfl

theorem cell23_586745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 1, 2, 3, 2].length) (baseStart_586745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_586745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_586745 prefixEnd_586745 := by exact prefixLift 586745
  have htrace : WordTrace (prefixWord ++ tailWord_586745) baseStart_586745 baseEnd_586745 := by
    simpa [prefixWord, tailWord_586745, baseEnd_586745] using wordTrace_append hprefix tailTrace_586745
  have hstable : (prefixWord ++ tailWord_586745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586745).length < 2 ^ (prefixWord ++ tailWord_586745).sum := by decide
  have hdescent : baseEnd_586745 < baseStart_586745 := by decide
  rcases family_descends (prefixWord ++ tailWord_586745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586771 : List Nat := [1, 1, 1, 2, 1, 4, 1, 1, 5, 2, 4]
def baseStart_586771 : Nat := 118140960795 + 586771 * 2 ^ 59
def prefixEnd_586771 : Nat := 4983230072969 + 3 ^ 40 * 586771 * 2
def baseEnd_586771 : Nat := 301295557119428989463995

theorem tailTrace_586771 : CollatzResearch.WordTrace tailWord_586771 prefixEnd_586771 301295557119428989463995 := by
  unfold tailWord_586771
  simp only [CollatzResearch.WordTrace]
  refine ⟨21401296557236354353584167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14267531038157569569056111 21401296557236354353584167)
  ·
    refine ⟨32101944835854531530376251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21401296557236354353584167 32101944835854531530376251)
    ·
      refine ⟨48152917253781797295564377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32101944835854531530376251 48152917253781797295564377)
      ·
        refine ⟨36114687940336347971673283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48152917253781797295564377 36114687940336347971673283)
        ·
          refine ⟨54172031910504521957509925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36114687940336347971673283 54172031910504521957509925)
          ·
            refine ⟨10157255983219597867033111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54172031910504521957509925 10157255983219597867033111)
            ·
              refine ⟨15235883974829396800549667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10157255983219597867033111 15235883974829396800549667)
              ·
                refine ⟨22853825962244095200824501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15235883974829396800549667 22853825962244095200824501)
                ·
                  refine ⟨2142546183960383925077297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22853825962244095200824501 2142546183960383925077297)
                  ·
                    refine ⟨1606909637970287943807973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2142546183960383925077297 1606909637970287943807973)
                    ·
                      refine ⟨301295557119428989463995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1606909637970287943807973 301295557119428989463995)
                      ·
                        rfl

theorem cell23_586771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 5, 2, 4].length) (baseStart_586771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_586771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_586771 prefixEnd_586771 := by exact prefixLift 586771
  have htrace : WordTrace (prefixWord ++ tailWord_586771) baseStart_586771 baseEnd_586771 := by
    simpa [prefixWord, tailWord_586771, baseEnd_586771] using wordTrace_append hprefix tailTrace_586771
  have hstable : (prefixWord ++ tailWord_586771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586771).length < 2 ^ (prefixWord ++ tailWord_586771).sum := by decide
  have hdescent : baseEnd_586771 < baseStart_586771 := by decide
  rcases family_descends (prefixWord ++ tailWord_586771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586778 : List Nat := [3, 1, 1, 3, 1, 2, 1, 1, 5, 2, 3]
def baseStart_586778 : Nat := 118140960795 + 586778 * 2 ^ 59
def prefixEnd_586778 : Nat := 4983230072969 + 3 ^ 40 * 586778 * 2
def baseEnd_586778 : Nat := 301299151484010462076463

theorem tailTrace_586778 : CollatzResearch.WordTrace tailWord_586778 prefixEnd_586778 301299151484010462076463 := by
  unfold tailWord_586778
  simp only [CollatzResearch.WordTrace]
  refine ⟨5350387967052748637272247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14267701245473996366059325 5350387967052748637272247)
  ·
    refine ⟨8025581950579122955908371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5350387967052748637272247 8025581950579122955908371)
    ·
      refine ⟨12038372925868684433862557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8025581950579122955908371 12038372925868684433862557)
      ·
        refine ⟨4514389847200756662698459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12038372925868684433862557 4514389847200756662698459)
        ·
          refine ⟨6771584770801134994047689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4514389847200756662698459 6771584770801134994047689)
          ·
            refine ⟨5078688578100851245535767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6771584770801134994047689 5078688578100851245535767)
            ·
              refine ⟨7618032867151276868303651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5078688578100851245535767 7618032867151276868303651)
              ·
                refine ⟨11427049300726915302455477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7618032867151276868303651 11427049300726915302455477)
                ·
                  refine ⟨1071285871943148309605201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11427049300726915302455477 1071285871943148309605201)
                  ·
                    refine ⟨803464403957361232203901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1071285871943148309605201 803464403957361232203901)
                    ·
                      refine ⟨301299151484010462076463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 803464403957361232203901 301299151484010462076463)
                      ·
                        rfl

theorem cell23_586778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 5, 2, 3].length) (baseStart_586778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_586778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_586778 prefixEnd_586778 := by exact prefixLift 586778
  have htrace : WordTrace (prefixWord ++ tailWord_586778) baseStart_586778 baseEnd_586778 := by
    simpa [prefixWord, tailWord_586778, baseEnd_586778] using wordTrace_append hprefix tailTrace_586778
  have hstable : (prefixWord ++ tailWord_586778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586778).length < 2 ^ (prefixWord ++ tailWord_586778).sum := by decide
  have hdescent : baseEnd_586778 < baseStart_586778 := by decide
  rcases family_descends (prefixWord ++ tailWord_586778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586785 : List Nat := [1, 2, 3, 2, 3, 1, 2, 3, 2, 4]
def baseStart_586785 : Nat := 118140960795 + 586785 * 2 ^ 59
def prefixEnd_586785 : Nat := 4983230072969 + 3 ^ 40 * 586785 * 2
def baseEnd_586785 : Nat := 100434248616197311562977

theorem tailTrace_586785 : CollatzResearch.WordTrace tailWord_586785 prefixEnd_586785 100434248616197311562977 := by
  unfold tailWord_586785
  simp only [CollatzResearch.WordTrace]
  refine ⟨21401807179185634744593809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14267871452790423163062539 21401807179185634744593809)
  ·
    refine ⟨16051355384389226058445357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21401807179185634744593809 16051355384389226058445357)
    ·
      refine ⟨6019258269145959771917009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16051355384389226058445357 6019258269145959771917009)
      ·
        refine ⟨4514443701859469828937757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6019258269145959771917009 4514443701859469828937757)
        ·
          refine ⟨1692916388197301185851659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4514443701859469828937757 1692916388197301185851659)
          ·
            refine ⟨2539374582295951778777489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1692916388197301185851659 2539374582295951778777489)
            ·
              refine ⟨1904530936721963834083117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2539374582295951778777489 1904530936721963834083117)
              ·
                refine ⟨714199101270736437781169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1904530936721963834083117 714199101270736437781169)
                ·
                  refine ⟨535649325953052328335877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 714199101270736437781169 535649325953052328335877)
                  ·
                    refine ⟨100434248616197311562977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 535649325953052328335877 100434248616197311562977)
                    ·
                      rfl

theorem cell23_586785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 3, 2, 4].length) (baseStart_586785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_586785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_586785 prefixEnd_586785 := by exact prefixLift 586785
  have htrace : WordTrace (prefixWord ++ tailWord_586785) baseStart_586785 baseEnd_586785 := by
    simpa [prefixWord, tailWord_586785, baseEnd_586785] using wordTrace_append hprefix tailTrace_586785
  have hstable : (prefixWord ++ tailWord_586785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586785).length < 2 ^ (prefixWord ++ tailWord_586785).sum := by decide
  have hdescent : baseEnd_586785 < baseStart_586785 := by decide
  rcases family_descends (prefixWord ++ tailWord_586785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586809 : List Nat := [1, 2, 1, 5, 2, 1, 1, 5, 1, 2, 2]
def baseStart_586809 : Nat := 118140960795 + 586809 * 2 ^ 59
def prefixEnd_586809 : Nat := 4983230072969 + 3 ^ 40 * 586809 * 2
def baseEnd_586809 : Nat := 301315069384299840788821

theorem tailTrace_586809 : CollatzResearch.WordTrace tailWord_586809 prefixEnd_586809 301315069384299840788821 := by
  unfold tailWord_586809
  simp only [CollatzResearch.WordTrace]
  refine ⟨21402682531098686843467481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14268455020732457895644987 21402682531098686843467481)
  ·
    refine ⟨16052011898324015132600611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21402682531098686843467481 16052011898324015132600611)
    ·
      refine ⟨24078017847486022698900917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16052011898324015132600611 24078017847486022698900917)
      ·
        refine ⟨2257314173201814628021961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24078017847486022698900917 2257314173201814628021961)
        ·
          refine ⟨1692985629901360971016471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2257314173201814628021961 1692985629901360971016471)
          ·
            refine ⟨2539478444852041456524707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1692985629901360971016471 2539478444852041456524707)
            ·
              refine ⟨3809217667278062184787061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2539478444852041456524707 3809217667278062184787061)
              ·
                refine ⟨357114156307318329823787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3809217667278062184787061 357114156307318329823787)
                ·
                  refine ⟨535671234460977494735681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 357114156307318329823787 535671234460977494735681)
                  ·
                    refine ⟨401753425845733121051761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 535671234460977494735681 401753425845733121051761)
                    ·
                      refine ⟨301315069384299840788821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 401753425845733121051761 301315069384299840788821)
                      ·
                        rfl

theorem cell23_586809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 5, 1, 2, 2].length) (baseStart_586809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_586809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_586809 prefixEnd_586809 := by exact prefixLift 586809
  have htrace : WordTrace (prefixWord ++ tailWord_586809) baseStart_586809 baseEnd_586809 := by
    simpa [prefixWord, tailWord_586809, baseEnd_586809] using wordTrace_append hprefix tailTrace_586809
  have hstable : (prefixWord ++ tailWord_586809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586809).length < 2 ^ (prefixWord ++ tailWord_586809).sum := by decide
  have hdescent : baseEnd_586809 < baseStart_586809 := by decide
  rcases family_descends (prefixWord ++ tailWord_586809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586812 : List Nat := [2, 2, 2, 2, 2, 2, 4, 1, 1, 2, 3]
def baseStart_586812 : Nat := 118140960795 + 586812 * 2 ^ 59
def prefixEnd_586812 : Nat := 4983230072969 + 3 ^ 40 * 586812 * 2
def baseEnd_586812 : Nat := 301316609826263329051307

theorem tailTrace_586812 : CollatzResearch.WordTrace tailWord_586812 prefixEnd_586812 301316609826263329051307 := by
  unfold tailWord_586812
  simp only [CollatzResearch.WordTrace]
  refine ⟨10701395975043909177913345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14268527966725212237217793 10701395975043909177913345)
  ·
    refine ⟨8026046981282931883435009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10701395975043909177913345 8026046981282931883435009)
    ·
      refine ⟨6019535235962198912576257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8026046981282931883435009 6019535235962198912576257)
      ·
        refine ⟨4514651426971649184432193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6019535235962198912576257 4514651426971649184432193)
        ·
          refine ⟨3385988570228736888324145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4514651426971649184432193 3385988570228736888324145)
          ·
            refine ⟨2539491427671552666243109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3385988570228736888324145 2539491427671552666243109)
            ·
              refine ⟨476154642688416124920583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2539491427671552666243109 476154642688416124920583)
              ·
                refine ⟨714231964032624187380875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 476154642688416124920583 714231964032624187380875)
                ·
                  refine ⟨1071347946048936281071313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 714231964032624187380875 1071347946048936281071313)
                  ·
                    refine ⟨803510959536702210803485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1071347946048936281071313 803510959536702210803485)
                    ·
                      refine ⟨301316609826263329051307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 803510959536702210803485 301316609826263329051307)
                      ·
                        rfl

theorem cell23_586812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 4, 1, 1, 2, 3].length) (baseStart_586812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_586812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_586812 prefixEnd_586812 := by exact prefixLift 586812
  have htrace : WordTrace (prefixWord ++ tailWord_586812) baseStart_586812 baseEnd_586812 := by
    simpa [prefixWord, tailWord_586812, baseEnd_586812] using wordTrace_append hprefix tailTrace_586812
  have hstable : (prefixWord ++ tailWord_586812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586812).length < 2 ^ (prefixWord ++ tailWord_586812).sum := by decide
  have hdescent : baseEnd_586812 < baseStart_586812 := by decide
  rcases family_descends (prefixWord ++ tailWord_586812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586825 : List Nat := [1, 2, 1, 1, 2, 2, 2, 6, 2, 1, 3]
def baseStart_586825 : Nat := 118140960795 + 586825 * 2 ^ 59
def prefixEnd_586825 : Nat := 4983230072969 + 3 ^ 40 * 586825 * 2
def baseEnd_586825 : Nat := 301323285074771778188747

theorem tailTrace_586825 : CollatzResearch.WordTrace tailWord_586825 prefixEnd_586825 301323285074771778188747 := by
  unfold tailWord_586825
  simp only [CollatzResearch.WordTrace]
  refine ⟨21403266099040721576049929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14268844066027147717366619 21403266099040721576049929)
  ·
    refine ⟨16052449574280541182037447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21403266099040721576049929 16052449574280541182037447)
    ·
      refine ⟨24078674361420811773056171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16052449574280541182037447 24078674361420811773056171)
      ·
        refine ⟨36118011542131217659584257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24078674361420811773056171 36118011542131217659584257)
        ·
          refine ⟨27088508656598413244688193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36118011542131217659584257 27088508656598413244688193)
          ·
            refine ⟨20316381492448809933516145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27088508656598413244688193 20316381492448809933516145)
            ·
              refine ⟨15237286119336607450137109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20316381492448809933516145 15237286119336607450137109)
              ·
                refine ⟨714247786843903474225177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15237286119336607450137109 714247786843903474225177)
                ·
                  refine ⟨535685840132927605668883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 714247786843903474225177 535685840132927605668883)
                  ·
                    refine ⟨803528760199391408503325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 535685840132927605668883 803528760199391408503325)
                    ·
                      refine ⟨301323285074771778188747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 803528760199391408503325 301323285074771778188747)
                      ·
                        rfl

theorem cell23_586825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 6, 2, 1, 3].length) (baseStart_586825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_586825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_586825 prefixEnd_586825 := by exact prefixLift 586825
  have htrace : WordTrace (prefixWord ++ tailWord_586825) baseStart_586825 baseEnd_586825 := by
    simpa [prefixWord, tailWord_586825, baseEnd_586825] using wordTrace_append hprefix tailTrace_586825
  have hstable : (prefixWord ++ tailWord_586825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586825).length < 2 ^ (prefixWord ++ tailWord_586825).sum := by decide
  have hdescent : baseEnd_586825 < baseStart_586825 := by decide
  rcases family_descends (prefixWord ++ tailWord_586825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586841 : List Nat := [1, 2, 1, 2, 2, 1, 2, 3, 1, 8]
def baseStart_586841 : Nat := 118140960795 + 586841 * 2 ^ 59
def prefixEnd_586841 : Nat := 4983230072969 + 3 ^ 40 * 586841 * 2
def baseEnd_586841 : Nat := 100443833588414571862891

theorem tailTrace_586841 : CollatzResearch.WordTrace tailWord_586841 prefixEnd_586841 100443833588414571862891 := by
  unfold tailWord_586841
  simp only [CollatzResearch.WordTrace]
  refine ⟨21403849666982756308632377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14269233111321837539088251 21403849666982756308632377)
  ·
    refine ⟨16052887250237067231474283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21403849666982756308632377 16052887250237067231474283)
    ·
      refine ⟨24079330875355600847211425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16052887250237067231474283 24079330875355600847211425)
      ·
        refine ⟨18059498156516700635408569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24079330875355600847211425 18059498156516700635408569)
        ·
          refine ⟨13544623617387525476556427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18059498156516700635408569 13544623617387525476556427)
          ·
            refine ⟨20316935426081288214834641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13544623617387525476556427 20316935426081288214834641)
            ·
              refine ⟨15237701569560966161125981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20316935426081288214834641 15237701569560966161125981)
              ·
                refine ⟨5714138088585362310422243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15237701569560966161125981 5714138088585362310422243)
                ·
                  refine ⟨8571207132878043465633365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5714138088585362310422243 8571207132878043465633365)
                  ·
                    refine ⟨100443833588414571862891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 8571207132878043465633365 100443833588414571862891)
                    ·
                      rfl

theorem cell23_586841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 8].length) (baseStart_586841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_586841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_586841 prefixEnd_586841 := by exact prefixLift 586841
  have htrace : WordTrace (prefixWord ++ tailWord_586841) baseStart_586841 baseEnd_586841 := by
    simpa [prefixWord, tailWord_586841, baseEnd_586841] using wordTrace_append hprefix tailTrace_586841
  have hstable : (prefixWord ++ tailWord_586841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586841).length < 2 ^ (prefixWord ++ tailWord_586841).sum := by decide
  have hdescent : baseEnd_586841 < baseStart_586841 := by decide
  rcases family_descends (prefixWord ++ tailWord_586841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586846 : List Nat := [4, 4, 1, 1, 1, 2, 2, 2, 1, 2, 3]
def baseStart_586846 : Nat := 118140960795 + 586846 * 2 ^ 59
def prefixEnd_586846 : Nat := 4983230072969 + 3 ^ 40 * 586846 * 2
def baseEnd_586846 : Nat := 301334068168516196026151

theorem tailTrace_586846 : CollatzResearch.WordTrace tailWord_586846 prefixEnd_586846 301334068168516196026151 := by
  unfold tailWord_586846
  simp only [CollatzResearch.WordTrace]
  refine ⟨2675504003995580270320549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14269354687976428108376261 2675504003995580270320549)
  ·
    refine ⟨501657000749171300685103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2675504003995580270320549 501657000749171300685103)
    ·
      refine ⟨752485501123756951027655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 501657000749171300685103 752485501123756951027655)
      ·
        refine ⟨1128728251685635426541483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 752485501123756951027655 1128728251685635426541483)
        ·
          refine ⟨1693092377528453139812225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1128728251685635426541483 1693092377528453139812225)
          ·
            refine ⟨1269819283146339854859169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1693092377528453139812225 1269819283146339854859169)
            ·
              refine ⟨952364462359754891144377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1269819283146339854859169 952364462359754891144377)
              ·
                refine ⟨714273346769816168358283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 952364462359754891144377 714273346769816168358283)
                ·
                  refine ⟨1071410020154724252537425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 714273346769816168358283 1071410020154724252537425)
                  ·
                    refine ⟨803557515116043189403069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1071410020154724252537425 803557515116043189403069)
                    ·
                      refine ⟨301334068168516196026151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 803557515116043189403069 301334068168516196026151)
                      ·
                        rfl

theorem cell23_586846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_586846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_586846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_586846 prefixEnd_586846 := by exact prefixLift 586846
  have htrace : WordTrace (prefixWord ++ tailWord_586846) baseStart_586846 baseEnd_586846 := by
    simpa [prefixWord, tailWord_586846, baseEnd_586846] using wordTrace_append hprefix tailTrace_586846
  have hstable : (prefixWord ++ tailWord_586846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586846).length < 2 ^ (prefixWord ++ tailWord_586846).sum := by decide
  have hdescent : baseEnd_586846 < baseStart_586846 := by decide
  rcases family_descends (prefixWord ++ tailWord_586846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586899 : List Nat := [1, 1, 1, 2, 1, 2, 8, 1, 2, 2, 2]
def baseStart_586899 : Nat := 118140960795 + 586899 * 2 ^ 59
def prefixEnd_586899 : Nat := 4983230072969 + 3 ^ 40 * 586899 * 2
def baseEnd_586899 : Nat := 301361282643204488663407

theorem tailTrace_586899 : CollatzResearch.WordTrace tailWord_586899 prefixEnd_586899 301361282643204488663407 := by
  unfold tailWord_586899
  simp only [CollatzResearch.WordTrace]
  refine ⟨21405965100772632214243751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14270643400515088142829167 21405965100772632214243751)
  ·
    refine ⟨32108947651158948321365627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21405965100772632214243751 32108947651158948321365627)
    ·
      refine ⟨48163421476738422482048441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32108947651158948321365627 48163421476738422482048441)
      ·
        refine ⟨36122566107553816861536331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48163421476738422482048441 36122566107553816861536331)
        ·
          refine ⟨54183849161330725292304497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36122566107553816861536331 54183849161330725292304497)
          ·
            refine ⟨40637886870998043969228373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54183849161330725292304497 40637886870998043969228373)
            ·
              refine ⟨476225236769508327764395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 40637886870998043969228373 476225236769508327764395)
              ·
                refine ⟨714337855154262491646593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 476225236769508327764395 714337855154262491646593)
                ·
                  refine ⟨535753391365696868734945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 714337855154262491646593 535753391365696868734945)
                  ·
                    refine ⟨401815043524272651551209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 535753391365696868734945 401815043524272651551209)
                    ·
                      refine ⟨301361282643204488663407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 401815043524272651551209 301361282643204488663407)
                      ·
                        rfl

theorem cell23_586899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 8, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 8, 1, 2, 2, 2].length) (baseStart_586899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_586899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_586899 prefixEnd_586899 := by exact prefixLift 586899
  have htrace : WordTrace (prefixWord ++ tailWord_586899) baseStart_586899 baseEnd_586899 := by
    simpa [prefixWord, tailWord_586899, baseEnd_586899] using wordTrace_append hprefix tailTrace_586899
  have hstable : (prefixWord ++ tailWord_586899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586899).length < 2 ^ (prefixWord ++ tailWord_586899).sum := by decide
  have hdescent : baseEnd_586899 < baseStart_586899 := by decide
  rcases family_descends (prefixWord ++ tailWord_586899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586938 : List Nat := [3, 1, 1, 1, 2, 2, 1, 2, 3, 3, 4]
def baseStart_586938 : Nat := 118140960795 + 586938 * 2 ^ 59
def prefixEnd_586938 : Nat := 4983230072969 + 3 ^ 40 * 586938 * 2
def baseEnd_586938 : Nat := 301381308388729836075727

theorem tailTrace_586938 : CollatzResearch.WordTrace tailWord_586938 prefixEnd_586938 301381308388729836075727 := by
  unfold tailWord_586938
  simp only [CollatzResearch.WordTrace]
  refine ⟨5351846886907835468728367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14271591698420894583275645 5351846886907835468728367)
  ·
    refine ⟨8027770330361753203092551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5351846886907835468728367 8027770330361753203092551)
    ·
      refine ⟨12041655495542629804638827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8027770330361753203092551 12041655495542629804638827)
      ·
        refine ⟨18062483243313944706958241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12041655495542629804638827 18062483243313944706958241)
        ·
          refine ⟨13546862432485458530218681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18062483243313944706958241 13546862432485458530218681)
          ·
            refine ⟨10160146824364093897664011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13546862432485458530218681 10160146824364093897664011)
            ·
              refine ⟨15240220236546140846496017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10160146824364093897664011 15240220236546140846496017)
              ·
                refine ⟨11430165177409605634872013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15240220236546140846496017 11430165177409605634872013)
                ·
                  refine ⟨4286311941528602113077005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11430165177409605634872013 4286311941528602113077005)
                  ·
                    refine ⟨1607366978073225792403877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4286311941528602113077005 1607366978073225792403877)
                    ·
                      refine ⟨301381308388729836075727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1607366978073225792403877 301381308388729836075727)
                      ·
                        rfl

theorem cell23_586938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 3, 3, 4].length) (baseStart_586938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_586938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_586938 prefixEnd_586938 := by exact prefixLift 586938
  have htrace : WordTrace (prefixWord ++ tailWord_586938) baseStart_586938 baseEnd_586938 := by
    simpa [prefixWord, tailWord_586938, baseEnd_586938] using wordTrace_append hprefix tailTrace_586938
  have hstable : (prefixWord ++ tailWord_586938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586938).length < 2 ^ (prefixWord ++ tailWord_586938).sum := by decide
  have hdescent : baseEnd_586938 < baseStart_586938 := by decide
  rcases family_descends (prefixWord ++ tailWord_586938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586942 : List Nat := [4, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2]
def baseStart_586942 : Nat := 118140960795 + 586942 * 2 ^ 59
def prefixEnd_586942 : Nat := 4983230072969 + 3 ^ 40 * 586942 * 2
def baseEnd_586942 : Nat := 301383362311347820425709

theorem tailTrace_586942 : CollatzResearch.WordTrace tailWord_586942 prefixEnd_586942 301383362311347820425709 := by
  unfold tailWord_586942
  simp only [CollatzResearch.WordTrace]
  refine ⟨2675941679952106319757385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14271688959744567038706053 2675941679952106319757385)
  ·
    refine ⟨2006956259964079739818039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2675941679952106319757385 2006956259964079739818039)
    ·
      refine ⟨3010434389946119609727059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2006956259964079739818039 3010434389946119609727059)
      ·
        refine ⟨4515651584919179414590589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3010434389946119609727059 4515651584919179414590589)
        ·
          refine ⟨1693369344344692280471471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4515651584919179414590589 1693369344344692280471471)
          ·
            refine ⟨2540054016517038420707207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1693369344344692280471471 2540054016517038420707207)
            ·
              refine ⟨3810081024775557631060811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2540054016517038420707207 3810081024775557631060811)
              ·
                refine ⟨5715121537163336446591217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3810081024775557631060811 5715121537163336446591217)
                ·
                  refine ⟨4286341152872502334943413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5715121537163336446591217 4286341152872502334943413)
                  ·
                    refine ⟨401844483081797093900945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4286341152872502334943413 401844483081797093900945)
                    ·
                      refine ⟨301383362311347820425709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 401844483081797093900945 301383362311347820425709)
                      ·
                        rfl

theorem cell23_586942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2].length) (baseStart_586942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_586942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_586942 prefixEnd_586942 := by exact prefixLift 586942
  have htrace : WordTrace (prefixWord ++ tailWord_586942) baseStart_586942 baseEnd_586942 := by
    simpa [prefixWord, tailWord_586942, baseEnd_586942] using wordTrace_append hprefix tailTrace_586942
  have hstable : (prefixWord ++ tailWord_586942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586942).length < 2 ^ (prefixWord ++ tailWord_586942).sum := by decide
  have hdescent : baseEnd_586942 < baseStart_586942 := by decide
  rcases family_descends (prefixWord ++ tailWord_586942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586995 : List Nat := [1, 1, 1, 2, 2, 5, 3, 2, 6]
def baseStart_586995 : Nat := 118140960795 + 586995 * 2 ^ 59
def prefixEnd_586995 : Nat := 4983230072969 + 3 ^ 40 * 586995 * 2
def baseEnd_586995 : Nat := 33490064087337345895885

theorem tailTrace_586995 : CollatzResearch.WordTrace tailWord_586995 prefixEnd_586995 33490064087337345895885 := by
  unfold tailWord_586995
  simp only [CollatzResearch.WordTrace]
  refine ⟨21409466508424840609738439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14272977672283227073158959 21409466508424840609738439)
  ·
    refine ⟨32114199762637260914607659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21409466508424840609738439 32114199762637260914607659)
    ·
      refine ⟨48171299643955891371911489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32114199762637260914607659 48171299643955891371911489)
      ·
        refine ⟨36128474732966918528933617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48171299643955891371911489 36128474732966918528933617)
        ·
          refine ⟨27096356049725188896700213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36128474732966918528933617 27096356049725188896700213)
          ·
            refine ⟨2540283379661736459065645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27096356049725188896700213 2540283379661736459065645)
            ·
              refine ⟨952606267373151172149617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2540283379661736459065645 952606267373151172149617)
              ·
                refine ⟨714454700529863379112213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 952606267373151172149617 714454700529863379112213)
                ·
                  refine ⟨33490064087337345895885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 714454700529863379112213 33490064087337345895885)
                  ·
                    rfl

theorem cell23_586995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 2, 6].length) (baseStart_586995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_586995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_586995 prefixEnd_586995 := by exact prefixLift 586995
  have htrace : WordTrace (prefixWord ++ tailWord_586995) baseStart_586995 baseEnd_586995 := by
    simpa [prefixWord, tailWord_586995, baseEnd_586995] using wordTrace_append hprefix tailTrace_586995
  have hstable : (prefixWord ++ tailWord_586995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586995).length < 2 ^ (prefixWord ++ tailWord_586995).sum := by decide
  have hdescent : baseEnd_586995 < baseStart_586995 := by decide
  rcases family_descends (prefixWord ++ tailWord_586995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587032 : List Nat := [2, 1, 2, 3, 1, 3, 2, 1, 1, 5, 2]
def baseStart_587032 : Nat := 118140960795 + 587032 * 2 ^ 59
def prefixEnd_587032 : Nat := 4983230072969 + 3 ^ 40 * 587032 * 2
def baseEnd_587032 : Nat := 301429575570252468300295

theorem tailTrace_587032 : CollatzResearch.WordTrace tailWord_587032 prefixEnd_587032 301429575570252468300295 := by
  unfold tailWord_587032
  simp only [CollatzResearch.WordTrace]
  refine ⟨10705408004645397964417675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14273877339527197285890233 10705408004645397964417675)
  ·
    refine ⟨16058112006968096946626513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10705408004645397964417675 16058112006968096946626513)
    ·
      refine ⟨12043584005226072709969885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16058112006968096946626513 12043584005226072709969885)
      ·
        refine ⟨4516344001959777266238707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12043584005226072709969885 4516344001959777266238707)
        ·
          refine ⟨6774516002939665899358061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4516344001959777266238707 6774516002939665899358061)
          ·
            refine ⟨2540443501102374712259273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6774516002939665899358061 2540443501102374712259273)
            ·
              refine ⟨1905332625826781034194455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2540443501102374712259273 1905332625826781034194455)
              ·
                refine ⟨2857998938740171551291683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1905332625826781034194455 2857998938740171551291683)
                ·
                  refine ⟨4286998408110257326937525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2857998938740171551291683 4286998408110257326937525)
                  ·
                    refine ⟨401906100760336624400393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4286998408110257326937525 401906100760336624400393)
                    ·
                      refine ⟨301429575570252468300295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 401906100760336624400393 301429575570252468300295)
                      ·
                        rfl

theorem cell23_587032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 1, 5, 2].length) (baseStart_587032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_587032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_587032 prefixEnd_587032 := by exact prefixLift 587032
  have htrace : WordTrace (prefixWord ++ tailWord_587032) baseStart_587032 baseEnd_587032 := by
    simpa [prefixWord, tailWord_587032, baseEnd_587032] using wordTrace_append hprefix tailTrace_587032
  have hstable : (prefixWord ++ tailWord_587032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587032).length < 2 ^ (prefixWord ++ tailWord_587032).sum := by decide
  have hdescent : baseEnd_587032 < baseStart_587032 := by decide
  rcases family_descends (prefixWord ++ tailWord_587032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587056 : List Nat := [2, 1, 1, 1, 2, 2, 7, 2, 1, 1, 3]
def baseStart_587056 : Nat := 118140960795 + 587056 * 2 ^ 59
def prefixEnd_587056 : Nat := 4983230072969 + 3 ^ 40 * 587056 * 2
def baseEnd_587056 : Nat := 301441899105960374400185

theorem tailTrace_587056 : CollatzResearch.WordTrace tailWord_587056 prefixEnd_587056 301441899105960374400185 := by
  unfold tailWord_587056
  simp only [CollatzResearch.WordTrace]
  refine ⟨10705845680601924013854511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14274460907469232018472681 10705845680601924013854511)
  ·
    refine ⟨16058768520902886020781767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10705845680601924013854511 16058768520902886020781767)
    ·
      refine ⟨24088152781354329031172651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16058768520902886020781767 24088152781354329031172651)
      ·
        refine ⟨36132229172031493546758977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24088152781354329031172651 36132229172031493546758977)
        ·
          refine ⟨27099171879023620160069233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36132229172031493546758977 27099171879023620160069233)
          ·
            refine ⟨20324378909267715120051925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27099171879023620160069233 20324378909267715120051925)
            ·
              refine ⟨476352630685962073126217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 20324378909267715120051925 476352630685962073126217)
              ·
                refine ⟨357264473014471554844663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 476352630685962073126217 357264473014471554844663)
                ·
                  refine ⟨535896709521707332266995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 357264473014471554844663 535896709521707332266995)
                  ·
                    refine ⟨803845064282560998400493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 535896709521707332266995 803845064282560998400493)
                    ·
                      refine ⟨301441899105960374400185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 803845064282560998400493 301441899105960374400185)
                      ·
                        rfl

theorem cell23_587056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 7, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 7, 2, 1, 1, 3].length) (baseStart_587056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_587056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_587056 prefixEnd_587056 := by exact prefixLift 587056
  have htrace : WordTrace (prefixWord ++ tailWord_587056) baseStart_587056 baseEnd_587056 := by
    simpa [prefixWord, tailWord_587056, baseEnd_587056] using wordTrace_append hprefix tailTrace_587056
  have hstable : (prefixWord ++ tailWord_587056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587056).length < 2 ^ (prefixWord ++ tailWord_587056).sum := by decide
  have hdescent : baseEnd_587056 < baseStart_587056 := by decide
  rcases family_descends (prefixWord ++ tailWord_587056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587072 : List Nat := [2, 1, 1, 2, 2, 1, 5, 3, 2, 4]
def baseStart_587072 : Nat := 118140960795 + 587072 * 2 ^ 59
def prefixEnd_587072 : Nat := 4983230072969 + 3 ^ 40 * 587072 * 2
def baseEnd_587072 : Nat := 100483371598810770600037

theorem tailTrace_587072 : CollatzResearch.WordTrace tailWord_587072 prefixEnd_587072 100483371598810770600037 := by
  unfold tailWord_587072
  simp only [CollatzResearch.WordTrace]
  refine ⟨10706137464572941380145735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14274849952763921840194313 10706137464572941380145735)
  ·
    refine ⟨16059206196859412070218603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10706137464572941380145735 16059206196859412070218603)
    ·
      refine ⟨24088809295289118105327905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16059206196859412070218603 24088809295289118105327905)
      ·
        refine ⟨18066606971466838578995929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24088809295289118105327905 18066606971466838578995929)
        ·
          refine ⟨13549955228600128934246947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18066606971466838578995929 13549955228600128934246947)
          ·
            refine ⟨20324932842900193401370421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13549955228600128934246947 20324932842900193401370421)
            ·
              refine ⟨1905462454021893131378477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20324932842900193401370421 1905462454021893131378477)
              ·
                refine ⟨714548420258209924266929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1905462454021893131378477 714548420258209924266929)
                ·
                  refine ⟨535911315193657443200197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 714548420258209924266929 535911315193657443200197)
                  ·
                    refine ⟨100483371598810770600037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 535911315193657443200197 100483371598810770600037)
                    ·
                      rfl

theorem cell23_587072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 3, 2, 4].length) (baseStart_587072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_587072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_587072 prefixEnd_587072 := by exact prefixLift 587072
  have htrace : WordTrace (prefixWord ++ tailWord_587072) baseStart_587072 baseEnd_587072 := by
    simpa [prefixWord, tailWord_587072, baseEnd_587072] using wordTrace_append hprefix tailTrace_587072
  have hstable : (prefixWord ++ tailWord_587072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587072).length < 2 ^ (prefixWord ++ tailWord_587072).sum := by decide
  have hdescent : baseEnd_587072 < baseStart_587072 := by decide
  rcases family_descends (prefixWord ++ tailWord_587072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587075 : List Nat := [1, 1, 1, 3, 1, 3, 1, 5, 1, 2, 4]
def baseStart_587075 : Nat := 118140960795 + 587075 * 2 ^ 59
def prefixEnd_587075 : Nat := 4983230072969 + 3 ^ 40 * 587075 * 2
def baseEnd_587075 : Nat := 301451655238395800062597

theorem tailTrace_587075 : CollatzResearch.WordTrace tailWord_587075 prefixEnd_587075 301451655238395800062597 := by
  unfold tailWord_587075
  simp only [CollatzResearch.WordTrace]
  refine ⟨21412384348135014272650679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14274922898756676181767119 21412384348135014272650679)
  ·
    refine ⟨32118576522202521408976019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21412384348135014272650679 32118576522202521408976019)
    ·
      refine ⟨48177864783303782113464029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32118576522202521408976019 48177864783303782113464029)
      ·
        refine ⟨18066699293738918292549011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48177864783303782113464029 18066699293738918292549011)
        ·
          refine ⟨27100048940608377438823517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18066699293738918292549011 27100048940608377438823517)
          ·
            refine ⟨10162518352728141539558819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27100048940608377438823517 10162518352728141539558819)
            ·
              refine ⟨15243777529092212309338229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10162518352728141539558819 15243777529092212309338229)
              ·
                refine ⟨1429104143352394904000459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15243777529092212309338229 1429104143352394904000459)
                ·
                  refine ⟨2143656215028592356000689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1429104143352394904000459 2143656215028592356000689)
                  ·
                    refine ⟨1607742161271444267000517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2143656215028592356000689 1607742161271444267000517)
                    ·
                      refine ⟨301451655238395800062597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1607742161271444267000517 301451655238395800062597)
                      ·
                        rfl

theorem cell23_587075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 5, 1, 2, 4].length) (baseStart_587075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_587075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_587075 prefixEnd_587075 := by exact prefixLift 587075
  have htrace : WordTrace (prefixWord ++ tailWord_587075) baseStart_587075 baseEnd_587075 := by
    simpa [prefixWord, tailWord_587075, baseEnd_587075] using wordTrace_append hprefix tailTrace_587075
  have hstable : (prefixWord ++ tailWord_587075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587075).length < 2 ^ (prefixWord ++ tailWord_587075).sum := by decide
  have hdescent : baseEnd_587075 < baseStart_587075 := by decide
  rcases family_descends (prefixWord ++ tailWord_587075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587076 : List Nat := [2, 3, 4, 1, 1, 3, 1, 2, 1, 5]
def baseStart_587076 : Nat := 118140960795 + 587076 * 2 ^ 59
def prefixEnd_587076 : Nat := 4983230072969 + 3 ^ 40 * 587076 * 2
def baseEnd_587076 : Nat := 100484056239683432050031

theorem tailTrace_587076 : CollatzResearch.WordTrace tailWord_587076 prefixEnd_587076 100484056239683432050031 := by
  unfold tailWord_587076
  simp only [CollatzResearch.WordTrace]
  refine ⟨10706210410565695721718541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14274947214087594295624721 10706210410565695721718541)
  ·
    refine ⟨4014828903962135895644453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10706210410565695721718541 4014828903962135895644453)
    ·
      refine ⟨752780419492900480433335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4014828903962135895644453 752780419492900480433335)
      ·
        refine ⟨1129170629239350720650003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 752780419492900480433335 1129170629239350720650003)
        ·
          refine ⟨1693755943859026080975005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1129170629239350720650003 1693755943859026080975005)
          ·
            refine ⟨635158478947134780365627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1693755943859026080975005 635158478947134780365627)
            ·
              refine ⟨952737718420702170548441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 635158478947134780365627 952737718420702170548441)
              ·
                refine ⟨714553288815526627911331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 952737718420702170548441 714553288815526627911331)
                ·
                  refine ⟨1071829933223289941866997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 714553288815526627911331 1071829933223289941866997)
                  ·
                    refine ⟨100484056239683432050031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1071829933223289941866997 100484056239683432050031)
                    ·
                      rfl

theorem cell23_587076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_587076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_587076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_587076 prefixEnd_587076 := by exact prefixLift 587076
  have htrace : WordTrace (prefixWord ++ tailWord_587076) baseStart_587076 baseEnd_587076 := by
    simpa [prefixWord, tailWord_587076, baseEnd_587076] using wordTrace_append hprefix tailTrace_587076
  have hstable : (prefixWord ++ tailWord_587076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587076).length < 2 ^ (prefixWord ++ tailWord_587076).sum := by decide
  have hdescent : baseEnd_587076 < baseStart_587076 := by decide
  rcases family_descends (prefixWord ++ tailWord_587076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587079 : List Nat := [1, 1, 4, 1, 2, 5, 1, 2, 1, 1, 4]
def baseStart_587079 : Nat := 118140960795 + 587079 * 2 ^ 59
def prefixEnd_587079 : Nat := 4983230072969 + 3 ^ 40 * 587079 * 2
def baseEnd_587079 : Nat := 301453709161013784412579

theorem tailTrace_587079 : CollatzResearch.WordTrace tailWord_587079 prefixEnd_587079 301453709161013784412579 := by
  unfold tailWord_587079
  simp only [CollatzResearch.WordTrace]
  refine ⟨21412530240120522955796291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14275020160080348637197527 21412530240120522955796291)
  ·
    refine ⟨32118795360180784433694437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21412530240120522955796291 32118795360180784433694437)
    ·
      refine ⟨6022274130033897081317707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32118795360180784433694437 6022274130033897081317707)
      ·
        refine ⟨9033411195050845621976561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6022274130033897081317707 9033411195050845621976561)
        ·
          refine ⟨6775058396288134216482421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9033411195050845621976561 6775058396288134216482421)
          ·
            refine ⟨635161724652012582795227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6775058396288134216482421 635161724652012582795227)
            ·
              refine ⟨952742586978018874192841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 635161724652012582795227 952742586978018874192841)
              ·
                refine ⟨714556940233514155644631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 952742586978018874192841 714556940233514155644631)
                ·
                  refine ⟨1071835410350271233466947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 714556940233514155644631 1071835410350271233466947)
                  ·
                    refine ⟨1607753115525406850200421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1071835410350271233466947 1607753115525406850200421)
                    ·
                      refine ⟨301453709161013784412579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1607753115525406850200421 301453709161013784412579)
                      ·
                        rfl

theorem cell23_587079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 2, 1, 1, 4].length) (baseStart_587079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_587079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_587079 prefixEnd_587079 := by exact prefixLift 587079
  have htrace : WordTrace (prefixWord ++ tailWord_587079) baseStart_587079 baseEnd_587079 := by
    simpa [prefixWord, tailWord_587079, baseEnd_587079] using wordTrace_append hprefix tailTrace_587079
  have hstable : (prefixWord ++ tailWord_587079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587079).length < 2 ^ (prefixWord ++ tailWord_587079).sum := by decide
  have hdescent : baseEnd_587079 < baseStart_587079 := by decide
  rcases family_descends (prefixWord ++ tailWord_587079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587092 : List Nat := [2, 4, 1, 1, 2, 1, 3, 2, 1, 2, 4]
def baseStart_587092 : Nat := 118140960795 + 587092 * 2 ^ 59
def prefixEnd_587092 : Nat := 4983230072969 + 3 ^ 40 * 587092 * 2
def baseEnd_587092 : Nat := 301460384409522233550019

theorem tailTrace_587092 : CollatzResearch.WordTrace tailWord_587092 prefixEnd_587092 301460384409522233550019 := by
  unfold tailWord_587092
  simp only [CollatzResearch.WordTrace]
  refine ⟨10706502194536713088009765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14275336259382284117346353 10706502194536713088009765)
  ·
    refine ⟨2007469161475633704001831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10706502194536713088009765 2007469161475633704001831)
    ·
      refine ⟨3011203742213450556002747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2007469161475633704001831 3011203742213450556002747)
      ·
        refine ⟨4516805613320175834004121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3011203742213450556002747 4516805613320175834004121)
        ·
          refine ⟨3387604209990131875503091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4516805613320175834004121 3387604209990131875503091)
          ·
            refine ⟨5081406314985197813254637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3387604209990131875503091 5081406314985197813254637)
            ·
              refine ⟨1905527368119449179970489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5081406314985197813254637 1905527368119449179970489)
              ·
                refine ⟨1429145526089586884977867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1905527368119449179970489 1429145526089586884977867)
                ·
                  refine ⟨2143718289134380327466801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1429145526089586884977867 2143718289134380327466801)
                  ·
                    refine ⟨1607788716850785245600101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2143718289134380327466801 1607788716850785245600101)
                    ·
                      refine ⟨301460384409522233550019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1607788716850785245600101 301460384409522233550019)
                      ·
                        rfl

theorem cell23_587092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_587092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_587092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_587092 prefixEnd_587092 := by exact prefixLift 587092
  have htrace : WordTrace (prefixWord ++ tailWord_587092) baseStart_587092 baseEnd_587092 := by
    simpa [prefixWord, tailWord_587092, baseEnd_587092] using wordTrace_append hprefix tailTrace_587092
  have hstable : (prefixWord ++ tailWord_587092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587092).length < 2 ^ (prefixWord ++ tailWord_587092).sum := by decide
  have hdescent : baseEnd_587092 < baseStart_587092 := by decide
  rcases family_descends (prefixWord ++ tailWord_587092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587096 : List Nat := [2, 1, 2, 2, 1, 1, 4, 5, 1, 2, 2]
def baseStart_587096 : Nat := 118140960795 + 587096 * 2 ^ 59
def prefixEnd_587096 : Nat := 4983230072969 + 3 ^ 40 * 587096 * 2
def baseEnd_587096 : Nat := 301462438332140217900001

theorem tailTrace_587096 : CollatzResearch.WordTrace tailWord_587096 prefixEnd_587096 301462438332140217900001 := by
  unfold tailWord_587096
  simp only [CollatzResearch.WordTrace]
  refine ⟨10706575140529467429582571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14275433520705956572776761 10706575140529467429582571)
  ·
    refine ⟨16059862710794201144373857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10706575140529467429582571 16059862710794201144373857)
    ·
      refine ⟨12044897033095650858280393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16059862710794201144373857 12044897033095650858280393)
      ·
        refine ⟨9033672774821738143710295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12044897033095650858280393 9033672774821738143710295)
        ·
          refine ⟨13550509162232607215565443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9033672774821738143710295 13550509162232607215565443)
          ·
            refine ⟨20325763743348910823348165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13550509162232607215565443 20325763743348910823348165)
            ·
              refine ⟨3811080701877920779377781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20325763743348910823348165 3811080701877920779377781)
              ·
                refine ⟨357288815801055073066667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3811080701877920779377781 357288815801055073066667)
                ·
                  refine ⟨535933223701582609600001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 357288815801055073066667 535933223701582609600001)
                  ·
                    refine ⟨401949917776186957200001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 535933223701582609600001 401949917776186957200001)
                    ·
                      refine ⟨301462438332140217900001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 401949917776186957200001 301462438332140217900001)
                      ·
                        rfl

theorem cell23_587096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 5, 1, 2, 2].length) (baseStart_587096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_587096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_587096 prefixEnd_587096 := by exact prefixLift 587096
  have htrace : WordTrace (prefixWord ++ tailWord_587096) baseStart_587096 baseEnd_587096 := by
    simpa [prefixWord, tailWord_587096, baseEnd_587096] using wordTrace_append hprefix tailTrace_587096
  have hstable : (prefixWord ++ tailWord_587096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587096).length < 2 ^ (prefixWord ++ tailWord_587096).sum := by decide
  have hdescent : baseEnd_587096 < baseStart_587096 := by decide
  rcases family_descends (prefixWord ++ tailWord_587096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587129 : List Nat := [1, 2, 1, 3, 2, 1, 4, 3, 2, 1, 3]
def baseStart_587129 : Nat := 118140960795 + 587129 * 2 ^ 59
def prefixEnd_587129 : Nat := 4983230072969 + 3 ^ 40 * 587129 * 2
def baseEnd_587129 : Nat := 301479383193738588787349

theorem tailTrace_587129 : CollatzResearch.WordTrace tailWord_587129 prefixEnd_587129 301479383193738588787349 := by
  unfold tailWord_587129
  simp only [CollatzResearch.WordTrace]
  refine ⟨21414353889939381495116441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14276235926626254330077627 21414353889939381495116441)
  ·
    refine ⟨16060765417454536121337331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21414353889939381495116441 16060765417454536121337331)
    ·
      refine ⟨24091148126181804182005997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16060765417454536121337331 24091148126181804182005997)
      ·
        refine ⟨9034180547318176568252249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24091148126181804182005997 9034180547318176568252249)
        ·
          refine ⟨6775635410488632426189187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9034180547318176568252249 6775635410488632426189187)
          ·
            refine ⟨10163453115732948639283781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6775635410488632426189187 10163453115732948639283781)
            ·
              refine ⟨1905647459199927869865709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10163453115732948639283781 1905647459199927869865709)
              ·
                refine ⟨714617797199972951199641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1905647459199927869865709 714617797199972951199641)
                ·
                  refine ⟨535963347899979713399731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 714617797199972951199641 535963347899979713399731)
                  ·
                    refine ⟨803945021849969570099597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 535963347899979713399731 803945021849969570099597)
                    ·
                      refine ⟨301479383193738588787349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 803945021849969570099597 301479383193738588787349)
                      ·
                        rfl

theorem cell23_587129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 3, 2, 1, 3].length) (baseStart_587129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_587129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_587129 prefixEnd_587129 := by exact prefixLift 587129
  have htrace : WordTrace (prefixWord ++ tailWord_587129) baseStart_587129 baseEnd_587129 := by
    simpa [prefixWord, tailWord_587129, baseEnd_587129] using wordTrace_append hprefix tailTrace_587129
  have hstable : (prefixWord ++ tailWord_587129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587129).length < 2 ^ (prefixWord ++ tailWord_587129).sum := by decide
  have hdescent : baseEnd_587129 < baseStart_587129 := by decide
  rcases family_descends (prefixWord ++ tailWord_587129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587139 : List Nat := [1, 1, 1, 3, 5, 1, 2, 1, 3, 3, 2]
def baseStart_587139 : Nat := 118140960795 + 587139 * 2 ^ 59
def prefixEnd_587139 : Nat := 4983230072969 + 3 ^ 40 * 587139 * 2
def baseEnd_587139 : Nat := 301484518000283549662303

theorem tailTrace_587139 : CollatzResearch.WordTrace tailWord_587139 prefixEnd_587139 301484518000283549662303 := by
  unfold tailWord_587139
  simp only [CollatzResearch.WordTrace]
  refine ⟨21414718619903153202980471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14276479079935435468653647 21414718619903153202980471)
  ·
    refine ⟨32122077929854729804470707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21414718619903153202980471 32122077929854729804470707)
    ·
      refine ⟨48183116894782094706706061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32122077929854729804470707 48183116894782094706706061)
      ·
        refine ⟨18068668835543285515014773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48183116894782094706706061 18068668835543285515014773)
        ·
          refine ⟨1693937703332183017032635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18068668835543285515014773 1693937703332183017032635)
          ·
            refine ⟨2540906554998274525548953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1693937703332183017032635 2540906554998274525548953)
            ·
              refine ⟨1905679916248705894161715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2540906554998274525548953 1905679916248705894161715)
              ·
                refine ⟨2858519874373058841242573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1905679916248705894161715 2858519874373058841242573)
                ·
                  refine ⟨1071944952889897065465965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2858519874373058841242573 1071944952889897065465965)
                  ·
                    refine ⟨401979357333711399549737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1071944952889897065465965 401979357333711399549737)
                    ·
                      refine ⟨301484518000283549662303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 401979357333711399549737 301484518000283549662303)
                      ·
                        rfl

theorem cell23_587139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 3, 3, 2].length) (baseStart_587139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_587139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_587139 prefixEnd_587139 := by exact prefixLift 587139
  have htrace : WordTrace (prefixWord ++ tailWord_587139) baseStart_587139 baseEnd_587139 := by
    simpa [prefixWord, tailWord_587139, baseEnd_587139] using wordTrace_append hprefix tailTrace_587139
  have hstable : (prefixWord ++ tailWord_587139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587139).length < 2 ^ (prefixWord ++ tailWord_587139).sum := by decide
  have hdescent : baseEnd_587139 < baseStart_587139 := by decide
  rcases family_descends (prefixWord ++ tailWord_587139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587150 : List Nat := [4, 1, 1, 4, 3, 1, 2, 1, 1, 2, 3]
def baseStart_587150 : Nat := 118140960795 + 587150 * 2 ^ 59
def prefixEnd_587150 : Nat := 4983230072969 + 3 ^ 40 * 587150 * 2
def baseEnd_587150 : Nat := 301490166287483006624753

theorem tailTrace_587150 : CollatzResearch.WordTrace tailWord_587150 prefixEnd_587150 301490166287483006624753 := by
  unfold tailWord_587150
  simp only [CollatzResearch.WordTrace]
  refine ⟨2676889977857912760203863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14276746548575534721087269 2676889977857912760203863)
  ·
    refine ⟨4015334966786869140305795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2676889977857912760203863 4015334966786869140305795)
    ·
      refine ⟨6023002450180303710458693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4015334966786869140305795 6023002450180303710458693)
      ·
        refine ⟨1129312959408806945711005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6023002450180303710458693 1129312959408806945711005)
        ·
          refine ⟨423492359778302604641627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1129312959408806945711005 423492359778302604641627)
          ·
            refine ⟨635238539667453906962441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 423492359778302604641627 635238539667453906962441)
            ·
              refine ⟨476428904750590430221831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 635238539667453906962441 476428904750590430221831)
              ·
                refine ⟨714643357125885645332747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 476428904750590430221831 714643357125885645332747)
                ·
                  refine ⟨1071965035688828467999121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 714643357125885645332747 1071965035688828467999121)
                  ·
                    refine ⟨803973776766621350999341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1071965035688828467999121 803973776766621350999341)
                    ·
                      refine ⟨301490166287483006624753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 803973776766621350999341 301490166287483006624753)
                      ·
                        rfl

theorem cell23_587150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_587150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_587150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_587150 prefixEnd_587150 := by exact prefixLift 587150
  have htrace : WordTrace (prefixWord ++ tailWord_587150) baseStart_587150 baseEnd_587150 := by
    simpa [prefixWord, tailWord_587150, baseEnd_587150] using wordTrace_append hprefix tailTrace_587150
  have hstable : (prefixWord ++ tailWord_587150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587150).length < 2 ^ (prefixWord ++ tailWord_587150).sum := by decide
  have hdescent : baseEnd_587150 < baseStart_587150 := by decide
  rcases family_descends (prefixWord ++ tailWord_587150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587226 : List Nat := [3, 1, 1, 2, 3, 3, 3, 2, 5]
def baseStart_587226 : Nat := 118140960795 + 587226 * 2 ^ 59
def prefixEnd_587226 : Nat := 4983230072969 + 3 ^ 40 * 587226 * 2
def baseEnd_587226 : Nat := 33503243424136078808267

theorem tailTrace_587226 : CollatzResearch.WordTrace tailWord_587226 prefixEnd_587226 33503243424136078808267 := by
  unfold tailWord_587226
  simp only [CollatzResearch.WordTrace]
  refine ⟨5354472942646991765349383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14278594513725311374265021 5354472942646991765349383)
  ·
    refine ⟨8031709413970487648024075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5354472942646991765349383 8031709413970487648024075)
    ·
      refine ⟨12047564120955731472036113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8031709413970487648024075 12047564120955731472036113)
      ·
        refine ⟨9035673090716798604027085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12047564120955731472036113 9035673090716798604027085)
        ·
          refine ⟨3388377409018799476510157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9035673090716798604027085 3388377409018799476510157)
          ·
            refine ⟨1270641528382049803691309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3388377409018799476510157 1270641528382049803691309)
            ·
              refine ⟨476490573143268676384241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1270641528382049803691309 476490573143268676384241)
              ·
                refine ⟨357367929857451507288181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 476490573143268676384241 357367929857451507288181)
                ·
                  refine ⟨33503243424136078808267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 357367929857451507288181 33503243424136078808267)
                  ·
                    rfl

theorem cell23_587226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 3, 2, 5].length) (baseStart_587226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_587226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_587226 prefixEnd_587226 := by exact prefixLift 587226
  have htrace : WordTrace (prefixWord ++ tailWord_587226) baseStart_587226 baseEnd_587226 := by
    simpa [prefixWord, tailWord_587226, baseEnd_587226] using wordTrace_append hprefix tailTrace_587226
  have hstable : (prefixWord ++ tailWord_587226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587226).length < 2 ^ (prefixWord ++ tailWord_587226).sum := by decide
  have hdescent : baseEnd_587226 < baseStart_587226 := by decide
  rcases family_descends (prefixWord ++ tailWord_587226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587277 : List Nat := [1, 7, 1, 1, 2, 2, 2, 2, 5]
def baseStart_587277 : Nat := 118140960795 + 587277 * 2 ^ 59
def prefixEnd_587277 : Nat := 4983230072969 + 3 ^ 40 * 587277 * 2
def baseEnd_587277 : Nat := 33506153147844889970741

theorem tailTrace_587277 : CollatzResearch.WordTrace tailWord_587277 prefixEnd_587277 33506153147844889970741 := by
  unfold tailWord_587277
  simp only [CollatzResearch.WordTrace]
  refine ⟨21419751893403202771504085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14279834595602135181002723 21419751893403202771504085)
  ·
    refine ⟨502025435001637564957127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 21419751893403202771504085 502025435001637564957127)
    ·
      refine ⟨753038152502456347435691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 502025435001637564957127 753038152502456347435691)
      ·
        refine ⟨1129557228753684521153537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 753038152502456347435691 1129557228753684521153537)
        ·
          refine ⟨847167921565263390865153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1129557228753684521153537 847167921565263390865153)
          ·
            refine ⟨635375941173947543148865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 847167921565263390865153 635375941173947543148865)
            ·
              refine ⟨476531955880460657361649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 635375941173947543148865 476531955880460657361649)
              ·
                refine ⟨357398966910345493021237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 476531955880460657361649 357398966910345493021237)
                ·
                  refine ⟨33506153147844889970741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 357398966910345493021237 33506153147844889970741)
                  ·
                    rfl

theorem cell23_587277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_587277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_587277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_587277 prefixEnd_587277 := by exact prefixLift 587277
  have htrace : WordTrace (prefixWord ++ tailWord_587277) baseStart_587277 baseEnd_587277 := by
    simpa [prefixWord, tailWord_587277, baseEnd_587277] using wordTrace_append hprefix tailTrace_587277
  have hstable : (prefixWord ++ tailWord_587277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587277).length < 2 ^ (prefixWord ++ tailWord_587277).sum := by decide
  have hdescent : baseEnd_587277 < baseStart_587277 := by decide
  rcases family_descends (prefixWord ++ tailWord_587277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587369 : List Nat := [1, 2, 1, 1, 1, 4, 2, 3, 3, 2, 3]
def baseStart_587369 : Nat := 118140960795 + 587369 * 2 ^ 59
def prefixEnd_587369 : Nat := 4983230072969 + 3 ^ 40 * 587369 * 2
def baseEnd_587369 : Nat := 301602618550817649786245

theorem tailTrace_587369 : CollatzResearch.WordTrace tailWord_587369 prefixEnd_587369 301602618550817649786245 := by
  unfold tailWord_587369
  simp only [CollatzResearch.WordTrace]
  refine ⟨21423107409069902483853161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14282071606046601655902107 21423107409069902483853161)
  ·
    refine ⟨16067330556802426862889871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21423107409069902483853161 16067330556802426862889871)
    ·
      refine ⟨24100995835203640294334807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16067330556802426862889871 24100995835203640294334807)
      ·
        refine ⟨36151493752805460441502211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24100995835203640294334807 36151493752805460441502211)
        ·
          refine ⟨54227240629208190662253317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36151493752805460441502211 54227240629208190662253317)
          ·
            refine ⟨10167607617976535749172497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54227240629208190662253317 10167607617976535749172497)
            ·
              refine ⟨7625705713482401811879373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10167607617976535749172497 7625705713482401811879373)
              ·
                refine ⟨2859639642555900679454765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7625705713482401811879373 2859639642555900679454765)
                ·
                  refine ⟨1072364865958462754795537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2859639642555900679454765 1072364865958462754795537)
                  ·
                    refine ⟨804273649468847066096653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1072364865958462754795537 804273649468847066096653)
                    ·
                      refine ⟨301602618550817649786245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 804273649468847066096653 301602618550817649786245)
                      ·
                        rfl

theorem cell23_587369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 3, 2, 3].length) (baseStart_587369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_587369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_587369 prefixEnd_587369 := by exact prefixLift 587369
  have htrace : WordTrace (prefixWord ++ tailWord_587369) baseStart_587369 baseEnd_587369 := by
    simpa [prefixWord, tailWord_587369, baseEnd_587369] using wordTrace_append hprefix tailTrace_587369
  have hstable : (prefixWord ++ tailWord_587369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587369).length < 2 ^ (prefixWord ++ tailWord_587369).sum := by decide
  have hdescent : baseEnd_587369 < baseStart_587369 := by decide
  rcases family_descends (prefixWord ++ tailWord_587369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587389 : List Nat := [1, 4, 1, 1, 4, 3, 9]
def baseStart_587389 : Nat := 118140960795 + 587389 * 2 ^ 59
def prefixEnd_587389 : Nat := 4983230072969 + 3 ^ 40 * 587389 * 2
def baseEnd_587389 : Nat := 3723615903258118167113

theorem tailTrace_587389 : CollatzResearch.WordTrace tailWord_587389 prefixEnd_587389 3723615903258118167113 := by
  unfold tailWord_587389
  simp only [CollatzResearch.WordTrace]
  refine ⟨21423836868997445899581221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14282557912664963933054147 21423836868997445899581221)
  ·
    refine ⟨4016969412937021106171479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21423836868997445899581221 4016969412937021106171479)
    ·
      refine ⟨6025454119405531659257219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4016969412937021106171479 6025454119405531659257219)
      ·
        refine ⟨9038181179108297488885829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6025454119405531659257219 9038181179108297488885829)
        ·
          refine ⟨1694658971082805779166093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9038181179108297488885829 1694658971082805779166093)
          ·
            refine ⟨635497114156052167187285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1694658971082805779166093 635497114156052167187285)
            ·
              refine ⟨3723615903258118167113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 635497114156052167187285 3723615903258118167113)
              ·
                rfl

theorem cell23_587389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 9].length) (baseStart_587389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_587389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_587389 prefixEnd_587389 := by exact prefixLift 587389
  have htrace : WordTrace (prefixWord ++ tailWord_587389) baseStart_587389 baseEnd_587389 := by
    simpa [prefixWord, tailWord_587389, baseEnd_587389] using wordTrace_append hprefix tailTrace_587389
  have hstable : (prefixWord ++ tailWord_587389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587389).length < 2 ^ (prefixWord ++ tailWord_587389).sum := by decide
  have hdescent : baseEnd_587389 < baseStart_587389 := by decide
  rcases family_descends (prefixWord ++ tailWord_587389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587420 : List Nat := [2, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3]
def baseStart_587420 : Nat := 118140960795 + 587420 * 2 ^ 59
def prefixEnd_587420 : Nat := 4983230072969 + 3 ^ 40 * 587420 * 2
def baseEnd_587420 : Nat := 301628806064196950248511

theorem tailTrace_587420 : CollatzResearch.WordTrace tailWord_587420 prefixEnd_587420 301628806064196950248511 := by
  unfold tailWord_587420
  simp only [CollatzResearch.WordTrace]
  refine ⟨10712483765942569096979857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14283311687923425462639809 10712483765942569096979857)
  ·
    refine ⟨8034362824456926822734893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10712483765942569096979857 8034362824456926822734893)
    ·
      refine ⟨3012886059171347558525585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8034362824456926822734893 3012886059171347558525585)
      ·
        refine ⟨2259664544378510668894189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3012886059171347558525585 2259664544378510668894189)
        ·
          refine ⟨847374204141941500835321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2259664544378510668894189 847374204141941500835321)
          ·
            refine ⟨635530653106456125626491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 847374204141941500835321 635530653106456125626491)
            ·
              refine ⟨953295979659684188439737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 635530653106456125626491 953295979659684188439737)
              ·
                refine ⟨714971984744763141329803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 953295979659684188439737 714971984744763141329803)
                ·
                  refine ⟨1072457977117144711994705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 714971984744763141329803 1072457977117144711994705)
                  ·
                    refine ⟨804343482837858533996029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1072457977117144711994705 804343482837858533996029)
                    ·
                      refine ⟨301628806064196950248511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 804343482837858533996029 301628806064196950248511)
                      ·
                        rfl

theorem cell23_587420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_587420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_587420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_587420 prefixEnd_587420 := by exact prefixLift 587420
  have htrace : WordTrace (prefixWord ++ tailWord_587420) baseStart_587420 baseEnd_587420 := by
    simpa [prefixWord, tailWord_587420, baseEnd_587420] using wordTrace_append hprefix tailTrace_587420
  have hstable : (prefixWord ++ tailWord_587420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587420).length < 2 ^ (prefixWord ++ tailWord_587420).sum := by decide
  have hdescent : baseEnd_587420 < baseStart_587420 := by decide
  rcases family_descends (prefixWord ++ tailWord_587420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587456 : List Nat := [2, 1, 1, 2, 4, 1, 1, 2, 3, 4, 2]
def baseStart_587456 : Nat := 118140960795 + 587456 * 2 ^ 59
def prefixEnd_587456 : Nat := 4983230072969 + 3 ^ 40 * 587456 * 2
def baseEnd_587456 : Nat := 301647291367758809398345

theorem tailTrace_587456 : CollatzResearch.WordTrace tailWord_587456 prefixEnd_587456 301647291367758809398345 := by
  unfold tailWord_587456
  simp only [CollatzResearch.WordTrace]
  refine ⟨10713140279877358171135111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14284187039836477561513481 10713140279877358171135111)
  ·
    refine ⟨16069710419816037256702667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10713140279877358171135111 16069710419816037256702667)
    ·
      refine ⟨24104565629724055885054001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16069710419816037256702667 24104565629724055885054001)
      ·
        refine ⟨18078424222293041913790501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24104565629724055885054001 18078424222293041913790501)
        ·
          refine ⟨3389704541679945358835719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18078424222293041913790501 3389704541679945358835719)
          ·
            refine ⟨5084556812519918038253579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3389704541679945358835719 5084556812519918038253579)
            ·
              refine ⟨7626835218779877057380369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5084556812519918038253579 7626835218779877057380369)
              ·
                refine ⟨5720126414084907793035277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7626835218779877057380369 5720126414084907793035277)
                ·
                  refine ⟨2145047405281840422388229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5720126414084907793035277 2145047405281840422388229)
                  ·
                    refine ⟨402196388490345079197793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2145047405281840422388229 402196388490345079197793)
                    ·
                      refine ⟨301647291367758809398345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 402196388490345079197793 301647291367758809398345)
                      ·
                        rfl

theorem cell23_587456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 3, 4, 2].length) (baseStart_587456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_587456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_587456 prefixEnd_587456 := by exact prefixLift 587456
  have htrace : WordTrace (prefixWord ++ tailWord_587456) baseStart_587456 baseEnd_587456 := by
    simpa [prefixWord, tailWord_587456, baseEnd_587456] using wordTrace_append hprefix tailTrace_587456
  have hstable : (prefixWord ++ tailWord_587456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587456).length < 2 ^ (prefixWord ++ tailWord_587456).sum := by decide
  have hdescent : baseEnd_587456 < baseStart_587456 := by decide
  rcases family_descends (prefixWord ++ tailWord_587456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587466 : List Nat := [3, 1, 2, 1, 5, 1, 1, 1, 2, 6]
def baseStart_587466 : Nat := 118140960795 + 587466 * 2 ^ 59
def prefixEnd_587466 : Nat := 4983230072969 + 3 ^ 40 * 587466 * 2
def baseEnd_587466 : Nat := 100550808724767923424433

theorem tailTrace_587466 : CollatzResearch.WordTrace tailWord_587466 prefixEnd_587466 100550808724767923424433 := by
  unfold tailWord_587466
  simp only [CollatzResearch.WordTrace]
  refine ⟨5356661322429622012533563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14284430193145658700089501 5356661322429622012533563)
  ·
    refine ⟨8034991983644433018800345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5356661322429622012533563 8034991983644433018800345)
    ·
      refine ⟨6026243987733324764100259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8034991983644433018800345 6026243987733324764100259)
      ·
        refine ⟨9039365981599987146150389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6026243987733324764100259 9039365981599987146150389)
        ·
          refine ⟨847440560774998794951599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9039365981599987146150389 847440560774998794951599)
          ·
            refine ⟨1271160841162498192427399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 847440560774998794951599 1271160841162498192427399)
            ·
              refine ⟨1906741261743747288641099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1271160841162498192427399 1906741261743747288641099)
              ·
                refine ⟨2860111892615620932961649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1906741261743747288641099 2860111892615620932961649)
                ·
                  refine ⟨2145083919461715699721237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2860111892615620932961649 2145083919461715699721237)
                  ·
                    refine ⟨100550808724767923424433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2145083919461715699721237 100550808724767923424433)
                    ·
                      rfl

theorem cell23_587466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 2, 6].length) (baseStart_587466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_587466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_587466 prefixEnd_587466 := by exact prefixLift 587466
  have htrace : WordTrace (prefixWord ++ tailWord_587466) baseStart_587466 baseEnd_587466 := by
    simpa [prefixWord, tailWord_587466, baseEnd_587466] using wordTrace_append hprefix tailTrace_587466
  have hstable : (prefixWord ++ tailWord_587466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587466).length < 2 ^ (prefixWord ++ tailWord_587466).sum := by decide
  have hdescent : baseEnd_587466 < baseStart_587466 := by decide
  rcases family_descends (prefixWord ++ tailWord_587466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587473 : List Nat := [1, 2, 2, 1, 2, 5, 2, 1, 1, 4, 2]
def baseStart_587473 : Nat := 118140960795 + 587473 * 2 ^ 59
def prefixEnd_587473 : Nat := 4983230072969 + 3 ^ 40 * 587473 * 2
def baseEnd_587473 : Nat := 301656020538885242885767

theorem tailTrace_587473 : CollatzResearch.WordTrace tailWord_587473 prefixEnd_587473 301656020538885242885767 := by
  unfold tailWord_587473
  simp only [CollatzResearch.WordTrace]
  refine ⟨21426900600693128245639073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14284600400462085497092715 21426900600693128245639073)
  ·
    refine ⟨16070175450519846184229305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21426900600693128245639073 16070175450519846184229305)
    ·
      refine ⟨12052631587889884638171979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16070175450519846184229305 12052631587889884638171979)
      ·
        refine ⟨18078947381834826957257969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12052631587889884638171979 18078947381834826957257969)
        ·
          refine ⟨13559210536376120217943477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18078947381834826957257969 13559210536376120217943477)
          ·
            refine ⟨1271175987785261270432201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13559210536376120217943477 1271175987785261270432201)
            ·
              refine ⟨953381990838945952824151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1271175987785261270432201 953381990838945952824151)
              ·
                refine ⟨1430072986258418929236227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 953381990838945952824151 1430072986258418929236227)
                ·
                  refine ⟨2145109479387628393854341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1430072986258418929236227 2145109479387628393854341)
                  ·
                    refine ⟨402208027385180323847689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2145109479387628393854341 402208027385180323847689)
                    ·
                      refine ⟨301656020538885242885767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 402208027385180323847689 301656020538885242885767)
                      ·
                        rfl

theorem cell23_587473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 1, 1, 4, 2].length) (baseStart_587473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_587473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_587473 prefixEnd_587473 := by exact prefixLift 587473
  have htrace : WordTrace (prefixWord ++ tailWord_587473) baseStart_587473 baseEnd_587473 := by
    simpa [prefixWord, tailWord_587473, baseEnd_587473] using wordTrace_append hprefix tailTrace_587473
  have hstable : (prefixWord ++ tailWord_587473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587473).length < 2 ^ (prefixWord ++ tailWord_587473).sum := by decide
  have hdescent : baseEnd_587473 < baseStart_587473 := by decide
  rcases family_descends (prefixWord ++ tailWord_587473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587479 : List Nat := [1, 1, 3, 2, 1, 3, 3, 2, 7]
def baseStart_587479 : Nat := 118140960795 + 587479 * 2 ^ 59
def prefixEnd_587479 : Nat := 4983230072969 + 3 ^ 40 * 587479 * 2
def baseEnd_587479 : Nat := 33517677935868024378971

theorem tailTrace_587479 : CollatzResearch.WordTrace tailWord_587479 prefixEnd_587479 33517677935868024378971 := by
  unfold tailWord_587479
  simp only [CollatzResearch.WordTrace]
  refine ⟨21427119438671391270357491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14284746292447594180238327 21427119438671391270357491)
  ·
    refine ⟨32140679158007086905536237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21427119438671391270357491 32140679158007086905536237)
    ·
      refine ⟨12052754684252657589576089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32140679158007086905536237 12052754684252657589576089)
      ·
        refine ⟨9039566013189493192182067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12052754684252657589576089 9039566013189493192182067)
        ·
          refine ⟨13559349019784239788273101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9039566013189493192182067 13559349019784239788273101)
          ·
            refine ⟨5084755882419089920602413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13559349019784239788273101 5084755882419089920602413)
            ·
              refine ⟨1906783455907158720225905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5084755882419089920602413 1906783455907158720225905)
              ·
                refine ⟨1430087591930369040169429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1906783455907158720225905 1430087591930369040169429)
                ·
                  refine ⟨33517677935868024378971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1430087591930369040169429 33517677935868024378971)
                  ·
                    rfl

theorem cell23_587479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 2, 7].length) (baseStart_587479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_587479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_587479 prefixEnd_587479 := by exact prefixLift 587479
  have htrace : WordTrace (prefixWord ++ tailWord_587479) baseStart_587479 baseEnd_587479 := by
    simpa [prefixWord, tailWord_587479, baseEnd_587479] using wordTrace_append hprefix tailTrace_587479
  have hstable : (prefixWord ++ tailWord_587479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587479).length < 2 ^ (prefixWord ++ tailWord_587479).sum := by decide
  have hdescent : baseEnd_587479 < baseStart_587479 := by decide
  rcases family_descends (prefixWord ++ tailWord_587479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587506 : List Nat := [3, 2, 1, 3, 1, 1, 1, 1, 4, 3, 3]
def baseStart_587506 : Nat := 118140960795 + 587506 * 2 ^ 59
def prefixEnd_587506 : Nat := 4983230072969 + 3 ^ 40 * 587506 * 2
def baseEnd_587506 : Nat := 301672965400483613773115

theorem tailTrace_587506 : CollatzResearch.WordTrace tailWord_587506 prefixEnd_587506 301672965400483613773115 := by
  unfold tailWord_587506
  simp only [CollatzResearch.WordTrace]
  refine ⟨5357026052393393720397593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14285402806382383254393581 5357026052393393720397593)
  ·
    refine ⟨4017769539295045290298195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5357026052393393720397593 4017769539295045290298195)
    ·
      refine ⟨6026654308942567935447293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4017769539295045290298195 6026654308942567935447293)
      ·
        refine ⟨2259995365853462975792735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6026654308942567935447293 2259995365853462975792735)
        ·
          refine ⟨3389993048780194463689103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2259995365853462975792735 3389993048780194463689103)
          ·
            refine ⟨5084989573170291695533655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3389993048780194463689103 5084989573170291695533655)
            ·
              refine ⟨7627484359755437543300483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5084989573170291695533655 7627484359755437543300483)
              ·
                refine ⟨11441226539633156314950725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7627484359755437543300483 11441226539633156314950725)
                ·
                  refine ⟨2145229976181216809053261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11441226539633156314950725 2145229976181216809053261)
                  ·
                    refine ⟨804461241067956303394973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2145229976181216809053261 804461241067956303394973)
                    ·
                      refine ⟨301672965400483613773115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 804461241067956303394973 301672965400483613773115)
                      ·
                        rfl

theorem cell23_587506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_587506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_587506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_587506 prefixEnd_587506 := by exact prefixLift 587506
  have htrace : WordTrace (prefixWord ++ tailWord_587506) baseStart_587506 baseEnd_587506 := by
    simpa [prefixWord, tailWord_587506, baseEnd_587506] using wordTrace_append hprefix tailTrace_587506
  have hstable : (prefixWord ++ tailWord_587506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587506).length < 2 ^ (prefixWord ++ tailWord_587506).sum := by decide
  have hdescent : baseEnd_587506 < baseStart_587506 := by decide
  rcases family_descends (prefixWord ++ tailWord_587506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587519 : List Nat := [1, 1, 2, 2, 1, 3, 2, 3, 1, 2, 5]
def baseStart_587519 : Nat := 118140960795 + 587519 * 2 ^ 59
def prefixEnd_587519 : Nat := 4983230072969 + 3 ^ 40 * 587519 * 2
def baseEnd_587519 : Nat := 301679640648992062910555

theorem tailTrace_587519 : CollatzResearch.WordTrace tailWord_587519 prefixEnd_587519 301679640648992062910555 := by
  unfold tailWord_587519
  simp only [CollatzResearch.WordTrace]
  refine ⟨21428578358526478101813611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14285718905684318734542407 21428578358526478101813611)
  ·
    refine ⟨32142867537789717152720417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21428578358526478101813611 32142867537789717152720417)
    ·
      refine ⟨24107150653342287864540313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32142867537789717152720417 24107150653342287864540313)
      ·
        refine ⟨18080362990006715898405235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24107150653342287864540313 18080362990006715898405235)
        ·
          refine ⟨27120544485010073847607853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18080362990006715898405235 27120544485010073847607853)
          ·
            refine ⟨10170204181878777692852945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27120544485010073847607853 10170204181878777692852945)
            ·
              refine ⟨7627653136409083269639709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10170204181878777692852945 7627653136409083269639709)
              ·
                refine ⟨2860369926153406226114891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7627653136409083269639709 2860369926153406226114891)
                ·
                  refine ⟨4290554889230109339172337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2860369926153406226114891 4290554889230109339172337)
                  ·
                    refine ⟨3217916166922582004379253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4290554889230109339172337 3217916166922582004379253)
                    ·
                      refine ⟨301679640648992062910555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3217916166922582004379253 301679640648992062910555)
                      ·
                        rfl

theorem cell23_587519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 2, 5].length) (baseStart_587519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_587519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_587519 prefixEnd_587519 := by exact prefixLift 587519
  have htrace : WordTrace (prefixWord ++ tailWord_587519) baseStart_587519 baseEnd_587519 := by
    simpa [prefixWord, tailWord_587519, baseEnd_587519] using wordTrace_append hprefix tailTrace_587519
  have hstable : (prefixWord ++ tailWord_587519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587519).length < 2 ^ (prefixWord ++ tailWord_587519).sum := by decide
  have hdescent : baseEnd_587519 < baseStart_587519 := by decide
  rcases family_descends (prefixWord ++ tailWord_587519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587546 : List Nat := [3, 1, 1, 3, 2, 2, 2, 1, 1, 3, 4]
def baseStart_587546 : Nat := 118140960795 + 587546 * 2 ^ 59
def prefixEnd_587546 : Nat := 4983230072969 + 3 ^ 40 * 587546 * 2
def baseEnd_587546 : Nat := 301693504626663457272931

theorem tailTrace_587546 : CollatzResearch.WordTrace tailWord_587546 prefixEnd_587546 301693504626663457272931 := by
  unfold tailWord_587546
  simp only [CollatzResearch.WordTrace]
  refine ⟨5357390782357165428261623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14286375419619107808697661 5357390782357165428261623)
  ·
    refine ⟨8036086173535748142392435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5357390782357165428261623 8036086173535748142392435)
    ·
      refine ⟨12054129260303622213588653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8036086173535748142392435 12054129260303622213588653)
      ·
        refine ⟨4520298472613858330095745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12054129260303622213588653 4520298472613858330095745)
        ·
          refine ⟨3390223854460393747571809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4520298472613858330095745 3390223854460393747571809)
          ·
            refine ⟨2542667890845295310678857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3390223854460393747571809 2542667890845295310678857)
            ·
              refine ⟨1907000918133971483009143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2542667890845295310678857 1907000918133971483009143)
              ·
                refine ⟨2860501377200957224513715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1907000918133971483009143 2860501377200957224513715)
                ·
                  refine ⟨4290752065801435836770573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2860501377200957224513715 4290752065801435836770573)
                  ·
                    refine ⟨1609032024675538438788965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4290752065801435836770573 1609032024675538438788965)
                    ·
                      refine ⟨301693504626663457272931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1609032024675538438788965 301693504626663457272931)
                      ·
                        rfl

theorem cell23_587546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_587546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_587546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_587546 prefixEnd_587546 := by exact prefixLift 587546
  have htrace : WordTrace (prefixWord ++ tailWord_587546) baseStart_587546 baseEnd_587546 := by
    simpa [prefixWord, tailWord_587546, baseEnd_587546] using wordTrace_append hprefix tailTrace_587546
  have hstable : (prefixWord ++ tailWord_587546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587546).length < 2 ^ (prefixWord ++ tailWord_587546).sum := by decide
  have hdescent : baseEnd_587546 < baseStart_587546 := by decide
  rcases family_descends (prefixWord ++ tailWord_587546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587653 : List Nat := [1, 3, 1, 1, 3, 2, 2, 4, 1, 1, 4]
def baseStart_587653 : Nat := 118140960795 + 587653 * 2 ^ 59
def prefixEnd_587653 : Nat := 4983230072969 + 3 ^ 40 * 587653 * 2
def baseEnd_587653 : Nat := 301748447056694538634939

theorem tailTrace_587653 : CollatzResearch.WordTrace tailWord_587653 prefixEnd_587653 301748447056694538634939 := by
  unfold tailWord_587653
  simp only [CollatzResearch.WordTrace]
  refine ⟨21433465740041018987191613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14288977160027345991461075 21433465740041018987191613)
  ·
    refine ⟨8037549652515382120196855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21433465740041018987191613 8037549652515382120196855)
    ·
      refine ⟨12056324478773073180295283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8037549652515382120196855 12056324478773073180295283)
      ·
        refine ⟨18084486718159609770442925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12056324478773073180295283 18084486718159609770442925)
        ·
          refine ⟨6781682519309853663916097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18084486718159609770442925 6781682519309853663916097)
          ·
            refine ⟨5086261889482390247937073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6781682519309853663916097 5086261889482390247937073)
            ·
              refine ⟨3814696417111792685952805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5086261889482390247937073 3814696417111792685952805)
              ·
                refine ⟨715255578208461128616151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3814696417111792685952805 715255578208461128616151)
                ·
                  refine ⟨1072883367312691692924227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 715255578208461128616151 1072883367312691692924227)
                  ·
                    refine ⟨1609325050969037539386341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1072883367312691692924227 1609325050969037539386341)
                    ·
                      refine ⟨301748447056694538634939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1609325050969037539386341 301748447056694538634939)
                      ·
                        rfl

theorem cell23_587653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 4, 1, 1, 4].length) (baseStart_587653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_587653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_587653 prefixEnd_587653 := by exact prefixLift 587653
  have htrace : WordTrace (prefixWord ++ tailWord_587653) baseStart_587653 baseEnd_587653 := by
    simpa [prefixWord, tailWord_587653, baseEnd_587653] using wordTrace_append hprefix tailTrace_587653
  have hstable : (prefixWord ++ tailWord_587653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587653).length < 2 ^ (prefixWord ++ tailWord_587653).sum := by decide
  have hdescent : baseEnd_587653 < baseStart_587653 := by decide
  rcases family_descends (prefixWord ++ tailWord_587653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587687 : List Nat := [1, 1, 6, 1, 2, 1, 1, 3, 3, 2, 2]
def baseStart_587687 : Nat := 118140960795 + 587687 * 2 ^ 59
def prefixEnd_587687 : Nat := 4983230072969 + 3 ^ 40 * 587687 * 2
def baseEnd_587687 : Nat := 301765905398947405609783

theorem tailTrace_587687 : CollatzResearch.WordTrace tailWord_587687 prefixEnd_587687 301765905398947405609783 := by
  unfold tailWord_587687
  simp only [CollatzResearch.WordTrace]
  refine ⟨21434705821917842793929315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14289803881278561862619543 21434705821917842793929315)
  ·
    refine ⟨32152058732876764190893973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21434705821917842793929315 32152058732876764190893973)
    ·
      refine ⟨1507127753103598321448155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 32152058732876764190893973 1507127753103598321448155)
      ·
        refine ⟨2260691629655397482172233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1507127753103598321448155 2260691629655397482172233)
        ·
          refine ⟨1695518722241548111629175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2260691629655397482172233 1695518722241548111629175)
          ·
            refine ⟨2543278083362322167443763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1695518722241548111629175 2543278083362322167443763)
            ·
              refine ⟨3814917125043483251165645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2543278083362322167443763 3814917125043483251165645)
              ·
                refine ⟨1430593921891306219187117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3814917125043483251165645 1430593921891306219187117)
                ·
                  refine ⟨536472720709239832195169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1430593921891306219187117 536472720709239832195169)
                  ·
                    refine ⟨402354540531929874146377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 536472720709239832195169 402354540531929874146377)
                    ·
                      refine ⟨301765905398947405609783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 402354540531929874146377 301765905398947405609783)
                      ·
                        rfl

theorem cell23_587687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 3, 3, 2, 2].length) (baseStart_587687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_587687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_587687 prefixEnd_587687 := by exact prefixLift 587687
  have htrace : WordTrace (prefixWord ++ tailWord_587687) baseStart_587687 baseEnd_587687 := by
    simpa [prefixWord, tailWord_587687, baseEnd_587687] using wordTrace_append hprefix tailTrace_587687
  have hstable : (prefixWord ++ tailWord_587687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587687).length < 2 ^ (prefixWord ++ tailWord_587687).sum := by decide
  have hdescent : baseEnd_587687 < baseStart_587687 := by decide
  rcases family_descends (prefixWord ++ tailWord_587687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587697 : List Nat := [1, 2, 2, 4, 2, 2, 3, 1, 2, 4]
def baseStart_587697 : Nat := 118140960795 + 587697 * 2 ^ 59
def prefixEnd_587697 : Nat := 4983230072969 + 3 ^ 40 * 587697 * 2
def baseEnd_587697 : Nat := 100590346735164122161579

theorem tailTrace_587697 : CollatzResearch.WordTrace tailWord_587697 prefixEnd_587697 100590346735164122161579 := by
  unfold tailWord_587697
  simp only [CollatzResearch.WordTrace]
  refine ⟨21435070551881614501793345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14290047034587743001195563 21435070551881614501793345)
  ·
    refine ⟨16076302913911210876345009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21435070551881614501793345 16076302913911210876345009)
    ·
      refine ⟨12057227185433408157258757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16076302913911210876345009 12057227185433408157258757)
      ·
        refine ⟨2260730097268764029486017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12057227185433408157258757 2260730097268764029486017)
        ·
          refine ⟨1695547572951573022114513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2260730097268764029486017 1695547572951573022114513)
          ·
            refine ⟨1271660679713679766585885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1695547572951573022114513 1271660679713679766585885)
            ·
              refine ⟨476872754892629912469707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1271660679713679766585885 476872754892629912469707)
              ·
                refine ⟨715309132338944868704561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 476872754892629912469707 715309132338944868704561)
                ·
                  refine ⟨536481849254208651528421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 715309132338944868704561 536481849254208651528421)
                  ·
                    refine ⟨100590346735164122161579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 536481849254208651528421 100590346735164122161579)
                    ·
                      rfl

theorem cell23_587697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 3, 1, 2, 4].length) (baseStart_587697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_587697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_587697 prefixEnd_587697 := by exact prefixLift 587697
  have htrace : WordTrace (prefixWord ++ tailWord_587697) baseStart_587697 baseEnd_587697 := by
    simpa [prefixWord, tailWord_587697, baseEnd_587697] using wordTrace_append hprefix tailTrace_587697
  have hstable : (prefixWord ++ tailWord_587697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587697).length < 2 ^ (prefixWord ++ tailWord_587697).sum := by decide
  have hdescent : baseEnd_587697 < baseStart_587697 := by decide
  rcases family_descends (prefixWord ++ tailWord_587697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587710 : List Nat := [4, 2, 1, 1, 1, 5, 2, 7]
def baseStart_587710 : Nat := 118140960795 + 587710 * 2 ^ 59
def prefixEnd_587710 : Nat := 4983230072969 + 3 ^ 40 * 587710 * 2
def baseEnd_587710 : Nat := 11176952424222252430451

theorem tailTrace_587710 : CollatzResearch.WordTrace tailWord_587710 prefixEnd_587710 11176952424222252430451 := by
  unfold tailWord_587710
  simp only [CollatzResearch.WordTrace]
  refine ⟨2679443087604314715252073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14290363133889678481344389 2679443087604314715252073)
  ·
    refine ⟨2009582315703236036439055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2679443087604314715252073 2009582315703236036439055)
    ·
      refine ⟨3014373473554854054658583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2009582315703236036439055 3014373473554854054658583)
      ·
        refine ⟨4521560210332281081987875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3014373473554854054658583 4521560210332281081987875)
        ·
          refine ⟨6782340315498421622981813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4521560210332281081987875 6782340315498421622981813)
          ·
            refine ⟨635844404577977027154545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6782340315498421622981813 635844404577977027154545)
            ·
              refine ⟨476883303433482770365909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 635844404577977027154545 476883303433482770365909)
              ·
                refine ⟨11176952424222252430451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 476883303433482770365909 11176952424222252430451)
                ·
                  rfl

theorem cell23_587710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 2, 7].length) (baseStart_587710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_587710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_587710 prefixEnd_587710 := by exact prefixLift 587710
  have htrace : WordTrace (prefixWord ++ tailWord_587710) baseStart_587710 baseEnd_587710 := by
    simpa [prefixWord, tailWord_587710, baseEnd_587710] using wordTrace_append hprefix tailTrace_587710
  have hstable : (prefixWord ++ tailWord_587710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587710).length < 2 ^ (prefixWord ++ tailWord_587710).sum := by decide
  have hdescent : baseEnd_587710 < baseStart_587710 := by decide
  rcases family_descends (prefixWord ++ tailWord_587710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587720 : List Nat := [2, 1, 3, 1, 4, 1, 1, 2, 4, 1, 3]
def baseStart_587720 : Nat := 118140960795 + 587720 * 2 ^ 59
def prefixEnd_587720 : Nat := 4983230072969 + 3 ^ 40 * 587720 * 2
def baseEnd_587720 : Nat := 301782850260545776497131

theorem tailTrace_587720 : CollatzResearch.WordTrace tailWord_587720 prefixEnd_587720 301782850260545776497131 := by
  unfold tailWord_587720
  simp only [CollatzResearch.WordTrace]
  refine ⟨10717954715399144714940307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14290606287198859619920409 10717954715399144714940307)
  ·
    refine ⟨16076932073098717072410461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10717954715399144714940307 16076932073098717072410461)
    ·
      refine ⟨6028849527412018902153923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16076932073098717072410461 6028849527412018902153923)
      ·
        refine ⟨9043274291118028353230885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6028849527412018902153923 9043274291118028353230885)
        ·
          refine ⟨1695613929584630316230791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9043274291118028353230885 1695613929584630316230791)
          ·
            refine ⟨2543420894376945474346187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1695613929584630316230791 2543420894376945474346187)
            ·
              refine ⟨3815131341565418211519281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2543420894376945474346187 3815131341565418211519281)
              ·
                refine ⟨2861348506174063658639461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3815131341565418211519281 2861348506174063658639461)
                ·
                  refine ⟨536502844907636935994899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2861348506174063658639461 536502844907636935994899)
                  ·
                    refine ⟨804754267361455403992349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 536502844907636935994899 804754267361455403992349)
                    ·
                      refine ⟨301782850260545776497131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 804754267361455403992349 301782850260545776497131)
                      ·
                        rfl

theorem cell23_587720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 4, 1, 3].length) (baseStart_587720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_587720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_587720 prefixEnd_587720 := by exact prefixLift 587720
  have htrace : WordTrace (prefixWord ++ tailWord_587720) baseStart_587720 baseEnd_587720 := by
    simpa [prefixWord, tailWord_587720, baseEnd_587720] using wordTrace_append hprefix tailTrace_587720
  have hstable : (prefixWord ++ tailWord_587720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587720).length < 2 ^ (prefixWord ++ tailWord_587720).sum := by decide
  have hdescent : baseEnd_587720 < baseStart_587720 := by decide
  rcases family_descends (prefixWord ++ tailWord_587720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587756 : List Nat := [2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 6]
def baseStart_587756 : Nat := 118140960795 + 587756 * 2 ^ 59
def prefixEnd_587756 : Nat := 4983230072969 + 3 ^ 40 * 587756 * 2
def baseEnd_587756 : Nat := 301801335564107635646965

theorem tailTrace_587756 : CollatzResearch.WordTrace tailWord_587756 prefixEnd_587756 301801335564107635646965 := by
  unfold tailWord_587756
  simp only [CollatzResearch.WordTrace]
  refine ⟨10718611229333933789095561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14291481639111911718794081 10718611229333933789095561)
  ·
    refine ⟨8038958422000450341821671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10718611229333933789095561 8038958422000450341821671)
    ·
      refine ⟨12058437633000675512732507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8038958422000450341821671 12058437633000675512732507)
      ·
        refine ⟨18087656449501013269098761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12058437633000675512732507 18087656449501013269098761)
        ·
          refine ⟨13565742337125759951824071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18087656449501013269098761 13565742337125759951824071)
          ·
            refine ⟨20348613505688639927736107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13565742337125759951824071 20348613505688639927736107)
            ·
              refine ⟨30522920258532959891604161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20348613505688639927736107 30522920258532959891604161)
              ·
                refine ⟨22892190193899719918703121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30522920258532959891604161 22892190193899719918703121)
                ·
                  refine ⟨17169142645424789939027341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22892190193899719918703121 17169142645424789939027341)
                  ·
                    refine ⟨6438428492034296227135253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17169142645424789939027341 6438428492034296227135253)
                    ·
                      refine ⟨301801335564107635646965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6438428492034296227135253 301801335564107635646965)
                      ·
                        rfl

theorem cell23_587756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 6].length) (baseStart_587756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_587756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_587756 prefixEnd_587756 := by exact prefixLift 587756
  have htrace : WordTrace (prefixWord ++ tailWord_587756) baseStart_587756 baseEnd_587756 := by
    simpa [prefixWord, tailWord_587756, baseEnd_587756] using wordTrace_append hprefix tailTrace_587756
  have hstable : (prefixWord ++ tailWord_587756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587756).length < 2 ^ (prefixWord ++ tailWord_587756).sum := by decide
  have hdescent : baseEnd_587756 < baseStart_587756 := by decide
  rcases family_descends (prefixWord ++ tailWord_587756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587776 : List Nat := [2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 7]
def baseStart_587776 : Nat := 118140960795 + 587776 * 2 ^ 59
def prefixEnd_587776 : Nat := 4983230072969 + 3 ^ 40 * 587776 * 2
def baseEnd_587776 : Nat := 301811605177197557396873

theorem tailTrace_587776 : CollatzResearch.WordTrace tailWord_587776 prefixEnd_587776 301811605177197557396873 := by
  unfold tailWord_587776
  simp only [CollatzResearch.WordTrace]
  refine ⟨10718975959297705496959591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14291967945730273995946121 10718975959297705496959591)
  ·
    refine ⟨16078463938946558245439387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10718975959297705496959591 16078463938946558245439387)
    ·
      refine ⟨24117695908419837368159081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16078463938946558245439387 24117695908419837368159081)
      ·
        refine ⟨18088271931314878026119311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24117695908419837368159081 18088271931314878026119311)
        ·
          refine ⟨27132407896972317039178967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18088271931314878026119311 27132407896972317039178967)
          ·
            refine ⟨40698611845458475558768451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27132407896972317039178967 40698611845458475558768451)
            ·
              refine ⟨61047917768187713338152677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40698611845458475558768451 61047917768187713338152677)
              ·
                refine ⟨11446484581535196250903627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61047917768187713338152677 11446484581535196250903627)
                ·
                  refine ⟨17169726872302794376355441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11446484581535196250903627 17169726872302794376355441)
                  ·
                    refine ⟨12877295154227095782266581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17169726872302794376355441 12877295154227095782266581)
                    ·
                      refine ⟨301811605177197557396873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 12877295154227095782266581 301811605177197557396873)
                      ·
                        rfl

theorem cell23_587776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 7].length) (baseStart_587776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_587776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_587776 prefixEnd_587776 := by exact prefixLift 587776
  have htrace : WordTrace (prefixWord ++ tailWord_587776) baseStart_587776 baseEnd_587776 := by
    simpa [prefixWord, tailWord_587776, baseEnd_587776] using wordTrace_append hprefix tailTrace_587776
  have hstable : (prefixWord ++ tailWord_587776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587776).length < 2 ^ (prefixWord ++ tailWord_587776).sum := by decide
  have hdescent : baseEnd_587776 < baseStart_587776 := by decide
  rcases family_descends (prefixWord ++ tailWord_587776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587789 : List Nat := [1, 7, 1, 2, 2, 1, 2, 2, 1, 2, 2]
def baseStart_587789 : Nat := 118140960795 + 587789 * 2 ^ 59
def prefixEnd_587789 : Nat := 4983230072969 + 3 ^ 40 * 587789 * 2
def baseEnd_587789 : Nat := 301818280425706006534315

theorem tailTrace_587789 : CollatzResearch.WordTrace tailWord_587789 prefixEnd_587789 301818280425706006534315 := by
  unfold tailWord_587789
  simp only [CollatzResearch.WordTrace]
  refine ⟨21438426067548314214142421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14292284045032209476094947 21438426067548314214142421)
  ·
    refine ⟨502463110958163614393963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 21438426067548314214142421 502463110958163614393963)
    ·
      refine ⟨753694666437245421590945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 502463110958163614393963 753694666437245421590945)
      ·
        refine ⟨565270999827934066193209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 753694666437245421590945 565270999827934066193209)
        ·
          refine ⟨423953249870950549644907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 565270999827934066193209 423953249870950549644907)
          ·
            refine ⟨635929874806425824467361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 423953249870950549644907 635929874806425824467361)
            ·
              refine ⟨476947406104819368350521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 635929874806425824467361 476947406104819368350521)
              ·
                refine ⟨357710554578614526262891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 476947406104819368350521 357710554578614526262891)
                ·
                  refine ⟨536565831867921789394337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 357710554578614526262891 536565831867921789394337)
                  ·
                    refine ⟨402424373900941342045753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 536565831867921789394337 402424373900941342045753)
                    ·
                      refine ⟨301818280425706006534315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 402424373900941342045753 301818280425706006534315)
                      ·
                        rfl

theorem cell23_587789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_587789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_587789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_587789 prefixEnd_587789 := by exact prefixLift 587789
  have htrace : WordTrace (prefixWord ++ tailWord_587789) baseStart_587789 baseEnd_587789 := by
    simpa [prefixWord, tailWord_587789, baseEnd_587789] using wordTrace_append hprefix tailTrace_587789
  have hstable : (prefixWord ++ tailWord_587789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587789).length < 2 ^ (prefixWord ++ tailWord_587789).sum := by decide
  have hdescent : baseEnd_587789 < baseStart_587789 := by decide
  rcases family_descends (prefixWord ++ tailWord_587789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587800 : List Nat := [2, 1, 2, 3, 2, 1, 3, 4, 5]
def baseStart_587800 : Nat := 118140960795 + 587800 * 2 ^ 59
def prefixEnd_587800 : Nat := 4983230072969 + 3 ^ 40 * 587800 * 2
def baseEnd_587800 : Nat := 33535992079211718166307

theorem tailTrace_587800 : CollatzResearch.WordTrace tailWord_587800 prefixEnd_587800 33535992079211718166307 := by
  unfold tailWord_587800
  simp only [CollatzResearch.WordTrace]
  refine ⟨10719413635254231546396427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14292551513672308728528569 10719413635254231546396427)
  ·
    refine ⟨16079120452881347319594641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10719413635254231546396427 16079120452881347319594641)
    ·
      refine ⟨12059340339661010489695981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16079120452881347319594641 12059340339661010489695981)
      ·
        refine ⟨4522252627372878933635993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12059340339661010489695981 4522252627372878933635993)
        ·
          refine ⟨3391689470529659200226995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4522252627372878933635993 3391689470529659200226995)
          ·
            refine ⟨5087534205794488800340493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3391689470529659200226995 5087534205794488800340493)
            ·
              refine ⟨1907825327172933300127685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5087534205794488800340493 1907825327172933300127685)
              ·
                refine ⟨357717248844924993773941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1907825327172933300127685 357717248844924993773941)
                ·
                  refine ⟨33535992079211718166307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 357717248844924993773941 33535992079211718166307)
                  ·
                    rfl

theorem cell23_587800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 4, 5].length) (baseStart_587800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_587800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_587800 prefixEnd_587800 := by exact prefixLift 587800
  have htrace : WordTrace (prefixWord ++ tailWord_587800) baseStart_587800 baseEnd_587800 := by
    simpa [prefixWord, tailWord_587800, baseEnd_587800] using wordTrace_append hprefix tailTrace_587800
  have hstable : (prefixWord ++ tailWord_587800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587800).length < 2 ^ (prefixWord ++ tailWord_587800).sum := by decide
  have hdescent : baseEnd_587800 < baseStart_587800 := by decide
  rcases family_descends (prefixWord ++ tailWord_587800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587810 : List Nat := [3, 3, 1, 1, 1, 2, 3, 1, 2, 3, 3]
def baseStart_587810 : Nat := 118140960795 + 587810 * 2 ^ 59
def prefixEnd_587810 : Nat := 4983230072969 + 3 ^ 40 * 587810 * 2
def baseEnd_587810 : Nat := 301829063519450424371717

theorem tailTrace_587810 : CollatzResearch.WordTrace tailWord_587810 prefixEnd_587810 301829063519450424371717 := by
  unfold tailWord_587810
  simp only [CollatzResearch.WordTrace]
  refine ⟨5359798000118058700164221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14292794666981489867104589 5359798000118058700164221)
  ·
    refine ⟨2009924250044272012561583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5359798000118058700164221 2009924250044272012561583)
    ·
      refine ⟨3014886375066408018842375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2009924250044272012561583 3014886375066408018842375)
      ·
        refine ⟨4522329562599612028263563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3014886375066408018842375 4522329562599612028263563)
        ·
          refine ⟨6783494343899418042395345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4522329562599612028263563 6783494343899418042395345)
          ·
            refine ⟨5087620757924563531796509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6783494343899418042395345 5087620757924563531796509)
            ·
              refine ⟨1907857784221711324423691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5087620757924563531796509 1907857784221711324423691)
              ·
                refine ⟨2861786676332566986635537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1907857784221711324423691 2861786676332566986635537)
                ·
                  refine ⟨2146340007249425239976653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2861786676332566986635537 2146340007249425239976653)
                  ·
                    refine ⟨804877502718534464991245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2146340007249425239976653 804877502718534464991245)
                    ·
                      refine ⟨301829063519450424371717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 804877502718534464991245 301829063519450424371717)
                      ·
                        rfl

theorem cell23_587810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 2, 3, 3].length) (baseStart_587810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_587810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_587810 prefixEnd_587810 := by exact prefixLift 587810
  have htrace : WordTrace (prefixWord ++ tailWord_587810) baseStart_587810 baseEnd_587810 := by
    simpa [prefixWord, tailWord_587810, baseEnd_587810] using wordTrace_append hprefix tailTrace_587810
  have hstable : (prefixWord ++ tailWord_587810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587810).length < 2 ^ (prefixWord ++ tailWord_587810).sum := by decide
  have hdescent : baseEnd_587810 < baseStart_587810 := by decide
  rcases family_descends (prefixWord ++ tailWord_587810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587830 : List Nat := [5, 1, 2, 1, 1, 1, 3, 1, 1, 7]
def baseStart_587830 : Nat := 118140960795 + 587830 * 2 ^ 59
def prefixEnd_587830 : Nat := 4983230072969 + 3 ^ 40 * 587830 * 2
def baseEnd_587830 : Nat := 100613111044180115373875

theorem tailTrace_587830 : CollatzResearch.WordTrace tailWord_587830 prefixEnd_587830 100613111044180115373875 := by
  unfold tailWord_587830
  simp only [CollatzResearch.WordTrace]
  refine ⟨1339995091274986138524059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14293280973599852144256629 1339995091274986138524059)
  ·
    refine ⟨2009992636912479207786089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1339995091274986138524059 2009992636912479207786089)
    ·
      refine ⟨1507494477684359405839567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2009992636912479207786089 1507494477684359405839567)
      ·
        refine ⟨2261241716526539108759351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1507494477684359405839567 2261241716526539108759351)
        ·
          refine ⟨3391862574789808663139027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2261241716526539108759351 3391862574789808663139027)
          ·
            refine ⟨5087793862184712994708541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3391862574789808663139027 5087793862184712994708541)
            ·
              refine ⟨1907922698319267373015703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5087793862184712994708541 1907922698319267373015703)
              ·
                refine ⟨2861884047478901059523555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1907922698319267373015703 2861884047478901059523555)
                ·
                  refine ⟨4292826071218351589285333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2861884047478901059523555 4292826071218351589285333)
                  ·
                    refine ⟨100613111044180115373875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4292826071218351589285333 100613111044180115373875)
                    ·
                      rfl

theorem cell23_587830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_587830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_587830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_587830 prefixEnd_587830 := by exact prefixLift 587830
  have htrace : WordTrace (prefixWord ++ tailWord_587830) baseStart_587830 baseEnd_587830 := by
    simpa [prefixWord, tailWord_587830, baseEnd_587830] using wordTrace_append hprefix tailTrace_587830
  have hstable : (prefixWord ++ tailWord_587830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587830).length < 2 ^ (prefixWord ++ tailWord_587830).sum := by decide
  have hdescent : baseEnd_587830 < baseStart_587830 := by decide
  rcases family_descends (prefixWord ++ tailWord_587830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587923 : List Nat := [1, 1, 1, 2, 1, 2, 3, 1, 2, 5, 4]
def baseStart_587923 : Nat := 118140960795 + 587923 * 2 ^ 59
def prefixEnd_587923 : Nat := 4983230072969 + 3 ^ 40 * 587923 * 2
def baseEnd_587923 : Nat := 301887086833408482258697

theorem tailTrace_587923 : CollatzResearch.WordTrace tailWord_587923 prefixEnd_587923 301887086833408482258697 := by
  unfold tailWord_587923
  simp only [CollatzResearch.WordTrace]
  refine ⟨21443313449062855099520423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14295542299375236733013615 21443313449062855099520423)
  ·
    refine ⟨32164970173594282649280635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21443313449062855099520423 32164970173594282649280635)
    ·
      refine ⟨48247455260391423973920953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32164970173594282649280635 48247455260391423973920953)
      ·
        refine ⟨36185591445293567980440715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48247455260391423973920953 36185591445293567980440715)
        ·
          refine ⟨54278387167940351970661073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36185591445293567980440715 54278387167940351970661073)
          ·
            refine ⟨40708790375955263977995805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54278387167940351970661073 40708790375955263977995805)
            ·
              refine ⟨15265796390983223991748427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40708790375955263977995805 15265796390983223991748427)
              ·
                refine ⟨22898694586474835987622641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15265796390983223991748427 22898694586474835987622641)
                ·
                  refine ⟨17174020939856126990716981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22898694586474835987622641 17174020939856126990716981)
                  ·
                    refine ⟨1610064463111511905379717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17174020939856126990716981 1610064463111511905379717)
                    ·
                      refine ⟨301887086833408482258697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1610064463111511905379717 301887086833408482258697)
                      ·
                        rfl

theorem cell23_587923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 5, 4].length) (baseStart_587923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_587923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_587923 prefixEnd_587923 := by exact prefixLift 587923
  have htrace : WordTrace (prefixWord ++ tailWord_587923) baseStart_587923 baseEnd_587923 := by
    simpa [prefixWord, tailWord_587923, baseEnd_587923] using wordTrace_append hprefix tailTrace_587923
  have hstable : (prefixWord ++ tailWord_587923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587923).length < 2 ^ (prefixWord ++ tailWord_587923).sum := by decide
  have hdescent : baseEnd_587923 < baseStart_587923 := by decide
  rcases family_descends (prefixWord ++ tailWord_587923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587924 : List Nat := [2, 4, 2, 3, 1, 1, 1, 3, 6]
def baseStart_587924 : Nat := 118140960795 + 587924 * 2 ^ 59
def prefixEnd_587924 : Nat := 4983230072969 + 3 ^ 40 * 587924 * 2
def baseEnd_587924 : Nat := 33543066701562553149577

theorem tailTrace_587924 : CollatzResearch.WordTrace tailWord_587924 prefixEnd_587924 33543066701562553149577 := by
  unfold tailWord_587924
  simp only [CollatzResearch.WordTrace]
  refine ⟨10721674961029616135153413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14295566614706154846871217 10721674961029616135153413)
  ·
    refine ⟨2010314055193053025341265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10721674961029616135153413 2010314055193053025341265)
    ·
      refine ⟨1507735541394789769005949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2010314055193053025341265 1507735541394789769005949)
      ·
        refine ⟨565400828023046163377231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1507735541394789769005949 565400828023046163377231)
        ·
          refine ⟨848101242034569245065847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 565400828023046163377231 848101242034569245065847)
          ·
            refine ⟨1272151863051853867598771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 848101242034569245065847 1272151863051853867598771)
            ·
              refine ⟨1908227794577780801398157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1272151863051853867598771 1908227794577780801398157)
              ·
                refine ⟨715585422966667800524309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1908227794577780801398157 715585422966667800524309)
                ·
                  refine ⟨33543066701562553149577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 715585422966667800524309 33543066701562553149577)
                  ·
                    rfl

theorem cell23_587924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 3, 6].length) (baseStart_587924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_587924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_587924 prefixEnd_587924 := by exact prefixLift 587924
  have htrace : WordTrace (prefixWord ++ tailWord_587924) baseStart_587924 baseEnd_587924 := by
    simpa [prefixWord, tailWord_587924, baseEnd_587924] using wordTrace_append hprefix tailTrace_587924
  have hstable : (prefixWord ++ tailWord_587924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587924).length < 2 ^ (prefixWord ++ tailWord_587924).sum := by decide
  have hdescent : baseEnd_587924 < baseStart_587924 := by decide
  rcases family_descends (prefixWord ++ tailWord_587924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587937 : List Nat := [1, 2, 3, 3, 1, 2, 3, 2, 1, 5]
def baseStart_587937 : Nat := 118140960795 + 587937 * 2 ^ 59
def prefixEnd_587937 : Nat := 4983230072969 + 3 ^ 40 * 587937 * 2
def baseEnd_587937 : Nat := 100631425187523809161211

theorem tailTrace_587937 : CollatzResearch.WordTrace tailWord_587937 prefixEnd_587937 100631425187523809161211 := by
  unfold tailWord_587937
  simp only [CollatzResearch.WordTrace]
  refine ⟨21443824071012135490530065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14295882714008090327020043 21443824071012135490530065)
  ·
    refine ⟨16082868053259101617897549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21443824071012135490530065 16082868053259101617897549)
    ·
      refine ⟨6031075519972163106711581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16082868053259101617897549 6031075519972163106711581)
      ·
        refine ⟨2261653319989561165016843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6031075519972163106711581 2261653319989561165016843)
        ·
          refine ⟨3392479979984341747525265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2261653319989561165016843 3392479979984341747525265)
          ·
            refine ⟨2544359984988256310643949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3392479979984341747525265 2544359984988256310643949)
            ·
              refine ⟨954134994370596116491481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2544359984988256310643949 954134994370596116491481)
              ·
                refine ⟨715601245777947087368611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 954134994370596116491481 715601245777947087368611)
                ·
                  refine ⟨1073401868666920631052917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 715601245777947087368611 1073401868666920631052917)
                  ·
                    refine ⟨100631425187523809161211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1073401868666920631052917 100631425187523809161211)
                    ·
                      rfl

theorem cell23_587937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 2, 1, 5].length) (baseStart_587937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_587937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_587937 prefixEnd_587937 := by exact prefixLift 587937
  have htrace : WordTrace (prefixWord ++ tailWord_587937) baseStart_587937 baseEnd_587937 := by
    simpa [prefixWord, tailWord_587937, baseEnd_587937] using wordTrace_append hprefix tailTrace_587937
  have hstable : (prefixWord ++ tailWord_587937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587937).length < 2 ^ (prefixWord ++ tailWord_587937).sum := by decide
  have hdescent : baseEnd_587937 < baseStart_587937 := by decide
  rcases family_descends (prefixWord ++ tailWord_587937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587968 : List Nat := [2, 1, 1, 2, 5, 3, 2, 2, 1, 1, 3]
def baseStart_587968 : Nat := 118140960795 + 587968 * 2 ^ 59
def prefixEnd_587968 : Nat := 4983230072969 + 3 ^ 40 * 587968 * 2
def baseEnd_587968 : Nat := 301910193462860806195991

theorem tailTrace_587968 : CollatzResearch.WordTrace tailWord_587968 prefixEnd_587968 301910193462860806195991 := by
  unfold tailWord_587968
  simp only [CollatzResearch.WordTrace]
  refine ⟨10722477366949913892454279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14296636489266551856605705 10722477366949913892454279)
  ·
    refine ⟨16083716050424870838681419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10722477366949913892454279 16083716050424870838681419)
    ·
      refine ⟨24125574075637306258022129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16083716050424870838681419 24125574075637306258022129)
      ·
        refine ⟨18094180556727979693516597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24125574075637306258022129 18094180556727979693516597)
        ·
          refine ⟨1696329427193248096267181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18094180556727979693516597 1696329427193248096267181)
          ·
            refine ⟨636123535197468036100193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1696329427193248096267181 636123535197468036100193)
            ·
              refine ⟨477092651398101027075145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 636123535197468036100193 477092651398101027075145)
              ·
                refine ⟨357819488548575770306359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 477092651398101027075145 357819488548575770306359)
                ·
                  refine ⟨536729232822863655459539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 357819488548575770306359 536729232822863655459539)
                  ·
                    refine ⟨805093849234295483189309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 536729232822863655459539 805093849234295483189309)
                    ·
                      refine ⟨301910193462860806195991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 805093849234295483189309 301910193462860806195991)
                      ·
                        rfl

theorem cell23_587968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 2, 2, 1, 1, 3].length) (baseStart_587968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_587968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_587968 prefixEnd_587968 := by exact prefixLift 587968
  have htrace : WordTrace (prefixWord ++ tailWord_587968) baseStart_587968 baseEnd_587968 := by
    simpa [prefixWord, tailWord_587968, baseEnd_587968] using wordTrace_append hprefix tailTrace_587968
  have hstable : (prefixWord ++ tailWord_587968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587968).length < 2 ^ (prefixWord ++ tailWord_587968).sum := by decide
  have hdescent : baseEnd_587968 < baseStart_587968 := by decide
  rcases family_descends (prefixWord ++ tailWord_587968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588002 : List Nat := [3, 3, 4, 1, 1, 1, 2, 3, 1, 1, 3]
def baseStart_588002 : Nat := 118140960795 + 588002 * 2 ^ 59
def prefixEnd_588002 : Nat := 4983230072969 + 3 ^ 40 * 588002 * 2
def baseEnd_588002 : Nat := 301927651805113673170835

theorem tailTrace_588002 : CollatzResearch.WordTrace tailWord_588002 prefixEnd_588002 301927651805113673170835 := by
  unfold tailWord_588002
  simp only [CollatzResearch.WordTrace]
  refine ⟨5361548703944162897911565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14297463210517767727764173 5361548703944162897911565)
  ·
    refine ⟨2010580763979061086716837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5361548703944162897911565 2010580763979061086716837)
    ·
      refine ⟨376983893246073953759407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2010580763979061086716837 376983893246073953759407)
      ·
        refine ⟨565475839869110930639111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 376983893246073953759407 565475839869110930639111)
        ·
          refine ⟨848213759803666395958667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 565475839869110930639111 848213759803666395958667)
          ·
            refine ⟨1272320639705499593938001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 848213759803666395958667 1272320639705499593938001)
            ·
              refine ⟨954240479779124695453501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1272320639705499593938001 954240479779124695453501)
              ·
                refine ⟨357840179917171760795063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 954240479779124695453501 357840179917171760795063)
                ·
                  refine ⟨536760269875757641192595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 357840179917171760795063 536760269875757641192595)
                  ·
                    refine ⟨805140404813636461788893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 536760269875757641192595 805140404813636461788893)
                    ·
                      refine ⟨301927651805113673170835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 805140404813636461788893 301927651805113673170835)
                      ·
                        rfl

theorem cell23_588002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_588002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_588002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_588002 prefixEnd_588002 := by exact prefixLift 588002
  have htrace : WordTrace (prefixWord ++ tailWord_588002) baseStart_588002 baseEnd_588002 := by
    simpa [prefixWord, tailWord_588002, baseEnd_588002] using wordTrace_append hprefix tailTrace_588002
  have hstable : (prefixWord ++ tailWord_588002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588002).length < 2 ^ (prefixWord ++ tailWord_588002).sum := by decide
  have hdescent : baseEnd_588002 < baseStart_588002 := by decide
  rcases family_descends (prefixWord ++ tailWord_588002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588008 : List Nat := [2, 1, 4, 1, 2, 3, 2, 3, 1, 2, 2]
def baseStart_588008 : Nat := 118140960795 + 588008 * 2 ^ 59
def prefixEnd_588008 : Nat := 4983230072969 + 3 ^ 40 * 588008 * 2
def baseEnd_588008 : Nat := 301930732689040649695807

theorem tailTrace_588008 : CollatzResearch.WordTrace tailWord_588008 prefixEnd_588008 301930732689040649695807 := by
  unfold tailWord_588008
  simp only [CollatzResearch.WordTrace]
  refine ⟨10723206826877457308182339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14297609102503276410909785 10723206826877457308182339)
  ·
    refine ⟨16084810240316185962273509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10723206826877457308182339 16084810240316185962273509)
    ·
      refine ⟨3015901920059284867926283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16084810240316185962273509 3015901920059284867926283)
      ·
        refine ⟨4523852880088927301889425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3015901920059284867926283 4523852880088927301889425)
        ·
          refine ⟨3392889660066695476417069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4523852880088927301889425 3392889660066695476417069)
          ·
            refine ⟨1272333622525010803656401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3392889660066695476417069 1272333622525010803656401)
            ·
              refine ⟨954250216893758102742301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1272333622525010803656401 954250216893758102742301)
              ·
                refine ⟨357843831335159288528363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 954250216893758102742301 357843831335159288528363)
                ·
                  refine ⟨536765747002738932792545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 357843831335159288528363 536765747002738932792545)
                  ·
                    refine ⟨402574310252054199594409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 536765747002738932792545 402574310252054199594409)
                    ·
                      refine ⟨301930732689040649695807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 402574310252054199594409 301930732689040649695807)
                      ·
                        rfl

theorem cell23_588008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 3, 1, 2, 2].length) (baseStart_588008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_588008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_588008 prefixEnd_588008 := by exact prefixLift 588008
  have htrace : WordTrace (prefixWord ++ tailWord_588008) baseStart_588008 baseEnd_588008 := by
    simpa [prefixWord, tailWord_588008, baseEnd_588008] using wordTrace_append hprefix tailTrace_588008
  have hstable : (prefixWord ++ tailWord_588008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588008).length < 2 ^ (prefixWord ++ tailWord_588008).sum := by decide
  have hdescent : baseEnd_588008 < baseStart_588008 := by decide
  rcases family_descends (prefixWord ++ tailWord_588008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588041 : List Nat := [1, 2, 1, 1, 3, 5, 3, 1, 2, 1, 3]
def baseStart_588041 : Nat := 118140960795 + 588041 * 2 ^ 59
def prefixEnd_588041 : Nat := 4983230072969 + 3 ^ 40 * 588041 * 2
def baseEnd_588041 : Nat := 301947677550639020583155

theorem tailTrace_588041 : CollatzResearch.WordTrace tailWord_588041 prefixEnd_588041 301947677550639020583155 := by
  unfold tailWord_588041
  simp only [CollatzResearch.WordTrace]
  refine ⟨21447617262635361252315977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14298411508423574168210651 21447617262635361252315977)
  ·
    refine ⟨16085712946976520939236983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21447617262635361252315977 16085712946976520939236983)
    ·
      refine ⟨24128569420464781408855475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16085712946976520939236983 24128569420464781408855475)
      ·
        refine ⟨36192854130697172113283213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24128569420464781408855475 36192854130697172113283213)
        ·
          refine ⟨13572320299011439542481205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36192854130697172113283213 13572320299011439542481205)
          ·
            refine ⟨1272405028032322457107613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13572320299011439542481205 1272405028032322457107613)
            ·
              refine ⟨477151885512120921415355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1272405028032322457107613 477151885512120921415355)
              ·
                refine ⟨715727828268181382123033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 477151885512120921415355 715727828268181382123033)
                ·
                  refine ⟨536795871201136036592275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 715727828268181382123033 536795871201136036592275)
                  ·
                    refine ⟨805193806801704054888413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 536795871201136036592275 805193806801704054888413)
                    ·
                      refine ⟨301947677550639020583155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 805193806801704054888413 301947677550639020583155)
                      ·
                        rfl

theorem cell23_588041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 3, 1, 2, 1, 3].length) (baseStart_588041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_588041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_588041 prefixEnd_588041 := by exact prefixLift 588041
  have htrace : WordTrace (prefixWord ++ tailWord_588041) baseStart_588041 baseEnd_588041 := by
    simpa [prefixWord, tailWord_588041, baseEnd_588041] using wordTrace_append hprefix tailTrace_588041
  have hstable : (prefixWord ++ tailWord_588041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588041).length < 2 ^ (prefixWord ++ tailWord_588041).sum := by decide
  have hdescent : baseEnd_588041 < baseStart_588041 := by decide
  rcases family_descends (prefixWord ++ tailWord_588041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588087 : List Nat := [1, 1, 3, 1, 2, 1, 1, 8, 5]
def baseStart_588087 : Nat := 118140960795 + 588087 * 2 ^ 59
def prefixEnd_588087 : Nat := 4983230072969 + 3 ^ 40 * 588087 * 2
def baseEnd_588087 : Nat := 33552366406749537845327

theorem tailTrace_588087 : CollatzResearch.WordTrace tailWord_588087 prefixEnd_588087 33552366406749537845327 := by
  unfold tailWord_588087
  simp only [CollatzResearch.WordTrace]
  refine ⟨21449295020468711108490515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14299530013645807405660343 21449295020468711108490515)
  ·
    refine ⟨32173942530703066662735773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21449295020468711108490515 32173942530703066662735773)
    ·
      refine ⟨12065228449013649998525915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32173942530703066662735773 12065228449013649998525915)
      ·
        refine ⟨18097842673520474997788873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12065228449013649998525915 18097842673520474997788873)
        ·
          refine ⟨13573382005140356248341655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18097842673520474997788873 13573382005140356248341655)
          ·
            refine ⟨20360073007710534372512483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13573382005140356248341655 20360073007710534372512483)
            ·
              refine ⟨30540109511565801558768725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20360073007710534372512483 30540109511565801558768725)
              ·
                refine ⟨357891908338661737016821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 30540109511565801558768725 357891908338661737016821)
                ·
                  refine ⟨33552366406749537845327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 357891908338661737016821 33552366406749537845327)
                  ·
                    rfl

theorem cell23_588087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 8, 5].length) (baseStart_588087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_588087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_588087 prefixEnd_588087 := by exact prefixLift 588087
  have htrace : WordTrace (prefixWord ++ tailWord_588087) baseStart_588087 baseEnd_588087 := by
    simpa [prefixWord, tailWord_588087, baseEnd_588087] using wordTrace_append hprefix tailTrace_588087
  have hstable : (prefixWord ++ tailWord_588087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588087).length < 2 ^ (prefixWord ++ tailWord_588087).sum := by decide
  have hdescent : baseEnd_588087 < baseStart_588087 := by decide
  rcases family_descends (prefixWord ++ tailWord_588087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588107 : List Nat := [1, 1, 1, 1, 3, 1, 1, 3, 4, 5, 2]
def baseStart_588107 : Nat := 118140960795 + 588107 * 2 ^ 59
def prefixEnd_588107 : Nat := 4983230072969 + 3 ^ 40 * 588107 * 2
def baseEnd_588107 : Nat := 301981567273835762357851

theorem tailTrace_588107 : CollatzResearch.WordTrace tailWord_588107 prefixEnd_588107 301981567273835762357851 := by
  unfold tailWord_588107
  simp only [CollatzResearch.WordTrace]
  refine ⟨21450024480396254524218575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14300016320264169682812383 21450024480396254524218575)
  ·
    refine ⟨32175036720594381786327863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21450024480396254524218575 32175036720594381786327863)
    ·
      refine ⟨48262555080891572679491795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32175036720594381786327863 48262555080891572679491795)
      ·
        refine ⟨72393832621337359019237693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48262555080891572679491795 72393832621337359019237693)
        ·
          refine ⟨27147687233001509632214135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72393832621337359019237693 27147687233001509632214135)
          ·
            refine ⟨40721530849502264448321203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27147687233001509632214135 40721530849502264448321203)
            ·
              refine ⟨61082296274253396672481805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40721530849502264448321203 61082296274253396672481805)
              ·
                refine ⟨22905861102845023752180677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61082296274253396672481805 22905861102845023752180677)
                ·
                  refine ⟨4294848956783441953533877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22905861102845023752180677 4294848956783441953533877)
                  ·
                    refine ⟨402642089698447683143801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4294848956783441953533877 402642089698447683143801)
                    ·
                      refine ⟨301981567273835762357851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 402642089698447683143801 301981567273835762357851)
                      ·
                        rfl

theorem cell23_588107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 5, 2].length) (baseStart_588107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_588107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_588107 prefixEnd_588107 := by exact prefixLift 588107
  have htrace : WordTrace (prefixWord ++ tailWord_588107) baseStart_588107 baseEnd_588107 := by
    simpa [prefixWord, tailWord_588107, baseEnd_588107] using wordTrace_append hprefix tailTrace_588107
  have hstable : (prefixWord ++ tailWord_588107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588107).length < 2 ^ (prefixWord ++ tailWord_588107).sum := by decide
  have hdescent : baseEnd_588107 < baseStart_588107 := by decide
  rcases family_descends (prefixWord ++ tailWord_588107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588137 : List Nat := [1, 2, 1, 1, 1, 3, 3, 4, 2, 1, 4]
def baseStart_588137 : Nat := 118140960795 + 588137 * 2 ^ 59
def prefixEnd_588137 : Nat := 4983230072969 + 3 ^ 40 * 588137 * 2
def baseEnd_588137 : Nat := 301996971693470644982713

theorem tailTrace_588137 : CollatzResearch.WordTrace tailWord_588137 prefixEnd_588137 301996971693470644982713 := by
  unfold tailWord_588137
  simp only [CollatzResearch.WordTrace]
  refine ⟨21451118670287569647810665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14300745780191713098540443 21451118670287569647810665)
  ·
    refine ⟨16088339002715677235857999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21451118670287569647810665 16088339002715677235857999)
    ·
      refine ⟨24132508504073515853786999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16088339002715677235857999 24132508504073515853786999)
      ·
        refine ⟨36198762756110273780680499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24132508504073515853786999 36198762756110273780680499)
        ·
          refine ⟨54298144134165410671020749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36198762756110273780680499 54298144134165410671020749)
          ·
            refine ⟨20361804050312029001632781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54298144134165410671020749 20361804050312029001632781)
            ·
              refine ⟨7635676518867010875612293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20361804050312029001632781 7635676518867010875612293)
              ·
                refine ⟨1431689347287564539177305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7635676518867010875612293 1431689347287564539177305)
                ·
                  refine ⟨1073767010465673404382979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1431689347287564539177305 1073767010465673404382979)
                  ·
                    refine ⟨1610650515698510106574469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1073767010465673404382979 1610650515698510106574469)
                    ·
                      refine ⟨301996971693470644982713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1610650515698510106574469 301996971693470644982713)
                      ·
                        rfl

theorem cell23_588137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 4, 2, 1, 4].length) (baseStart_588137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_588137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_588137 prefixEnd_588137 := by exact prefixLift 588137
  have htrace : WordTrace (prefixWord ++ tailWord_588137) baseStart_588137 baseEnd_588137 := by
    simpa [prefixWord, tailWord_588137, baseEnd_588137] using wordTrace_append hprefix tailTrace_588137
  have hstable : (prefixWord ++ tailWord_588137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588137).length < 2 ^ (prefixWord ++ tailWord_588137).sum := by decide
  have hdescent : baseEnd_588137 < baseStart_588137 := by decide
  rcases family_descends (prefixWord ++ tailWord_588137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588138 : List Nat := [3, 1, 3, 3, 1, 3, 2, 2, 5]
def baseStart_588138 : Nat := 118140960795 + 588138 * 2 ^ 59
def prefixEnd_588138 : Nat := 4983230072969 + 3 ^ 40 * 588138 * 2
def baseEnd_588138 : Nat := 33555276130458349007801

theorem tailTrace_588138 : CollatzResearch.WordTrace tailWord_588138 prefixEnd_588138 33555276130458349007801 := by
  unfold tailWord_588138
  simp only [CollatzResearch.WordTrace]
  refine ⟨5362788785820986704649267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14300770095522631212398045 5362788785820986704649267)
  ·
    refine ⟨8044183178731480056973901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5362788785820986704649267 8044183178731480056973901)
    ·
      refine ⟨3016568692024305021365213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8044183178731480056973901 3016568692024305021365213)
      ·
        refine ⟨1131213259509114383011955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3016568692024305021365213 1131213259509114383011955)
        ·
          refine ⟨1696819889263671574517933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1131213259509114383011955 1696819889263671574517933)
          ·
            refine ⟨636307458473876840444225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1696819889263671574517933 636307458473876840444225)
            ·
              refine ⟨477230593855407630333169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 636307458473876840444225 477230593855407630333169)
              ·
                refine ⟨357922945391555722749877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 477230593855407630333169 357922945391555722749877)
                ·
                  refine ⟨33555276130458349007801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 357922945391555722749877 33555276130458349007801)
                  ·
                    rfl

theorem cell23_588138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 2, 2, 5].length) (baseStart_588138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_588138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_588138 prefixEnd_588138 := by exact prefixLift 588138
  have htrace : WordTrace (prefixWord ++ tailWord_588138) baseStart_588138 baseEnd_588138 := by
    simpa [prefixWord, tailWord_588138, baseEnd_588138] using wordTrace_append hprefix tailTrace_588138
  have hstable : (prefixWord ++ tailWord_588138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588138).length < 2 ^ (prefixWord ++ tailWord_588138).sum := by decide
  have hdescent : baseEnd_588138 < baseStart_588138 := by decide
  rcases family_descends (prefixWord ++ tailWord_588138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588160 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 12]
def baseStart_588160 : Nat := 118140960795 + 588160 * 2 ^ 59
def prefixEnd_588160 : Nat := 4983230072969 + 3 ^ 40 * 588160 * 2
def baseEnd_588160 : Nat := 33556531305391561666123

theorem tailTrace_588160 : CollatzResearch.WordTrace tailWord_588160 prefixEnd_588160 33556531305391561666123 := by
  unfold tailWord_588160
  simp only [CollatzResearch.WordTrace]
  refine ⟨10725978774602122287948967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14301305032802829717265289 10725978774602122287948967)
  ·
    refine ⟨16088968161903183431923451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10725978774602122287948967 16088968161903183431923451)
    ·
      refine ⟨24133452242854775147885177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16088968161903183431923451 24133452242854775147885177)
      ·
        refine ⟨18100089182141081360913883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24133452242854775147885177 18100089182141081360913883)
        ·
          refine ⟨27150133773211622041370825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18100089182141081360913883 27150133773211622041370825)
          ·
            refine ⟨20362600329908716531028119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27150133773211622041370825 20362600329908716531028119)
            ·
              refine ⟨30543900494863074796542179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20362600329908716531028119 30543900494863074796542179)
              ·
                refine ⟨45815850742294612194813269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30543900494863074796542179 45815850742294612194813269)
                ·
                  refine ⟨33556531305391561666123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 45815850742294612194813269 33556531305391561666123)
                  ·
                    rfl

theorem cell23_588160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 12].length) (baseStart_588160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_588160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_588160 prefixEnd_588160 := by exact prefixLift 588160
  have htrace : WordTrace (prefixWord ++ tailWord_588160) baseStart_588160 baseEnd_588160 := by
    simpa [prefixWord, tailWord_588160, baseEnd_588160] using wordTrace_append hprefix tailTrace_588160
  have hstable : (prefixWord ++ tailWord_588160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588160).length < 2 ^ (prefixWord ++ tailWord_588160).sum := by decide
  have hdescent : baseEnd_588160 < baseStart_588160 := by decide
  rcases family_descends (prefixWord ++ tailWord_588160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588164 : List Nat := [2, 3, 2, 1, 1, 2, 3, 2, 3, 4]
def baseStart_588164 : Nat := 118140960795 + 588164 * 2 ^ 59
def prefixEnd_588164 : Nat := 4983230072969 + 3 ^ 40 * 588164 * 2
def baseEnd_588164 : Nat := 100670278557047346448363

theorem tailTrace_588164 : CollatzResearch.WordTrace tailWord_588164 prefixEnd_588164 100670278557047346448363 := by
  unfold tailWord_588164
  simp only [CollatzResearch.WordTrace]
  refine ⟨10726051720594876629521773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14301402294126502172695697 10726051720594876629521773)
  ·
    refine ⟨4022269395223078736070665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10726051720594876629521773 4022269395223078736070665)
    ·
      refine ⟨3016702046417309052052999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4022269395223078736070665 3016702046417309052052999)
      ·
        refine ⟨4525053069625963578079499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3016702046417309052052999 4525053069625963578079499)
        ·
          refine ⟨6787579604438945367119249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4525053069625963578079499 6787579604438945367119249)
          ·
            refine ⟨5090684703329209025339437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6787579604438945367119249 5090684703329209025339437)
            ·
              refine ⟨1909006763748453384502289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5090684703329209025339437 1909006763748453384502289)
              ·
                refine ⟨1431755072811340038376717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1909006763748453384502289 1431755072811340038376717)
                ·
                  refine ⟨536908152304252514391269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1431755072811340038376717 536908152304252514391269)
                  ·
                    refine ⟨100670278557047346448363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 536908152304252514391269 100670278557047346448363)
                    ·
                      rfl

theorem cell23_588164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 2, 3, 4].length) (baseStart_588164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_588164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_588164 prefixEnd_588164 := by exact prefixLift 588164
  have htrace : WordTrace (prefixWord ++ tailWord_588164) baseStart_588164 baseEnd_588164 := by
    simpa [prefixWord, tailWord_588164, baseEnd_588164] using wordTrace_append hprefix tailTrace_588164
  have hstable : (prefixWord ++ tailWord_588164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588164).length < 2 ^ (prefixWord ++ tailWord_588164).sum := by decide
  have hdescent : baseEnd_588164 < baseStart_588164 := by decide
  rcases family_descends (prefixWord ++ tailWord_588164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588221 : List Nat := [1, 4, 1, 2, 2, 2, 2, 2, 3, 1, 3]
def baseStart_588221 : Nat := 118140960795 + 588221 * 2 ^ 59
def prefixEnd_588221 : Nat := 4983230072969 + 3 ^ 40 * 588221 * 2
def baseEnd_588221 : Nat := 302040104068448316332327

theorem tailTrace_588221 : CollatzResearch.WordTrace tailWord_588221 prefixEnd_588221 302040104068448316332327 := by
  unfold tailWord_588221
  simp only [CollatzResearch.WordTrace]
  refine ⟨21454182401983251993868517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14302788267988834662579011 21454182401983251993868517)
  ·
    refine ⟨4022659200371859748850347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21454182401983251993868517 4022659200371859748850347)
    ·
      refine ⟨6033988800557789623275521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4022659200371859748850347 6033988800557789623275521)
      ·
        refine ⟨4525491600418342217456641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6033988800557789623275521 4525491600418342217456641)
        ·
          refine ⟨3394118700313756663092481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4525491600418342217456641 3394118700313756663092481)
          ·
            refine ⟨2545589025235317497319361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3394118700313756663092481 2545589025235317497319361)
            ·
              refine ⟨1909191768926488122989521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2545589025235317497319361 1909191768926488122989521)
              ·
                refine ⟨1431893826694866092242141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1909191768926488122989521 1431893826694866092242141)
                ·
                  refine ⟨536960185010574784590803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1431893826694866092242141 536960185010574784590803)
                  ·
                    refine ⟨805440277515862176886205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 536960185010574784590803 805440277515862176886205)
                    ·
                      refine ⟨302040104068448316332327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 805440277515862176886205 302040104068448316332327)
                      ·
                        rfl

theorem cell23_588221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 2, 3, 1, 3].length) (baseStart_588221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_588221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_588221 prefixEnd_588221 := by exact prefixLift 588221
  have htrace : WordTrace (prefixWord ++ tailWord_588221) baseStart_588221 baseEnd_588221 := by
    simpa [prefixWord, tailWord_588221, baseEnd_588221] using wordTrace_append hprefix tailTrace_588221
  have hstable : (prefixWord ++ tailWord_588221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588221).length < 2 ^ (prefixWord ++ tailWord_588221).sum := by decide
  have hdescent : baseEnd_588221 < baseStart_588221 := by decide
  rcases family_descends (prefixWord ++ tailWord_588221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588255 : List Nat := [1, 1, 2, 3, 3, 3, 3, 2, 1, 1, 3]
def baseStart_588255 : Nat := 118140960795 + 588255 * 2 ^ 59
def prefixEnd_588255 : Nat := 4983230072969 + 3 ^ 40 * 588255 * 2
def baseEnd_588255 : Nat := 302057562410701183307171

theorem tailTrace_588255 : CollatzResearch.WordTrace tailWord_588255 prefixEnd_588255 302057562410701183307171 := by
  unfold tailWord_588255
  simp only [CollatzResearch.WordTrace]
  refine ⟨21455422483860075800606219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14303614989240050533737479 21455422483860075800606219)
  ·
    refine ⟨32183133725790113700909329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21455422483860075800606219 32183133725790113700909329)
    ·
      refine ⟨24137350294342585275681997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32183133725790113700909329 24137350294342585275681997)
      ·
        refine ⟨9051506360378469478380749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24137350294342585275681997 9051506360378469478380749)
        ·
          refine ⟨3394314885141926054392781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9051506360378469478380749 3394314885141926054392781)
          ·
            refine ⟨1272868081928222270397293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3394314885141926054392781 1272868081928222270397293)
            ·
              refine ⟨477325530723083351398985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1272868081928222270397293 477325530723083351398985)
              ·
                refine ⟨357994148042312513549239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 477325530723083351398985 357994148042312513549239)
                ·
                  refine ⟨536991222063468770323859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 357994148042312513549239 536991222063468770323859)
                  ·
                    refine ⟨805486833095203155485789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 536991222063468770323859 805486833095203155485789)
                    ·
                      refine ⟨302057562410701183307171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 805486833095203155485789 302057562410701183307171)
                      ·
                        rfl

theorem cell23_588255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 3, 2, 1, 1, 3].length) (baseStart_588255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_588255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_588255 prefixEnd_588255 := by exact prefixLift 588255
  have htrace : WordTrace (prefixWord ++ tailWord_588255) baseStart_588255 baseEnd_588255 := by
    simpa [prefixWord, tailWord_588255, baseEnd_588255] using wordTrace_append hprefix tailTrace_588255
  have hstable : (prefixWord ++ tailWord_588255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588255).length < 2 ^ (prefixWord ++ tailWord_588255).sum := by decide
  have hdescent : baseEnd_588255 < baseStart_588255 := by decide
  rcases family_descends (prefixWord ++ tailWord_588255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588257 : List Nat := [1, 2, 3, 1, 2, 2, 1, 1, 3, 1, 6]
def baseStart_588257 : Nat := 118140960795 + 588257 * 2 ^ 59
def prefixEnd_588257 : Nat := 4983230072969 + 3 ^ 40 * 588257 * 2
def baseEnd_588257 : Nat := 302058589372010175482161

theorem tailTrace_588257 : CollatzResearch.WordTrace tailWord_588257 prefixEnd_588257 302058589372010175482161 := by
  unfold tailWord_588257
  simp only [CollatzResearch.WordTrace]
  refine ⟨21455495429852830142179025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14303663619901886761452683 21455495429852830142179025)
  ·
    refine ⟨16091621572389622606634269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21455495429852830142179025 16091621572389622606634269)
    ·
      refine ⟨6034358089646108477487851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16091621572389622606634269 6034358089646108477487851)
      ·
        refine ⟨9051537134469162716231777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6034358089646108477487851 9051537134469162716231777)
        ·
          refine ⟨6788652850851872037173833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9051537134469162716231777 6788652850851872037173833)
          ·
            refine ⟨5091489638138904027880375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6788652850851872037173833 5091489638138904027880375)
            ·
              refine ⟨7637234457208356041820563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5091489638138904027880375 7637234457208356041820563)
              ·
                refine ⟨11455851685812534062730845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7637234457208356041820563 11455851685812534062730845)
                ·
                  refine ⟨4295944382179700273524067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11455851685812534062730845 4295944382179700273524067)
                  ·
                    refine ⟨6443916573269550410286101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4295944382179700273524067 6443916573269550410286101)
                    ·
                      refine ⟨302058589372010175482161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6443916573269550410286101 302058589372010175482161)
                      ·
                        rfl

theorem cell23_588257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_588257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_588257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_588257 prefixEnd_588257 := by exact prefixLift 588257
  have htrace : WordTrace (prefixWord ++ tailWord_588257) baseStart_588257 baseEnd_588257 := by
    simpa [prefixWord, tailWord_588257, baseEnd_588257] using wordTrace_append hprefix tailTrace_588257
  have hstable : (prefixWord ++ tailWord_588257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588257).length < 2 ^ (prefixWord ++ tailWord_588257).sum := by decide
  have hdescent : baseEnd_588257 < baseStart_588257 := by decide
  rcases family_descends (prefixWord ++ tailWord_588257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588264 : List Nat := [2, 1, 4, 1, 1, 3, 2, 2, 1, 1, 5]
def baseStart_588264 : Nat := 118140960795 + 588264 * 2 ^ 59
def prefixEnd_588264 : Nat := 4983230072969 + 3 ^ 40 * 588264 * 2
def baseEnd_588264 : Nat := 302062183736591648094629

theorem tailTrace_588264 : CollatzResearch.WordTrace tailWord_588264 prefixEnd_588264 302062183736591648094629 := by
  unfold tailWord_588264
  simp only [CollatzResearch.WordTrace]
  refine ⟨10727875370413735168841923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14303833827218313558455897 10727875370413735168841923)
  ·
    refine ⟨16091813055620602753262885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10727875370413735168841923 16091813055620602753262885)
    ·
      refine ⟨3017214947928863016236791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16091813055620602753262885 3017214947928863016236791)
      ·
        refine ⟨4525822421893294524355187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3017214947928863016236791 4525822421893294524355187)
        ·
          refine ⟨6788733632839941786532781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4525822421893294524355187 6788733632839941786532781)
          ·
            refine ⟨2545775112314978169949793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6788733632839941786532781 2545775112314978169949793)
            ·
              refine ⟨1909331334236233627462345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2545775112314978169949793 1909331334236233627462345)
              ·
                refine ⟨1431998500677175220596759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1909331334236233627462345 1431998500677175220596759)
                ·
                  refine ⟨2147997751015762830895139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1431998500677175220596759 2147997751015762830895139)
                  ·
                    refine ⟨3221996626523644246342709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2147997751015762830895139 3221996626523644246342709)
                    ·
                      refine ⟨302062183736591648094629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3221996626523644246342709 302062183736591648094629)
                      ·
                        rfl

theorem cell23_588264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_588264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_588264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_588264 prefixEnd_588264 := by exact prefixLift 588264
  have htrace : WordTrace (prefixWord ++ tailWord_588264) baseStart_588264 baseEnd_588264 := by
    simpa [prefixWord, tailWord_588264, baseEnd_588264] using wordTrace_append hprefix tailTrace_588264
  have hstable : (prefixWord ++ tailWord_588264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588264).length < 2 ^ (prefixWord ++ tailWord_588264).sum := by decide
  have hdescent : baseEnd_588264 < baseStart_588264 := by decide
  rcases family_descends (prefixWord ++ tailWord_588264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588267 : List Nat := [1, 1, 1, 1, 2, 3, 6, 8]
def baseStart_588267 : Nat := 118140960795 + 588267 * 2 ^ 59
def prefixEnd_588267 : Nat := 4983230072969 + 3 ^ 40 * 588267 * 2
def baseEnd_588267 : Nat := 11187545339946486531745

theorem tailTrace_588267 : CollatzResearch.WordTrace tailWord_588267 prefixEnd_588267 11187545339946486531745 := by
  unfold tailWord_588267
  simp only [CollatzResearch.WordTrace]
  refine ⟨21455860159816601850043055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14303906773211067900028703 21455860159816601850043055)
  ·
    refine ⟨32183790239724902775064583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21455860159816601850043055 32183790239724902775064583)
    ·
      refine ⟨48275685359587354162596875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32183790239724902775064583 48275685359587354162596875)
      ·
        refine ⟨72413528039381031243895313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48275685359587354162596875 72413528039381031243895313)
        ·
          refine ⟨54310146029535773432921485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72413528039381031243895313 54310146029535773432921485)
          ·
            refine ⟨20366304761075915037345557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54310146029535773432921485 20366304761075915037345557)
            ·
              refine ⟨954670535675433517375573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20366304761075915037345557 954670535675433517375573)
              ·
                refine ⟨11187545339946486531745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 954670535675433517375573 11187545339946486531745)
                ·
                  rfl

theorem cell23_588267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 8].length) (baseStart_588267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_588267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_588267 prefixEnd_588267 := by exact prefixLift 588267
  have htrace : WordTrace (prefixWord ++ tailWord_588267) baseStart_588267 baseEnd_588267 := by
    simpa [prefixWord, tailWord_588267, baseEnd_588267] using wordTrace_append hprefix tailTrace_588267
  have hstable : (prefixWord ++ tailWord_588267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588267).length < 2 ^ (prefixWord ++ tailWord_588267).sum := by decide
  have hdescent : baseEnd_588267 < baseStart_588267 := by decide
  rcases family_descends (prefixWord ++ tailWord_588267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588278 : List Nat := [5, 1, 1, 1, 2, 1, 2, 1, 5, 2, 2]
def baseStart_588278 : Nat := 118140960795 + 588278 * 2 ^ 59
def prefixEnd_588278 : Nat := 4983230072969 + 3 ^ 40 * 588278 * 2
def baseEnd_588278 : Nat := 302069372465754593319565

theorem tailTrace_588278 : CollatzResearch.WordTrace tailWord_588278 prefixEnd_588278 302069372465754593319565 := by
  unfold tailWord_588278
  simp only [CollatzResearch.WordTrace]
  refine ⟨1341016335173546920543343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14304174241851167152462325 1341016335173546920543343)
  ·
    refine ⟨2011524502760320380815015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1341016335173546920543343 2011524502760320380815015)
    ·
      refine ⟨3017286754140480571222523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2011524502760320380815015 3017286754140480571222523)
      ·
        refine ⟨4525930131210720856833785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3017286754140480571222523 4525930131210720856833785)
        ·
          refine ⟨3394447598408040642625339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4525930131210720856833785 3394447598408040642625339)
          ·
            refine ⟨5091671397612060963938009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3394447598408040642625339 5091671397612060963938009)
            ·
              refine ⟨3818753548209045722953507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5091671397612060963938009 3818753548209045722953507)
              ·
                refine ⟨5728130322313568584430261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3818753548209045722953507 5728130322313568584430261)
                ·
                  refine ⟨537012217716897054790337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5728130322313568584430261 537012217716897054790337)
                  ·
                    refine ⟨402759163287672791092753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 537012217716897054790337 402759163287672791092753)
                    ·
                      refine ⟨302069372465754593319565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 402759163287672791092753 302069372465754593319565)
                      ·
                        rfl

theorem cell23_588278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 5, 2, 2].length) (baseStart_588278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_588278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_588278 prefixEnd_588278 := by exact prefixLift 588278
  have htrace : WordTrace (prefixWord ++ tailWord_588278) baseStart_588278 baseEnd_588278 := by
    simpa [prefixWord, tailWord_588278, baseEnd_588278] using wordTrace_append hprefix tailTrace_588278
  have hstable : (prefixWord ++ tailWord_588278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588278).length < 2 ^ (prefixWord ++ tailWord_588278).sum := by decide
  have hdescent : baseEnd_588278 < baseStart_588278 := by decide
  rcases family_descends (prefixWord ++ tailWord_588278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588281 : List Nat := [1, 2, 1, 3, 1, 2, 5, 2, 1, 2, 3]
def baseStart_588281 : Nat := 118140960795 + 588281 * 2 ^ 59
def prefixEnd_588281 : Nat := 4983230072969 + 3 ^ 40 * 588281 * 2
def baseEnd_588281 : Nat := 302070912907718081582051

theorem tailTrace_588281 : CollatzResearch.WordTrace tailWord_588281 prefixEnd_588281 302070912907718081582051 := by
  unfold tailWord_588281
  simp only [CollatzResearch.WordTrace]
  refine ⟨21456370781765882241052697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14304247187843921494035131 21456370781765882241052697)
  ·
    refine ⟨16092278086324411680789523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21456370781765882241052697 16092278086324411680789523)
    ·
      refine ⟨24138417129486617521184285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16092278086324411680789523 24138417129486617521184285)
      ·
        refine ⟨9051906423557481570444107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24138417129486617521184285 9051906423557481570444107)
        ·
          refine ⟨13577859635336222355666161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9051906423557481570444107 13577859635336222355666161)
          ·
            refine ⟨10183394726502166766749621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13577859635336222355666161 10183394726502166766749621)
            ·
              refine ⟨954693255609578134382777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10183394726502166766749621 954693255609578134382777)
              ·
                refine ⟨716019941707183600787083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 954693255609578134382777 716019941707183600787083)
                ·
                  refine ⟨1074029912560775401180625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 716019941707183600787083 1074029912560775401180625)
                  ·
                    refine ⟨805522434420581550885469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1074029912560775401180625 805522434420581550885469)
                    ·
                      refine ⟨302070912907718081582051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 805522434420581550885469 302070912907718081582051)
                      ·
                        rfl

theorem cell23_588281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 2, 1, 2, 3].length) (baseStart_588281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_588281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_588281 prefixEnd_588281 := by exact prefixLift 588281
  have htrace : WordTrace (prefixWord ++ tailWord_588281) baseStart_588281 baseEnd_588281 := by
    simpa [prefixWord, tailWord_588281, baseEnd_588281] using wordTrace_append hprefix tailTrace_588281
  have hstable : (prefixWord ++ tailWord_588281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588281).length < 2 ^ (prefixWord ++ tailWord_588281).sum := by decide
  have hdescent : baseEnd_588281 < baseStart_588281 := by decide
  rcases family_descends (prefixWord ++ tailWord_588281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588298 : List Nat := [3, 1, 2, 2, 2, 1, 5, 1, 1, 2, 3]
def baseStart_588298 : Nat := 118140960795 + 588298 * 2 ^ 59
def prefixEnd_588298 : Nat := 4983230072969 + 3 ^ 40 * 588298 * 2
def baseEnd_588298 : Nat := 302079642078844515069473

theorem tailTrace_588298 : CollatzResearch.WordTrace tailWord_588298 prefixEnd_588298 302079642078844515069473 := by
  unfold tailWord_588298
  simp only [CollatzResearch.WordTrace]
  refine ⟨5364247705676073536105387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14304660548469529429614365 5364247705676073536105387)
  ·
    refine ⟨8046371558514110304158081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5364247705676073536105387 8046371558514110304158081)
    ·
      refine ⟨6034778668885582728118561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8046371558514110304158081 6034778668885582728118561)
      ·
        refine ⟨4526084001664187046088921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6034778668885582728118561 4526084001664187046088921)
        ·
          refine ⟨3394563001248140284566691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4526084001664187046088921 3394563001248140284566691)
          ·
            refine ⟨5091844501872210426850037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3394563001248140284566691 5091844501872210426850037)
            ·
              refine ⟨477360422050519727517191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5091844501872210426850037 477360422050519727517191)
              ·
                refine ⟨716040633075779591275787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 477360422050519727517191 716040633075779591275787)
                ·
                  refine ⟨1074060949613669386913681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 716040633075779591275787 1074060949613669386913681)
                  ·
                    refine ⟨805545712210252040185261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1074060949613669386913681 805545712210252040185261)
                    ·
                      refine ⟨302079642078844515069473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 805545712210252040185261 302079642078844515069473)
                      ·
                        rfl

theorem cell23_588298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 5, 1, 1, 2, 3].length) (baseStart_588298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_588298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_588298 prefixEnd_588298 := by exact prefixLift 588298
  have htrace : WordTrace (prefixWord ++ tailWord_588298) baseStart_588298 baseEnd_588298 := by
    simpa [prefixWord, tailWord_588298, baseEnd_588298] using wordTrace_append hprefix tailTrace_588298
  have hstable : (prefixWord ++ tailWord_588298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588298).length < 2 ^ (prefixWord ++ tailWord_588298).sum := by decide
  have hdescent : baseEnd_588298 < baseStart_588298 := by decide
  rcases family_descends (prefixWord ++ tailWord_588298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588301 : List Nat := [1, 7, 1, 1, 1, 12]
def baseStart_588301 : Nat := 118140960795 + 588301 * 2 ^ 59
def prefixEnd_588301 : Nat := 4983230072969 + 3 ^ 40 * 588301 * 2
def baseEnd_588301 : Nat := 1243132438357234581613

theorem tailTrace_588301 : CollatzResearch.WordTrace tailWord_588301 prefixEnd_588301 1243132438357234581613 := by
  unfold tailWord_588301
  simp only [CollatzResearch.WordTrace]
  refine ⟨21457100241693425656780757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14304733494462283771187171 21457100241693425656780757)
  ·
    refine ⟨502900786914689663830799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 21457100241693425656780757 502900786914689663830799)
    ·
      refine ⟨754351180372034495746199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 502900786914689663830799 754351180372034495746199)
      ·
        refine ⟨1131526770558051743619299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 754351180372034495746199 1131526770558051743619299)
        ·
          refine ⟨1697290155837077615428949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1131526770558051743619299 1697290155837077615428949)
          ·
            refine ⟨1243132438357234581613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 1697290155837077615428949 1243132438357234581613)
            ·
              rfl

theorem cell23_588301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 12].length) (baseStart_588301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_588301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_588301 prefixEnd_588301 := by exact prefixLift 588301
  have htrace : WordTrace (prefixWord ++ tailWord_588301) baseStart_588301 baseEnd_588301 := by
    simpa [prefixWord, tailWord_588301, baseEnd_588301] using wordTrace_append hprefix tailTrace_588301
  have hstable : (prefixWord ++ tailWord_588301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588301).length < 2 ^ (prefixWord ++ tailWord_588301).sum := by decide
  have hdescent : baseEnd_588301 < baseStart_588301 := by decide
  rcases family_descends (prefixWord ++ tailWord_588301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588304 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 4, 7, 2]
def baseStart_588304 : Nat := 118140960795 + 588304 * 2 ^ 59
def prefixEnd_588304 : Nat := 4983230072969 + 3 ^ 40 * 588304 * 2
def baseEnd_588304 : Nat := 302082722962771491594445

theorem tailTrace_588304 : CollatzResearch.WordTrace tailWord_588304 prefixEnd_588304 302082722962771491594445 := by
  unfold tailWord_588304
  simp only [CollatzResearch.WordTrace]
  refine ⟨10728604830341278584569983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14304806440455038112759977 10728604830341278584569983)
  ·
    refine ⟨16092907245511917876854975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10728604830341278584569983 16092907245511917876854975)
    ·
      refine ⟨24139360868267876815282463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16092907245511917876854975 24139360868267876815282463)
      ·
        refine ⟨36209041302401815222923695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24139360868267876815282463 36209041302401815222923695)
        ·
          refine ⟨54313561953602722834385543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36209041302401815222923695 54313561953602722834385543)
          ·
            refine ⟨81470342930404084251578315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54313561953602722834385543 81470342930404084251578315)
            ·
              refine ⟨122205514395606126377367473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81470342930404084251578315 122205514395606126377367473)
              ·
                refine ⟨91654135796704594783025605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 122205514395606126377367473 91654135796704594783025605)
                ·
                  refine ⟨17185150461882111521817301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 91654135796704594783025605 17185150461882111521817301)
                  ·
                    refine ⟨402776963950361988792593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17185150461882111521817301 402776963950361988792593)
                    ·
                      refine ⟨302082722962771491594445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 402776963950361988792593 302082722962771491594445)
                      ·
                        rfl

theorem cell23_588304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 4, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 4, 7, 2].length) (baseStart_588304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_588304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_588304 prefixEnd_588304 := by exact prefixLift 588304
  have htrace : WordTrace (prefixWord ++ tailWord_588304) baseStart_588304 baseEnd_588304 := by
    simpa [prefixWord, tailWord_588304, baseEnd_588304] using wordTrace_append hprefix tailTrace_588304
  have hstable : (prefixWord ++ tailWord_588304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588304).length < 2 ^ (prefixWord ++ tailWord_588304).sum := by decide
  have hdescent : baseEnd_588304 < baseStart_588304 := by decide
  rcases family_descends (prefixWord ++ tailWord_588304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588312 : List Nat := [2, 1, 2, 3, 3, 1, 4, 2, 1, 2, 2]
def baseStart_588312 : Nat := 118140960795 + 588312 * 2 ^ 59
def prefixEnd_588312 : Nat := 4983230072969 + 3 ^ 40 * 588312 * 2
def baseEnd_588312 : Nat := 302086830808007460294409

theorem tailTrace_588312 : CollatzResearch.WordTrace tailWord_588312 prefixEnd_588312 302086830808007460294409 := by
  unfold tailWord_588312
  simp only [CollatzResearch.WordTrace]
  refine ⟨10728750722326787267715595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14305000963102383023620793 10728750722326787267715595)
  ·
    refine ⟨16093126083490180901573393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10728750722326787267715595 16093126083490180901573393)
    ·
      refine ⟨12069844562617635676180045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16093126083490180901573393 12069844562617635676180045)
      ·
        refine ⟨4526191710981613378567517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12069844562617635676180045 4526191710981613378567517)
        ·
          refine ⟨1697321891618105016962819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4526191710981613378567517 1697321891618105016962819)
          ·
            refine ⟨2545982837427157525444229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1697321891618105016962819 2545982837427157525444229)
            ·
              refine ⟨477371782017592036020793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2545982837427157525444229 477371782017592036020793)
              ·
                refine ⟨358028836513194027015595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 477371782017592036020793 358028836513194027015595)
                ·
                  refine ⟨537043254769791040523393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 358028836513194027015595 537043254769791040523393)
                  ·
                    refine ⟨402782441077343280392545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 537043254769791040523393 402782441077343280392545)
                    ·
                      refine ⟨302086830808007460294409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 402782441077343280392545 302086830808007460294409)
                      ·
                        rfl

theorem cell23_588312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 4, 2, 1, 2, 2].length) (baseStart_588312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_588312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_588312 prefixEnd_588312 := by exact prefixLift 588312
  have htrace : WordTrace (prefixWord ++ tailWord_588312) baseStart_588312 baseEnd_588312 := by
    simpa [prefixWord, tailWord_588312, baseEnd_588312] using wordTrace_append hprefix tailTrace_588312
  have hstable : (prefixWord ++ tailWord_588312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588312).length < 2 ^ (prefixWord ++ tailWord_588312).sum := by decide
  have hdescent : baseEnd_588312 < baseStart_588312 := by decide
  rcases family_descends (prefixWord ++ tailWord_588312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588321 : List Nat := [1, 2, 3, 2, 2, 1, 1, 1, 5, 3, 2]
def baseStart_588321 : Nat := 118140960795 + 588321 * 2 ^ 59
def prefixEnd_588321 : Nat := 4983230072969 + 3 ^ 40 * 588321 * 2
def baseEnd_588321 : Nat := 302091452133897925081867

theorem tailTrace_588321 : CollatzResearch.WordTrace tailWord_588321 prefixEnd_588321 302091452133897925081867 := by
  unfold tailWord_588321
  simp only [CollatzResearch.WordTrace]
  refine ⟨21457829701620969072508817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14305219801080646048339211 21457829701620969072508817)
  ·
    refine ⟨16093372276215726804381613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21457829701620969072508817 16093372276215726804381613)
    ·
      refine ⟨6035014603580897551643105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16093372276215726804381613 6035014603580897551643105)
      ·
        refine ⟨4526260952685673163732329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6035014603580897551643105 4526260952685673163732329)
        ·
          refine ⟨3394695714514254872799247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4526260952685673163732329 3394695714514254872799247)
          ·
            refine ⟨5092043571771382309198871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3394695714514254872799247 5092043571771382309198871)
            ·
              refine ⟨7638065357657073463798307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5092043571771382309198871 7638065357657073463798307)
              ·
                refine ⟨11457098036485610195697461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7638065357657073463798307 11457098036485610195697461)
                ·
                  refine ⟨1074102940920525955846637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11457098036485610195697461 1074102940920525955846637)
                  ·
                    refine ⟨402788602845197233442489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1074102940920525955846637 402788602845197233442489)
                    ·
                      refine ⟨302091452133897925081867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 402788602845197233442489 302091452133897925081867)
                      ·
                        rfl

theorem cell23_588321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 5, 3, 2].length) (baseStart_588321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_588321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_588321 prefixEnd_588321 := by exact prefixLift 588321
  have htrace : WordTrace (prefixWord ++ tailWord_588321) baseStart_588321 baseEnd_588321 := by
    simpa [prefixWord, tailWord_588321, baseEnd_588321] using wordTrace_append hprefix tailTrace_588321
  have hstable : (prefixWord ++ tailWord_588321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588321).length < 2 ^ (prefixWord ++ tailWord_588321).sum := by decide
  have hdescent : baseEnd_588321 < baseStart_588321 := by decide
  rcases family_descends (prefixWord ++ tailWord_588321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588328 : List Nat := [2, 1, 5, 2, 1, 2, 2, 1, 1, 3, 3]
def baseStart_588328 : Nat := 118140960795 + 588328 * 2 ^ 59
def prefixEnd_588328 : Nat := 4983230072969 + 3 ^ 40 * 588328 * 2
def baseEnd_588328 : Nat := 302095046498479397694335

theorem tailTrace_588328 : CollatzResearch.WordTrace tailWord_588328 prefixEnd_588328 302095046498479397694335 := by
  unfold tailWord_588328
  simp only [CollatzResearch.WordTrace]
  refine ⟨10729042506297804634006819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14305390008397072845342425 10729042506297804634006819)
  ·
    refine ⟨16093563759446706951010229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10729042506297804634006819 16093563759446706951010229)
    ·
      refine ⟨1508771602448128776657209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16093563759446706951010229 1508771602448128776657209)
      ·
        refine ⟨1131578701836096582492907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1508771602448128776657209 1131578701836096582492907)
        ·
          refine ⟨1697368052754144873739361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1131578701836096582492907 1697368052754144873739361)
          ·
            refine ⟨1273026039565608655304521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1697368052754144873739361 1273026039565608655304521)
            ·
              refine ⟨954769529674206491478391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1273026039565608655304521 954769529674206491478391)
              ·
                refine ⟨1432154294511309737217587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 954769529674206491478391 1432154294511309737217587)
                ·
                  refine ⟨2148231441766964605826381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1432154294511309737217587 2148231441766964605826381)
                  ·
                    refine ⟨805586790662611727184893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2148231441766964605826381 805586790662611727184893)
                    ·
                      refine ⟨302095046498479397694335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 805586790662611727184893 302095046498479397694335)
                      ·
                        rfl

theorem cell23_588328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_588328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_588328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_588328 prefixEnd_588328 := by exact prefixLift 588328
  have htrace : WordTrace (prefixWord ++ tailWord_588328) baseStart_588328 baseEnd_588328 := by
    simpa [prefixWord, tailWord_588328, baseEnd_588328] using wordTrace_append hprefix tailTrace_588328
  have hstable : (prefixWord ++ tailWord_588328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588328).length < 2 ^ (prefixWord ++ tailWord_588328).sum := by decide
  have hdescent : baseEnd_588328 < baseStart_588328 := by decide
  rcases family_descends (prefixWord ++ tailWord_588328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588347 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 6]
def baseStart_588347 : Nat := 118140960795 + 588347 * 2 ^ 59
def prefixEnd_588347 : Nat := 4983230072969 + 3 ^ 40 * 588347 * 2
def baseEnd_588347 : Nat := 302104802630914823356747

theorem tailTrace_588347 : CollatzResearch.WordTrace tailWord_588347 prefixEnd_588347 302104802630914823356747 := by
  unfold tailWord_588347
  simp only [CollatzResearch.WordTrace]
  refine ⟨21458777999526775512955295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14305851999684517008636863 21458777999526775512955295)
  ·
    refine ⟨32188166999290163269432943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21458777999526775512955295 32188166999290163269432943)
    ·
      refine ⟨48282250498935244904149415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32188166999290163269432943 48282250498935244904149415)
      ·
        refine ⟨72423375748402867356224123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48282250498935244904149415 72423375748402867356224123)
        ·
          refine ⟨108635063622604301034336185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72423375748402867356224123 108635063622604301034336185)
          ·
            refine ⟨81476297716953225775752139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108635063622604301034336185 81476297716953225775752139)
            ·
              refine ⟨122214446575429838663628209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81476297716953225775752139 122214446575429838663628209)
              ·
                refine ⟨91660834931572378997721157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 122214446575429838663628209 91660834931572378997721157)
                ·
                  refine ⟨17186406549669821062072717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 91660834931572378997721157 17186406549669821062072717)
                  ·
                    refine ⟨6444902456126182898277269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17186406549669821062072717 6444902456126182898277269)
                    ·
                      refine ⟨302104802630914823356747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6444902456126182898277269 302104802630914823356747)
                      ·
                        rfl

theorem cell23_588347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 6].length) (baseStart_588347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_588347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_588347 prefixEnd_588347 := by exact prefixLift 588347
  have htrace : WordTrace (prefixWord ++ tailWord_588347) baseStart_588347 baseEnd_588347 := by
    simpa [prefixWord, tailWord_588347, baseEnd_588347] using wordTrace_append hprefix tailTrace_588347
  have hstable : (prefixWord ++ tailWord_588347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588347).length < 2 ^ (prefixWord ++ tailWord_588347).sum := by decide
  have hdescent : baseEnd_588347 < baseStart_588347 := by decide
  rcases family_descends (prefixWord ++ tailWord_588347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588351 : List Nat := [1, 1, 2, 2, 3, 2, 1, 4, 1, 4, 2]
def baseStart_588351 : Nat := 118140960795 + 588351 * 2 ^ 59
def prefixEnd_588351 : Nat := 4983230072969 + 3 ^ 40 * 588351 * 2
def baseEnd_588351 : Nat := 302106856553532807706729

theorem tailTrace_588351 : CollatzResearch.WordTrace tailWord_588351 prefixEnd_588351 302106856553532807706729 := by
  unfold tailWord_588351
  simp only [CollatzResearch.WordTrace]
  refine ⟨21458923891512284196100907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14305949261008189464067271 21458923891512284196100907)
  ·
    refine ⟨32188385837268426294151361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21458923891512284196100907 32188385837268426294151361)
    ·
      refine ⟨24141289377951319720613521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32188385837268426294151361 24141289377951319720613521)
      ·
        refine ⟨18105967033463489790460141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24141289377951319720613521 18105967033463489790460141)
        ·
          refine ⟨6789737637548808671422553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18105967033463489790460141 6789737637548808671422553)
          ·
            refine ⟨5092303228161606503566915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6789737637548808671422553 5092303228161606503566915)
            ·
              refine ⟨7638454842242409755350373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5092303228161606503566915 7638454842242409755350373)
              ·
                refine ⟨1432210282920451829128195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7638454842242409755350373 1432210282920451829128195)
                ·
                  refine ⟨2148315424380677743692293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1432210282920451829128195 2148315424380677743692293)
                  ·
                    refine ⟨402809142071377076942305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2148315424380677743692293 402809142071377076942305)
                    ·
                      refine ⟨302106856553532807706729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 402809142071377076942305 302106856553532807706729)
                      ·
                        rfl

theorem cell23_588351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 4, 1, 4, 2].length) (baseStart_588351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_588351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_588351 prefixEnd_588351 := by exact prefixLift 588351
  have htrace : WordTrace (prefixWord ++ tailWord_588351) baseStart_588351 baseEnd_588351 := by
    simpa [prefixWord, tailWord_588351, baseEnd_588351] using wordTrace_append hprefix tailTrace_588351
  have hstable : (prefixWord ++ tailWord_588351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588351).length < 2 ^ (prefixWord ++ tailWord_588351).sum := by decide
  have hdescent : baseEnd_588351 < baseStart_588351 := by decide
  rcases family_descends (prefixWord ++ tailWord_588351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588364 : List Nat := [2, 2, 1, 3, 1, 2, 1, 1, 4, 2, 4]
def baseStart_588364 : Nat := 118140960795 + 588364 * 2 ^ 59
def prefixEnd_588364 : Nat := 4983230072969 + 3 ^ 40 * 588364 * 2
def baseEnd_588364 : Nat := 302113531802041256844169

theorem tailTrace_588364 : CollatzResearch.WordTrace tailWord_588364 prefixEnd_588364 302113531802041256844169 := by
  unfold tailWord_588364
  simp only [CollatzResearch.WordTrace]
  refine ⟨10729699020232593708162073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14306265360310124944216097 10729699020232593708162073)
  ·
    refine ⟨8047274265174445281121555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10729699020232593708162073 8047274265174445281121555)
    ·
      refine ⟨12070911397761667921682333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8047274265174445281121555 12070911397761667921682333)
      ·
        refine ⟨4526591774160625470630875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12070911397761667921682333 4526591774160625470630875)
        ·
          refine ⟨6789887661240938205946313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4526591774160625470630875 6789887661240938205946313)
          ·
            refine ⟨5092415745930703654459735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6789887661240938205946313 5092415745930703654459735)
            ·
              refine ⟨7638623618896055481689603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5092415745930703654459735 7638623618896055481689603)
              ·
                refine ⟨11457935428344083222534405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7638623618896055481689603 11457935428344083222534405)
                ·
                  refine ⟨2148362892814515604225201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11457935428344083222534405 2148362892814515604225201)
                  ·
                    refine ⟨1611272169610886703168901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2148362892814515604225201 1611272169610886703168901)
                    ·
                      refine ⟨302113531802041256844169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1611272169610886703168901 302113531802041256844169)
                      ·
                        rfl

theorem cell23_588364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_588364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_588364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_588364 prefixEnd_588364 := by exact prefixLift 588364
  have htrace : WordTrace (prefixWord ++ tailWord_588364) baseStart_588364 baseEnd_588364 := by
    simpa [prefixWord, tailWord_588364, baseEnd_588364] using wordTrace_append hprefix tailTrace_588364
  have hstable : (prefixWord ++ tailWord_588364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588364).length < 2 ^ (prefixWord ++ tailWord_588364).sum := by decide
  have hdescent : baseEnd_588364 < baseStart_588364 := by decide
  rcases family_descends (prefixWord ++ tailWord_588364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588368 : List Nat := [2, 1, 1, 1, 1, 3, 2, 6, 2, 2, 2]
def baseStart_588368 : Nat := 118140960795 + 588368 * 2 ^ 59
def prefixEnd_588368 : Nat := 4983230072969 + 3 ^ 40 * 588368 * 2
def baseEnd_588368 : Nat := 302115585724659241194151

theorem tailTrace_588368 : CollatzResearch.WordTrace tailWord_588368 prefixEnd_588368 302115585724659241194151 := by
  unfold tailWord_588368
  simp only [CollatzResearch.WordTrace]
  refine ⟨10729771966225348049734879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14306362621633797399646505 10729771966225348049734879)
  ·
    refine ⟨16094657949338022074602319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10729771966225348049734879 16094657949338022074602319)
    ·
      refine ⟨24141986924007033111903479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16094657949338022074602319 24141986924007033111903479)
      ·
        refine ⟨36212980386010549667855219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24141986924007033111903479 36212980386010549667855219)
        ·
          refine ⟨54319470579015824501782829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36212980386010549667855219 54319470579015824501782829)
          ·
            refine ⟨20369801467130934188168561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54319470579015824501782829 20369801467130934188168561)
            ·
              refine ⟨15277351100348200641126421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20369801467130934188168561 15277351100348200641126421)
              ·
                refine ⟨716125832828821905052801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15277351100348200641126421 716125832828821905052801)
                ·
                  refine ⟨537094374621616428789601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 716125832828821905052801 537094374621616428789601)
                  ·
                    refine ⟨402820780966212321592201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 537094374621616428789601 402820780966212321592201)
                    ·
                      refine ⟨302115585724659241194151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 402820780966212321592201 302115585724659241194151)
                      ·
                        rfl

theorem cell23_588368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 6, 2, 2, 2].length) (baseStart_588368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_588368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_588368 prefixEnd_588368 := by exact prefixLift 588368
  have htrace : WordTrace (prefixWord ++ tailWord_588368) baseStart_588368 baseEnd_588368 := by
    simpa [prefixWord, tailWord_588368, baseEnd_588368] using wordTrace_append hprefix tailTrace_588368
  have hstable : (prefixWord ++ tailWord_588368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588368).length < 2 ^ (prefixWord ++ tailWord_588368).sum := by decide
  have hdescent : baseEnd_588368 < baseStart_588368 := by decide
  rcases family_descends (prefixWord ++ tailWord_588368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588421 : List Nat := [1, 3, 1, 1, 4, 3, 1, 2, 2, 5]
def baseStart_588421 : Nat := 118140960795 + 588421 * 2 ^ 59
def prefixEnd_588421 : Nat := 4983230072969 + 3 ^ 40 * 588421 * 2
def baseEnd_588421 : Nat := 100714266733115844610469

theorem tailTrace_588421 : CollatzResearch.WordTrace tailWord_588421 prefixEnd_588421 100714266733115844610469 := by
  unfold tailWord_588421
  simp only [CollatzResearch.WordTrace]
  refine ⟨21461477001258686151149117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14307651334172457434099411 21461477001258686151149117)
  ·
    refine ⟨8048053875472007306680919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21461477001258686151149117 8048053875472007306680919)
    ·
      refine ⟨12072080813208010960021379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8048053875472007306680919 12072080813208010960021379)
      ·
        refine ⟨18108121219812016440032069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12072080813208010960021379 18108121219812016440032069)
        ·
          refine ⟨3395272728714753082506013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18108121219812016440032069 3395272728714753082506013)
          ·
            refine ⟨1273227273268032405939755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3395272728714753082506013 1273227273268032405939755)
            ·
              refine ⟨1909840909902048608909633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1273227273268032405939755 1909840909902048608909633)
              ·
                refine ⟨1432380682426536456682225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1909840909902048608909633 1432380682426536456682225)
                ·
                  refine ⟨1074285511819902342511669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1432380682426536456682225 1074285511819902342511669)
                  ·
                    refine ⟨100714266733115844610469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1074285511819902342511669 100714266733115844610469)
                    ·
                      rfl

theorem cell23_588421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 2, 2, 5].length) (baseStart_588421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_588421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_588421 prefixEnd_588421 := by exact prefixLift 588421
  have htrace : WordTrace (prefixWord ++ tailWord_588421) baseStart_588421 baseEnd_588421 := by
    simpa [prefixWord, tailWord_588421, baseEnd_588421] using wordTrace_append hprefix tailTrace_588421
  have hstable : (prefixWord ++ tailWord_588421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588421).length < 2 ^ (prefixWord ++ tailWord_588421).sum := by decide
  have hdescent : baseEnd_588421 < baseStart_588421 := by decide
  rcases family_descends (prefixWord ++ tailWord_588421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588441 : List Nat := [1, 2, 1, 2, 1, 2, 4, 1, 1, 6, 2]
def baseStart_588441 : Nat := 118140960795 + 588441 * 2 ^ 59
def prefixEnd_588441 : Nat := 4983230072969 + 3 ^ 40 * 588441 * 2
def baseEnd_588441 : Nat := 302153069812437455581315

theorem tailTrace_588441 : CollatzResearch.WordTrace tailWord_588441 prefixEnd_588441 302153069812437455581315 := by
  unfold tailWord_588441
  simp only [CollatzResearch.WordTrace]
  refine ⟨21462206461186229566877177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14308137640790819711251451 21462206461186229566877177)
  ·
    refine ⟨16096654845889672175157883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21462206461186229566877177 16096654845889672175157883)
    ·
      refine ⟨24144982268834508262736825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16096654845889672175157883 24144982268834508262736825)
      ·
        refine ⟨18108736701625881197052619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24144982268834508262736825 18108736701625881197052619)
        ·
          refine ⟨27163105052438821795578929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18108736701625881197052619 27163105052438821795578929)
          ·
            refine ⟨20372328789329116346684197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27163105052438821795578929 20372328789329116346684197)
            ·
              refine ⟨3819811647999209315003287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20372328789329116346684197 3819811647999209315003287)
              ·
                refine ⟨5729717471998813972504931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3819811647999209315003287 5729717471998813972504931)
                ·
                  refine ⟨8594576207998220958757397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5729717471998813972504931 8594576207998220958757397)
                  ·
                    refine ⟨402870759749916607441753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8594576207998220958757397 402870759749916607441753)
                    ·
                      refine ⟨302153069812437455581315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 402870759749916607441753 302153069812437455581315)
                      ·
                        rfl

theorem cell23_588441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 6, 2].length) (baseStart_588441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_588441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_588441 prefixEnd_588441 := by exact prefixLift 588441
  have htrace : WordTrace (prefixWord ++ tailWord_588441) baseStart_588441 baseEnd_588441 := by
    simpa [prefixWord, tailWord_588441, baseEnd_588441] using wordTrace_append hprefix tailTrace_588441
  have hstable : (prefixWord ++ tailWord_588441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588441).length < 2 ^ (prefixWord ++ tailWord_588441).sum := by decide
  have hdescent : baseEnd_588441 < baseStart_588441 := by decide
  rcases family_descends (prefixWord ++ tailWord_588441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588455 : List Nat := [1, 1, 6, 3, 1, 1, 2, 1, 2, 5]
def baseStart_588455 : Nat := 118140960795 + 588455 * 2 ^ 59
def prefixEnd_588455 : Nat := 4983230072969 + 3 ^ 40 * 588455 * 2
def baseEnd_588455 : Nat := 100720086180533466935417

theorem tailTrace_588455 : CollatzResearch.WordTrace tailWord_588455 prefixEnd_588455 100720086180533466935417 := by
  unfold tailWord_588455
  simp only [CollatzResearch.WordTrace]
  refine ⟨21462717083135509957886819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14308478055423673305257879 21462717083135509957886819)
  ·
    refine ⟨32194075624703264936830229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21462717083135509957886819 32194075624703264936830229)
    ·
      refine ⟨1509097294907965543913917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 32194075624703264936830229 1509097294907965543913917)
      ·
        refine ⟨565911485590487078967719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1509097294907965543913917 565911485590487078967719)
        ·
          refine ⟨848867228385730618451579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 565911485590487078967719 848867228385730618451579)
          ·
            refine ⟨1273300842578595927677369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 848867228385730618451579 1273300842578595927677369)
            ·
              refine ⟨954975631933946945758027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1273300842578595927677369 954975631933946945758027)
              ·
                refine ⟨1432463447900920418637041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 954975631933946945758027 1432463447900920418637041)
                ·
                  refine ⟨1074347585925690313977781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1432463447900920418637041 1074347585925690313977781)
                  ·
                    refine ⟨100720086180533466935417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1074347585925690313977781 100720086180533466935417)
                    ·
                      rfl

theorem cell23_588455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_588455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_588455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_588455 prefixEnd_588455 := by exact prefixLift 588455
  have htrace : WordTrace (prefixWord ++ tailWord_588455) baseStart_588455 baseEnd_588455 := by
    simpa [prefixWord, tailWord_588455, baseEnd_588455] using wordTrace_append hprefix tailTrace_588455
  have hstable : (prefixWord ++ tailWord_588455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588455).length < 2 ^ (prefixWord ++ tailWord_588455).sum := by decide
  have hdescent : baseEnd_588455 < baseStart_588455 := by decide
  rcases family_descends (prefixWord ++ tailWord_588455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588478 : List Nat := [4, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3]
def baseStart_588478 : Nat := 118140960795 + 588478 * 2 ^ 59
def prefixEnd_588478 : Nat := 4983230072969 + 3 ^ 40 * 588478 * 2
def baseEnd_588478 : Nat := 302172068596653810818645

theorem tailTrace_588478 : CollatzResearch.WordTrace tailWord_588478 prefixEnd_588478 302172068596653810818645 := by
  unfold tailWord_588478
  simp only [CollatzResearch.WordTrace]
  refine ⟨2682944495256523110746761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14309037308034789923982725 2682944495256523110746761)
  ·
    refine ⟨2012208371442392333060071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2682944495256523110746761 2012208371442392333060071)
    ·
      refine ⟨3018312557163588499590107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2012208371442392333060071 3018312557163588499590107)
      ·
        refine ⟨4527468835745382749385161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3018312557163588499590107 4527468835745382749385161)
        ·
          refine ⟨3395601626809037062038871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4527468835745382749385161 3395601626809037062038871)
          ·
            refine ⟨5093402440213555593058307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3395601626809037062038871 5093402440213555593058307)
            ·
              refine ⟨7640103660320333389587461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5093402440213555593058307 7640103660320333389587461)
              ·
                refine ⟨1432519436310062510547649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7640103660320333389587461 1432519436310062510547649)
                ·
                  refine ⟨1074389577232546882910737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1432519436310062510547649 1074389577232546882910737)
                  ·
                    refine ⟨805792182924410162183053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1074389577232546882910737 805792182924410162183053)
                    ·
                      refine ⟨302172068596653810818645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 805792182924410162183053 302172068596653810818645)
                      ·
                        rfl

theorem cell23_588478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3].length) (baseStart_588478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_588478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_588478 prefixEnd_588478 := by exact prefixLift 588478
  have htrace : WordTrace (prefixWord ++ tailWord_588478) baseStart_588478 baseEnd_588478 := by
    simpa [prefixWord, tailWord_588478, baseEnd_588478] using wordTrace_append hprefix tailTrace_588478
  have hstable : (prefixWord ++ tailWord_588478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588478).length < 2 ^ (prefixWord ++ tailWord_588478).sum := by decide
  have hdescent : baseEnd_588478 < baseStart_588478 := by decide
  rcases family_descends (prefixWord ++ tailWord_588478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588511 : List Nat := [1, 1, 2, 3, 2, 3, 2, 1, 3, 5]
def baseStart_588511 : Nat := 118140960795 + 588511 * 2 ^ 59
def prefixEnd_588511 : Nat := 4983230072969 + 3 ^ 40 * 588511 * 2
def baseEnd_588511 : Nat := 100729671152750727235331

theorem tailTrace_588511 : CollatzResearch.WordTrace tailWord_588511 prefixEnd_588511 100729671152750727235331 := by
  unfold tailWord_588511
  simp only [CollatzResearch.WordTrace]
  refine ⟨21464759570932631521925387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14309839713955087681283591 21464759570932631521925387)
  ·
    refine ⟨32197139356398947282888081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21464759570932631521925387 32197139356398947282888081)
    ·
      refine ⟨24147854517299210462166061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32197139356398947282888081 24147854517299210462166061)
      ·
        refine ⟨9055445443987203923312273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24147854517299210462166061 9055445443987203923312273)
        ·
          refine ⟨6791584082990402942484205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9055445443987203923312273 6791584082990402942484205)
          ·
            refine ⟨2546844031121401103431577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6791584082990402942484205 2546844031121401103431577)
            ·
              refine ⟨1910133023341050827573683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2546844031121401103431577 1910133023341050827573683)
              ·
                refine ⟨2865199535011576241360525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1910133023341050827573683 2865199535011576241360525)
                ·
                  refine ⟨1074449825629341090510197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2865199535011576241360525 1074449825629341090510197)
                  ·
                    refine ⟨100729671152750727235331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1074449825629341090510197 100729671152750727235331)
                    ·
                      rfl

theorem cell23_588511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 3, 5].length) (baseStart_588511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_588511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_588511 prefixEnd_588511 := by exact prefixLift 588511
  have htrace : WordTrace (prefixWord ++ tailWord_588511) baseStart_588511 baseEnd_588511 := by
    simpa [prefixWord, tailWord_588511, baseEnd_588511] using wordTrace_append hprefix tailTrace_588511
  have hstable : (prefixWord ++ tailWord_588511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588511).length < 2 ^ (prefixWord ++ tailWord_588511).sum := by decide
  have hdescent : baseEnd_588511 < baseStart_588511 := by decide
  rcases family_descends (prefixWord ++ tailWord_588511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588542 : List Nat := [4, 2, 2, 1, 2, 2, 2, 1, 3, 1, 3]
def baseStart_588542 : Nat := 118140960795 + 588542 * 2 ^ 59
def prefixEnd_588542 : Nat := 4983230072969 + 3 ^ 40 * 588542 * 2
def baseEnd_588542 : Nat := 302204931358541560418351

theorem tailTrace_588542 : CollatzResearch.WordTrace tailWord_588542 prefixEnd_588542 302204931358541560418351 := by
  unfold tailWord_588542
  simp only [CollatzResearch.WordTrace]
  refine ⟨2683236279227540477037985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14310593489213549210869253 2683236279227540477037985)
  ·
    refine ⟨2012427209420655357778489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2683236279227540477037985 2012427209420655357778489)
    ·
      refine ⟨1509320407065491518333867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2012427209420655357778489 1509320407065491518333867)
      ·
        refine ⟨2263980610598237277500801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1509320407065491518333867 2263980610598237277500801)
        ·
          refine ⟨1697985457948677958125601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2263980610598237277500801 1697985457948677958125601)
          ·
            refine ⟨1273489093461508468594201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1697985457948677958125601 1273489093461508468594201)
            ·
              refine ⟨955116820096131351445651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1273489093461508468594201 955116820096131351445651)
              ·
                refine ⟨1432675230144197027168477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 955116820096131351445651 1432675230144197027168477)
                ·
                  refine ⟨537253211304073885188179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1432675230144197027168477 537253211304073885188179)
                  ·
                    refine ⟨805879816956110827782269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 537253211304073885188179 805879816956110827782269)
                    ·
                      refine ⟨302204931358541560418351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 805879816956110827782269 302204931358541560418351)
                      ·
                        rfl

theorem cell23_588542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_588542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_588542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_588542 prefixEnd_588542 := by exact prefixLift 588542
  have htrace : WordTrace (prefixWord ++ tailWord_588542) baseStart_588542 baseEnd_588542 := by
    simpa [prefixWord, tailWord_588542, baseEnd_588542] using wordTrace_append hprefix tailTrace_588542
  have hstable : (prefixWord ++ tailWord_588542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588542).length < 2 ^ (prefixWord ++ tailWord_588542).sum := by decide
  have hdescent : baseEnd_588542 < baseStart_588542 := by decide
  rcases family_descends (prefixWord ++ tailWord_588542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588562 : List Nat := [3, 2, 4, 1, 2, 1, 2, 2, 1, 5]
def baseStart_588562 : Nat := 118140960795 + 588562 * 2 ^ 59
def prefixEnd_588562 : Nat := 4983230072969 + 3 ^ 40 * 588562 * 2
def baseEnd_588562 : Nat := 100738400323877160722753

theorem tailTrace_588562 : CollatzResearch.WordTrace tailWord_588562 prefixEnd_588562 100738400323877160722753 := by
  unfold tailWord_588562
  simp only [CollatzResearch.WordTrace]
  refine ⟨5366654923436966808007985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14311079795831911488021293 5366654923436966808007985)
  ·
    refine ⟨4024991192577725106005989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5366654923436966808007985 4024991192577725106005989)
    ·
      refine ⟨754685848608323457376123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4024991192577725106005989 754685848608323457376123)
      ·
        refine ⟨1132028772912485186064185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 754685848608323457376123 1132028772912485186064185)
        ·
          refine ⟨849021579684363889548139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1132028772912485186064185 849021579684363889548139)
          ·
            refine ⟨1273532369526545834322209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 849021579684363889548139 1273532369526545834322209)
            ·
              refine ⟨955149277144909375741657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1273532369526545834322209 955149277144909375741657)
              ·
                refine ⟨716361957858682031806243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 955149277144909375741657 716361957858682031806243)
                ·
                  refine ⟨1074542936788023047709365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 716361957858682031806243 1074542936788023047709365)
                  ·
                    refine ⟨100738400323877160722753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1074542936788023047709365 100738400323877160722753)
                    ·
                      rfl

theorem cell23_588562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_588562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_588562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_588562 prefixEnd_588562 := by exact prefixLift 588562
  have htrace : WordTrace (prefixWord ++ tailWord_588562) baseStart_588562 baseEnd_588562 := by
    simpa [prefixWord, tailWord_588562, baseEnd_588562] using wordTrace_append hprefix tailTrace_588562
  have hstable : (prefixWord ++ tailWord_588562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588562).length < 2 ^ (prefixWord ++ tailWord_588562).sum := by decide
  have hdescent : baseEnd_588562 < baseStart_588562 := by decide
  rcases family_descends (prefixWord ++ tailWord_588562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588565 : List Nat := [1, 3, 2, 1, 2, 2, 1, 4, 3, 2, 2]
def baseStart_588565 : Nat := 118140960795 + 588565 * 2 ^ 59
def prefixEnd_588565 : Nat := 4983230072969 + 3 ^ 40 * 588565 * 2
def baseEnd_588565 : Nat := 302216741413594970430745

theorem tailTrace_588565 : CollatzResearch.WordTrace tailWord_588565 prefixEnd_588565 302216741413594970430745 := by
  unfold tailWord_588565
  simp only [CollatzResearch.WordTrace]
  refine ⟨21466729112736998744391149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14311152741824665829594099 21466729112736998744391149)
  ·
    refine ⟨8050023417276374529146681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21466729112736998744391149 8050023417276374529146681)
    ·
      refine ⟨6037517562957280896860011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8050023417276374529146681 6037517562957280896860011)
      ·
        refine ⟨9056276344435921345290017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6037517562957280896860011 9056276344435921345290017)
        ·
          refine ⟨6792207258326941008967513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9056276344435921345290017 6792207258326941008967513)
          ·
            refine ⟨5094155443745205756725635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6792207258326941008967513 5094155443745205756725635)
            ·
              refine ⟨7641233165617808635088453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5094155443745205756725635 7641233165617808635088453)
              ·
                refine ⟨1432731218553339119079085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7641233165617808635088453 1432731218553339119079085)
                ·
                  refine ⟨537274206957502169654657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1432731218553339119079085 537274206957502169654657)
                  ·
                    refine ⟨402955655218126627240993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 537274206957502169654657 402955655218126627240993)
                    ·
                      refine ⟨302216741413594970430745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 402955655218126627240993 302216741413594970430745)
                      ·
                        rfl

theorem cell23_588565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 4, 3, 2, 2].length) (baseStart_588565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_588565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_588565 prefixEnd_588565 := by exact prefixLift 588565
  have htrace : WordTrace (prefixWord ++ tailWord_588565) baseStart_588565 baseEnd_588565 := by
    simpa [prefixWord, tailWord_588565, baseEnd_588565] using wordTrace_append hprefix tailTrace_588565
  have hstable : (prefixWord ++ tailWord_588565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588565).length < 2 ^ (prefixWord ++ tailWord_588565).sum := by decide
  have hdescent : baseEnd_588565 < baseStart_588565 := by decide
  rcases family_descends (prefixWord ++ tailWord_588565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588599 : List Nat := [1, 1, 3, 1, 2, 1, 7, 2, 1, 2, 2]
def baseStart_588599 : Nat := 118140960795 + 588599 * 2 ^ 59
def prefixEnd_588599 : Nat := 4983230072969 + 3 ^ 40 * 588599 * 2
def baseEnd_588599 : Nat := 302234199755847837405589

theorem tailTrace_588599 : CollatzResearch.WordTrace tailWord_588599 prefixEnd_588599 302234199755847837405589 := by
  unfold tailWord_588599
  simp only [CollatzResearch.WordTrace]
  refine ⟨21467969194613822551128851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14311979463075881700752567 21467969194613822551128851)
  ·
    refine ⟨32201953791920733826693277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21467969194613822551128851 32201953791920733826693277)
    ·
      refine ⟨12075732671970275185009979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32201953791920733826693277 12075732671970275185009979)
      ·
        refine ⟨18113599007955412777514969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12075732671970275185009979 18113599007955412777514969)
        ·
          refine ⟨13585199255966559583136227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18113599007955412777514969 13585199255966559583136227)
          ·
            refine ⟨20377798883949839374704341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13585199255966559583136227 20377798883949839374704341)
            ·
              refine ⟨477604661342574360344633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 20377798883949839374704341 477604661342574360344633)
              ·
                refine ⟨358203496006930770258475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 477604661342574360344633 358203496006930770258475)
                ·
                  refine ⟨537305244010396155387713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 358203496006930770258475 537305244010396155387713)
                  ·
                    refine ⟨402978933007797116540785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 537305244010396155387713 402978933007797116540785)
                    ·
                      refine ⟨302234199755847837405589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 402978933007797116540785 302234199755847837405589)
                      ·
                        rfl

theorem cell23_588599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 7, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 7, 2, 1, 2, 2].length) (baseStart_588599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_588599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_588599 prefixEnd_588599 := by exact prefixLift 588599
  have htrace : WordTrace (prefixWord ++ tailWord_588599) baseStart_588599 baseEnd_588599 := by
    simpa [prefixWord, tailWord_588599, baseEnd_588599] using wordTrace_append hprefix tailTrace_588599
  have hstable : (prefixWord ++ tailWord_588599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588599).length < 2 ^ (prefixWord ++ tailWord_588599).sum := by decide
  have hdescent : baseEnd_588599 < baseStart_588599 := by decide
  rcases family_descends (prefixWord ++ tailWord_588599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588641 : List Nat := [1, 2, 3, 1, 1, 1, 2, 3, 1, 3, 5]
def baseStart_588641 : Nat := 118140960795 + 588641 * 2 ^ 59
def prefixEnd_588641 : Nat := 4983230072969 + 3 ^ 40 * 588641 * 2
def baseEnd_588641 : Nat := 302255765943336673080395

theorem tailTrace_588641 : CollatzResearch.WordTrace tailWord_588641 prefixEnd_588641 302255765943336673080395 := by
  unfold tailWord_588641
  simp only [CollatzResearch.WordTrace]
  refine ⟨21469501060461663724157777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14313000706974442482771851 21469501060461663724157777)
  ·
    refine ⟨16102125795346247793118333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21469501060461663724157777 16102125795346247793118333)
    ·
      refine ⟨6038297173254842922419375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16102125795346247793118333 6038297173254842922419375)
      ·
        refine ⟨9057445759882264383629063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6038297173254842922419375 9057445759882264383629063)
        ·
          refine ⟨13586168639823396575443595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9057445759882264383629063 13586168639823396575443595)
          ·
            refine ⟨20379252959735094863165393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13586168639823396575443595 20379252959735094863165393)
            ·
              refine ⟨15284439719801321147374045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20379252959735094863165393 15284439719801321147374045)
              ·
                refine ⟨5731664894925495430265267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15284439719801321147374045 5731664894925495430265267)
                ·
                  refine ⟨8597497342388243145397901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5731664894925495430265267 8597497342388243145397901)
                  ·
                    refine ⟨3224061503395591179524213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8597497342388243145397901 3224061503395591179524213)
                    ·
                      refine ⟨302255765943336673080395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3224061503395591179524213 302255765943336673080395)
                      ·
                        rfl

theorem cell23_588641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_588641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_588641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_588641 prefixEnd_588641 := by exact prefixLift 588641
  have htrace : WordTrace (prefixWord ++ tailWord_588641) baseStart_588641 baseEnd_588641 := by
    simpa [prefixWord, tailWord_588641, baseEnd_588641] using wordTrace_append hprefix tailTrace_588641
  have hstable : (prefixWord ++ tailWord_588641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588641).length < 2 ^ (prefixWord ++ tailWord_588641).sum := by decide
  have hdescent : baseEnd_588641 < baseStart_588641 := by decide
  rcases family_descends (prefixWord ++ tailWord_588641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588655 : List Nat := [1, 1, 2, 1, 3, 1, 1, 5, 4, 2, 2]
def baseStart_588655 : Nat := 118140960795 + 588655 * 2 ^ 59
def prefixEnd_588655 : Nat := 4983230072969 + 3 ^ 40 * 588655 * 2
def baseEnd_588655 : Nat := 302262954672499618305331

theorem tailTrace_588655 : CollatzResearch.WordTrace tailWord_588655 prefixEnd_588655 302262954672499618305331 := by
  unfold tailWord_588655
  simp only [CollatzResearch.WordTrace]
  refine ⟨21470011682410944115167419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14313341121607296076778279 21470011682410944115167419)
  ·
    refine ⟨32205017523616416172751129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21470011682410944115167419 32205017523616416172751129)
    ·
      refine ⟨24153763142712312129563347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32205017523616416172751129 24153763142712312129563347)
      ·
        refine ⟨36230644714068468194345021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24153763142712312129563347 36230644714068468194345021)
        ·
          refine ⟨13586491767775675572879383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36230644714068468194345021 13586491767775675572879383)
          ·
            refine ⟨20379737651663513359319075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13586491767775675572879383 20379737651663513359319075)
            ·
              refine ⟨30569606477495270038978613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20379737651663513359319075 30569606477495270038978613)
              ·
                refine ⟨2865900607265181566154245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30569606477495270038978613 2865900607265181566154245)
                ·
                  refine ⟨537356363862221543653921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2865900607265181566154245 537356363862221543653921)
                  ·
                    refine ⟨403017272896666157740441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 537356363862221543653921 403017272896666157740441)
                    ·
                      refine ⟨302262954672499618305331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 403017272896666157740441 302262954672499618305331)
                      ·
                        rfl

theorem cell23_588655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 4, 2, 2].length) (baseStart_588655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_588655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_588655 prefixEnd_588655 := by exact prefixLift 588655
  have htrace : WordTrace (prefixWord ++ tailWord_588655) baseStart_588655 baseEnd_588655 := by
    simpa [prefixWord, tailWord_588655, baseEnd_588655] using wordTrace_append hprefix tailTrace_588655
  have hstable : (prefixWord ++ tailWord_588655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588655).length < 2 ^ (prefixWord ++ tailWord_588655).sum := by decide
  have hdescent : baseEnd_588655 < baseStart_588655 := by decide
  rcases family_descends (prefixWord ++ tailWord_588655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588658 : List Nat := [3, 2, 1, 2, 1, 1, 3, 1, 2, 4, 3]
def baseStart_588658 : Nat := 118140960795 + 588658 * 2 ^ 59
def prefixEnd_588658 : Nat := 4983230072969 + 3 ^ 40 * 588658 * 2
def baseEnd_588658 : Nat := 302264495114463106567817

theorem tailTrace_588658 : CollatzResearch.WordTrace tailWord_588658 prefixEnd_588658 302264495114463106567817 := by
  unfold tailWord_588658
  simp only [CollatzResearch.WordTrace]
  refine ⟨5367530275350018906881657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14313414067600050418351085 5367530275350018906881657)
  ·
    refine ⟨4025647706512514180161243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5367530275350018906881657 4025647706512514180161243)
    ·
      refine ⟨6038471559768771270241865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4025647706512514180161243 6038471559768771270241865)
      ·
        refine ⟨4528853669826578452681399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6038471559768771270241865 4528853669826578452681399)
        ·
          refine ⟨6793280504739867679022099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4528853669826578452681399 6793280504739867679022099)
          ·
            refine ⟨10189920757109801518533149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6793280504739867679022099 10189920757109801518533149)
            ·
              refine ⟨3821220283916175569449931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10189920757109801518533149 3821220283916175569449931)
              ·
                refine ⟨5731830425874263354174897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3821220283916175569449931 5731830425874263354174897)
                ·
                  refine ⟨4298872819405697515631173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5731830425874263354174897 4298872819405697515631173)
                  ·
                    refine ⟨806038653638568284180845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4298872819405697515631173 806038653638568284180845)
                    ·
                      refine ⟨302264495114463106567817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 806038653638568284180845 302264495114463106567817)
                      ·
                        rfl

theorem cell23_588658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 2, 4, 3].length) (baseStart_588658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_588658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_588658 prefixEnd_588658 := by exact prefixLift 588658
  have htrace : WordTrace (prefixWord ++ tailWord_588658) baseStart_588658 baseEnd_588658 := by
    simpa [prefixWord, tailWord_588658, baseEnd_588658] using wordTrace_append hprefix tailTrace_588658
  have hstable : (prefixWord ++ tailWord_588658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588658).length < 2 ^ (prefixWord ++ tailWord_588658).sum := by decide
  have hdescent : baseEnd_588658 < baseStart_588658 := by decide
  rcases family_descends (prefixWord ++ tailWord_588658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588695 : List Nat := [1, 1, 3, 3, 1, 2, 4, 3, 5]
def baseStart_588695 : Nat := 118140960795 + 588695 * 2 ^ 59
def prefixEnd_588695 : Nat := 4983230072969 + 3 ^ 40 * 588695 * 2
def baseEnd_588695 : Nat := 33587054877631051311683

theorem tailTrace_588695 : CollatzResearch.WordTrace tailWord_588695 prefixEnd_588695 33587054877631051311683 := by
  unfold tailWord_588695
  simp only [CollatzResearch.WordTrace]
  refine ⟨21471470602266030946623539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14314313734844020631082359 21471470602266030946623539)
  ·
    refine ⟨32207205903399046419935309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21471470602266030946623539 32207205903399046419935309)
    ·
      refine ⟨12077702213774642407475741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32207205903399046419935309 12077702213774642407475741)
      ·
        refine ⟨4529138330165490902803403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12077702213774642407475741 4529138330165490902803403)
        ·
          refine ⟨6793707495248236354205105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4529138330165490902803403 6793707495248236354205105)
          ·
            refine ⟨5095280621436177265653829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6793707495248236354205105 5095280621436177265653829)
            ·
              refine ⟨955365116519283237310093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5095280621436177265653829 955365116519283237310093)
              ·
                refine ⟨358261918694731213991285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 955365116519283237310093 358261918694731213991285)
                ·
                  refine ⟨33587054877631051311683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 358261918694731213991285 33587054877631051311683)
                  ·
                    rfl

theorem cell23_588695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 3, 5].length) (baseStart_588695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_588695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_588695 prefixEnd_588695 := by exact prefixLift 588695
  have htrace : WordTrace (prefixWord ++ tailWord_588695) baseStart_588695 baseEnd_588695 := by
    simpa [prefixWord, tailWord_588695, baseEnd_588695] using wordTrace_append hprefix tailTrace_588695
  have hstable : (prefixWord ++ tailWord_588695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588695).length < 2 ^ (prefixWord ++ tailWord_588695).sum := by decide
  have hdescent : baseEnd_588695 < baseStart_588695 := by decide
  rcases family_descends (prefixWord ++ tailWord_588695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588705 : List Nat := [1, 2, 3, 4, 1, 1, 1, 2, 2, 3, 3]
def baseStart_588705 : Nat := 118140960795 + 588705 * 2 ^ 59
def prefixEnd_588705 : Nat := 4983230072969 + 3 ^ 40 * 588705 * 2
def baseEnd_588705 : Nat := 302288628705224422680101

theorem tailTrace_588705 : CollatzResearch.WordTrace tailWord_588705 prefixEnd_588705 302288628705224422680101 := by
  unfold tailWord_588705
  simp only [CollatzResearch.WordTrace]
  refine ⟨21471835332229802654487569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14314556888153201769658379 21471835332229802654487569)
  ·
    refine ⟨16103876499172351990865677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21471835332229802654487569 16103876499172351990865677)
    ·
      refine ⟨6038953687189631996574629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16103876499172351990865677 6038953687189631996574629)
      ·
        refine ⟨1132303816348055999357743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6038953687189631996574629 1132303816348055999357743)
        ·
          refine ⟨1698455724522083999036615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1132303816348055999357743 1698455724522083999036615)
          ·
            refine ⟨2547683586783125998554923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1698455724522083999036615 2547683586783125998554923)
            ·
              refine ⟨3821525380174688997832385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2547683586783125998554923 3821525380174688997832385)
              ·
                refine ⟨2866144035131016748374289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3821525380174688997832385 2866144035131016748374289)
                ·
                  refine ⟨2149608026348262561280717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2866144035131016748374289 2149608026348262561280717)
                  ·
                    refine ⟨806103009880598460480269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2149608026348262561280717 806103009880598460480269)
                    ·
                      refine ⟨302288628705224422680101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 806103009880598460480269 302288628705224422680101)
                      ·
                        rfl

theorem cell23_588705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_588705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_588705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_588705 prefixEnd_588705 := by exact prefixLift 588705
  have htrace : WordTrace (prefixWord ++ tailWord_588705) baseStart_588705 baseEnd_588705 := by
    simpa [prefixWord, tailWord_588705, baseEnd_588705] using wordTrace_append hprefix tailTrace_588705
  have hstable : (prefixWord ++ tailWord_588705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588705).length < 2 ^ (prefixWord ++ tailWord_588705).sum := by decide
  have hdescent : baseEnd_588705 < baseStart_588705 := by decide
  rcases family_descends (prefixWord ++ tailWord_588705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588706 : List Nat := [3, 3, 1, 2, 2, 3, 1, 2, 2, 2, 2]
def baseStart_588706 : Nat := 118140960795 + 588706 * 2 ^ 59
def prefixEnd_588706 : Nat := 4983230072969 + 3 ^ 40 * 588706 * 2
def baseEnd_588706 : Nat := 302289142185878918767597

theorem tailTrace_588706 : CollatzResearch.WordTrace tailWord_588706 prefixEnd_588706 302289142185878918767597 := by
  unfold tailWord_588706
  simp only [CollatzResearch.WordTrace]
  refine ⟨5367967951306544956318493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14314581203484119883515981 5367967951306544956318493)
  ·
    refine ⟨2012987981739954358619435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5367967951306544956318493 2012987981739954358619435)
    ·
      refine ⟨3019481972609931537929153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2012987981739954358619435 3019481972609931537929153)
      ·
        refine ⟨2264611479457448653446865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3019481972609931537929153 2264611479457448653446865)
        ·
          refine ⟨1698458609593086490085149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2264611479457448653446865 1698458609593086490085149)
          ·
            refine ⟨636921978597407433781931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1698458609593086490085149 636921978597407433781931)
            ·
              refine ⟨955382967896111150672897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 636921978597407433781931 955382967896111150672897)
              ·
                refine ⟨716537225922083363004673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 955382967896111150672897 716537225922083363004673)
                ·
                  refine ⟨537402919441562522253505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 716537225922083363004673 537402919441562522253505)
                  ·
                    refine ⟨403052189581171891690129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 537402919441562522253505 403052189581171891690129)
                    ·
                      refine ⟨302289142185878918767597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 403052189581171891690129 302289142185878918767597)
                      ·
                        rfl

theorem cell23_588706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 2, 2, 2, 2].length) (baseStart_588706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_588706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_588706 prefixEnd_588706 := by exact prefixLift 588706
  have htrace : WordTrace (prefixWord ++ tailWord_588706) baseStart_588706 baseEnd_588706 := by
    simpa [prefixWord, tailWord_588706, baseEnd_588706] using wordTrace_append hprefix tailTrace_588706
  have hstable : (prefixWord ++ tailWord_588706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588706).length < 2 ^ (prefixWord ++ tailWord_588706).sum := by decide
  have hdescent : baseEnd_588706 < baseStart_588706 := by decide
  rcases family_descends (prefixWord ++ tailWord_588706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588708 : List Nat := [2, 3, 1, 2, 1, 2, 2, 1, 4, 5]
def baseStart_588708 : Nat := 118140960795 + 588708 * 2 ^ 59
def prefixEnd_588708 : Nat := 4983230072969 + 3 ^ 40 * 588708 * 2
def baseEnd_588708 : Nat := 100763389715729303647529

theorem tailTrace_588708 : CollatzResearch.WordTrace tailWord_588708 prefixEnd_588708 100763389715729303647529 := by
  unfold tailWord_588708
  simp only [CollatzResearch.WordTrace]
  refine ⟨10735972375609467083423389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14314629834145956111231185 10735972375609467083423389)
  ·
    refine ⟨4025989640853550156283771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10735972375609467083423389 4025989640853550156283771)
    ·
      refine ⟨6038984461280325234425657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4025989640853550156283771 6038984461280325234425657)
      ·
        refine ⟨4529238345960243925819243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6038984461280325234425657 4529238345960243925819243)
        ·
          refine ⟨6793857518940365888728865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4529238345960243925819243 6793857518940365888728865)
          ·
            refine ⟨5095393139205274416546649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6793857518940365888728865 5095393139205274416546649)
            ·
              refine ⟨3821544854403955812409987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5095393139205274416546649 3821544854403955812409987)
              ·
                refine ⟨5732317281605933718614981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3821544854403955812409987 5732317281605933718614981)
                ·
                  refine ⟨1074809490301112572240309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5732317281605933718614981 1074809490301112572240309)
                  ·
                    refine ⟨100763389715729303647529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1074809490301112572240309 100763389715729303647529)
                    ·
                      rfl

theorem cell23_588708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 4, 5].length) (baseStart_588708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_588708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_588708 prefixEnd_588708 := by exact prefixLift 588708
  have htrace : WordTrace (prefixWord ++ tailWord_588708) baseStart_588708 baseEnd_588708 := by
    simpa [prefixWord, tailWord_588708, baseEnd_588708] using wordTrace_append hprefix tailTrace_588708
  have hstable : (prefixWord ++ tailWord_588708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588708).length < 2 ^ (prefixWord ++ tailWord_588708).sum := by decide
  have hdescent : baseEnd_588708 < baseStart_588708 := by decide
  rcases family_descends (prefixWord ++ tailWord_588708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588728 : List Nat := [2, 1, 2, 1, 2, 4, 1, 2, 1, 3, 4]
def baseStart_588728 : Nat := 118140960795 + 588728 * 2 ^ 59
def prefixEnd_588728 : Nat := 4983230072969 + 3 ^ 40 * 588728 * 2
def baseEnd_588728 : Nat := 302300438760277832692495

theorem tailTrace_588728 : CollatzResearch.WordTrace tailWord_588728 prefixEnd_588728 302300438760277832692495 := by
  unfold tailWord_588728
  simp only [CollatzResearch.WordTrace]
  refine ⟨10736337105573238791287419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14315116140764318388383225 10736337105573238791287419)
  ·
    refine ⟨16104505658359858186931129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10736337105573238791287419 16104505658359858186931129)
    ·
      refine ⟨12078379243769893640198347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16104505658359858186931129 12078379243769893640198347)
      ·
        refine ⟨18117568865654840460297521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12078379243769893640198347 18117568865654840460297521)
        ·
          refine ⟨13588176649241130345223141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18117568865654840460297521 13588176649241130345223141)
          ·
            refine ⟨2547783121732711939729339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13588176649241130345223141 2547783121732711939729339)
            ·
              refine ⟨3821674682599067909594009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2547783121732711939729339 3821674682599067909594009)
              ·
                refine ⟨2866256011949300932195507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3821674682599067909594009 2866256011949300932195507)
                ·
                  refine ⟨4299384017923951398293261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2866256011949300932195507 4299384017923951398293261)
                  ·
                    refine ⟨1612269006721481774359973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4299384017923951398293261 1612269006721481774359973)
                    ·
                      refine ⟨302300438760277832692495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1612269006721481774359973 302300438760277832692495)
                      ·
                        rfl

theorem cell23_588728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 1, 3, 4].length) (baseStart_588728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_588728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_588728 prefixEnd_588728 := by exact prefixLift 588728
  have htrace : WordTrace (prefixWord ++ tailWord_588728) baseStart_588728 baseEnd_588728 := by
    simpa [prefixWord, tailWord_588728, baseEnd_588728] using wordTrace_append hprefix tailTrace_588728
  have hstable : (prefixWord ++ tailWord_588728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588728).length < 2 ^ (prefixWord ++ tailWord_588728).sum := by decide
  have hdescent : baseEnd_588728 < baseStart_588728 := by decide
  rcases family_descends (prefixWord ++ tailWord_588728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588731 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 9]
def baseStart_588731 : Nat := 118140960795 + 588731 * 2 ^ 59
def prefixEnd_588731 : Nat := 4983230072969 + 3 ^ 40 * 588731 * 2
def baseEnd_588731 : Nat := 302301979202241320954981

theorem tailTrace_588731 : CollatzResearch.WordTrace tailWord_588731 prefixEnd_588731 302301979202241320954981 := by
  unfold tailWord_588731
  simp only [CollatzResearch.WordTrace]
  refine ⟨21472783630135609094934047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14315189086757072729956031 21472783630135609094934047)
  ·
    refine ⟨32209175445203413642401071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21472783630135609094934047 32209175445203413642401071)
    ·
      refine ⟨48313763167805120463601607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32209175445203413642401071 48313763167805120463601607)
      ·
        refine ⟨72470644751707680695402411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48313763167805120463601607 72470644751707680695402411)
        ·
          refine ⟨108705967127561521043103617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72470644751707680695402411 108705967127561521043103617)
          ·
            refine ⟨81529475345671140782327713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108705967127561521043103617 81529475345671140782327713)
            ·
              refine ⟨61147106509253355586745785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81529475345671140782327713 61147106509253355586745785)
              ·
                refine ⟨45860329881940016690059339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61147106509253355586745785 45860329881940016690059339)
                ·
                  refine ⟨68790494822910025035089009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45860329881940016690059339 68790494822910025035089009)
                  ·
                    refine ⟨51592871117182518776316757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 68790494822910025035089009 51592871117182518776316757)
                    ·
                      refine ⟨302301979202241320954981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 51592871117182518776316757 302301979202241320954981)
                      ·
                        rfl

theorem cell23_588731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 9].length) (baseStart_588731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_588731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_588731 prefixEnd_588731 := by exact prefixLift 588731
  have htrace : WordTrace (prefixWord ++ tailWord_588731) baseStart_588731 baseEnd_588731 := by
    simpa [prefixWord, tailWord_588731, baseEnd_588731] using wordTrace_append hprefix tailTrace_588731
  have hstable : (prefixWord ++ tailWord_588731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588731).length < 2 ^ (prefixWord ++ tailWord_588731).sum := by decide
  have hdescent : baseEnd_588731 < baseStart_588731 := by decide
  rcases family_descends (prefixWord ++ tailWord_588731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588785 : List Nat := [1, 2, 2, 2, 4, 2, 1, 3, 6]
def baseStart_588785 : Nat := 118140960795 + 588785 * 2 ^ 59
def prefixEnd_588785 : Nat := 4983230072969 + 3 ^ 40 * 588785 * 2
def baseEnd_588785 : Nat := 33592189684176012186637

theorem tailTrace_588785 : CollatzResearch.WordTrace tailWord_588785 prefixEnd_588785 33592189684176012186637 := by
  unfold tailWord_588785
  simp only [CollatzResearch.WordTrace]
  refine ⟨21474753171939976317399809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14316502114626650878266539 21474753171939976317399809)
  ·
    refine ⟨16106064878954982238049857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21474753171939976317399809 16106064878954982238049857)
    ·
      refine ⟨12079548659216236678537393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16106064878954982238049857 12079548659216236678537393)
      ·
        refine ⟨9059661494412177508903045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12079548659216236678537393 9059661494412177508903045)
        ·
          refine ⟨1698686530202283282919321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9059661494412177508903045 1698686530202283282919321)
          ·
            refine ⟨1274014897651712462189491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1698686530202283282919321 1274014897651712462189491)
            ·
              refine ⟨1911022346477568693284237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1274014897651712462189491 1911022346477568693284237)
              ·
                refine ⟨716633379929088259981589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1911022346477568693284237 716633379929088259981589)
                ·
                  refine ⟨33592189684176012186637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 716633379929088259981589 33592189684176012186637)
                  ·
                    rfl

theorem cell23_588785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 3, 6].length) (baseStart_588785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_588785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_588785 prefixEnd_588785 := by exact prefixLift 588785
  have htrace : WordTrace (prefixWord ++ tailWord_588785) baseStart_588785 baseEnd_588785 := by
    simpa [prefixWord, tailWord_588785, baseEnd_588785] using wordTrace_append hprefix tailTrace_588785
  have hstable : (prefixWord ++ tailWord_588785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588785).length < 2 ^ (prefixWord ++ tailWord_588785).sum := by decide
  have hdescent : baseEnd_588785 < baseStart_588785 := by decide
  rcases family_descends (prefixWord ++ tailWord_588785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588795 : List Nat := [1, 1, 1, 1, 1, 3, 3, 3, 5, 1, 3]
def baseStart_588795 : Nat := 118140960795 + 588795 * 2 ^ 59
def prefixEnd_588795 : Nat := 4983230072969 + 3 ^ 40 * 588795 * 2
def baseEnd_588795 : Nat := 302334841964129070554687

theorem tailTrace_588795 : CollatzResearch.WordTrace tailWord_588795 prefixEnd_588795 302334841964129070554687 := by
  unfold tailWord_588795
  simp only [CollatzResearch.WordTrace]
  refine ⟨21475117901903748025263839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14316745267935832016842559 21475117901903748025263839)
  ·
    refine ⟨32212676852855622037895759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21475117901903748025263839 32212676852855622037895759)
    ·
      refine ⟨48319015279283433056843639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32212676852855622037895759 48319015279283433056843639)
      ·
        refine ⟨72478522918925149585265459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48319015279283433056843639 72478522918925149585265459)
        ·
          refine ⟨108717784378387724377898189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72478522918925149585265459 108717784378387724377898189)
          ·
            refine ⟨40769169141895396641711821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108717784378387724377898189 40769169141895396641711821)
            ·
              refine ⟨15288438428210773740641933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40769169141895396641711821 15288438428210773740641933)
              ·
                refine ⟨5733164410579040152740725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15288438428210773740641933 5733164410579040152740725)
                ·
                  refine ⟨537484163491785014319443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5733164410579040152740725 537484163491785014319443)
                  ·
                    refine ⟨806226245237677521479165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 537484163491785014319443 806226245237677521479165)
                    ·
                      refine ⟨302334841964129070554687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 806226245237677521479165 302334841964129070554687)
                      ·
                        rfl

theorem cell23_588795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 5, 1, 3].length) (baseStart_588795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_588795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_588795 prefixEnd_588795 := by exact prefixLift 588795
  have htrace : WordTrace (prefixWord ++ tailWord_588795) baseStart_588795 baseEnd_588795 := by
    simpa [prefixWord, tailWord_588795, baseEnd_588795] using wordTrace_append hprefix tailTrace_588795
  have hstable : (prefixWord ++ tailWord_588795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588795).length < 2 ^ (prefixWord ++ tailWord_588795).sum := by decide
  have hdescent : baseEnd_588795 < baseStart_588795 := by decide
  rcases family_descends (prefixWord ++ tailWord_588795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588835 : List Nat := [1, 1, 1, 4, 3, 2, 1, 2, 3, 1, 4]
def baseStart_588835 : Nat := 118140960795 + 588835 * 2 ^ 59
def prefixEnd_588835 : Nat := 4983230072969 + 3 ^ 40 * 588835 * 2
def baseEnd_588835 : Nat := 302355381190308914054503

theorem tailTrace_588835 : CollatzResearch.WordTrace tailWord_588835 prefixEnd_588835 302355381190308914054503 := by
  unfold tailWord_588835
  simp only [CollatzResearch.WordTrace]
  refine ⟨21476576821758834856719959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14317717881172556571146639 21476576821758834856719959)
  ·
    refine ⟨32214865232638252285079939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21476576821758834856719959 32214865232638252285079939)
    ·
      refine ⟨48322297848957378427619909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32214865232638252285079939 48322297848957378427619909)
      ·
        refine ⟨9060430846679508455178733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48322297848957378427619909 9060430846679508455178733)
        ·
          refine ⟨3397661567504815670692025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9060430846679508455178733 3397661567504815670692025)
          ·
            refine ⟨2548246175628611753019019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3397661567504815670692025 2548246175628611753019019)
            ·
              refine ⟨3822369263442917629528529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2548246175628611753019019 3822369263442917629528529)
              ·
                refine ⟨2866776947582188222146397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3822369263442917629528529 2866776947582188222146397)
                ·
                  refine ⟨1075041355343320583304899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2866776947582188222146397 1075041355343320583304899)
                  ·
                    refine ⟨1612562033014980874957349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1075041355343320583304899 1612562033014980874957349)
                    ·
                      refine ⟨302355381190308914054503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1612562033014980874957349 302355381190308914054503)
                      ·
                        rfl

theorem cell23_588835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 3, 1, 4].length) (baseStart_588835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_588835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_588835 prefixEnd_588835 := by exact prefixLift 588835
  have htrace : WordTrace (prefixWord ++ tailWord_588835) baseStart_588835 baseEnd_588835 := by
    simpa [prefixWord, tailWord_588835, baseEnd_588835] using wordTrace_append hprefix tailTrace_588835
  have hstable : (prefixWord ++ tailWord_588835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588835).length < 2 ^ (prefixWord ++ tailWord_588835).sum := by decide
  have hdescent : baseEnd_588835 < baseStart_588835 := by decide
  rcases family_descends (prefixWord ++ tailWord_588835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588858 : List Nat := [3, 1, 1, 1, 3, 1, 2, 11]
def baseStart_588858 : Nat := 118140960795 + 588858 * 2 ^ 59
def prefixEnd_588858 : Nat := 4983230072969 + 3 ^ 40 * 588858 * 2
def baseEnd_588858 : Nat := 11198784860939345335811

theorem tailTrace_588858 : CollatzResearch.WordTrace tailWord_588858 prefixEnd_588858 11198784860939345335811 := by
  unfold tailWord_588858
  simp only [CollatzResearch.WordTrace]
  refine ⟨5369353925168877446201807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14318277133783673189871485 5369353925168877446201807)
  ·
    refine ⟨8054030887753316169302711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5369353925168877446201807 8054030887753316169302711)
    ·
      refine ⟨12081046331629974253954067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8054030887753316169302711 12081046331629974253954067)
      ·
        refine ⟨18121569497444961380931101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12081046331629974253954067 18121569497444961380931101)
        ·
          refine ⟨6795588561541860517849163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18121569497444961380931101 6795588561541860517849163)
          ·
            refine ⟨10193382842312790776773745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6795588561541860517849163 10193382842312790776773745)
            ·
              refine ⟨7645037131734593082580309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10193382842312790776773745 7645037131734593082580309)
              ·
                refine ⟨11198784860939345335811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 7645037131734593082580309 11198784860939345335811)
                ·
                  rfl

theorem cell23_588858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 11].length) (baseStart_588858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_588858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_588858 prefixEnd_588858 := by exact prefixLift 588858
  have htrace : WordTrace (prefixWord ++ tailWord_588858) baseStart_588858 baseEnd_588858 := by
    simpa [prefixWord, tailWord_588858, baseEnd_588858] using wordTrace_append hprefix tailTrace_588858
  have hstable : (prefixWord ++ tailWord_588858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588858).length < 2 ^ (prefixWord ++ tailWord_588858).sum := by decide
  have hdescent : baseEnd_588858 < baseStart_588858 := by decide
  rcases family_descends (prefixWord ++ tailWord_588858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588862 : List Nat := [4, 2, 1, 3, 1, 1, 2, 2, 1, 6]
def baseStart_588862 : Nat := 118140960795 + 588862 * 2 ^ 59
def prefixEnd_588862 : Nat := 4983230072969 + 3 ^ 40 * 588862 * 2
def baseEnd_588862 : Nat := 100789748389326769472293

theorem tailTrace_588862 : CollatzResearch.WordTrace tailWord_588862 prefixEnd_588862 100789748389326769472293 := by
  unfold tailWord_588862
  simp only [CollatzResearch.WordTrace]
  refine ⟨2684695199082627308494105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14318374395107345645301893 2684695199082627308494105)
  ·
    refine ⟨2013521399311970481370579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2684695199082627308494105 2013521399311970481370579)
    ·
      refine ⟨3020282098967955722055869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2013521399311970481370579 3020282098967955722055869)
      ·
        refine ⟨1132605787112983395770951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3020282098967955722055869 1132605787112983395770951)
        ·
          refine ⟨1698908680669475093656427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1132605787112983395770951 1698908680669475093656427)
          ·
            refine ⟨2548363021004212640484641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1698908680669475093656427 2548363021004212640484641)
            ·
              refine ⟨1911272265753159480363481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2548363021004212640484641 1911272265753159480363481)
              ·
                refine ⟨1433454199314869610272611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1911272265753159480363481 1433454199314869610272611)
                ·
                  refine ⟨2150181298972304415408917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1433454199314869610272611 2150181298972304415408917)
                  ·
                    refine ⟨100789748389326769472293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2150181298972304415408917 100789748389326769472293)
                    ·
                      rfl

theorem cell23_588862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_588862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_588862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_588862 prefixEnd_588862 := by exact prefixLift 588862
  have htrace : WordTrace (prefixWord ++ tailWord_588862) baseStart_588862 baseEnd_588862 := by
    simpa [prefixWord, tailWord_588862, baseEnd_588862] using wordTrace_append hprefix tailTrace_588862
  have hstable : (prefixWord ++ tailWord_588862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588862).length < 2 ^ (prefixWord ++ tailWord_588862).sum := by decide
  have hdescent : baseEnd_588862 < baseStart_588862 := by decide
  rcases family_descends (prefixWord ++ tailWord_588862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588872 : List Nat := [2, 1, 3, 1, 1, 1, 5, 3, 1, 2, 3]
def baseStart_588872 : Nat := 118140960795 + 588872 * 2 ^ 59
def prefixEnd_588872 : Nat := 4983230072969 + 3 ^ 40 * 588872 * 2
def baseEnd_588872 : Nat := 302374379974525269291833

theorem tailTrace_588872 : CollatzResearch.WordTrace tailWord_588872 prefixEnd_588872 302374379974525269291833 := by
  unfold tailWord_588872
  simp only [CollatzResearch.WordTrace]
  refine ⟨10738963161312395087908435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14318617548416526783877913 10738963161312395087908435)
  ·
    refine ⟨16108444741968592631862653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10738963161312395087908435 16108444741968592631862653)
    ·
      refine ⟨6040666778238222236948495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16108444741968592631862653 6040666778238222236948495)
      ·
        refine ⟨9061000167357333355422743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6040666778238222236948495 9061000167357333355422743)
        ·
          refine ⟨13591500251036000033134115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9061000167357333355422743 13591500251036000033134115)
          ·
            refine ⟨20387250376554000049701173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13591500251036000033134115 20387250376554000049701173)
            ·
              refine ⟨1911304722801937504659485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20387250376554000049701173 1911304722801937504659485)
              ·
                refine ⟨716739271050726564247307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1911304722801937504659485 716739271050726564247307)
                ·
                  refine ⟨1075108906576089846370961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 716739271050726564247307 1075108906576089846370961)
                  ·
                    refine ⟨806331679932067384778221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1075108906576089846370961 806331679932067384778221)
                    ·
                      refine ⟨302374379974525269291833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 806331679932067384778221 302374379974525269291833)
                      ·
                        rfl

theorem cell23_588872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 3, 1, 2, 3].length) (baseStart_588872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_588872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_588872 prefixEnd_588872 := by exact prefixLift 588872
  have htrace : WordTrace (prefixWord ++ tailWord_588872) baseStart_588872 baseEnd_588872 := by
    simpa [prefixWord, tailWord_588872, baseEnd_588872] using wordTrace_append hprefix tailTrace_588872
  have hstable : (prefixWord ++ tailWord_588872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588872).length < 2 ^ (prefixWord ++ tailWord_588872).sum := by decide
  have hdescent : baseEnd_588872 < baseStart_588872 := by decide
  rcases family_descends (prefixWord ++ tailWord_588872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588926 : List Nat := [4, 2, 4, 1, 1, 2, 9]
def baseStart_588926 : Nat := 118140960795 + 588926 * 2 ^ 59
def prefixEnd_588926 : Nat := 4983230072969 + 3 ^ 40 * 588926 * 2
def baseEnd_588926 : Nat := 3733359357158864913785

theorem tailTrace_588926 : CollatzResearch.WordTrace tailWord_588926 prefixEnd_588926 3733359357158864913785 := by
  unfold tailWord_588926
  simp only [CollatzResearch.WordTrace]
  refine ⟨2684986983053644674785329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14319930576286104932188421 2684986983053644674785329)
  ·
    refine ⟨2013740237290233506088997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2684986983053644674785329 2013740237290233506088997)
    ·
      refine ⟨377576294491918782391687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2013740237290233506088997 377576294491918782391687)
      ·
        refine ⟨566364441737878173587531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 377576294491918782391687 566364441737878173587531)
        ·
          refine ⟨849546662606817260381297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 566364441737878173587531 849546662606817260381297)
          ·
            refine ⟨637159996955112945285973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 849546662606817260381297 637159996955112945285973)
            ·
              refine ⟨3733359357158864913785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 637159996955112945285973 3733359357158864913785)
              ·
                rfl

theorem cell23_588926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 9].length) (baseStart_588926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_588926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_588926 prefixEnd_588926 := by exact prefixLift 588926
  have htrace : WordTrace (prefixWord ++ tailWord_588926) baseStart_588926 baseEnd_588926 := by
    simpa [prefixWord, tailWord_588926, baseEnd_588926] using wordTrace_append hprefix tailTrace_588926
  have hstable : (prefixWord ++ tailWord_588926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588926).length < 2 ^ (prefixWord ++ tailWord_588926).sum := by decide
  have hdescent : baseEnd_588926 < baseStart_588926 := by decide
  rcases family_descends (prefixWord ++ tailWord_588926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588993 : List Nat := [1, 2, 6, 1, 1, 1, 1, 4, 2, 2, 2]
def baseStart_588993 : Nat := 118140960795 + 588993 * 2 ^ 59
def prefixEnd_588993 : Nat := 4983230072969 + 3 ^ 40 * 588993 * 2
def baseEnd_588993 : Nat := 302436511133719295878777

theorem tailTrace_588993 : CollatzResearch.WordTrace tailWord_588993 prefixEnd_588993 302436511133719295878777 := by
  unfold tailWord_588993
  simp only [CollatzResearch.WordTrace]
  refine ⟨21482339555186427840971633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14321559703457618560647755 21482339555186427840971633)
  ·
    refine ⟨16111754666389820880728725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21482339555186427840971633 16111754666389820880728725)
    ·
      refine ⟨755238499987022853784159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 16111754666389820880728725 755238499987022853784159)
      ·
        refine ⟨1132857749980534280676239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 755238499987022853784159 1132857749980534280676239)
        ·
          refine ⟨1699286624970801421014359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1132857749980534280676239 1699286624970801421014359)
          ·
            refine ⟨2548929937456202131521539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1699286624970801421014359 2548929937456202131521539)
            ·
              refine ⟨3823394906184303197282309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2548929937456202131521539 3823394906184303197282309)
              ·
                refine ⟨716886544909556849490433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3823394906184303197282309 716886544909556849490433)
                ·
                  refine ⟨537664908682167637117825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 716886544909556849490433 537664908682167637117825)
                  ·
                    refine ⟨403248681511625727838369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 537664908682167637117825 403248681511625727838369)
                    ·
                      refine ⟨302436511133719295878777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 403248681511625727838369 302436511133719295878777)
                      ·
                        rfl

theorem cell23_588993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_588993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_588993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_588993 prefixEnd_588993 := by exact prefixLift 588993
  have htrace : WordTrace (prefixWord ++ tailWord_588993) baseStart_588993 baseEnd_588993 := by
    simpa [prefixWord, tailWord_588993, baseEnd_588993] using wordTrace_append hprefix tailTrace_588993
  have hstable : (prefixWord ++ tailWord_588993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588993).length < 2 ^ (prefixWord ++ tailWord_588993).sum := by decide
  have hdescent : baseEnd_588993 < baseStart_588993 := by decide
  rcases family_descends (prefixWord ++ tailWord_588993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588995 : List Nat := [1, 1, 1, 3, 1, 1, 1, 5, 4, 5]
def baseStart_588995 : Nat := 118140960795 + 588995 * 2 ^ 59
def prefixEnd_588995 : Nat := 4983230072969 + 3 ^ 40 * 588995 * 2
def baseEnd_588995 : Nat := 100812512698342762684589

theorem tailTrace_588995 : CollatzResearch.WordTrace tailWord_588995 prefixEnd_588995 100812512698342762684589 := by
  unfold tailWord_588995
  simp only [CollatzResearch.WordTrace]
  refine ⟨21482412501179182182544439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14321608334119454788362959 21482412501179182182544439)
  ·
    refine ⟨32223618751768773273816659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21482412501179182182544439 32223618751768773273816659)
    ·
      refine ⟨48335428127653159910724989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32223618751768773273816659 48335428127653159910724989)
      ·
        refine ⟨18125785547869934966521871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48335428127653159910724989 18125785547869934966521871)
        ·
          refine ⟨27188678321804902449782807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18125785547869934966521871 27188678321804902449782807)
          ·
            refine ⟨40783017482707353674674211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27188678321804902449782807 40783017482707353674674211)
            ·
              refine ⟨61174526224061030512011317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40783017482707353674674211 61174526224061030512011317)
              ·
                refine ⟨5735111833505721610501061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61174526224061030512011317 5735111833505721610501061)
                ·
                  refine ⟨1075333468782322801968949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5735111833505721610501061 1075333468782322801968949)
                  ·
                    refine ⟨100812512698342762684589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1075333468782322801968949 100812512698342762684589)
                    ·
                      rfl

theorem cell23_588995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 4, 5].length) (baseStart_588995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_588995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_588995 prefixEnd_588995 := by exact prefixLift 588995
  have htrace : WordTrace (prefixWord ++ tailWord_588995) baseStart_588995 baseEnd_588995 := by
    simpa [prefixWord, tailWord_588995, baseEnd_588995] using wordTrace_append hprefix tailTrace_588995
  have hstable : (prefixWord ++ tailWord_588995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588995).length < 2 ^ (prefixWord ++ tailWord_588995).sum := by decide
  have hdescent : baseEnd_588995 < baseStart_588995 := by decide
  rcases family_descends (prefixWord ++ tailWord_588995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589032 : List Nat := [2, 1, 4, 1, 2, 1, 3, 1, 1, 3, 4]
def baseStart_589032 : Nat := 118140960795 + 589032 * 2 ^ 59
def prefixEnd_589032 : Nat := 4983230072969 + 3 ^ 40 * 589032 * 2
def baseEnd_589032 : Nat := 302456536879244643291097

theorem tailTrace_589032 : CollatzResearch.WordTrace tailWord_589032 prefixEnd_589032 302456536879244643291097 := by
  unfold tailWord_589032
  simp only [CollatzResearch.WordTrace]
  refine ⟨10741881001022568750820675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14322508001363425001094233 10741881001022568750820675)
  ·
    refine ⟨16112821501533853126231013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10741881001022568750820675 16112821501533853126231013)
    ·
      refine ⟨3021154031537597461168315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16112821501533853126231013 3021154031537597461168315)
      ·
        refine ⟨4531731047306396191752473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3021154031537597461168315 4531731047306396191752473)
        ·
          refine ⟨3398798285479797143814355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4531731047306396191752473 3398798285479797143814355)
          ·
            refine ⟨5098197428219695715721533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3398798285479797143814355 5098197428219695715721533)
            ·
              refine ⟨1911824035582385893395575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5098197428219695715721533 1911824035582385893395575)
              ·
                refine ⟨2867736053373578840093363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1911824035582385893395575 2867736053373578840093363)
                ·
                  refine ⟨4301604080060368260140045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2867736053373578840093363 4301604080060368260140045)
                  ·
                    refine ⟨1613101530022638097552517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4301604080060368260140045 1613101530022638097552517)
                    ·
                      refine ⟨302456536879244643291097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1613101530022638097552517 302456536879244643291097)
                      ·
                        rfl

theorem cell23_589032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_589032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_589032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_589032 prefixEnd_589032 := by exact prefixLift 589032
  have htrace : WordTrace (prefixWord ++ tailWord_589032) baseStart_589032 baseEnd_589032 := by
    simpa [prefixWord, tailWord_589032, baseEnd_589032] using wordTrace_append hprefix tailTrace_589032
  have hstable : (prefixWord ++ tailWord_589032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589032).length < 2 ^ (prefixWord ++ tailWord_589032).sum := by decide
  have hdescent : baseEnd_589032 < baseStart_589032 := by decide
  rcases family_descends (prefixWord ++ tailWord_589032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589044 : List Nat := [2, 6, 1, 2, 1, 2, 1, 2, 2, 2, 2]
def baseStart_589044 : Nat := 118140960795 + 589044 * 2 ^ 59
def prefixEnd_589044 : Nat := 4983230072969 + 3 ^ 40 * 589044 * 2
def baseEnd_589044 : Nat := 302462698647098596341043

theorem tailTrace_589044 : CollatzResearch.WordTrace tailWord_589044 prefixEnd_589044 302462698647098596341043 := by
  unfold tailWord_589044
  simp only [CollatzResearch.WordTrace]
  refine ⟨10742099839000831775539093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14322799785334442367385457 10742099839000831775539093)
  ·
    refine ⟨503535929953163989478395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 10742099839000831775539093 503535929953163989478395)
    ·
      refine ⟨755303894929745984217593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 503535929953163989478395 755303894929745984217593)
      ·
        refine ⟨566477921197309488163195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 755303894929745984217593 566477921197309488163195)
        ·
          refine ⟨849716881795964232244793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 566477921197309488163195 849716881795964232244793)
          ·
            refine ⟨637287661346973174183595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 849716881795964232244793 637287661346973174183595)
            ·
              refine ⟨955931492020459761275393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 637287661346973174183595 955931492020459761275393)
              ·
                refine ⟨716948619015344820956545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 955931492020459761275393 716948619015344820956545)
                ·
                  refine ⟨537711464261508615717409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 716948619015344820956545 537711464261508615717409)
                  ·
                    refine ⟨403283598196131461788057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 537711464261508615717409 403283598196131461788057)
                    ·
                      refine ⟨302462698647098596341043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 403283598196131461788057 302462698647098596341043)
                      ·
                        rfl

theorem cell23_589044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_589044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_589044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_589044 prefixEnd_589044 := by exact prefixLift 589044
  have htrace : WordTrace (prefixWord ++ tailWord_589044) baseStart_589044 baseEnd_589044 := by
    simpa [prefixWord, tailWord_589044, baseEnd_589044] using wordTrace_append hprefix tailTrace_589044
  have hstable : (prefixWord ++ tailWord_589044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589044).length < 2 ^ (prefixWord ++ tailWord_589044).sum := by decide
  have hdescent : baseEnd_589044 < baseStart_589044 := by decide
  rcases family_descends (prefixWord ++ tailWord_589044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589059 : List Nat := [1, 1, 1, 3, 2, 5, 2, 1, 3, 4]
def baseStart_589059 : Nat := 118140960795 + 589059 * 2 ^ 59
def prefixEnd_589059 : Nat := 4983230072969 + 3 ^ 40 * 589059 * 2
def baseEnd_589059 : Nat := 100823466952305345884491

theorem tailTrace_589059 : CollatzResearch.WordTrace tailWord_589059 prefixEnd_589059 100823466952305345884491 := by
  unfold tailWord_589059
  simp only [CollatzResearch.WordTrace]
  refine ⟨21484746772947321112874231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14323164515298214075249487 21484746772947321112874231)
  ·
    refine ⟨32227120159420981669311347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21484746772947321112874231 32227120159420981669311347)
    ·
      refine ⟨48340680239131472503967021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32227120159420981669311347 48340680239131472503967021)
      ·
        refine ⟨18127755089674302188987633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48340680239131472503967021 18127755089674302188987633)
        ·
          refine ⟨13595816317255726641740725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18127755089674302188987633 13595816317255726641740725)
          ·
            refine ⟨1274607779742724372663193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13595816317255726641740725 1274607779742724372663193)
            ·
              refine ⟨955955834807043279497395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1274607779742724372663193 955955834807043279497395)
              ·
                refine ⟨1433933752210564919246093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 955955834807043279497395 1433933752210564919246093)
                ·
                  refine ⟨537725157078961844717285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1433933752210564919246093 537725157078961844717285)
                  ·
                    refine ⟨100823466952305345884491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 537725157078961844717285 100823466952305345884491)
                    ·
                      rfl

theorem cell23_589059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 1, 3, 4].length) (baseStart_589059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_589059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_589059 prefixEnd_589059 := by exact prefixLift 589059
  have htrace : WordTrace (prefixWord ++ tailWord_589059) baseStart_589059 baseEnd_589059 := by
    simpa [prefixWord, tailWord_589059, baseEnd_589059] using wordTrace_append hprefix tailTrace_589059
  have hstable : (prefixWord ++ tailWord_589059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589059).length < 2 ^ (prefixWord ++ tailWord_589059).sum := by decide
  have hdescent : baseEnd_589059 < baseStart_589059 := by decide
  rcases family_descends (prefixWord ++ tailWord_589059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589093 : List Nat := [1, 3, 1, 2, 4, 3, 1, 3, 1, 4]
def baseStart_589093 : Nat := 118140960795 + 589093 * 2 ^ 59
def prefixEnd_589093 : Nat := 4983230072969 + 3 ^ 40 * 589093 * 2
def baseEnd_589093 : Nat := 100829286399722968209439

theorem tailTrace_589093 : CollatzResearch.WordTrace tailWord_589093 prefixEnd_589093 100829286399722968209439 := by
  unfold tailWord_589093
  simp only [CollatzResearch.WordTrace]
  refine ⟨21485986854824144919611933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14323991236549429946407955 21485986854824144919611933)
  ·
    refine ⟨8057245070559054344854475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21485986854824144919611933 8057245070559054344854475)
    ·
      refine ⟨12085867605838581517281713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8057245070559054344854475 12085867605838581517281713)
      ·
        refine ⟨9064400704378936137961285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12085867605838581517281713 9064400704378936137961285)
        ·
          refine ⟨1699575132071050525867741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9064400704378936137961285 1699575132071050525867741)
          ·
            refine ⟨637340674526643947200403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1699575132071050525867741 637340674526643947200403)
            ·
              refine ⟨956011011789965920800605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 637340674526643947200403 956011011789965920800605)
              ·
                refine ⟨358504129421237220300227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 956011011789965920800605 358504129421237220300227)
                ·
                  refine ⟨537756194131855830450341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 358504129421237220300227 537756194131855830450341)
                  ·
                    refine ⟨100829286399722968209439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 537756194131855830450341 100829286399722968209439)
                    ·
                      rfl

theorem cell23_589093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 3, 1, 4].length) (baseStart_589093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_589093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_589093 prefixEnd_589093 := by exact prefixLift 589093
  have htrace : WordTrace (prefixWord ++ tailWord_589093) baseStart_589093 baseEnd_589093 := by
    simpa [prefixWord, tailWord_589093, baseEnd_589093] using wordTrace_append hprefix tailTrace_589093
  have hstable : (prefixWord ++ tailWord_589093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589093).length < 2 ^ (prefixWord ++ tailWord_589093).sum := by decide
  have hdescent : baseEnd_589093 < baseStart_589093 := by decide
  rcases family_descends (prefixWord ++ tailWord_589093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589110 : List Nat := [5, 1, 2, 3, 1, 2, 1, 1, 3, 4]
def baseStart_589110 : Nat := 118140960795 + 589110 * 2 ^ 59
def prefixEnd_589110 : Nat := 4983230072969 + 3 ^ 40 * 589110 * 2
def baseEnd_589110 : Nat := 100832196123431779371913

theorem tailTrace_589110 : CollatzResearch.WordTrace tailWord_589110 prefixEnd_589110 100832196123431779371913 := by
  unfold tailWord_589110
  simp only [CollatzResearch.WordTrace]
  refine ⟨1342912930985159801436299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14324404597175037881987189 1342912930985159801436299)
  ·
    refine ⟨2014369396477739702154449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1342912930985159801436299 2014369396477739702154449)
    ·
      refine ⟨1510777047358304776615837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2014369396477739702154449 1510777047358304776615837)
      ·
        refine ⟨566541392759364291230939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1510777047358304776615837 566541392759364291230939)
        ·
          refine ⟨849812089139046436846409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 566541392759364291230939 849812089139046436846409)
          ·
            refine ⟨637359066854284827634807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 849812089139046436846409 637359066854284827634807)
            ·
              refine ⟨956038600281427241452211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 637359066854284827634807 956038600281427241452211)
              ·
                refine ⟨1434057900422140862178317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 956038600281427241452211 1434057900422140862178317)
                ·
                  refine ⟨537771712658302823316869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1434057900422140862178317 537771712658302823316869)
                  ·
                    refine ⟨100832196123431779371913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 537771712658302823316869 100832196123431779371913)
                    ·
                      rfl

theorem cell23_589110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_589110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_589110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_589110 prefixEnd_589110 := by exact prefixLift 589110
  have htrace : WordTrace (prefixWord ++ tailWord_589110) baseStart_589110 baseEnd_589110 := by
    simpa [prefixWord, tailWord_589110, baseEnd_589110] using wordTrace_append hprefix tailTrace_589110
  have hstable : (prefixWord ++ tailWord_589110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589110).length < 2 ^ (prefixWord ++ tailWord_589110).sum := by decide
  have hdescent : baseEnd_589110 < baseStart_589110 := by decide
  rcases family_descends (prefixWord ++ tailWord_589110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589116 : List Nat := [2, 2, 2, 2, 1, 3, 3, 1, 3, 1, 3]
def baseStart_589116 : Nat := 118140960795 + 589116 * 2 ^ 59
def prefixEnd_589116 : Nat := 4983230072969 + 3 ^ 40 * 589116 * 2
def baseEnd_589116 : Nat := 302499669254222314640711

theorem tailTrace_589116 : CollatzResearch.WordTrace tailWord_589116 prefixEnd_589116 302499669254222314640711 := by
  unfold tailWord_589116
  simp only [CollatzResearch.WordTrace]
  refine ⟨10743412866870409923849601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14324550489160546565132801 10743412866870409923849601)
  ·
    refine ⟨8057559650152807442887201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10743412866870409923849601 8057559650152807442887201)
    ·
      refine ⟨6043169737614605582165401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8057559650152807442887201 6043169737614605582165401)
      ·
        refine ⟨4532377303210954186624051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6043169737614605582165401 4532377303210954186624051)
        ·
          refine ⟨6798565954816431279936077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4532377303210954186624051 6798565954816431279936077)
          ·
            refine ⟨2549462233056161729976029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6798565954816431279936077 2549462233056161729976029)
            ·
              refine ⟨956048337396060648741011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2549462233056161729976029 956048337396060648741011)
              ·
                refine ⟨1434072506094090973111517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 956048337396060648741011 1434072506094090973111517)
                ·
                  refine ⟨537777189785284114916819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1434072506094090973111517 537777189785284114916819)
                  ·
                    refine ⟨806665784677926172375229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 537777189785284114916819 806665784677926172375229)
                    ·
                      refine ⟨302499669254222314640711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 806665784677926172375229 302499669254222314640711)
                      ·
                        rfl

theorem cell23_589116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 1, 3, 1, 3].length) (baseStart_589116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_589116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_589116 prefixEnd_589116 := by exact prefixLift 589116
  have htrace : WordTrace (prefixWord ++ tailWord_589116) baseStart_589116 baseEnd_589116 := by
    simpa [prefixWord, tailWord_589116, baseEnd_589116] using wordTrace_append hprefix tailTrace_589116
  have hstable : (prefixWord ++ tailWord_589116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589116).length < 2 ^ (prefixWord ++ tailWord_589116).sum := by decide
  have hdescent : baseEnd_589116 < baseStart_589116 := by decide
  rcases family_descends (prefixWord ++ tailWord_589116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589162 : List Nat := [3, 1, 3, 3, 13]
def baseStart_589162 : Nat := 118140960795 + 589162 * 2 ^ 59
def prefixEnd_589162 : Nat := 4983230072969 + 3 ^ 40 * 589162 * 2
def baseEnd_589162 : Nat := 414983936027886330131

theorem tailTrace_589162 : CollatzResearch.WordTrace tailWord_589162 prefixEnd_589162 414983936027886330131 := by
  unfold tailWord_589162
  simp only [CollatzResearch.WordTrace]
  refine ⟨5372125872893542425968435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14325668994382779802582493 5372125872893542425968435)
  ·
    refine ⟨8058188809340313638952653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5372125872893542425968435 8058188809340313638952653)
    ·
      refine ⟨3021820803502617614607245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8058188809340313638952653 3021820803502617614607245)
      ·
        refine ⟨1133182801313481605477717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3021820803502617614607245 1133182801313481605477717)
        ·
          refine ⟨414983936027886330131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 1133182801313481605477717 414983936027886330131)
          ·
            rfl

theorem cell23_589162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 13].length) (baseStart_589162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_589162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_589162 prefixEnd_589162 := by exact prefixLift 589162
  have htrace : WordTrace (prefixWord ++ tailWord_589162) baseStart_589162 baseEnd_589162 := by
    simpa [prefixWord, tailWord_589162, baseEnd_589162] using wordTrace_append hprefix tailTrace_589162
  have hstable : (prefixWord ++ tailWord_589162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589162).length < 2 ^ (prefixWord ++ tailWord_589162).sum := by decide
  have hdescent : baseEnd_589162 < baseStart_589162 := by decide
  rcases family_descends (prefixWord ++ tailWord_589162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589189 : List Nat := [1, 3, 1, 1, 3, 1, 3, 3, 1, 3, 3]
def baseStart_589189 : Nat := 118140960795 + 589189 * 2 ^ 59
def prefixEnd_589189 : Nat := 4983230072969 + 3 ^ 40 * 589189 * 2
def baseEnd_589189 : Nat := 302537153342000529027875

theorem tailTrace_589189 : CollatzResearch.WordTrace tailWord_589189 prefixEnd_589189 302537153342000529027875 := by
  unfold tailWord_589189
  simp only [CollatzResearch.WordTrace]
  refine ⟨21489488262476353315106621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14326325508317568876737747 21489488262476353315106621)
  ·
    refine ⟨8058558098428632493164983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21489488262476353315106621 8058558098428632493164983)
    ·
      refine ⟨12087837147642948739747475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8058558098428632493164983 12087837147642948739747475)
      ·
        refine ⟨18131755721464423109621213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12087837147642948739747475 18131755721464423109621213)
        ·
          refine ⟨6799408395549158666107955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18131755721464423109621213 6799408395549158666107955)
          ·
            refine ⟨10199112593323737999161933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6799408395549158666107955 10199112593323737999161933)
            ·
              refine ⟨3824667222496401749685725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10199112593323737999161933 3824667222496401749685725)
              ·
                refine ⟨1434250208436150656132147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3824667222496401749685725 1434250208436150656132147)
                ·
                  refine ⟨2151375312654225984198221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1434250208436150656132147 2151375312654225984198221)
                  ·
                    refine ⟨806765742245334744074333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2151375312654225984198221 806765742245334744074333)
                    ·
                      refine ⟨302537153342000529027875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 806765742245334744074333 302537153342000529027875)
                      ·
                        rfl

theorem cell23_589189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 3, 1, 3, 3].length) (baseStart_589189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_589189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_589189 prefixEnd_589189 := by exact prefixLift 589189
  have htrace : WordTrace (prefixWord ++ tailWord_589189) baseStart_589189 baseEnd_589189 := by
    simpa [prefixWord, tailWord_589189, baseEnd_589189] using wordTrace_append hprefix tailTrace_589189
  have hstable : (prefixWord ++ tailWord_589189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589189).length < 2 ^ (prefixWord ++ tailWord_589189).sum := by decide
  have hdescent : baseEnd_589189 < baseStart_589189 := by decide
  rcases family_descends (prefixWord ++ tailWord_589189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589232 : List Nat := [2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 5]
def baseStart_589232 : Nat := 118140960795 + 589232 * 2 ^ 59
def prefixEnd_589232 : Nat := 4983230072969 + 3 ^ 40 * 589232 * 2
def baseEnd_589232 : Nat := 302559233010143860790177

theorem tailTrace_589232 : CollatzResearch.WordTrace tailWord_589232 prefixEnd_589232 302559233010143860790177 := by
  unfold tailWord_589232
  simp only [CollatzResearch.WordTrace]
  refine ⟨10745528300660285829460975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14327371067547047772614633 10745528300660285829460975)
  ·
    refine ⟨16118292450990428744191463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10745528300660285829460975 16118292450990428744191463)
    ·
      refine ⟨24177438676485643116287195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16118292450990428744191463 24177438676485643116287195)
      ·
        refine ⟨36266158014728464674430793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24177438676485643116287195 36266158014728464674430793)
        ·
          refine ⟨27199618511046348505823095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36266158014728464674430793 27199618511046348505823095)
          ·
            refine ⟨40799427766569522758734643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27199618511046348505823095 40799427766569522758734643)
            ·
              refine ⟨61199141649854284138101965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40799427766569522758734643 61199141649854284138101965)
              ·
                refine ⟨22949678118695356551788237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61199141649854284138101965 22949678118695356551788237)
                ·
                  refine ⟨8606129294510758706920589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22949678118695356551788237 8606129294510758706920589)
                  ·
                    refine ⟨3227298485441534515095221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8606129294510758706920589 3227298485441534515095221)
                    ·
                      refine ⟨302559233010143860790177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3227298485441534515095221 302559233010143860790177)
                      ·
                        rfl

theorem cell23_589232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 5].length) (baseStart_589232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_589232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_589232 prefixEnd_589232 := by exact prefixLift 589232
  have htrace : WordTrace (prefixWord ++ tailWord_589232) baseStart_589232 baseEnd_589232 := by
    simpa [prefixWord, tailWord_589232, baseEnd_589232] using wordTrace_append hprefix tailTrace_589232
  have hstable : (prefixWord ++ tailWord_589232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589232).length < 2 ^ (prefixWord ++ tailWord_589232).sum := by decide
  have hdescent : baseEnd_589232 < baseStart_589232 := by decide
  rcases family_descends (prefixWord ++ tailWord_589232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589297 : List Nat := [1, 2, 2, 2, 3, 4, 2, 1, 2, 2, 2]
def baseStart_589297 : Nat := 118140960795 + 589297 * 2 ^ 59
def prefixEnd_589297 : Nat := 4983230072969 + 3 ^ 40 * 589297 * 2
def baseEnd_589297 : Nat := 302592609252686106477379

theorem tailTrace_589297 : CollatzResearch.WordTrace tailWord_589297 prefixEnd_589297 302592609252686106477379 := by
  unfold tailWord_589297
  simp only [CollatzResearch.WordTrace]
  refine ⟨21493427346085087760038145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14328951564056725173358763 21493427346085087760038145)
  ·
    refine ⟨16120070509563815820028609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21493427346085087760038145 16120070509563815820028609)
    ·
      refine ⟨12090052882172861865021457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16120070509563815820028609 12090052882172861865021457)
      ·
        refine ⟨9067539661629646398766093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12090052882172861865021457 9067539661629646398766093)
        ·
          refine ⟨3400327373111117399537285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9067539661629646398766093 3400327373111117399537285)
          ·
            refine ⟨637561382458334512413241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3400327373111117399537285 637561382458334512413241)
            ·
              refine ⟨478171036843750884309931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 637561382458334512413241 478171036843750884309931)
              ·
                refine ⟨717256555265626326464897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 478171036843750884309931 717256555265626326464897)
                ·
                  refine ⟨537942416449219744848673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 717256555265626326464897 537942416449219744848673)
                  ·
                    refine ⟨403456812336914808636505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 537942416449219744848673 403456812336914808636505)
                    ·
                      refine ⟨302592609252686106477379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 403456812336914808636505 302592609252686106477379)
                      ·
                        rfl

theorem cell23_589297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 2, 1, 2, 2, 2].length) (baseStart_589297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_589297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_589297 prefixEnd_589297 := by exact prefixLift 589297
  have htrace : WordTrace (prefixWord ++ tailWord_589297) baseStart_589297 baseEnd_589297 := by
    simpa [prefixWord, tailWord_589297, baseEnd_589297] using wordTrace_append hprefix tailTrace_589297
  have hstable : (prefixWord ++ tailWord_589297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589297).length < 2 ^ (prefixWord ++ tailWord_589297).sum := by decide
  have hdescent : baseEnd_589297 < baseStart_589297 := by decide
  rcases family_descends (prefixWord ++ tailWord_589297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589349 : List Nat := [1, 3, 1, 2, 2, 1, 1, 2, 2, 4, 4]
def baseStart_589349 : Nat := 118140960795 + 589349 * 2 ^ 59
def prefixEnd_589349 : Nat := 4983230072969 + 3 ^ 40 * 589349 * 2
def baseEnd_589349 : Nat := 302619310246719903027139

theorem tailTrace_589349 : CollatzResearch.WordTrace tailWord_589349 prefixEnd_589349 302619310246719903027139 := by
  unfold tailWord_589349
  simp only [CollatzResearch.WordTrace]
  refine ⟨21495323941896700640931101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14330215961264467093954067 21495323941896700640931101)
  ·
    refine ⟨8060746478211262740349163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21495323941896700640931101 8060746478211262740349163)
    ·
      refine ⟨12091119717316894110523745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8060746478211262740349163 12091119717316894110523745)
      ·
        refine ⟨9068339787987670582892809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12091119717316894110523745 9068339787987670582892809)
        ·
          refine ⟨6801254840990752937169607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9068339787987670582892809 6801254840990752937169607)
          ·
            refine ⟨10201882261486129405754411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6801254840990752937169607 10201882261486129405754411)
            ·
              refine ⟨15302823392229194108631617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10201882261486129405754411 15302823392229194108631617)
              ·
                refine ⟨11477117544171895581473713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15302823392229194108631617 11477117544171895581473713)
                ·
                  refine ⟨8607838158128921686105285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11477117544171895581473713 8607838158128921686105285)
                  ·
                    refine ⟨1613969654649172816144741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8607838158128921686105285 1613969654649172816144741)
                    ·
                      refine ⟨302619310246719903027139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1613969654649172816144741 302619310246719903027139)
                      ·
                        rfl

theorem cell23_589349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 4, 4].length) (baseStart_589349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_589349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_589349 prefixEnd_589349 := by exact prefixLift 589349
  have htrace : WordTrace (prefixWord ++ tailWord_589349) baseStart_589349 baseEnd_589349 := by
    simpa [prefixWord, tailWord_589349, baseEnd_589349] using wordTrace_append hprefix tailTrace_589349
  have hstable : (prefixWord ++ tailWord_589349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589349).length < 2 ^ (prefixWord ++ tailWord_589349).sum := by decide
  have hdescent : baseEnd_589349 < baseStart_589349 := by decide
  rcases family_descends (prefixWord ++ tailWord_589349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589373 : List Nat := [1, 4, 1, 3, 3, 1, 1, 1, 1, 4, 3]
def baseStart_589373 : Nat := 118140960795 + 589373 * 2 ^ 59
def prefixEnd_589373 : Nat := 4983230072969 + 3 ^ 40 * 589373 * 2
def baseEnd_589373 : Nat := 302631633782427809127029

theorem tailTrace_589373 : CollatzResearch.WordTrace tailWord_589373 prefixEnd_589373 302631633782427809127029 := by
  unfold tailWord_589373
  simp only [CollatzResearch.WordTrace]
  refine ⟨21496199293809752739804773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14330799529206501826536515 21496199293809752739804773)
  ·
    refine ⟨4030537367589328638713395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21496199293809752739804773 4030537367589328638713395)
    ·
      refine ⟨6045806051383992958070093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4030537367589328638713395 6045806051383992958070093)
      ·
        refine ⟨2267177269268997359276285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6045806051383992958070093 2267177269268997359276285)
        ·
          refine ⟨850191475975874009728607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2267177269268997359276285 850191475975874009728607)
          ·
            refine ⟨1275287213963811014592911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 850191475975874009728607 1275287213963811014592911)
            ·
              refine ⟨1912930820945716521889367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1275287213963811014592911 1912930820945716521889367)
              ·
                refine ⟨2869396231418574782834051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1912930820945716521889367 2869396231418574782834051)
                ·
                  refine ⟨4304094347127862174251077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2869396231418574782834051 4304094347127862174251077)
                  ·
                    refine ⟨807017690086474157672077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4304094347127862174251077 807017690086474157672077)
                    ·
                      refine ⟨302631633782427809127029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 807017690086474157672077 302631633782427809127029)
                      ·
                        rfl

theorem cell23_589373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_589373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_589373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_589373 prefixEnd_589373 := by exact prefixLift 589373
  have htrace : WordTrace (prefixWord ++ tailWord_589373) baseStart_589373 baseEnd_589373 := by
    simpa [prefixWord, tailWord_589373, baseEnd_589373] using wordTrace_append hprefix tailTrace_589373
  have hstable : (prefixWord ++ tailWord_589373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589373).length < 2 ^ (prefixWord ++ tailWord_589373).sum := by decide
  have hdescent : baseEnd_589373 < baseStart_589373 := by decide
  rcases family_descends (prefixWord ++ tailWord_589373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589413 : List Nat := [1, 3, 1, 3, 3, 1, 1, 2, 1, 5, 2]
def baseStart_589413 : Nat := 118140960795 + 589413 * 2 ^ 59
def prefixEnd_589413 : Nat := 4983230072969 + 3 ^ 40 * 589413 * 2
def baseEnd_589413 : Nat := 302652173008607652626845

theorem tailTrace_589413 : CollatzResearch.WordTrace tailWord_589413 prefixEnd_589413 302652173008607652626845 := by
  unfold tailWord_589413
  simp only [CollatzResearch.WordTrace]
  refine ⟨21497658213664839571260893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14331772142443226380840595 21497658213664839571260893)
  ·
    refine ⟨8061621830124314839222835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21497658213664839571260893 8061621830124314839222835)
    ·
      refine ⟨12092432745186472258834253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8061621830124314839222835 12092432745186472258834253)
      ·
        refine ⟨4534662279444927097062845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12092432745186472258834253 4534662279444927097062845)
        ·
          refine ⟨1700498354791847661398567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4534662279444927097062845 1700498354791847661398567)
          ·
            refine ⟨2550747532187771492097851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1700498354791847661398567 2550747532187771492097851)
            ·
              refine ⟨3826121298281657238146777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2550747532187771492097851 3826121298281657238146777)
              ·
                refine ⟨2869590973711242928610083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3826121298281657238146777 2869590973711242928610083)
                ·
                  refine ⟨4304386460566864392915125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2869590973711242928610083 4304386460566864392915125)
                  ·
                    refine ⟨403536230678143536835793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4304386460566864392915125 403536230678143536835793)
                    ·
                      refine ⟨302652173008607652626845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 403536230678143536835793 302652173008607652626845)
                      ·
                        rfl

theorem cell23_589413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 5, 2].length) (baseStart_589413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_589413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_589413 prefixEnd_589413 := by exact prefixLift 589413
  have htrace : WordTrace (prefixWord ++ tailWord_589413) baseStart_589413 baseEnd_589413 := by
    simpa [prefixWord, tailWord_589413, baseEnd_589413] using wordTrace_append hprefix tailTrace_589413
  have hstable : (prefixWord ++ tailWord_589413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589413).length < 2 ^ (prefixWord ++ tailWord_589413).sum := by decide
  have hdescent : baseEnd_589413 < baseStart_589413 := by decide
  rcases family_descends (prefixWord ++ tailWord_589413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589430 : List Nat := [5, 1, 1, 2, 2, 1, 2, 1, 1, 5, 2]
def baseStart_589430 : Nat := 118140960795 + 589430 * 2 ^ 59
def prefixEnd_589430 : Nat := 4983230072969 + 3 ^ 40 * 589430 * 2
def baseEnd_589430 : Nat := 302660902179734086114267

theorem tailTrace_589430 : CollatzResearch.WordTrace tailWord_589430 prefixEnd_589430 302660902179734086114267 := by
  unfold tailWord_589430
  simp only [CollatzResearch.WordTrace]
  refine ⟨1343642390912703217164359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14332185503068834316419829 1343642390912703217164359)
  ·
    refine ⟨2015463586369054825746539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1343642390912703217164359 2015463586369054825746539)
    ·
      refine ⟨3023195379553582238619809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2015463586369054825746539 3023195379553582238619809)
      ·
        refine ⟨2267396534665186678964857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3023195379553582238619809 2267396534665186678964857)
        ·
          refine ⟨1700547400998890009223643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2267396534665186678964857 1700547400998890009223643)
          ·
            refine ⟨2550821101498335013835465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1700547400998890009223643 2550821101498335013835465)
            ·
              refine ⟨1913115826123751260376599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2550821101498335013835465 1913115826123751260376599)
              ·
                refine ⟨2869673739185626890564899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1913115826123751260376599 2869673739185626890564899)
                ·
                  refine ⟨4304510608778440335847349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2869673739185626890564899 4304510608778440335847349)
                  ·
                    refine ⟨403547869572978781485689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4304510608778440335847349 403547869572978781485689)
                    ·
                      refine ⟨302660902179734086114267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 403547869572978781485689 302660902179734086114267)
                      ·
                        rfl

theorem cell23_589430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 1, 5, 2].length) (baseStart_589430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_589430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_589430 prefixEnd_589430 := by exact prefixLift 589430
  have htrace : WordTrace (prefixWord ++ tailWord_589430) baseStart_589430 baseEnd_589430 := by
    simpa [prefixWord, tailWord_589430, baseEnd_589430] using wordTrace_append hprefix tailTrace_589430
  have hstable : (prefixWord ++ tailWord_589430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589430).length < 2 ^ (prefixWord ++ tailWord_589430).sum := by decide
  have hdescent : baseEnd_589430 < baseStart_589430 := by decide
  rcases family_descends (prefixWord ++ tailWord_589430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589437 : List Nat := [1, 4, 1, 1, 4, 1, 3, 3, 1, 1, 3]
def baseStart_589437 : Nat := 118140960795 + 589437 * 2 ^ 59
def prefixEnd_589437 : Nat := 4983230072969 + 3 ^ 40 * 589437 * 2
def baseEnd_589437 : Nat := 302664496544315558726735

theorem tailTrace_589437 : CollatzResearch.WordTrace tailWord_589437 prefixEnd_589437 302664496544315558726735 := by
  unfold tailWord_589437
  simp only [CollatzResearch.WordTrace]
  refine ⟨21498533565577891670134565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14332355710385261113423043 21498533565577891670134565)
  ·
    refine ⟨4030975043545854688150231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21498533565577891670134565 4030975043545854688150231)
    ·
      refine ⟨6046462565318782032225347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4030975043545854688150231 6046462565318782032225347)
      ·
        refine ⟨9069693847978173048338021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6046462565318782032225347 9069693847978173048338021)
        ·
          refine ⟨1700567596495907446563379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9069693847978173048338021 1700567596495907446563379)
          ·
            refine ⟨2550851394743861169845069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1700567596495907446563379 2550851394743861169845069)
            ·
              refine ⟨956569273028947938691901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2550851394743861169845069 956569273028947938691901)
              ·
                refine ⟨358713477385855477009463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 956569273028947938691901 358713477385855477009463)
                ·
                  refine ⟨538070216078783215514195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 358713477385855477009463 538070216078783215514195)
                  ·
                    refine ⟨807105324118174823271293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 538070216078783215514195 807105324118174823271293)
                    ·
                      refine ⟨302664496544315558726735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 807105324118174823271293 302664496544315558726735)
                      ·
                        rfl

theorem cell23_589437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 3, 1, 1, 3].length) (baseStart_589437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_589437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_589437 prefixEnd_589437 := by exact prefixLift 589437
  have htrace : WordTrace (prefixWord ++ tailWord_589437) baseStart_589437 baseEnd_589437 := by
    simpa [prefixWord, tailWord_589437, baseEnd_589437] using wordTrace_append hprefix tailTrace_589437
  have hstable : (prefixWord ++ tailWord_589437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589437).length < 2 ^ (prefixWord ++ tailWord_589437).sum := by decide
  have hdescent : baseEnd_589437 < baseStart_589437 := by decide
  rcases family_descends (prefixWord ++ tailWord_589437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589449 : List Nat := [1, 2, 1, 1, 4, 1, 13]
def baseStart_589449 : Nat := 118140960795 + 589449 * 2 ^ 59
def prefixEnd_589449 : Nat := 4983230072969 + 3 ^ 40 * 589449 * 2
def baseEnd_589449 : Nat := 3736674793977401379959

theorem tailTrace_589449 : CollatzResearch.WordTrace tailWord_589449 prefixEnd_589449 3736674793977401379959 := by
  unfold tailWord_589449
  simp only [CollatzResearch.WordTrace]
  refine ⟨21498971241534417719571401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14332647494356278479714267 21498971241534417719571401)
  ·
    refine ⟨16124228431150813289678551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21498971241534417719571401 16124228431150813289678551)
    ·
      refine ⟨24186342646726219934517827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16124228431150813289678551 24186342646726219934517827)
      ·
        refine ⟨36279513970089329901776741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24186342646726219934517827 36279513970089329901776741)
        ·
          refine ⟨6802408869391749356583139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36279513970089329901776741 6802408869391749356583139)
          ·
            refine ⟨10203613304087624034874709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6802408869391749356583139 10203613304087624034874709)
            ·
              refine ⟨3736674793977401379959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 10203613304087624034874709 3736674793977401379959)
              ·
                rfl

theorem cell23_589449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 13].length) (baseStart_589449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_589449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_589449 prefixEnd_589449 := by exact prefixLift 589449
  have htrace : WordTrace (prefixWord ++ tailWord_589449) baseStart_589449 baseEnd_589449 := by
    simpa [prefixWord, tailWord_589449, baseEnd_589449] using wordTrace_append hprefix tailTrace_589449
  have hstable : (prefixWord ++ tailWord_589449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589449).length < 2 ^ (prefixWord ++ tailWord_589449).sum := by decide
  have hdescent : baseEnd_589449 < baseStart_589449 := by decide
  rcases family_descends (prefixWord ++ tailWord_589449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589454 : List Nat := [4, 1, 1, 3, 1, 3, 3, 2, 1, 1, 3]
def baseStart_589454 : Nat := 118140960795 + 589454 * 2 ^ 59
def prefixEnd_589454 : Nat := 4983230072969 + 3 ^ 40 * 589454 * 2
def baseEnd_589454 : Nat := 302673225715441992214157

theorem tailTrace_589454 : CollatzResearch.WordTrace tailWord_589454 prefixEnd_589454 302673225715441992214157 := by
  unfold tailWord_589454
  simp only [CollatzResearch.WordTrace]
  refine ⟨2687394200814537946687927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14332769071010869049002277 2687394200814537946687927)
  ·
    refine ⟨4031091301221806920031891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2687394200814537946687927 4031091301221806920031891)
    ·
      refine ⟨6046636951832710380047837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4031091301221806920031891 6046636951832710380047837)
      ·
        refine ⟨2267488856937266392517939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6046636951832710380047837 2267488856937266392517939)
        ·
          refine ⟨3401233285405899588776909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2267488856937266392517939 3401233285405899588776909)
          ·
            refine ⟨1275462482027212345791341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3401233285405899588776909 1275462482027212345791341)
            ·
              refine ⟨478298430760204629671753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1275462482027212345791341 478298430760204629671753)
              ·
                refine ⟨358723823070153472253815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 478298430760204629671753 358723823070153472253815)
                ·
                  refine ⟨538085734605230208380723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 358723823070153472253815 538085734605230208380723)
                  ·
                    refine ⟨807128601907845312571085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 538085734605230208380723 807128601907845312571085)
                    ·
                      refine ⟨302673225715441992214157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 807128601907845312571085 302673225715441992214157)
                      ·
                        rfl

theorem cell23_589454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 3, 2, 1, 1, 3].length) (baseStart_589454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_589454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_589454 prefixEnd_589454 := by exact prefixLift 589454
  have htrace : WordTrace (prefixWord ++ tailWord_589454) baseStart_589454 baseEnd_589454 := by
    simpa [prefixWord, tailWord_589454, baseEnd_589454] using wordTrace_append hprefix tailTrace_589454
  have hstable : (prefixWord ++ tailWord_589454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589454).length < 2 ^ (prefixWord ++ tailWord_589454).sum := by decide
  have hdescent : baseEnd_589454 < baseStart_589454 := by decide
  rcases family_descends (prefixWord ++ tailWord_589454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589459 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 7]
def baseStart_589459 : Nat := 118140960795 + 589459 * 2 ^ 59
def prefixEnd_589459 : Nat := 4983230072969 + 3 ^ 40 * 589459 * 2
def baseEnd_589459 : Nat := 302675793118714472651633

theorem tailTrace_589459 : CollatzResearch.WordTrace tailWord_589459 prefixEnd_589459 302675793118714472651633 := by
  unfold tailWord_589459
  simp only [CollatzResearch.WordTrace]
  refine ⟨21499335971498189427435431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14332890647665459618290287 21499335971498189427435431)
  ·
    refine ⟨32249003957247284141153147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21499335971498189427435431 32249003957247284141153147)
    ·
      refine ⟨48373505935870926211729721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32249003957247284141153147 48373505935870926211729721)
      ·
        refine ⟨36280129451903194658797291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48373505935870926211729721 36280129451903194658797291)
        ·
          refine ⟨54420194177854791988195937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36280129451903194658797291 54420194177854791988195937)
          ·
            refine ⟨40815145633391093991146953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54420194177854791988195937 40815145633391093991146953)
            ·
              refine ⟨30611359225043320493360215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40815145633391093991146953 30611359225043320493360215)
              ·
                refine ⟨45917038837564980740040323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30611359225043320493360215 45917038837564980740040323)
                ·
                  refine ⟨68875558256347471110060485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45917038837564980740040323 68875558256347471110060485)
                  ·
                    refine ⟨12914167173065150833136341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 68875558256347471110060485 12914167173065150833136341)
                    ·
                      refine ⟨302675793118714472651633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 12914167173065150833136341 302675793118714472651633)
                      ·
                        rfl

theorem cell23_589459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 7].length) (baseStart_589459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_589459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_589459 prefixEnd_589459 := by exact prefixLift 589459
  have htrace : WordTrace (prefixWord ++ tailWord_589459) baseStart_589459 baseEnd_589459 := by
    simpa [prefixWord, tailWord_589459, baseEnd_589459] using wordTrace_append hprefix tailTrace_589459
  have hstable : (prefixWord ++ tailWord_589459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589459).length < 2 ^ (prefixWord ++ tailWord_589459).sum := by decide
  have hdescent : baseEnd_589459 < baseStart_589459 := by decide
  rcases family_descends (prefixWord ++ tailWord_589459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589474 : List Nat := [3, 3, 1, 4, 2, 1, 1, 2, 1, 5]
def baseStart_589474 : Nat := 118140960795 + 589474 * 2 ^ 59
def prefixEnd_589474 : Nat := 4983230072969 + 3 ^ 40 * 589474 * 2
def baseEnd_589474 : Nat := 100894498442843971321355

theorem tailTrace_589474 : CollatzResearch.WordTrace tailWord_589474 prefixEnd_589474 100894498442843971321355 := by
  unfold tailWord_589474
  simp only [CollatzResearch.WordTrace]
  refine ⟨5374970766610961747307869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14333255377629231326154317 5374970766610961747307869)
  ·
    refine ⟨2015614037479110655240451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5374970766610961747307869 2015614037479110655240451)
    ·
      refine ⟨3023421056218665982860677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2015614037479110655240451 3023421056218665982860677)
      ·
        refine ⟨566891448040999871786377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3023421056218665982860677 566891448040999871786377)
        ·
          refine ⟨425168586030749903839783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 566891448040999871786377 425168586030749903839783)
          ·
            refine ⟨637752879046124855759675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 425168586030749903839783 637752879046124855759675)
            ·
              refine ⟨956629318569187283639513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 637752879046124855759675 956629318569187283639513)
              ·
                refine ⟨717471988926890462729635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 956629318569187283639513 717471988926890462729635)
                ·
                  refine ⟨1076207983390335694094453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 717471988926890462729635 1076207983390335694094453)
                  ·
                    refine ⟨100894498442843971321355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1076207983390335694094453 100894498442843971321355)
                    ·
                      rfl

theorem cell23_589474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 2, 1, 5].length) (baseStart_589474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_589474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_589474 prefixEnd_589474 := by exact prefixLift 589474
  have htrace : WordTrace (prefixWord ++ tailWord_589474) baseStart_589474 baseEnd_589474 := by
    simpa [prefixWord, tailWord_589474, baseEnd_589474] using wordTrace_append hprefix tailTrace_589474
  have hstable : (prefixWord ++ tailWord_589474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589474).length < 2 ^ (prefixWord ++ tailWord_589474).sum := by decide
  have hdescent : baseEnd_589474 < baseStart_589474 := by decide
  rcases family_descends (prefixWord ++ tailWord_589474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589494 : List Nat := [5, 1, 3, 1, 1, 2, 3, 1, 1, 1, 4]
def baseStart_589494 : Nat := 118140960795 + 589494 * 2 ^ 59
def prefixEnd_589494 : Nat := 4983230072969 + 3 ^ 40 * 589494 * 2
def baseEnd_589494 : Nat := 302693764941621835713973

theorem tailTrace_589494 : CollatzResearch.WordTrace tailWord_589494 prefixEnd_589494 302693764941621835713973 := by
  unfold tailWord_589494
  simp only [CollatzResearch.WordTrace]
  refine ⟨1343788282898211900309971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14333741684247593603306357 1343788282898211900309971)
  ·
    refine ⟨2015682424347317850464957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1343788282898211900309971 2015682424347317850464957)
    ·
      refine ⟨755880909130244193924359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2015682424347317850464957 755880909130244193924359)
      ·
        refine ⟨1133821363695366290886539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 755880909130244193924359 1133821363695366290886539)
        ·
          refine ⟨1700732045543049436329809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1133821363695366290886539 1700732045543049436329809)
          ·
            refine ⟨1275549034157287077247357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1700732045543049436329809 1275549034157287077247357)
            ·
              refine ⟨478330887808982653967759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1275549034157287077247357 478330887808982653967759)
              ·
                refine ⟨717496331713473980951639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 478330887808982653967759 717496331713473980951639)
                ·
                  refine ⟨1076244497570210971427459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 717496331713473980951639 1076244497570210971427459)
                  ·
                    refine ⟨1614366746355316457141189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1076244497570210971427459 1614366746355316457141189)
                    ·
                      refine ⟨302693764941621835713973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1614366746355316457141189 302693764941621835713973)
                      ·
                        rfl

theorem cell23_589494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_589494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_589494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_589494 prefixEnd_589494 := by exact prefixLift 589494
  have htrace : WordTrace (prefixWord ++ tailWord_589494) baseStart_589494 baseEnd_589494 := by
    simpa [prefixWord, tailWord_589494, baseEnd_589494] using wordTrace_append hprefix tailTrace_589494
  have hstable : (prefixWord ++ tailWord_589494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589494).length < 2 ^ (prefixWord ++ tailWord_589494).sum := by decide
  have hdescent : baseEnd_589494 < baseStart_589494 := by decide
  rcases family_descends (prefixWord ++ tailWord_589494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589536 : List Nat := [2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 5]
def baseStart_589536 : Nat := 118140960795 + 589536 * 2 ^ 59
def prefixEnd_589536 : Nat := 4983230072969 + 3 ^ 40 * 589536 * 2
def baseEnd_589536 : Nat := 302715331129110671388779

theorem tailTrace_589536 : CollatzResearch.WordTrace tailWord_589536 prefixEnd_589536 302715331129110671388779 := by
  unfold tailWord_589536
  simp only [CollatzResearch.WordTrace]
  refine ⟨10751072196109615788994231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14334762928146154385325641 10751072196109615788994231)
  ·
    refine ⟨16126608294164423683491347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10751072196109615788994231 16126608294164423683491347)
    ·
      refine ⟨24189912441246635525237021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16126608294164423683491347 24189912441246635525237021)
      ·
        refine ⟨9071217165467488321963883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24189912441246635525237021 9071217165467488321963883)
        ·
          refine ⟨13606825748201232482945825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9071217165467488321963883 13606825748201232482945825)
          ·
            refine ⟨10205119311150924362209369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13606825748201232482945825 10205119311150924362209369)
            ·
              refine ⟨7653839483363193271657027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10205119311150924362209369 7653839483363193271657027)
              ·
                refine ⟨11480759225044789907485541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7653839483363193271657027 11480759225044789907485541)
                ·
                  refine ⟨2152642354695898107653539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11480759225044789907485541 2152642354695898107653539)
                  ·
                    refine ⟨3228963532043847161480309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2152642354695898107653539 3228963532043847161480309)
                    ·
                      refine ⟨302715331129110671388779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3228963532043847161480309 302715331129110671388779)
                      ·
                        rfl

theorem cell23_589536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 5].length) (baseStart_589536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_589536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_589536 prefixEnd_589536 := by exact prefixLift 589536
  have htrace : WordTrace (prefixWord ++ tailWord_589536) baseStart_589536 baseEnd_589536 := by
    simpa [prefixWord, tailWord_589536, baseEnd_589536] using wordTrace_append hprefix tailTrace_589536
  have hstable : (prefixWord ++ tailWord_589536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589536).length < 2 ^ (prefixWord ++ tailWord_589536).sum := by decide
  have hdescent : baseEnd_589536 < baseStart_589536 := by decide
  rcases family_descends (prefixWord ++ tailWord_589536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589550 : List Nat := [4, 1, 2, 1, 1, 2, 1, 4, 1, 4, 2]
def baseStart_589550 : Nat := 118140960795 + 589550 * 2 ^ 59
def prefixEnd_589550 : Nat := 4983230072969 + 3 ^ 40 * 589550 * 2
def baseEnd_589550 : Nat := 302722519858273616613715

theorem tailTrace_589550 : CollatzResearch.WordTrace tailWord_589550 prefixEnd_589550 302722519858273616613715 := by
  unfold tailWord_589550
  simp only [CollatzResearch.WordTrace]
  refine ⟨2687831876771063996124763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14335103342779007979332069 2687831876771063996124763)
  ·
    refine ⟨4031747815156595994187145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2687831876771063996124763 4031747815156595994187145)
    ·
      refine ⟨3023810861367446995640359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4031747815156595994187145 3023810861367446995640359)
      ·
        refine ⟨4535716292051170493460539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3023810861367446995640359 4535716292051170493460539)
        ·
          refine ⟨6803574438076755740190809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4535716292051170493460539 6803574438076755740190809)
          ·
            refine ⟨5102680828557566805143107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6803574438076755740190809 5102680828557566805143107)
            ·
              refine ⟨7654021242836350207714661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5102680828557566805143107 7654021242836350207714661)
              ·
                refine ⟨1435128983031815663946499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7654021242836350207714661 1435128983031815663946499)
                ·
                  refine ⟨2152693474547723495919749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1435128983031815663946499 2152693474547723495919749)
                  ·
                    refine ⟨403630026477698155484953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2152693474547723495919749 403630026477698155484953)
                    ·
                      refine ⟨302722519858273616613715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 403630026477698155484953 302722519858273616613715)
                      ·
                        rfl

theorem cell23_589550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 4, 1, 4, 2].length) (baseStart_589550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_589550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_589550 prefixEnd_589550 := by exact prefixLift 589550
  have htrace : WordTrace (prefixWord ++ tailWord_589550) baseStart_589550 baseEnd_589550 := by
    simpa [prefixWord, tailWord_589550, baseEnd_589550] using wordTrace_append hprefix tailTrace_589550
  have hstable : (prefixWord ++ tailWord_589550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589550).length < 2 ^ (prefixWord ++ tailWord_589550).sum := by decide
  have hdescent : baseEnd_589550 < baseStart_589550 := by decide
  rcases family_descends (prefixWord ++ tailWord_589550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589567 : List Nat := [1, 1, 2, 2, 1, 3, 5, 2, 2, 2, 2]
def baseStart_589567 : Nat := 118140960795 + 589567 * 2 ^ 59
def prefixEnd_589567 : Nat := 4983230072969 + 3 ^ 40 * 589567 * 2
def baseEnd_589567 : Nat := 302731249029400050101137

theorem tailTrace_589567 : CollatzResearch.WordTrace tailWord_589567 prefixEnd_589567 302731249029400050101137 := by
  unfold tailWord_589567
  simp only [CollatzResearch.WordTrace]
  refine ⟨21503275055106923872366955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14335516703404615914911303 21503275055106923872366955)
  ·
    refine ⟨32254912582660385808550433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21503275055106923872366955 32254912582660385808550433)
    ·
      refine ⟨24191184436995289356412825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32254912582660385808550433 24191184436995289356412825)
      ·
        refine ⟨18143388327746467017309619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24191184436995289356412825 18143388327746467017309619)
        ·
          refine ⟨27215082491619700525964429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18143388327746467017309619 27215082491619700525964429)
          ·
            refine ⟨10205655934357387697236661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27215082491619700525964429 10205655934357387697236661)
            ·
              refine ⟨956780243846005096615937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10205655934357387697236661 956780243846005096615937)
              ·
                refine ⟨717585182884503822461953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 956780243846005096615937 717585182884503822461953)
                ·
                  refine ⟨538188887163377866846465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 717585182884503822461953 538188887163377866846465)
                  ·
                    refine ⟨403641665372533400134849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 538188887163377866846465 403641665372533400134849)
                    ·
                      refine ⟨302731249029400050101137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 403641665372533400134849 302731249029400050101137)
                      ·
                        rfl

theorem cell23_589567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 2, 2, 2, 2].length) (baseStart_589567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_589567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_589567 prefixEnd_589567 := by exact prefixLift 589567
  have htrace : WordTrace (prefixWord ++ tailWord_589567) baseStart_589567 baseEnd_589567 := by
    simpa [prefixWord, tailWord_589567, baseEnd_589567] using wordTrace_append hprefix tailTrace_589567
  have hstable : (prefixWord ++ tailWord_589567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589567).length < 2 ^ (prefixWord ++ tailWord_589567).sum := by decide
  have hdescent : baseEnd_589567 < baseStart_589567 := by decide
  rcases family_descends (prefixWord ++ tailWord_589567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589588 : List Nat := [2, 4, 4, 1, 1, 1, 2, 2, 1, 3, 2]
def baseStart_589588 : Nat := 118140960795 + 589588 * 2 ^ 59
def prefixEnd_589588 : Nat := 4983230072969 + 3 ^ 40 * 589588 * 2
def baseEnd_589588 : Nat := 302742032123144467938541

theorem tailTrace_589588 : CollatzResearch.WordTrace tailWord_589588 prefixEnd_589588 302742032123144467938541 := by
  unfold tailWord_589588
  simp only [CollatzResearch.WordTrace]
  refine ⟨10752020494015422229440709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14336027325353896305920945 10752020494015422229440709)
  ·
    refine ⟨2016003842627891668020133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10752020494015422229440709 2016003842627891668020133)
    ·
      refine ⟨378000720492729687753775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2016003842627891668020133 378000720492729687753775)
      ·
        refine ⟨567001080739094531630663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 378000720492729687753775 567001080739094531630663)
        ·
          refine ⟨850501621108641797445995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 567001080739094531630663 850501621108641797445995)
          ·
            refine ⟨1275752431662962696168993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 850501621108641797445995 1275752431662962696168993)
            ·
              refine ⟨956814323747222022126745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1275752431662962696168993 956814323747222022126745)
              ·
                refine ⟨717610742810416516595059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 956814323747222022126745 717610742810416516595059)
                ·
                  refine ⟨1076416114215624774892589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 717610742810416516595059 1076416114215624774892589)
                  ·
                    refine ⟨403656042830859290584721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1076416114215624774892589 403656042830859290584721)
                    ·
                      refine ⟨302742032123144467938541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 403656042830859290584721 302742032123144467938541)
                      ·
                        rfl

theorem cell23_589588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_589588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_589588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_589588 prefixEnd_589588 := by exact prefixLift 589588
  have htrace : WordTrace (prefixWord ++ tailWord_589588) baseStart_589588 baseEnd_589588 := by
    simpa [prefixWord, tailWord_589588, baseEnd_589588] using wordTrace_append hprefix tailTrace_589588
  have hstable : (prefixWord ++ tailWord_589588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589588).length < 2 ^ (prefixWord ++ tailWord_589588).sum := by decide
  have hdescent : baseEnd_589588 < baseStart_589588 := by decide
  rcases family_descends (prefixWord ++ tailWord_589588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589593 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 3, 7, 2]
def baseStart_589593 : Nat := 118140960795 + 589593 * 2 ^ 59
def prefixEnd_589593 : Nat := 4983230072969 + 3 ^ 40 * 589593 * 2
def baseEnd_589593 : Nat := 302744599526416948376017

theorem tailTrace_589593 : CollatzResearch.WordTrace tailWord_589593 prefixEnd_589593 302744599526416948376017 := by
  unfold tailWord_589593
  simp only [CollatzResearch.WordTrace]
  refine ⟨21504223353012730312813433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14336148902008486875208955 21504223353012730312813433)
  ·
    refine ⟨16128167514759547734610075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21504223353012730312813433 16128167514759547734610075)
    ·
      refine ⟨24192251272139321601915113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16128167514759547734610075 24192251272139321601915113)
      ·
        refine ⟨18144188454104491201436335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24192251272139321601915113 18144188454104491201436335)
        ·
          refine ⟨27216282681156736802154503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18144188454104491201436335 27216282681156736802154503)
          ·
            refine ⟨40824424021735105203231755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27216282681156736802154503 40824424021735105203231755)
            ·
              refine ⟨61236636032602657804847633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40824424021735105203231755 61236636032602657804847633)
              ·
                refine ⟨45927477024451993353635725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61236636032602657804847633 45927477024451993353635725)
                ·
                  refine ⟨17222803884169497507613397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45927477024451993353635725 17222803884169497507613397)
                  ·
                    refine ⟨403659466035222597834689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17222803884169497507613397 403659466035222597834689)
                    ·
                      refine ⟨302744599526416948376017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 403659466035222597834689 302744599526416948376017)
                      ·
                        rfl

theorem cell23_589593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 7, 2].length) (baseStart_589593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_589593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_589593 prefixEnd_589593 := by exact prefixLift 589593
  have htrace : WordTrace (prefixWord ++ tailWord_589593) baseStart_589593 baseEnd_589593 := by
    simpa [prefixWord, tailWord_589593, baseEnd_589593] using wordTrace_append hprefix tailTrace_589593
  have hstable : (prefixWord ++ tailWord_589593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589593).length < 2 ^ (prefixWord ++ tailWord_589593).sum := by decide
  have hdescent : baseEnd_589593 < baseStart_589593 := by decide
  rcases family_descends (prefixWord ++ tailWord_589593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589620 : List Nat := [2, 5, 1, 1, 2, 1, 1, 1, 4, 5]
def baseStart_589620 : Nat := 118140960795 + 589620 * 2 ^ 59
def prefixEnd_589620 : Nat := 4983230072969 + 3 ^ 40 * 589620 * 2
def baseEnd_589620 : Nat := 100919487834696114246131

theorem tailTrace_589620 : CollatzResearch.WordTrace tailWord_589620 prefixEnd_589620 100919487834696114246131 := by
  unfold tailWord_589620
  simp only [CollatzResearch.WordTrace]
  refine ⟨10752604061957456962023157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14336805415943275949364209 10752604061957456962023157)
  ·
    refine ⟨1008056630808511590189671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10752604061957456962023157 1008056630808511590189671)
    ·
      refine ⟨1512084946212767385284507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1008056630808511590189671 1512084946212767385284507)
      ·
        refine ⟨2268127419319151077926761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1512084946212767385284507 2268127419319151077926761)
        ·
          refine ⟨1701095564489363308445071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2268127419319151077926761 1701095564489363308445071)
          ·
            refine ⟨2551643346734044962667607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1701095564489363308445071 2551643346734044962667607)
            ·
              refine ⟨3827465020101067444001411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2551643346734044962667607 3827465020101067444001411)
              ·
                refine ⟨5741197530151601166002117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3827465020101067444001411 5741197530151601166002117)
                ·
                  refine ⟨1076474536903425218625397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5741197530151601166002117 1076474536903425218625397)
                  ·
                    refine ⟨100919487834696114246131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1076474536903425218625397 100919487834696114246131)
                    ·
                      rfl

theorem cell23_589620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_589620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_589620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_589620 prefixEnd_589620 := by exact prefixLift 589620
  have htrace : WordTrace (prefixWord ++ tailWord_589620) baseStart_589620 baseEnd_589620 := by
    simpa [prefixWord, tailWord_589620, baseEnd_589620] using wordTrace_append hprefix tailTrace_589620
  have hstable : (prefixWord ++ tailWord_589620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589620).length < 2 ^ (prefixWord ++ tailWord_589620).sum := by decide
  have hdescent : baseEnd_589620 < baseStart_589620 := by decide
  rcases family_descends (prefixWord ++ tailWord_589620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589630 : List Nat := [4, 2, 1, 2, 2, 2, 1, 1, 1, 2, 5]
def baseStart_589630 : Nat := 118140960795 + 589630 * 2 ^ 59
def prefixEnd_589630 : Nat := 4983230072969 + 3 ^ 40 * 589630 * 2
def baseEnd_589630 : Nat := 302763598310633303613347

theorem tailTrace_589630 : CollatzResearch.WordTrace tailWord_589630 prefixEnd_589630 302763598310633303613347 := by
  unfold tailWord_589630
  simp only [CollatzResearch.WordTrace]
  refine ⟨2688196606734835703988793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14337048569252457087940229 2688196606734835703988793)
  ·
    refine ⟨2016147455051126777991595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2688196606734835703988793 2016147455051126777991595)
    ·
      refine ⟨3024221182576690166987393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2016147455051126777991595 3024221182576690166987393)
      ·
        refine ⟨2268165886932517625240545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3024221182576690166987393 2268165886932517625240545)
        ·
          refine ⟨1701124415199388218930409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2268165886932517625240545 1701124415199388218930409)
          ·
            refine ⟨1275843311399541164197807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1701124415199388218930409 1275843311399541164197807)
            ·
              refine ⟨1913764967099311746296711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1275843311399541164197807 1913764967099311746296711)
              ·
                refine ⟨2870647450648967619445067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1913764967099311746296711 2870647450648967619445067)
                ·
                  refine ⟨4305971175973451429167601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2870647450648967619445067 4305971175973451429167601)
                  ·
                    refine ⟨3229478381980088571875701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4305971175973451429167601 3229478381980088571875701)
                    ·
                      refine ⟨302763598310633303613347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3229478381980088571875701 302763598310633303613347)
                      ·
                        rfl

theorem cell23_589630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_589630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_589630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_589630 prefixEnd_589630 := by exact prefixLift 589630
  have htrace : WordTrace (prefixWord ++ tailWord_589630) baseStart_589630 baseEnd_589630 := by
    simpa [prefixWord, tailWord_589630, baseEnd_589630] using wordTrace_append hprefix tailTrace_589630
  have hstable : (prefixWord ++ tailWord_589630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589630).length < 2 ^ (prefixWord ++ tailWord_589630).sum := by decide
  have hdescent : baseEnd_589630 < baseStart_589630 := by decide
  rcases family_descends (prefixWord ++ tailWord_589630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589727 : List Nat := [1, 1, 2, 5, 3, 1, 1, 3, 1, 5]
def baseStart_589727 : Nat := 118140960795 + 589727 * 2 ^ 59
def prefixEnd_589727 : Nat := 4983230072969 + 3 ^ 40 * 589727 * 2
def baseEnd_589727 : Nat := 100937801978039808033467

theorem tailTrace_589727 : CollatzResearch.WordTrace tailWord_589727 prefixEnd_589727 100937801978039808033467 := by
  unfold tailWord_589727
  simp only [CollatzResearch.WordTrace]
  refine ⟨21509110734527271198191435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14339407156351514132127623 21509110734527271198191435)
  ·
    refine ⟨32263666101790906797287153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21509110734527271198191435 32263666101790906797287153)
    ·
      refine ⟨24197749576343180097965365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32263666101790906797287153 24197749576343180097965365)
      ·
        refine ⟨2268539022782173134184253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24197749576343180097965365 2268539022782173134184253)
        ·
          refine ⟨850702133543314925319095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2268539022782173134184253 850702133543314925319095)
          ·
            refine ⟨1276053200314972387978643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 850702133543314925319095 1276053200314972387978643)
            ·
              refine ⟨1914079800472458581967965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1276053200314972387978643 1914079800472458581967965)
              ·
                refine ⟨717779925177171968237987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1914079800472458581967965 717779925177171968237987)
                ·
                  refine ⟨1076669887765757952356981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 717779925177171968237987 1076669887765757952356981)
                  ·
                    refine ⟨100937801978039808033467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1076669887765757952356981 100937801978039808033467)
                    ·
                      rfl

theorem cell23_589727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 3, 1, 5].length) (baseStart_589727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_589727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_589727 prefixEnd_589727 := by exact prefixLift 589727
  have htrace : WordTrace (prefixWord ++ tailWord_589727) baseStart_589727 baseEnd_589727 := by
    simpa [prefixWord, tailWord_589727, baseEnd_589727] using wordTrace_append hprefix tailTrace_589727
  have hstable : (prefixWord ++ tailWord_589727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589727).length < 2 ^ (prefixWord ++ tailWord_589727).sum := by decide
  have hdescent : baseEnd_589727 < baseStart_589727 := by decide
  rcases family_descends (prefixWord ++ tailWord_589727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589733 : List Nat := [1, 3, 1, 2, 1, 1, 1, 2, 5, 1, 5]
def baseStart_589733 : Nat := 118140960795 + 589733 * 2 ^ 59
def prefixEnd_589733 : Nat := 4983230072969 + 3 ^ 40 * 589733 * 2
def baseEnd_589733 : Nat := 302816486818046400625373

theorem tailTrace_589733 : CollatzResearch.WordTrace tailWord_589733 prefixEnd_589733 302816486818046400625373 := by
  unfold tailWord_589733
  simp only [CollatzResearch.WordTrace]
  refine ⟨21509329572505534222909853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14339553048337022815273235 21509329572505534222909853)
  ·
    refine ⟨8065998589689575333591195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21509329572505534222909853 8065998589689575333591195)
    ·
      refine ⟨12098997884534363000386793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8065998589689575333591195 12098997884534363000386793)
      ·
        refine ⟨9074248413400772250290095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12098997884534363000386793 9074248413400772250290095)
        ·
          refine ⟨13611372620101158375435143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9074248413400772250290095 13611372620101158375435143)
          ·
            refine ⟨20417058930151737563152715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13611372620101158375435143 20417058930151737563152715)
            ·
              refine ⟨30625588395227606344729073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20417058930151737563152715 30625588395227606344729073)
              ·
                refine ⟨22969191296420704758546805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30625588395227606344729073 22969191296420704758546805)
                ·
                  refine ⟨2153361684039441071113763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22969191296420704758546805 2153361684039441071113763)
                  ·
                    refine ⟨3230042526059161606670645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2153361684039441071113763 3230042526059161606670645)
                    ·
                      refine ⟨302816486818046400625373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3230042526059161606670645 302816486818046400625373)
                      ·
                        rfl

theorem cell23_589733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 5, 1, 5].length) (baseStart_589733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_589733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_589733 prefixEnd_589733 := by exact prefixLift 589733
  have htrace : WordTrace (prefixWord ++ tailWord_589733) baseStart_589733 baseEnd_589733 := by
    simpa [prefixWord, tailWord_589733, baseEnd_589733] using wordTrace_append hprefix tailTrace_589733
  have hstable : (prefixWord ++ tailWord_589733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589733).length < 2 ^ (prefixWord ++ tailWord_589733).sum := by decide
  have hdescent : baseEnd_589733 < baseStart_589733 := by decide
  rcases family_descends (prefixWord ++ tailWord_589733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589743 : List Nat := [1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 6]
def baseStart_589743 : Nat := 118140960795 + 589743 * 2 ^ 59
def prefixEnd_589743 : Nat := 4983230072969 + 3 ^ 40 * 589743 * 2
def baseEnd_589743 : Nat := 302821621624591361500327

theorem tailTrace_589743 : CollatzResearch.WordTrace tailWord_589743 prefixEnd_589743 302821621624591361500327 := by
  unfold tailWord_589743
  simp only [CollatzResearch.WordTrace]
  refine ⟨21509694302469305930773883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14339796201646203953849255 21509694302469305930773883)
  ·
    refine ⟨32264541453703958896160825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21509694302469305930773883 32264541453703958896160825)
    ·
      refine ⟨24198406090277969172120619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32264541453703958896160825 24198406090277969172120619)
      ·
        refine ⟨36297609135416953758180929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24198406090277969172120619 36297609135416953758180929)
        ·
          refine ⟨27223206851562715318635697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36297609135416953758180929 27223206851562715318635697)
          ·
            refine ⟨20417405138672036488976773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27223206851562715318635697 20417405138672036488976773)
            ·
              refine ⟨3828263463501006841683145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20417405138672036488976773 3828263463501006841683145)
              ·
                refine ⟨2871197597625755131262359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3828263463501006841683145 2871197597625755131262359)
                ·
                  refine ⟨4306796396438632696893539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2871197597625755131262359 4306796396438632696893539)
                  ·
                    refine ⟨6460194594657949045340309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4306796396438632696893539 6460194594657949045340309)
                    ·
                      refine ⟨302821621624591361500327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6460194594657949045340309 302821621624591361500327)
                      ·
                        rfl

theorem cell23_589743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 6].length) (baseStart_589743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_589743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_589743 prefixEnd_589743 := by exact prefixLift 589743
  have htrace : WordTrace (prefixWord ++ tailWord_589743) baseStart_589743 baseEnd_589743 := by
    simpa [prefixWord, tailWord_589743, baseEnd_589743] using wordTrace_append hprefix tailTrace_589743
  have hstable : (prefixWord ++ tailWord_589743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589743).length < 2 ^ (prefixWord ++ tailWord_589743).sum := by decide
  have hdescent : baseEnd_589743 < baseStart_589743 := by decide
  rcases family_descends (prefixWord ++ tailWord_589743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589753 : List Nat := [1, 2, 1, 4, 2, 1, 2, 10]
def baseStart_589753 : Nat := 118140960795 + 589753 * 2 ^ 59
def prefixEnd_589753 : Nat := 4983230072969 + 3 ^ 40 * 589753 * 2
def baseEnd_589753 : Nat := 11215805793745789717603

theorem tailTrace_589753 : CollatzResearch.WordTrace tailWord_589753 prefixEnd_589753 11215805793745789717603 := by
  unfold tailWord_589753
  simp only [CollatzResearch.WordTrace]
  refine ⟨21510059032433077638637913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14340039354955385092425275 21510059032433077638637913)
  ·
    refine ⟨16132544274324808228978435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21510059032433077638637913 16132544274324808228978435)
    ·
      refine ⟨24198816411487212343467653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16132544274324808228978435 24198816411487212343467653)
      ·
        refine ⟨4537278077153852314400185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24198816411487212343467653 4537278077153852314400185)
        ·
          refine ⟨3402958557865389235800139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4537278077153852314400185 3402958557865389235800139)
          ·
            refine ⟨5104437836798083853700209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3402958557865389235800139 5104437836798083853700209)
            ·
              refine ⟨3828328377598562890275157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5104437836798083853700209 3828328377598562890275157)
              ·
                refine ⟨11215805793745789717603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 3828328377598562890275157 11215805793745789717603)
                ·
                  rfl

theorem cell23_589753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 10].length) (baseStart_589753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_589753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_589753 prefixEnd_589753 := by exact prefixLift 589753
  have htrace : WordTrace (prefixWord ++ tailWord_589753) baseStart_589753 baseEnd_589753 := by
    simpa [prefixWord, tailWord_589753, baseEnd_589753] using wordTrace_append hprefix tailTrace_589753
  have hstable : (prefixWord ++ tailWord_589753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589753).length < 2 ^ (prefixWord ++ tailWord_589753).sum := by decide
  have hdescent : baseEnd_589753 < baseStart_589753 := by decide
  rcases family_descends (prefixWord ++ tailWord_589753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589757 : List Nat := [1, 4, 1, 2, 3, 3, 1, 1, 1, 6]
def baseStart_589757 : Nat := 118140960795 + 589757 * 2 ^ 59
def prefixEnd_589757 : Nat := 4983230072969 + 3 ^ 40 * 589757 * 2
def baseEnd_589757 : Nat := 100942936784584768908421

theorem tailTrace_589757 : CollatzResearch.WordTrace tailWord_589757 prefixEnd_589757 100942936784584768908421 := by
  unfold tailWord_589757
  simp only [CollatzResearch.WordTrace]
  refine ⟨21510204924418586321783525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14340136616279057547855683 21510204924418586321783525)
  ·
    refine ⟨4033163423328484935334411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21510204924418586321783525 4033163423328484935334411)
    ·
      refine ⟨6049745134992727403001617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4033163423328484935334411 6049745134992727403001617)
      ·
        refine ⟨4537308851244545552251213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6049745134992727403001617 4537308851244545552251213)
        ·
          refine ⟨1701490819216704582094205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4537308851244545552251213 1701490819216704582094205)
          ·
            refine ⟨638059057206264218285327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1701490819216704582094205 638059057206264218285327)
            ·
              refine ⟨957088585809396327427991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 638059057206264218285327 957088585809396327427991)
              ·
                refine ⟨1435632878714094491141987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 957088585809396327427991 1435632878714094491141987)
                ·
                  refine ⟨2153449318071141736712981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1435632878714094491141987 2153449318071141736712981)
                  ·
                    refine ⟨100942936784584768908421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2153449318071141736712981 100942936784584768908421)
                    ·
                      rfl

theorem cell23_589757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 1, 1, 6].length) (baseStart_589757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_589757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_589757 prefixEnd_589757 := by exact prefixLift 589757
  have htrace : WordTrace (prefixWord ++ tailWord_589757) baseStart_589757 baseEnd_589757 := by
    simpa [prefixWord, tailWord_589757, baseEnd_589757] using wordTrace_append hprefix tailTrace_589757
  have hstable : (prefixWord ++ tailWord_589757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589757).length < 2 ^ (prefixWord ++ tailWord_589757).sum := by decide
  have hdescent : baseEnd_589757 < baseStart_589757 := by decide
  rcases family_descends (prefixWord ++ tailWord_589757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589770 : List Nat := [3, 1, 2, 1, 2, 1, 6, 7]
def baseStart_589770 : Nat := 118140960795 + 589770 * 2 ^ 59
def prefixEnd_589770 : Nat := 4983230072969 + 3 ^ 40 * 589770 * 2
def baseEnd_589770 : Nat := 11216129096380102068989

theorem tailTrace_589770 : CollatzResearch.WordTrace tailWord_589770 prefixEnd_589770 11216129096380102068989 := by
  unfold tailWord_589770
  simp only [CollatzResearch.WordTrace]
  refine ⟨5377669768342872385501691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14340452715580993028004509 5377669768342872385501691)
  ·
    refine ⟨8066504652514308578252537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5377669768342872385501691 8066504652514308578252537)
    ·
      refine ⟨6049878489385731433689403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8066504652514308578252537 6049878489385731433689403)
      ·
        refine ⟨9074817734078597150534105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6049878489385731433689403 9074817734078597150534105)
        ·
          refine ⟨6806113300558947862900579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9074817734078597150534105 6806113300558947862900579)
          ·
            refine ⟨10209169950838421794350869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6806113300558947862900579 10209169950838421794350869)
            ·
              refine ⟨478554841445551021610197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10209169950838421794350869 478554841445551021610197)
              ·
                refine ⟨11216129096380102068989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 478554841445551021610197 11216129096380102068989)
                ·
                  rfl

theorem cell23_589770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 6, 7].length) (baseStart_589770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_589770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_589770 prefixEnd_589770 := by exact prefixLift 589770
  have htrace : WordTrace (prefixWord ++ tailWord_589770) baseStart_589770 baseEnd_589770 := by
    simpa [prefixWord, tailWord_589770, baseEnd_589770] using wordTrace_append hprefix tailTrace_589770
  have hstable : (prefixWord ++ tailWord_589770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589770).length < 2 ^ (prefixWord ++ tailWord_589770).sum := by decide
  have hdescent : baseEnd_589770 < baseStart_589770 := by decide
  rcases family_descends (prefixWord ++ tailWord_589770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589807 : List Nat := [1, 1, 2, 1, 4, 2, 2, 2, 3, 3, 2]
def baseStart_589807 : Nat := 118140960795 + 589807 * 2 ^ 59
def prefixEnd_589807 : Nat := 4983230072969 + 3 ^ 40 * 589807 * 2
def baseEnd_589807 : Nat := 302854484386479111100033

theorem tailTrace_589807 : CollatzResearch.WordTrace tailWord_589807 prefixEnd_589807 302854484386479111100033 := by
  unfold tailWord_589807
  simp only [CollatzResearch.WordTrace]
  refine ⟨21512028574237444861103675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14341352382824963240735783 21512028574237444861103675)
  ·
    refine ⟨32268042861356167291655513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21512028574237444861103675 32268042861356167291655513)
    ·
      refine ⟨24201032146017125468741635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32268042861356167291655513 24201032146017125468741635)
      ·
        refine ⟨36301548219025688203112453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24201032146017125468741635 36301548219025688203112453)
        ·
          refine ⟨6806540291067316538083585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36301548219025688203112453 6806540291067316538083585)
          ·
            refine ⟨5104905218300487403562689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6806540291067316538083585 5104905218300487403562689)
            ·
              refine ⟨3828678913725365552672017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5104905218300487403562689 3828678913725365552672017)
              ·
                refine ⟨2871509185294024164504013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3828678913725365552672017 2871509185294024164504013)
                ·
                  refine ⟨1076815944485259061689005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2871509185294024164504013 1076815944485259061689005)
                  ·
                    refine ⟨403805979181972148133377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1076815944485259061689005 403805979181972148133377)
                    ·
                      refine ⟨302854484386479111100033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 403805979181972148133377 302854484386479111100033)
                      ·
                        rfl

theorem cell23_589807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 3, 3, 2].length) (baseStart_589807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_589807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_589807 prefixEnd_589807 := by exact prefixLift 589807
  have htrace : WordTrace (prefixWord ++ tailWord_589807) baseStart_589807 baseEnd_589807 := by
    simpa [prefixWord, tailWord_589807, baseEnd_589807] using wordTrace_append hprefix tailTrace_589807
  have hstable : (prefixWord ++ tailWord_589807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589807).length < 2 ^ (prefixWord ++ tailWord_589807).sum := by decide
  have hdescent : baseEnd_589807 < baseStart_589807 := by decide
  rcases family_descends (prefixWord ++ tailWord_589807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589864 : List Nat := [2, 1, 5, 3, 1, 1, 1, 1, 2, 6]
def baseStart_589864 : Nat := 118140960795 + 589864 * 2 ^ 59
def prefixEnd_589864 : Nat := 4983230072969 + 3 ^ 40 * 589864 * 2
def baseEnd_589864 : Nat := 100961250927928462695757

theorem tailTrace_589864 : CollatzResearch.WordTrace tailWord_589864 prefixEnd_589864 100961250927928462695757 := by
  unfold tailWord_589864
  simp only [CollatzResearch.WordTrace]
  refine ⟨10757053767515471797964323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14342738356687295730619097 10757053767515471797964323)
  ·
    refine ⟨16135580651273207696946485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10757053767515471797964323 16135580651273207696946485)
    ·
      refine ⟨1512710686056863221588733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16135580651273207696946485 1512710686056863221588733)
      ·
        refine ⟨567266507271323708095775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1512710686056863221588733 567266507271323708095775)
        ·
          refine ⟨850899760906985562143663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 567266507271323708095775 850899760906985562143663)
          ·
            refine ⟨1276349641360478343215495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 850899760906985562143663 1276349641360478343215495)
            ·
              refine ⟨1914524462040717514823243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1276349641360478343215495 1914524462040717514823243)
              ·
                refine ⟨2871786693061076272234865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1914524462040717514823243 2871786693061076272234865)
                ·
                  refine ⟨2153840019795807204176149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2871786693061076272234865 2153840019795807204176149)
                  ·
                    refine ⟨100961250927928462695757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2153840019795807204176149 100961250927928462695757)
                    ·
                      rfl

theorem cell23_589864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_589864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_589864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_589864 prefixEnd_589864 := by exact prefixLift 589864
  have htrace : WordTrace (prefixWord ++ tailWord_589864) baseStart_589864 baseEnd_589864 := by
    simpa [prefixWord, tailWord_589864, baseEnd_589864] using wordTrace_append hprefix tailTrace_589864
  have hstable : (prefixWord ++ tailWord_589864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589864).length < 2 ^ (prefixWord ++ tailWord_589864).sum := by decide
  have hdescent : baseEnd_589864 < baseStart_589864 := by decide
  rcases family_descends (prefixWord ++ tailWord_589864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589900 : List Nat := [2, 2, 1, 3, 1, 1, 2, 1, 3, 2, 5]
def baseStart_589900 : Nat := 118140960795 + 589900 * 2 ^ 59
def prefixEnd_589900 : Nat := 4983230072969 + 3 ^ 40 * 589900 * 2
def baseEnd_589900 : Nat := 302902238087347247237105

theorem tailTrace_589900 : CollatzResearch.WordTrace tailWord_589900 prefixEnd_589900 302902238087347247237105 := by
  unfold tailWord_589900
  simp only [CollatzResearch.WordTrace]
  refine ⟨10757710281450260872119577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14343613708600347829492769 10757710281450260872119577)
  ·
    refine ⟨8068282711087695654089683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10757710281450260872119577 8068282711087695654089683)
    ·
      refine ⟨12102424066631543481134525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8068282711087695654089683 12102424066631543481134525)
      ·
        refine ⟨4538409024986828805425447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12102424066631543481134525 4538409024986828805425447)
        ·
          refine ⟨6807613537480243208138171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4538409024986828805425447 6807613537480243208138171)
          ·
            refine ⟨10211420306220364812207257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6807613537480243208138171 10211420306220364812207257)
            ·
              refine ⟨7658565229665273609155443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10211420306220364812207257 7658565229665273609155443)
              ·
                refine ⟨11487847844497910413733165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7658565229665273609155443 11487847844497910413733165)
                ·
                  refine ⟨4307942941686716405149937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11487847844497910413733165 4307942941686716405149937)
                  ·
                    refine ⟨3230957206265037303862453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4307942941686716405149937 3230957206265037303862453)
                    ·
                      refine ⟨302902238087347247237105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3230957206265037303862453 302902238087347247237105)
                      ·
                        rfl

theorem cell23_589900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_589900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_589900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_589900 prefixEnd_589900 := by exact prefixLift 589900
  have htrace : WordTrace (prefixWord ++ tailWord_589900) baseStart_589900 baseEnd_589900 := by
    simpa [prefixWord, tailWord_589900, baseEnd_589900] using wordTrace_append hprefix tailTrace_589900
  have hstable : (prefixWord ++ tailWord_589900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589900).length < 2 ^ (prefixWord ++ tailWord_589900).sum := by decide
  have hdescent : baseEnd_589900 < baseStart_589900 := by decide
  rcases family_descends (prefixWord ++ tailWord_589900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589937 : List Nat := [1, 2, 2, 2, 1, 1, 3, 4, 3, 4]
def baseStart_589937 : Nat := 118140960795 + 589937 * 2 ^ 59
def prefixEnd_589937 : Nat := 4983230072969 + 3 ^ 40 * 589937 * 2
def baseEnd_589937 : Nat := 100973745623854534158145

theorem tailTrace_589937 : CollatzResearch.WordTrace tailWord_589937 prefixEnd_589937 100973745623854534158145 := by
  unfold tailWord_589937
  simp only [CollatzResearch.WordTrace]
  refine ⟨21516770063766477063336065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14344513375844318042224043 21516770063766477063336065)
  ·
    refine ⟨16137577547824857797502049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21516770063766477063336065 16137577547824857797502049)
    ·
      refine ⟨12103183160868643348126537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16137577547824857797502049 12103183160868643348126537)
      ·
        refine ⟨9077387370651482511094903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12103183160868643348126537 9077387370651482511094903)
        ·
          refine ⟨13616081055977223766642355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9077387370651482511094903 13616081055977223766642355)
          ·
            refine ⟨20424121583965835649963533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13616081055977223766642355 20424121583965835649963533)
            ·
              refine ⟨7659045593987188368736325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20424121583965835649963533 7659045593987188368736325)
              ·
                refine ⟨1436071048872597819138061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7659045593987188368736325 1436071048872597819138061)
                ·
                  refine ⟨538526643327224182176773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1436071048872597819138061 538526643327224182176773)
                  ·
                    refine ⟨100973745623854534158145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 538526643327224182176773 100973745623854534158145)
                    ·
                      rfl

theorem cell23_589937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 4, 3, 4].length) (baseStart_589937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_589937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_589937 prefixEnd_589937 := by exact prefixLift 589937
  have htrace : WordTrace (prefixWord ++ tailWord_589937) baseStart_589937 baseEnd_589937 := by
    simpa [prefixWord, tailWord_589937, baseEnd_589937] using wordTrace_append hprefix tailTrace_589937
  have hstable : (prefixWord ++ tailWord_589937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589937).length < 2 ^ (prefixWord ++ tailWord_589937).sum := by decide
  have hdescent : baseEnd_589937 < baseStart_589937 := by decide
  rcases family_descends (prefixWord ++ tailWord_589937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589984 : List Nat := [2, 1, 1, 4, 2, 2, 4, 1, 6]
def baseStart_589984 : Nat := 118140960795 + 589984 * 2 ^ 59
def prefixEnd_589984 : Nat := 4983230072969 + 3 ^ 40 * 589984 * 2
def baseEnd_589984 : Nat := 33660596718036102065191

theorem tailTrace_589984 : CollatzResearch.WordTrace tailWord_589984 prefixEnd_589984 33660596718036102065191 := by
  unfold tailWord_589984
  simp only [CollatzResearch.WordTrace]
  refine ⟨10759242147298102045148503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14345656196397469393531337 10759242147298102045148503)
  ·
    refine ⟨16138863220947153067722755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10759242147298102045148503 16138863220947153067722755)
    ·
      refine ⟨24208294831420729601584133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16138863220947153067722755 24208294831420729601584133)
      ·
        refine ⟨4539055280891386800297025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24208294831420729601584133 4539055280891386800297025)
        ·
          refine ⟨3404291460668540100222769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4539055280891386800297025 3404291460668540100222769)
          ·
            refine ⟨2553218595501405075167077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3404291460668540100222769 2553218595501405075167077)
            ·
              refine ⟨478728486656513451593827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2553218595501405075167077 478728486656513451593827)
              ·
                refine ⟨718092729984770177390741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 478728486656513451593827 718092729984770177390741)
                ·
                  refine ⟨33660596718036102065191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 718092729984770177390741 33660596718036102065191)
                  ·
                    rfl

theorem cell23_589984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 4, 1, 6].length) (baseStart_589984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_589984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_589984 prefixEnd_589984 := by exact prefixLift 589984
  have htrace : WordTrace (prefixWord ++ tailWord_589984) baseStart_589984 baseEnd_589984 := by
    simpa [prefixWord, tailWord_589984, baseEnd_589984] using wordTrace_append hprefix tailTrace_589984
  have hstable : (prefixWord ++ tailWord_589984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589984).length < 2 ^ (prefixWord ++ tailWord_589984).sum := by decide
  have hdescent : baseEnd_589984 < baseStart_589984 := by decide
  rcases family_descends (prefixWord ++ tailWord_589984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590011 : List Nat := [1, 1, 1, 1, 1, 2, 6, 5, 1, 1, 3]
def baseStart_590011 : Nat := 118140960795 + 590011 * 2 ^ 59
def prefixEnd_590011 : Nat := 4983230072969 + 3 ^ 40 * 590011 * 2
def baseEnd_590011 : Nat := 302959234439996312949095

theorem tailTrace_590011 : CollatzResearch.WordTrace tailWord_590011 prefixEnd_590011 302959234439996312949095 := by
  unfold tailWord_590011
  simp only [CollatzResearch.WordTrace]
  refine ⟨21519469065498387701529887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14346312710332258467686591 21519469065498387701529887)
  ·
    refine ⟨32279203598247581552294831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21519469065498387701529887 32279203598247581552294831)
    ·
      refine ⟨48418805397371372328442247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32279203598247581552294831 48418805397371372328442247)
      ·
        refine ⟨72628208096057058492663371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48418805397371372328442247 72628208096057058492663371)
        ·
          refine ⟨108942312144085587738995057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72628208096057058492663371 108942312144085587738995057)
          ·
            refine ⟨81706734108064190804246293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108942312144085587738995057 81706734108064190804246293)
            ·
              refine ⟨3830003161315508943949045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 81706734108064190804246293 3830003161315508943949045)
              ·
                refine ⟨359062796373328963495223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3830003161315508943949045 359062796373328963495223)
                ·
                  refine ⟨538594194559993445242835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 359062796373328963495223 538594194559993445242835)
                  ·
                    refine ⟨807891291839990167864253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 538594194559993445242835 807891291839990167864253)
                    ·
                      refine ⟨302959234439996312949095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 807891291839990167864253 302959234439996312949095)
                      ·
                        rfl

theorem cell23_590011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 5, 1, 1, 3].length) (baseStart_590011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_590011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_590011 prefixEnd_590011 := by exact prefixLift 590011
  have htrace : WordTrace (prefixWord ++ tailWord_590011) baseStart_590011 baseEnd_590011 := by
    simpa [prefixWord, tailWord_590011, baseEnd_590011] using wordTrace_append hprefix tailTrace_590011
  have hstable : (prefixWord ++ tailWord_590011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590011).length < 2 ^ (prefixWord ++ tailWord_590011).sum := by decide
  have hdescent : baseEnd_590011 < baseStart_590011 := by decide
  rcases family_descends (prefixWord ++ tailWord_590011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590018 : List Nat := [3, 5, 1, 1, 1, 2, 2, 2, 6]
def baseStart_590018 : Nat := 118140960795 + 590018 * 2 ^ 59
def prefixEnd_590018 : Nat := 4983230072969 + 3 ^ 40 * 590018 * 2
def baseEnd_590018 : Nat := 33662536533841976173507

theorem tailTrace_590018 : CollatzResearch.WordTrace tailWord_590018 prefixEnd_590018 33662536533841976173507 := by
  unfold tailWord_590018
  simp only [CollatzResearch.WordTrace]
  refine ⟨5379931094118256974258677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14346482917648685264689805 5379931094118256974258677)
  ·
    refine ⟨504368540073586591336751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5379931094118256974258677 504368540073586591336751)
    ·
      refine ⟨756552810110379887005127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 504368540073586591336751 756552810110379887005127)
      ·
        refine ⟨1134829215165569830507691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 756552810110379887005127 1134829215165569830507691)
        ·
          refine ⟨1702243822748354745761537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1134829215165569830507691 1702243822748354745761537)
          ·
            refine ⟨1276682867061266059321153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1702243822748354745761537 1276682867061266059321153)
            ·
              refine ⟨957512150295949544490865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1276682867061266059321153 957512150295949544490865)
              ·
                refine ⟨718134112721962158368149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 957512150295949544490865 718134112721962158368149)
                ·
                  refine ⟨33662536533841976173507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 718134112721962158368149 33662536533841976173507)
                  ·
                    rfl

theorem cell23_590018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_590018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_590018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_590018 prefixEnd_590018 := by exact prefixLift 590018
  have htrace : WordTrace (prefixWord ++ tailWord_590018) baseStart_590018 baseEnd_590018 := by
    simpa [prefixWord, tailWord_590018, baseEnd_590018] using wordTrace_append hprefix tailTrace_590018
  have hstable : (prefixWord ++ tailWord_590018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590018).length < 2 ^ (prefixWord ++ tailWord_590018).sum := by decide
  have hdescent : baseEnd_590018 < baseStart_590018 := by decide
  rcases family_descends (prefixWord ++ tailWord_590018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590034 : List Nat := [3, 2, 2, 2, 1, 2, 1, 2, 3, 1, 4]
def baseStart_590034 : Nat := 118140960795 + 590034 * 2 ^ 59
def prefixEnd_590034 : Nat := 4983230072969 + 3 ^ 40 * 590034 * 2
def baseEnd_590034 : Nat := 302971044495049722961489

theorem tailTrace_590034 : CollatzResearch.WordTrace tailWord_590034 prefixEnd_590034 302971044495049722961489 := by
  unfold tailWord_590034
  simp only [CollatzResearch.WordTrace]
  refine ⟨5380076986103765657404289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14346871962943375086411437 5380076986103765657404289)
  ·
    refine ⟨4035057739577824243053217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5380076986103765657404289 4035057739577824243053217)
    ·
      refine ⟨3026293304683368182289913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4035057739577824243053217 3026293304683368182289913)
      ·
        refine ⟨2269719978512526136717435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3026293304683368182289913 2269719978512526136717435)
        ·
          refine ⟨3404579967768789205076153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2269719978512526136717435 3404579967768789205076153)
          ·
            refine ⟨2553434975826591903807115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3404579967768789205076153 2553434975826591903807115)
            ·
              refine ⟨3830152463739887855710673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2553434975826591903807115 3830152463739887855710673)
              ·
                refine ⟨2872614347804915891783005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3830152463739887855710673 2872614347804915891783005)
                ·
                  refine ⟨1077230380426843459418627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2872614347804915891783005 1077230380426843459418627)
                  ·
                    refine ⟨1615845570640265189127941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1077230380426843459418627 1615845570640265189127941)
                    ·
                      refine ⟨302971044495049722961489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1615845570640265189127941 302971044495049722961489)
                      ·
                        rfl

theorem cell23_590034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_590034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_590034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_590034 prefixEnd_590034 := by exact prefixLift 590034
  have htrace : WordTrace (prefixWord ++ tailWord_590034) baseStart_590034 baseEnd_590034 := by
    simpa [prefixWord, tailWord_590034, baseEnd_590034] using wordTrace_append hprefix tailTrace_590034
  have hstable : (prefixWord ++ tailWord_590034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590034).length < 2 ^ (prefixWord ++ tailWord_590034).sum := by decide
  have hdescent : baseEnd_590034 < baseStart_590034 := by decide
  rcases family_descends (prefixWord ++ tailWord_590034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590101 : List Nat := [1, 3, 2, 1, 2, 1, 2, 5, 2, 1, 3]
def baseStart_590101 : Nat := 118140960795 + 590101 * 2 ^ 59
def prefixEnd_590101 : Nat := 4983230072969 + 3 ^ 40 * 590101 * 2
def baseEnd_590101 : Nat := 303005447698900960823681

theorem tailTrace_590101 : CollatzResearch.WordTrace tailWord_590101 prefixEnd_590101 303005447698900960823681 := by
  unfold tailWord_590101
  simp only [CollatzResearch.WordTrace]
  refine ⟨21522751635172333072306157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14348501090114888714870771 21522751635172333072306157)
  ·
    refine ⟨8071031863189624902114809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21522751635172333072306157 8071031863189624902114809)
    ·
      refine ⟨6053273897392218676586107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8071031863189624902114809 6053273897392218676586107)
      ·
        refine ⟨9079910846088328014879161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6053273897392218676586107 9079910846088328014879161)
        ·
          refine ⟨6809933134566246011159371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9079910846088328014879161 6809933134566246011159371)
          ·
            refine ⟨10214899701849369016739057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6809933134566246011159371 10214899701849369016739057)
            ·
              refine ⟨7661174776387026762554293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10214899701849369016739057 7661174776387026762554293)
              ·
                refine ⟨718235135286283758989465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7661174776387026762554293 718235135286283758989465)
                ·
                  refine ⟨538676351464712819242099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 718235135286283758989465 538676351464712819242099)
                  ·
                    refine ⟨808014527197069228863149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 538676351464712819242099 808014527197069228863149)
                    ·
                      refine ⟨303005447698900960823681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 808014527197069228863149 303005447698900960823681)
                      ·
                        rfl

theorem cell23_590101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 5, 2, 1, 3].length) (baseStart_590101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_590101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_590101 prefixEnd_590101 := by exact prefixLift 590101
  have htrace : WordTrace (prefixWord ++ tailWord_590101) baseStart_590101 baseEnd_590101 := by
    simpa [prefixWord, tailWord_590101, baseEnd_590101] using wordTrace_append hprefix tailTrace_590101
  have hstable : (prefixWord ++ tailWord_590101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590101).length < 2 ^ (prefixWord ++ tailWord_590101).sum := by decide
  have hdescent : baseEnd_590101 < baseStart_590101 := by decide
  rcases family_descends (prefixWord ++ tailWord_590101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590107 : List Nat := [1, 1, 1, 1, 1, 1, 6, 2, 2, 3, 4]
def baseStart_590107 : Nat := 118140960795 + 590107 * 2 ^ 59
def prefixEnd_590107 : Nat := 4983230072969 + 3 ^ 40 * 590107 * 2
def baseEnd_590107 : Nat := 303008528582827937348653

theorem tailTrace_590107 : CollatzResearch.WordTrace tailWord_590107 prefixEnd_590107 303008528582827937348653 := by
  unfold tailWord_590107
  simp only [CollatzResearch.WordTrace]
  refine ⟨21522970473150596097024575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14348646982100397398016383 21522970473150596097024575)
  ·
    refine ⟨32284455709725894145536863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21522970473150596097024575 32284455709725894145536863)
    ·
      refine ⟨48426683564588841218305295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32284455709725894145536863 48426683564588841218305295)
      ·
        refine ⟨72640025346883261827457943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48426683564588841218305295 72640025346883261827457943)
        ·
          refine ⟨108960038020324892741186915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72640025346883261827457943 108960038020324892741186915)
          ·
            refine ⟨163440057030487339111780373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108960038020324892741186915 163440057030487339111780373)
            ·
              refine ⟨7661252673304094020864705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 163440057030487339111780373 7661252673304094020864705)
              ·
                refine ⟨5745939504978070515648529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7661252673304094020864705 5745939504978070515648529)
                ·
                  refine ⟨4309454628733552886736397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5745939504978070515648529 4309454628733552886736397)
                  ·
                    refine ⟨1616045485775082332526149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4309454628733552886736397 1616045485775082332526149)
                    ·
                      refine ⟨303008528582827937348653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1616045485775082332526149 303008528582827937348653)
                      ·
                        rfl

theorem cell23_590107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 3, 4].length) (baseStart_590107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_590107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_590107 prefixEnd_590107 := by exact prefixLift 590107
  have htrace : WordTrace (prefixWord ++ tailWord_590107) baseStart_590107 baseEnd_590107 := by
    simpa [prefixWord, tailWord_590107, baseEnd_590107] using wordTrace_append hprefix tailTrace_590107
  have hstable : (prefixWord ++ tailWord_590107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590107).length < 2 ^ (prefixWord ++ tailWord_590107).sum := by decide
  have hdescent : baseEnd_590107 < baseStart_590107 := by decide
  rcases family_descends (prefixWord ++ tailWord_590107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590114 : List Nat := [3, 3, 1, 1, 3, 1, 1, 1, 2, 2, 5]
def baseStart_590114 : Nat := 118140960795 + 590114 * 2 ^ 59
def prefixEnd_590114 : Nat := 4983230072969 + 3 ^ 40 * 590114 * 2
def baseEnd_590114 : Nat := 303012122947409409961121

theorem tailTrace_590114 : CollatzResearch.WordTrace tailWord_590114 prefixEnd_590114 303012122947409409961121 := by
  unfold tailWord_590114
  simp only [CollatzResearch.WordTrace]
  refine ⟨5380806446031309073132349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14348817189416824195019597 5380806446031309073132349)
  ·
    refine ⟨2017802417261740902424631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5380806446031309073132349 2017802417261740902424631)
    ·
      refine ⟨3026703625892611353636947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2017802417261740902424631 3026703625892611353636947)
      ·
        refine ⟨4540055438838917030455421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3026703625892611353636947 4540055438838917030455421)
        ·
          refine ⟨1702520789564593886420783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4540055438838917030455421 1702520789564593886420783)
          ·
            refine ⟨2553781184346890829631175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1702520789564593886420783 2553781184346890829631175)
            ·
              refine ⟨3830671776520336244446763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2553781184346890829631175 3830671776520336244446763)
              ·
                refine ⟨5746007664780504366670145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3830671776520336244446763 5746007664780504366670145)
                ·
                  refine ⟨4309505748585378275002609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5746007664780504366670145 4309505748585378275002609)
                  ·
                    refine ⟨3232129311439033706251957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4309505748585378275002609 3232129311439033706251957)
                    ·
                      refine ⟨303012122947409409961121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3232129311439033706251957 303012122947409409961121)
                      ·
                        rfl

theorem cell23_590114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_590114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_590114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_590114 prefixEnd_590114 := by exact prefixLift 590114
  have htrace : WordTrace (prefixWord ++ tailWord_590114) baseStart_590114 baseEnd_590114 := by
    simpa [prefixWord, tailWord_590114, baseEnd_590114] using wordTrace_append hprefix tailTrace_590114
  have hstable : (prefixWord ++ tailWord_590114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590114).length < 2 ^ (prefixWord ++ tailWord_590114).sum := by decide
  have hdescent : baseEnd_590114 < baseStart_590114 := by decide
  rcases family_descends (prefixWord ++ tailWord_590114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590127 : List Nat := [1, 1, 2, 1, 2, 1, 5, 1, 1, 3, 5]
def baseStart_590127 : Nat := 118140960795 + 590127 * 2 ^ 59
def prefixEnd_590127 : Nat := 4983230072969 + 3 ^ 40 * 590127 * 2
def baseEnd_590127 : Nat := 303018798195917859098561

theorem tailTrace_590127 : CollatzResearch.WordTrace tailWord_590127 prefixEnd_590127 303018798195917859098561 := by
  unfold tailWord_590127
  simp only [CollatzResearch.WordTrace]
  refine ⟨21523699933078139512752635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14349133288718759675168423 21523699933078139512752635)
  ·
    refine ⟨32285549899617209269128953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21523699933078139512752635 32285549899617209269128953)
    ·
      refine ⟨24214162424712906951846715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32285549899617209269128953 24214162424712906951846715)
      ·
        refine ⟨36321243637069360427770073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24214162424712906951846715 36321243637069360427770073)
        ·
          refine ⟨27240932727802020320827555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36321243637069360427770073 27240932727802020320827555)
          ·
            refine ⟨40861399091703030481241333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27240932727802020320827555 40861399091703030481241333)
            ·
              refine ⟨3830756164847159107616375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40861399091703030481241333 3830756164847159107616375)
              ·
                refine ⟨5746134247270738661424563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3830756164847159107616375 5746134247270738661424563)
                ·
                  refine ⟨8619201370906107992136845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5746134247270738661424563 8619201370906107992136845)
                  ·
                    refine ⟨3232200514089790497051317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8619201370906107992136845 3232200514089790497051317)
                    ·
                      refine ⟨303018798195917859098561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3232200514089790497051317 303018798195917859098561)
                      ·
                        rfl

theorem cell23_590127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 3, 5].length) (baseStart_590127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_590127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_590127 prefixEnd_590127 := by exact prefixLift 590127
  have htrace : WordTrace (prefixWord ++ tailWord_590127) baseStart_590127 baseEnd_590127 := by
    simpa [prefixWord, tailWord_590127, baseEnd_590127] using wordTrace_append hprefix tailTrace_590127
  have hstable : (prefixWord ++ tailWord_590127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590127).length < 2 ^ (prefixWord ++ tailWord_590127).sum := by decide
  have hdescent : baseEnd_590127 < baseStart_590127 := by decide
  rcases family_descends (prefixWord ++ tailWord_590127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590187 : List Nat := [1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 7]
def baseStart_590187 : Nat := 118140960795 + 590187 * 2 ^ 59
def prefixEnd_590187 : Nat := 4983230072969 + 3 ^ 40 * 590187 * 2
def baseEnd_590187 : Nat := 303049607035187624348285

theorem tailTrace_590187 : CollatzResearch.WordTrace tailWord_590187 prefixEnd_590187 303049607035187624348285 := by
  unfold tailWord_590187
  simp only [CollatzResearch.WordTrace]
  refine ⟨21525888312860769759936815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14350592208573846506624543 21525888312860769759936815)
  ·
    refine ⟨32288832469291154639905223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21525888312860769759936815 32288832469291154639905223)
    ·
      refine ⟨48433248703936731959857835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32288832469291154639905223 48433248703936731959857835)
      ·
        refine ⟨72649873055905097939786753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48433248703936731959857835 72649873055905097939786753)
        ·
          refine ⟨54487404791928823454840065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72649873055905097939786753 54487404791928823454840065)
          ·
            refine ⟨40865553593946617591130049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54487404791928823454840065 40865553593946617591130049)
            ·
              refine ⟨30649165195459963193347537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40865553593946617591130049 30649165195459963193347537)
              ·
                refine ⟨22986873896594972395010653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30649165195459963193347537 22986873896594972395010653)
                ·
                  refine ⟨8620077711223114648128995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22986873896594972395010653 8620077711223114648128995)
                  ·
                    refine ⟨12930116566834671972193493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8620077711223114648128995 12930116566834671972193493)
                    ·
                      refine ⟨303049607035187624348285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 12930116566834671972193493 303049607035187624348285)
                      ·
                        rfl

theorem cell23_590187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 7].length) (baseStart_590187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_590187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_590187 prefixEnd_590187 := by exact prefixLift 590187
  have htrace : WordTrace (prefixWord ++ tailWord_590187) baseStart_590187 baseEnd_590187 := by
    simpa [prefixWord, tailWord_590187, baseEnd_590187] using wordTrace_append hprefix tailTrace_590187
  have hstable : (prefixWord ++ tailWord_590187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590187).length < 2 ^ (prefixWord ++ tailWord_590187).sum := by decide
  have hdescent : baseEnd_590187 < baseStart_590187 := by decide
  rcases family_descends (prefixWord ++ tailWord_590187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590231 : List Nat := [1, 1, 3, 3, 1, 1, 5, 1, 2, 1, 4]
def baseStart_590231 : Nat := 118140960795 + 590231 * 2 ^ 59
def prefixEnd_590231 : Nat := 4983230072969 + 3 ^ 40 * 590231 * 2
def baseEnd_590231 : Nat := 303072200183985452198083

theorem tailTrace_590231 : CollatzResearch.WordTrace tailWord_590231 prefixEnd_590231 303072200183985452198083 := by
  unfold tailWord_590231
  simp only [CollatzResearch.WordTrace]
  refine ⟨21527493124701365274538547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14351662083134243516359031 21527493124701365274538547)
  ·
    refine ⟨32291239687052047911807821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21527493124701365274538547 32291239687052047911807821)
    ·
      refine ⟨12109214882644517966927933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32291239687052047911807821 12109214882644517966927933)
      ·
        refine ⟨4540955580991694237597975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12109214882644517966927933 4540955580991694237597975)
        ·
          refine ⟨6811433371487541356396963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4540955580991694237597975 6811433371487541356396963)
          ·
            refine ⟨10217150057231312034595445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6811433371487541356396963 10217150057231312034595445)
            ·
              refine ⟨957857817865435503243323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10217150057231312034595445 957857817865435503243323)
              ·
                refine ⟨1436786726798153254864985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 957857817865435503243323 1436786726798153254864985)
                ·
                  refine ⟨1077590045098614941148739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1436786726798153254864985 1077590045098614941148739)
                  ·
                    refine ⟨1616385067647922411723109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1077590045098614941148739 1616385067647922411723109)
                    ·
                      refine ⟨303072200183985452198083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1616385067647922411723109 303072200183985452198083)
                      ·
                        rfl

theorem cell23_590231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 1, 2, 1, 4].length) (baseStart_590231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_590231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_590231 prefixEnd_590231 := by exact prefixLift 590231
  have htrace : WordTrace (prefixWord ++ tailWord_590231) baseStart_590231 baseEnd_590231 := by
    simpa [prefixWord, tailWord_590231, baseEnd_590231] using wordTrace_append hprefix tailTrace_590231
  have hstable : (prefixWord ++ tailWord_590231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590231).length < 2 ^ (prefixWord ++ tailWord_590231).sum := by decide
  have hdescent : baseEnd_590231 < baseStart_590231 := by decide
  rcases family_descends (prefixWord ++ tailWord_590231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590244 : List Nat := [2, 3, 1, 2, 1, 1, 3, 1, 2, 1, 6]
def baseStart_590244 : Nat := 118140960795 + 590244 * 2 ^ 59
def prefixEnd_590244 : Nat := 4983230072969 + 3 ^ 40 * 590244 * 2
def baseEnd_590244 : Nat := 303078875432493901335523

theorem tailTrace_590244 : CollatzResearch.WordTrace tailWord_590244 prefixEnd_590244 303078875432493901335523 := by
  unfold tailWord_590244
  simp only [CollatzResearch.WordTrace]
  refine ⟨10763983636827134247380893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14351978182436178996507857 10763983636827134247380893)
  ·
    refine ⟨4036493863810175342767835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10763983636827134247380893 4036493863810175342767835)
    ·
      refine ⟨6054740795715263014151753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4036493863810175342767835 6054740795715263014151753)
      ·
        refine ⟨4541055596786447260613815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6054740795715263014151753 4541055596786447260613815)
        ·
          refine ⟨6811583395179670890920723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4541055596786447260613815 6811583395179670890920723)
          ·
            refine ⟨10217375092769506336381085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6811583395179670890920723 10217375092769506336381085)
            ·
              refine ⟨3831515659788564876142907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10217375092769506336381085 3831515659788564876142907)
              ·
                refine ⟨5747273489682847314214361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3831515659788564876142907 5747273489682847314214361)
                ·
                  refine ⟨4310455117262135485660771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5747273489682847314214361 4310455117262135485660771)
                  ·
                    refine ⟨6465682675893203228491157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4310455117262135485660771 6465682675893203228491157)
                    ·
                      refine ⟨303078875432493901335523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6465682675893203228491157 303078875432493901335523)
                      ·
                        rfl

theorem cell23_590244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_590244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_590244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_590244 prefixEnd_590244 := by exact prefixLift 590244
  have htrace : WordTrace (prefixWord ++ tailWord_590244) baseStart_590244 baseEnd_590244 := by
    simpa [prefixWord, tailWord_590244, baseEnd_590244] using wordTrace_append hprefix tailTrace_590244
  have hstable : (prefixWord ++ tailWord_590244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590244).length < 2 ^ (prefixWord ++ tailWord_590244).sum := by decide
  have hdescent : baseEnd_590244 < baseStart_590244 := by decide
  rcases family_descends (prefixWord ++ tailWord_590244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590258 : List Nat := [3, 2, 1, 1, 1, 1, 3, 6, 1, 4]
def baseStart_590258 : Nat := 118140960795 + 590258 * 2 ^ 59
def prefixEnd_590258 : Nat := 4983230072969 + 3 ^ 40 * 590258 * 2
def baseEnd_590258 : Nat := 101028688053885615520153

theorem tailTrace_590258 : CollatzResearch.WordTrace tailWord_590258 prefixEnd_590258 101028688053885615520153 := by
  unfold tailWord_590258
  simp only [CollatzResearch.WordTrace]
  refine ⟨5382119473900887221442857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14352318597069032590514285 5382119473900887221442857)
  ·
    refine ⟨4036589605425665416082143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5382119473900887221442857 4036589605425665416082143)
    ·
      refine ⟨6054884408138498124123215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4036589605425665416082143 6054884408138498124123215)
      ·
        refine ⟨9082326612207747186184823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6054884408138498124123215 9082326612207747186184823)
        ·
          refine ⟨13623489918311620779277235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9082326612207747186184823 13623489918311620779277235)
          ·
            refine ⟨20435234877467431168915853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13623489918311620779277235 20435234877467431168915853)
            ·
              refine ⟨7663213079050286688343445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20435234877467431168915853 7663213079050286688343445)
              ·
                refine ⟨359213113080482188516099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7663213079050286688343445 359213113080482188516099)
                ·
                  refine ⟨538819669620723282774149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 359213113080482188516099 538819669620723282774149)
                  ·
                    refine ⟨101028688053885615520153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 538819669620723282774149 101028688053885615520153)
                    ·
                      rfl

theorem cell23_590258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 6, 1, 4].length) (baseStart_590258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_590258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_590258 prefixEnd_590258 := by exact prefixLift 590258
  have htrace : WordTrace (prefixWord ++ tailWord_590258) baseStart_590258 baseEnd_590258 := by
    simpa [prefixWord, tailWord_590258, baseEnd_590258] using wordTrace_append hprefix tailTrace_590258
  have hstable : (prefixWord ++ tailWord_590258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590258).length < 2 ^ (prefixWord ++ tailWord_590258).sum := by decide
  have hdescent : baseEnd_590258 < baseStart_590258 := by decide
  rcases family_descends (prefixWord ++ tailWord_590258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590292 : List Nat := [2, 4, 1, 2, 2, 3, 1, 3, 1, 4]
def baseStart_590292 : Nat := 118140960795 + 590292 * 2 ^ 59
def prefixEnd_590292 : Nat := 4983230072969 + 3 ^ 40 * 590292 * 2
def baseEnd_590292 : Nat := 101034507501303237845101

theorem tailTrace_590292 : CollatzResearch.WordTrace tailWord_590292 prefixEnd_590292 101034507501303237845101 := by
  unfold tailWord_590292
  simp only [CollatzResearch.WordTrace]
  refine ⟨10764858988740186346254565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14353145318320248461672753 10764858988740186346254565)
  ·
    refine ⟨2018411060388784939922731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10764858988740186346254565 2018411060388784939922731)
    ·
      refine ⟨3027616590583177409884097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2018411060388784939922731 3027616590583177409884097)
      ·
        refine ⟨2270712442937383057413073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3027616590583177409884097 2270712442937383057413073)
        ·
          refine ⟨1703034332203037293059805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2270712442937383057413073 1703034332203037293059805)
          ·
            refine ⟨638637874576138984897427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1703034332203037293059805 638637874576138984897427)
            ·
              refine ⟨957956811864208477346141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 638637874576138984897427 957956811864208477346141)
              ·
                refine ⟨359233804449078179004803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 957956811864208477346141 359233804449078179004803)
                ·
                  refine ⟨538850706673617268507205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 359233804449078179004803 538850706673617268507205)
                  ·
                    refine ⟨101034507501303237845101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 538850706673617268507205 101034507501303237845101)
                    ·
                      rfl

theorem cell23_590292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 3, 1, 4].length) (baseStart_590292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_590292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_590292 prefixEnd_590292 := by exact prefixLift 590292
  have htrace : WordTrace (prefixWord ++ tailWord_590292) baseStart_590292 baseEnd_590292 := by
    simpa [prefixWord, tailWord_590292, baseEnd_590292] using wordTrace_append hprefix tailTrace_590292
  have hstable : (prefixWord ++ tailWord_590292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590292).length < 2 ^ (prefixWord ++ tailWord_590292).sum := by decide
  have hdescent : baseEnd_590292 < baseStart_590292 := by decide
  rcases family_descends (prefixWord ++ tailWord_590292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590321 : List Nat := [1, 2, 2, 2, 3, 1, 2, 2, 3, 1, 4]
def baseStart_590321 : Nat := 118140960795 + 590321 * 2 ^ 59
def prefixEnd_590321 : Nat := 4983230072969 + 3 ^ 40 * 590321 * 2
def baseEnd_590321 : Nat := 303118413442890100072669

theorem tailTrace_590321 : CollatzResearch.WordTrace tailWord_590321 prefixEnd_590321 303118413442890100072669 := by
  unfold tailWord_590321
  simp only [CollatzResearch.WordTrace]
  refine ⟨21530775694375310645314817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14353850462916873763543211 21530775694375310645314817)
  ·
    refine ⟨16148081770781482983986113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21530775694375310645314817 16148081770781482983986113)
    ·
      refine ⟨12111061328086112237989585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16148081770781482983986113 12111061328086112237989585)
      ·
        refine ⟨9083295996064584178492189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12111061328086112237989585 9083295996064584178492189)
        ·
          refine ⟨3406235998524219066934571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9083295996064584178492189 3406235998524219066934571)
          ·
            refine ⟨5109353997786328600401857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3406235998524219066934571 5109353997786328600401857)
            ·
              refine ⟨3832015498339746450301393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5109353997786328600401857 3832015498339746450301393)
              ·
                refine ⟨2874011623754809837726045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3832015498339746450301393 2874011623754809837726045)
                ·
                  refine ⟨1077754358908053689147267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2874011623754809837726045 1077754358908053689147267)
                  ·
                    refine ⟨1616631538362080533720901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1077754358908053689147267 1616631538362080533720901)
                    ·
                      refine ⟨303118413442890100072669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1616631538362080533720901 303118413442890100072669)
                      ·
                        rfl

theorem cell23_590321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 3, 1, 4].length) (baseStart_590321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_590321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_590321 prefixEnd_590321 := by exact prefixLift 590321
  have htrace : WordTrace (prefixWord ++ tailWord_590321) baseStart_590321 baseEnd_590321 := by
    simpa [prefixWord, tailWord_590321, baseEnd_590321] using wordTrace_append hprefix tailTrace_590321
  have hstable : (prefixWord ++ tailWord_590321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590321).length < 2 ^ (prefixWord ++ tailWord_590321).sum := by decide
  have hdescent : baseEnd_590321 < baseStart_590321 := by decide
  rcases family_descends (prefixWord ++ tailWord_590321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590322 : List Nat := [3, 2, 1, 4, 3, 1, 2, 1, 6]
def baseStart_590322 : Nat := 118140960795 + 590322 * 2 ^ 59
def prefixEnd_590322 : Nat := 4983230072969 + 3 ^ 40 * 590322 * 2
def baseEnd_590322 : Nat := 33679880769282732906685

theorem tailTrace_590322 : CollatzResearch.WordTrace tailWord_590322 prefixEnd_590322 33679880769282732906685 := by
  unfold tailWord_590322
  simp only [CollatzResearch.WordTrace]
  refine ⟨5382703041842921954025305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14353874778247791877400813 5382703041842921954025305)
  ·
    refine ⟨4037027281382191465518979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5382703041842921954025305 4037027281382191465518979)
    ·
      refine ⟨6055540922073287198278469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4037027281382191465518979 6055540922073287198278469)
      ·
        refine ⟨1135413922888741349677213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6055540922073287198278469 1135413922888741349677213)
        ·
          refine ⟨425780221083278006128955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1135413922888741349677213 425780221083278006128955)
          ·
            refine ⟨638670331624917009193433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 425780221083278006128955 638670331624917009193433)
            ·
              refine ⟨479002748718687756895075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 638670331624917009193433 479002748718687756895075)
              ·
                refine ⟨718504123078031635342613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 479002748718687756895075 718504123078031635342613)
                ·
                  refine ⟨33679880769282732906685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 718504123078031635342613 33679880769282732906685)
                  ·
                    rfl

theorem cell23_590322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 2, 1, 6].length) (baseStart_590322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_590322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_590322 prefixEnd_590322 := by exact prefixLift 590322
  have htrace : WordTrace (prefixWord ++ tailWord_590322) baseStart_590322 baseEnd_590322 := by
    simpa [prefixWord, tailWord_590322, baseEnd_590322] using wordTrace_append hprefix tailTrace_590322
  have hstable : (prefixWord ++ tailWord_590322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590322).length < 2 ^ (prefixWord ++ tailWord_590322).sum := by decide
  have hdescent : baseEnd_590322 < baseStart_590322 := by decide
  rcases family_descends (prefixWord ++ tailWord_590322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590365 : List Nat := [1, 4, 2, 2, 1, 3, 2, 2, 2, 4]
def baseStart_590365 : Nat := 118140960795 + 590365 * 2 ^ 59
def prefixEnd_590365 : Nat := 4983230072969 + 3 ^ 40 * 590365 * 2
def baseEnd_590365 : Nat := 101047002197229309307489

theorem tailTrace_590365 : CollatzResearch.WordTrace tailWord_590365 prefixEnd_590365 101047002197229309307489 := by
  unfold tailWord_590365
  simp only [CollatzResearch.WordTrace]
  refine ⟨21532380506215906159916549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14354920337477270773277699 21532380506215906159916549)
  ·
    refine ⟨4037321344915482404984353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21532380506215906159916549 4037321344915482404984353)
    ·
      refine ⟨3027991008686611803738265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4037321344915482404984353 3027991008686611803738265)
      ·
        refine ⟨2270993256514958852803699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3027991008686611803738265 2270993256514958852803699)
        ·
          refine ⟨3406489884772438279205549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2270993256514958852803699 3406489884772438279205549)
          ·
            refine ⟨1277433706789664354702081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3406489884772438279205549 1277433706789664354702081)
            ·
              refine ⟨958075280092248266026561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1277433706789664354702081 958075280092248266026561)
              ·
                refine ⟨718556460069186199519921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 958075280092248266026561 718556460069186199519921)
                ·
                  refine ⟨538917345051889649639941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 718556460069186199519921 538917345051889649639941)
                  ·
                    refine ⟨101047002197229309307489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 538917345051889649639941 101047002197229309307489)
                    ·
                      rfl

theorem cell23_590365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 2, 2, 4].length) (baseStart_590365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_590365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_590365 prefixEnd_590365 := by exact prefixLift 590365
  have htrace : WordTrace (prefixWord ++ tailWord_590365) baseStart_590365 baseEnd_590365 := by
    simpa [prefixWord, tailWord_590365, baseEnd_590365] using wordTrace_append hprefix tailTrace_590365
  have hstable : (prefixWord ++ tailWord_590365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590365).length < 2 ^ (prefixWord ++ tailWord_590365).sum := by decide
  have hdescent : baseEnd_590365 < baseStart_590365 := by decide
  rcases family_descends (prefixWord ++ tailWord_590365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590378 : List Nat := [3, 1, 4, 1, 1, 4, 1, 8]
def baseStart_590378 : Nat := 118140960795 + 590378 * 2 ^ 59
def prefixEnd_590378 : Nat := 4983230072969 + 3 ^ 40 * 590378 * 2
def baseEnd_590378 : Nat := 11227691920007273224441

theorem tailTrace_590378 : CollatzResearch.WordTrace tailWord_590378 prefixEnd_590378 11227691920007273224441 := by
  unfold tailWord_590378
  simp only [CollatzResearch.WordTrace]
  refine ⟨5383213663792202345034947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14355236436779206253426525 5383213663792202345034947)
  ·
    refine ⟨8074820495688303517552421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5383213663792202345034947 8074820495688303517552421)
    ·
      refine ⟨1514028842941556909541079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8074820495688303517552421 1514028842941556909541079)
      ·
        refine ⟨2271043264412335364311619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1514028842941556909541079 2271043264412335364311619)
        ·
          refine ⟨3406564896618503046467429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2271043264412335364311619 3406564896618503046467429)
          ·
            refine ⟨638730918115969321212643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3406564896618503046467429 638730918115969321212643)
            ·
              refine ⟨958096377173953981818965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 638730918115969321212643 958096377173953981818965)
              ·
                refine ⟨11227691920007273224441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 958096377173953981818965 11227691920007273224441)
                ·
                  rfl

theorem cell23_590378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 8].length) (baseStart_590378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_590378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_590378 prefixEnd_590378 := by exact prefixLift 590378
  have htrace : WordTrace (prefixWord ++ tailWord_590378) baseStart_590378 baseEnd_590378 := by
    simpa [prefixWord, tailWord_590378, baseEnd_590378] using wordTrace_append hprefix tailTrace_590378
  have hstable : (prefixWord ++ tailWord_590378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590378).length < 2 ^ (prefixWord ++ tailWord_590378).sum := by decide
  have hdescent : baseEnd_590378 < baseStart_590378 := by decide
  rcases family_descends (prefixWord ++ tailWord_590378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590406 : List Nat := [6, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2]
def baseStart_590406 : Nat := 118140960795 + 590406 * 2 ^ 59
def prefixEnd_590406 : Nat := 4983230072969 + 3 ^ 40 * 590406 * 2
def baseEnd_590406 : Nat := 303162059298522267509779

theorem tailTrace_590406 : CollatzResearch.WordTrace tailWord_590406 prefixEnd_590406 303162059298522267509779 := by
  unfold tailWord_590406
  simp only [CollatzResearch.WordTrace]
  refine ⟨672933621845855317567471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14355917266044913441439381 672933621845855317567471)
  ·
    refine ⟨1009400432768782976351207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 672933621845855317567471 1009400432768782976351207)
    ·
      refine ⟨1514100649153174464526811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1009400432768782976351207 1514100649153174464526811)
      ·
        refine ⟨2271150973729761696790217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1514100649153174464526811 2271150973729761696790217)
        ·
          refine ⟨1703363230297321272592663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2271150973729761696790217 1703363230297321272592663)
          ·
            refine ⟨2555044845445981908888995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1703363230297321272592663 2555044845445981908888995)
            ·
              refine ⟨3832567268168972863333493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2555044845445981908888995 3832567268168972863333493)
              ·
                refine ⟨359303181390841205937515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3832567268168972863333493 359303181390841205937515)
                ·
                  refine ⟨538954772086261808906273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 359303181390841205937515 538954772086261808906273)
                  ·
                    refine ⟨404216079064696356679705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 538954772086261808906273 404216079064696356679705)
                    ·
                      refine ⟨303162059298522267509779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 404216079064696356679705 303162059298522267509779)
                      ·
                        rfl

theorem cell23_590406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2].length) (baseStart_590406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_590406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_590406 prefixEnd_590406 := by exact prefixLift 590406
  have htrace : WordTrace (prefixWord ++ tailWord_590406) baseStart_590406 baseEnd_590406 := by
    simpa [prefixWord, tailWord_590406, baseEnd_590406] using wordTrace_append hprefix tailTrace_590406
  have hstable : (prefixWord ++ tailWord_590406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590406).length < 2 ^ (prefixWord ++ tailWord_590406).sum := by decide
  have hdescent : baseEnd_590406 < baseStart_590406 := by decide
  rcases family_descends (prefixWord ++ tailWord_590406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590421 : List Nat := [1, 3, 2, 2, 1, 1, 3, 2, 2, 6]
def baseStart_590421 : Nat := 118140960795 + 590421 * 2 ^ 59
def prefixEnd_590421 : Nat := 4983230072969 + 3 ^ 40 * 590421 * 2
def baseEnd_590421 : Nat := 101056587169446569607403

theorem tailTrace_590421 : CollatzResearch.WordTrace tailWord_590421 prefixEnd_590421 101056587169446569607403 := by
  unfold tailWord_590421
  simp only [CollatzResearch.WordTrace]
  refine ⟨21534422994013027723955117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14356281996008685149303411 21534422994013027723955117)
  ·
    refine ⟨8075408622754885396483169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21534422994013027723955117 8075408622754885396483169)
    ·
      refine ⟨6056556467066164047362377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8075408622754885396483169 6056556467066164047362377)
      ·
        refine ⟨4542417350299623035521783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6056556467066164047362377 4542417350299623035521783)
        ·
          refine ⟨6813626025449434553282675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4542417350299623035521783 6813626025449434553282675)
          ·
            refine ⟨10220439038174151829924013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6813626025449434553282675 10220439038174151829924013)
            ·
              refine ⟨3832664639315306936221505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10220439038174151829924013 3832664639315306936221505)
              ·
                refine ⟨2874498479486480202166129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3832664639315306936221505 2874498479486480202166129)
                ·
                  refine ⟨2155873859614860151624597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2874498479486480202166129 2155873859614860151624597)
                  ·
                    refine ⟨101056587169446569607403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2155873859614860151624597 101056587169446569607403)
                    ·
                      rfl

theorem cell23_590421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 2, 6].length) (baseStart_590421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_590421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_590421 prefixEnd_590421 := by exact prefixLift 590421
  have htrace : WordTrace (prefixWord ++ tailWord_590421) baseStart_590421 baseEnd_590421 := by
    simpa [prefixWord, tailWord_590421, baseEnd_590421] using wordTrace_append hprefix tailTrace_590421
  have hstable : (prefixWord ++ tailWord_590421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590421).length < 2 ^ (prefixWord ++ tailWord_590421).sum := by decide
  have hdescent : baseEnd_590421 < baseStart_590421 := by decide
  rcases family_descends (prefixWord ++ tailWord_590421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590431 : List Nat := [1, 1, 2, 3, 1, 1, 1, 3, 1, 6, 3]
def baseStart_590431 : Nat := 118140960795 + 590431 * 2 ^ 59
def prefixEnd_590431 : Nat := 4983230072969 + 3 ^ 40 * 590431 * 2
def baseEnd_590431 : Nat := 303174896314884669697163

theorem tailTrace_590431 : CollatzResearch.WordTrace tailWord_590431 prefixEnd_590431 303174896314884669697163 := by
  unfold tailWord_590431
  simp only [CollatzResearch.WordTrace]
  refine ⟨21534787723976799431819147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14356525149317866287879431 21534787723976799431819147)
  ·
    refine ⟨32302181585965199147728721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21534787723976799431819147 32302181585965199147728721)
    ·
      refine ⟨24226636189473899360796541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32302181585965199147728721 24226636189473899360796541)
      ·
        refine ⟨9084988571052712260298703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24226636189473899360796541 9084988571052712260298703)
        ·
          refine ⟨13627482856579068390448055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9084988571052712260298703 13627482856579068390448055)
          ·
            refine ⟨20441224284868602585672083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13627482856579068390448055 20441224284868602585672083)
            ·
              refine ⟨30661836427302903878508125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20441224284868602585672083 30661836427302903878508125)
              ·
                refine ⟨11498188660238588954440547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30661836427302903878508125 11498188660238588954440547)
                ·
                  refine ⟨17247282990357883431660821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11498188660238588954440547 17247282990357883431660821)
                  ·
                    refine ⟨808466390173025785859101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17247282990357883431660821 808466390173025785859101)
                    ·
                      refine ⟨303174896314884669697163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 808466390173025785859101 303174896314884669697163)
                      ·
                        rfl

theorem cell23_590431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 6, 3].length) (baseStart_590431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_590431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_590431 prefixEnd_590431 := by exact prefixLift 590431
  have htrace : WordTrace (prefixWord ++ tailWord_590431) baseStart_590431 baseEnd_590431 := by
    simpa [prefixWord, tailWord_590431, baseEnd_590431] using wordTrace_append hprefix tailTrace_590431
  have hstable : (prefixWord ++ tailWord_590431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590431).length < 2 ^ (prefixWord ++ tailWord_590431).sum := by decide
  have hdescent : baseEnd_590431 < baseStart_590431 := by decide
  rcases family_descends (prefixWord ++ tailWord_590431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590496 : List Nat := [2, 1, 1, 4, 4, 2, 2, 1, 2, 2, 2]
def baseStart_590496 : Nat := 118140960795 + 590496 * 2 ^ 59
def prefixEnd_590496 : Nat := 4983230072969 + 3 ^ 40 * 590496 * 2
def baseEnd_590496 : Nat := 303208272557426915384365

theorem tailTrace_590496 : CollatzResearch.WordTrace tailWord_590496 prefixEnd_590496 303208272557426915384365 := by
  unfold tailWord_590496
  simp only [CollatzResearch.WordTrace]
  refine ⟨10768579234370657766467671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14358105645827543688623561 10768579234370657766467671)
  ·
    refine ⟨16152868851555986649701507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10768579234370657766467671 16152868851555986649701507)
    ·
      refine ⟨24229303277333979974552261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16152868851555986649701507 24229303277333979974552261)
      ·
        refine ⟨4542994364500121245228549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24229303277333979974552261 4542994364500121245228549)
        ·
          refine ⟨851811443343772733480353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4542994364500121245228549 851811443343772733480353)
          ·
            refine ⟨638858582507829550110265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 851811443343772733480353 638858582507829550110265)
            ·
              refine ⟨479143936880872162582699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 638858582507829550110265 479143936880872162582699)
              ·
                refine ⟨718715905321308243874049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 479143936880872162582699 718715905321308243874049)
                ·
                  refine ⟨539036928990981182905537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 718715905321308243874049 539036928990981182905537)
                  ·
                    refine ⟨404277696743235887179153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 539036928990981182905537 404277696743235887179153)
                    ·
                      refine ⟨303208272557426915384365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 404277696743235887179153 303208272557426915384365)
                      ·
                        rfl

theorem cell23_590496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 2, 1, 2, 2, 2].length) (baseStart_590496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_590496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_590496 prefixEnd_590496 := by exact prefixLift 590496
  have htrace : WordTrace (prefixWord ++ tailWord_590496) baseStart_590496 baseEnd_590496 := by
    simpa [prefixWord, tailWord_590496, baseEnd_590496] using wordTrace_append hprefix tailTrace_590496
  have hstable : (prefixWord ++ tailWord_590496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590496).length < 2 ^ (prefixWord ++ tailWord_590496).sum := by decide
  have hdescent : baseEnd_590496 < baseStart_590496 := by decide
  rcases family_descends (prefixWord ++ tailWord_590496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590595 : List Nat := [1, 1, 1, 3, 2, 2, 1, 3, 4, 3, 2]
def baseStart_590595 : Nat := 118140960795 + 590595 * 2 ^ 59
def prefixEnd_590595 : Nat := 4983230072969 + 3 ^ 40 * 590595 * 2
def baseEnd_590595 : Nat := 303259107142222028046409

theorem tailTrace_590595 : CollatzResearch.WordTrace tailWord_590595 prefixEnd_590595 303259107142222028046409 := by
  unfold tailWord_590595
  simp only [CollatzResearch.WordTrace]
  refine ⟨21540769295382655440789239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14360512863588436960526159 21540769295382655440789239)
  ·
    refine ⟨32311153943073983161183859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21540769295382655440789239 32311153943073983161183859)
    ·
      refine ⟨48466730914610974741775789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32311153943073983161183859 48466730914610974741775789)
      ·
        refine ⟨18175024092979115528165921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48466730914610974741775789 18175024092979115528165921)
        ·
          refine ⟨13631268069734336646124441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18175024092979115528165921 13631268069734336646124441)
          ·
            refine ⟨10223451052300752484593331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13631268069734336646124441 10223451052300752484593331)
            ·
              refine ⟨15335176578451128726889997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10223451052300752484593331 15335176578451128726889997)
              ·
                refine ⟨5750691216919173272583749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15335176578451128726889997 5750691216919173272583749)
                ·
                  refine ⟨1078254603172344988609453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5750691216919173272583749 1078254603172344988609453)
                  ·
                    refine ⟨404345476189629370728545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1078254603172344988609453 404345476189629370728545)
                    ·
                      refine ⟨303259107142222028046409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 404345476189629370728545 303259107142222028046409)
                      ·
                        rfl

theorem cell23_590595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 4, 3, 2].length) (baseStart_590595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_590595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_590595 prefixEnd_590595 := by exact prefixLift 590595
  have htrace : WordTrace (prefixWord ++ tailWord_590595) baseStart_590595 baseEnd_590595 := by
    simpa [prefixWord, tailWord_590595, baseEnd_590595] using wordTrace_append hprefix tailTrace_590595
  have hstable : (prefixWord ++ tailWord_590595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590595).length < 2 ^ (prefixWord ++ tailWord_590595).sum := by decide
  have hdescent : baseEnd_590595 < baseStart_590595 := by decide
  rcases family_descends (prefixWord ++ tailWord_590595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590602 : List Nat := [3, 1, 2, 2, 1, 2, 4, 1, 3, 1, 3]
def baseStart_590602 : Nat := 118140960795 + 590602 * 2 ^ 59
def prefixEnd_590602 : Nat := 4983230072969 + 3 ^ 40 * 590602 * 2
def baseEnd_590602 : Nat := 303262701506803500658877

theorem tailTrace_590602 : CollatzResearch.WordTrace tailWord_590602 prefixEnd_590602 303262701506803500658877 := by
  unfold tailWord_590602
  simp only [CollatzResearch.WordTrace]
  refine ⟨5385256151589323909073515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14360683070904863757529373 5385256151589323909073515)
  ·
    refine ⟨8077884227383985863610273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5385256151589323909073515 8077884227383985863610273)
    ·
      refine ⟨6058413170537989397707705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8077884227383985863610273 6058413170537989397707705)
      ·
        refine ⟨4543809877903492048280779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6058413170537989397707705 4543809877903492048280779)
        ·
          refine ⟨6815714816855238072421169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4543809877903492048280779 6815714816855238072421169)
          ·
            refine ⟨5111786112641428554315877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6815714816855238072421169 5111786112641428554315877)
            ·
              refine ⟨958459896120267853934227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5111786112641428554315877 958459896120267853934227)
              ·
                refine ⟨1437689844180401780901341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 958459896120267853934227 1437689844180401780901341)
                ·
                  refine ⟨539133691567650667838003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1437689844180401780901341 539133691567650667838003)
                  ·
                    refine ⟨808700537351476001757005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 539133691567650667838003 808700537351476001757005)
                    ·
                      refine ⟨303262701506803500658877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 808700537351476001757005 303262701506803500658877)
                      ·
                        rfl

theorem cell23_590602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 1, 3, 1, 3].length) (baseStart_590602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_590602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_590602 prefixEnd_590602 := by exact prefixLift 590602
  have htrace : WordTrace (prefixWord ++ tailWord_590602) baseStart_590602 baseEnd_590602 := by
    simpa [prefixWord, tailWord_590602, baseEnd_590602] using wordTrace_append hprefix tailTrace_590602
  have hstable : (prefixWord ++ tailWord_590602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590602).length < 2 ^ (prefixWord ++ tailWord_590602).sum := by decide
  have hdescent : baseEnd_590602 < baseStart_590602 := by decide
  rcases family_descends (prefixWord ++ tailWord_590602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590625 : List Nat := [1, 2, 3, 2, 1, 2, 1, 1, 2, 6, 2]
def baseStart_590625 : Nat := 118140960795 + 590625 * 2 ^ 59
def prefixEnd_590625 : Nat := 4983230072969 + 3 ^ 40 * 590625 * 2
def baseEnd_590625 : Nat := 303274511561856910671271

theorem tailTrace_590625 : CollatzResearch.WordTrace tailWord_590625 prefixEnd_590625 303274511561856910671271 := by
  unfold tailWord_590625
  simp only [CollatzResearch.WordTrace]
  refine ⟨21541863485273970564381329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14361242323515980376254219 21541863485273970564381329)
  ·
    refine ⟨16156397613955477923285997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21541863485273970564381329 16156397613955477923285997)
    ·
      refine ⟨6058649105233304221232249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16156397613955477923285997 6058649105233304221232249)
      ·
        refine ⟨4543986828924978165924187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6058649105233304221232249 4543986828924978165924187)
        ·
          refine ⟨6815980243387467248886281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4543986828924978165924187 6815980243387467248886281)
          ·
            refine ⟨5111985182540600436664711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6815980243387467248886281 5111985182540600436664711)
            ·
              refine ⟨7667977773810900654997067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5111985182540600436664711 7667977773810900654997067)
              ·
                refine ⟨11501966660716350982495601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7667977773810900654997067 11501966660716350982495601)
                ·
                  refine ⟨8626474995537263236871701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11501966660716350982495601 8626474995537263236871701)
                  ·
                    refine ⟨404366015415809214228361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8626474995537263236871701 404366015415809214228361)
                    ·
                      refine ⟨303274511561856910671271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 404366015415809214228361 303274511561856910671271)
                      ·
                        rfl

theorem cell23_590625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 6, 2].length) (baseStart_590625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_590625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_590625 prefixEnd_590625 := by exact prefixLift 590625
  have htrace : WordTrace (prefixWord ++ tailWord_590625) baseStart_590625 baseEnd_590625 := by
    simpa [prefixWord, tailWord_590625, baseEnd_590625] using wordTrace_append hprefix tailTrace_590625
  have hstable : (prefixWord ++ tailWord_590625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590625).length < 2 ^ (prefixWord ++ tailWord_590625).sum := by decide
  have hdescent : baseEnd_590625 < baseStart_590625 := by decide
  rcases family_descends (prefixWord ++ tailWord_590625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590645 : List Nat := [1, 3, 3, 1, 3, 1, 1, 3, 1, 1, 5]
def baseStart_590645 : Nat := 118140960795 + 590645 * 2 ^ 59
def prefixEnd_590645 : Nat := 4983230072969 + 3 ^ 40 * 590645 * 2
def baseEnd_590645 : Nat := 303284781174946832421179

theorem tailTrace_590645 : CollatzResearch.WordTrace tailWord_590645 prefixEnd_590645 303284781174946832421179 := by
  unfold tailWord_590645
  simp only [CollatzResearch.WordTrace]
  refine ⟨21542592945201513980109389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14361728630134342653406259 21542592945201513980109389)
  ·
    refine ⟨8078472354450567742541021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21542592945201513980109389 8078472354450567742541021)
    ·
      refine ⟨3029427132918962903452883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8078472354450567742541021 3029427132918962903452883)
      ·
        refine ⟨4544140699378444355179325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3029427132918962903452883 4544140699378444355179325)
        ·
          refine ⟨1704052762266916633192247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4544140699378444355179325 1704052762266916633192247)
          ·
            refine ⟨2556079143400374949788371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1704052762266916633192247 2556079143400374949788371)
            ·
              refine ⟨3834118715100562424682557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2556079143400374949788371 3834118715100562424682557)
              ·
                refine ⟨1437794518162710909255959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3834118715100562424682557 1437794518162710909255959)
                ·
                  refine ⟨2156691777244066363883939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1437794518162710909255959 2156691777244066363883939)
                  ·
                    refine ⟨3235037665866099545825909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2156691777244066363883939 3235037665866099545825909)
                    ·
                      refine ⟨303284781174946832421179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3235037665866099545825909 303284781174946832421179)
                      ·
                        rfl

theorem cell23_590645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_590645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_590645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_590645 prefixEnd_590645 := by exact prefixLift 590645
  have htrace : WordTrace (prefixWord ++ tailWord_590645) baseStart_590645 baseEnd_590645 := by
    simpa [prefixWord, tailWord_590645, baseEnd_590645] using wordTrace_append hprefix tailTrace_590645
  have hstable : (prefixWord ++ tailWord_590645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590645).length < 2 ^ (prefixWord ++ tailWord_590645).sum := by decide
  have hdescent : baseEnd_590645 < baseStart_590645 := by decide
  rcases family_descends (prefixWord ++ tailWord_590645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590646 : List Nat := [5, 1, 2, 2, 2, 1, 1, 2, 2, 3, 2]
def baseStart_590646 : Nat := 118140960795 + 590646 * 2 ^ 59
def prefixEnd_590646 : Nat := 4983230072969 + 3 ^ 40 * 590646 * 2
def baseEnd_590646 : Nat := 303285294655601328508675

theorem tailTrace_590646 : CollatzResearch.WordTrace tailWord_590646 prefixEnd_590646 303285294655601328508675 := by
  unfold tailWord_590646
  simp only [CollatzResearch.WordTrace]
  refine ⟨1346414338637368196930987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14361752945465260767263861 1346414338637368196930987)
  ·
    refine ⟨2019621507956052295396481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1346414338637368196930987 2019621507956052295396481)
    ·
      refine ⟨1514716130967039221547361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2019621507956052295396481 1514716130967039221547361)
      ·
        refine ⟨1136037098225279416160521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1514716130967039221547361 1136037098225279416160521)
        ·
          refine ⟨852027823668959562120391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1136037098225279416160521 852027823668959562120391)
          ·
            refine ⟨1278041735503439343180587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 852027823668959562120391 1278041735503439343180587)
            ·
              refine ⟨1917062603255159014770881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1278041735503439343180587 1917062603255159014770881)
              ·
                refine ⟨1437796952441369261078161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1917062603255159014770881 1437796952441369261078161)
                ·
                  refine ⟨1078347714331026945808621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1437796952441369261078161 1078347714331026945808621)
                  ·
                    refine ⟨404380392874135104678233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1078347714331026945808621 404380392874135104678233)
                    ·
                      refine ⟨303285294655601328508675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 404380392874135104678233 303285294655601328508675)
                      ·
                        rfl

theorem cell23_590646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_590646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_590646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_590646 prefixEnd_590646 := by exact prefixLift 590646
  have htrace : WordTrace (prefixWord ++ tailWord_590646) baseStart_590646 baseEnd_590646 := by
    simpa [prefixWord, tailWord_590646, baseEnd_590646] using wordTrace_append hprefix tailTrace_590646
  have hstable : (prefixWord ++ tailWord_590646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590646).length < 2 ^ (prefixWord ++ tailWord_590646).sum := by decide
  have hdescent : baseEnd_590646 < baseStart_590646 := by decide
  rcases family_descends (prefixWord ++ tailWord_590646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590653 : List Nat := [1, 4, 1, 4, 2, 1, 3, 2, 1, 1, 3]
def baseStart_590653 : Nat := 118140960795 + 590653 * 2 ^ 59
def prefixEnd_590653 : Nat := 4983230072969 + 3 ^ 40 * 590653 * 2
def baseEnd_590653 : Nat := 303288889020182801121143

theorem tailTrace_590653 : CollatzResearch.WordTrace tailWord_590653 prefixEnd_590653 303288889020182801121143 := by
  unfold tailWord_590653
  simp only [CollatzResearch.WordTrace]
  refine ⟨21542884729172531346400613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14361923152781687564267075 21542884729172531346400613)
  ·
    refine ⟨4039290886719849627450115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21542884729172531346400613 4039290886719849627450115)
    ·
      refine ⟨6058936330079774441175173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4039290886719849627450115 6058936330079774441175173)
      ·
        refine ⟨1136050561889957707720345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6058936330079774441175173 1136050561889957707720345)
        ·
          refine ⟨852037921417468280790259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1136050561889957707720345 852037921417468280790259)
          ·
            refine ⟨1278056882126202421185389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 852037921417468280790259 1278056882126202421185389)
            ·
              refine ⟨479271330797325907944521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1278056882126202421185389 479271330797325907944521)
              ·
                refine ⟨359453498097994430958391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 479271330797325907944521 359453498097994430958391)
                ·
                  refine ⟨539180247146991646437587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 359453498097994430958391 539180247146991646437587)
                  ·
                    refine ⟨808770370720487469656381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 539180247146991646437587 808770370720487469656381)
                    ·
                      refine ⟨303288889020182801121143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 808770370720487469656381 303288889020182801121143)
                      ·
                        rfl

theorem cell23_590653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_590653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_590653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_590653 prefixEnd_590653 := by exact prefixLift 590653
  have htrace : WordTrace (prefixWord ++ tailWord_590653) baseStart_590653 baseEnd_590653 := by
    simpa [prefixWord, tailWord_590653, baseEnd_590653] using wordTrace_append hprefix tailTrace_590653
  have hstable : (prefixWord ++ tailWord_590653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590653).length < 2 ^ (prefixWord ++ tailWord_590653).sum := by decide
  have hdescent : baseEnd_590653 < baseStart_590653 := by decide
  rcases family_descends (prefixWord ++ tailWord_590653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590676 : List Nat := [2, 4, 1, 1, 5, 1, 1, 2, 1, 1, 4]
def baseStart_590676 : Nat := 118140960795 + 590676 * 2 ^ 59
def prefixEnd_590676 : Nat := 4983230072969 + 3 ^ 40 * 590676 * 2
def baseEnd_590676 : Nat := 303300699075236211133537

theorem tailTrace_590676 : CollatzResearch.WordTrace tailWord_590676 prefixEnd_590676 303300699075236211133537 := by
  unfold tailWord_590676
  simp only [CollatzResearch.WordTrace]
  refine ⟨10771861804044603137243941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14362482405392804182991921 10771861804044603137243941)
  ·
    refine ⟨2019724088258363088233239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10771861804044603137243941 2019724088258363088233239)
    ·
      refine ⟨3029586132387544632349859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2019724088258363088233239 3029586132387544632349859)
      ·
        refine ⟨4544379198581316948524789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3029586132387544632349859 4544379198581316948524789)
        ·
          refine ⟨426035549866998463924199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4544379198581316948524789 426035549866998463924199)
          ·
            refine ⟨639053324800497695886299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 426035549866998463924199 639053324800497695886299)
            ·
              refine ⟨958579987200746543829449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 639053324800497695886299 958579987200746543829449)
              ·
                refine ⟨718934990400559907872087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 958579987200746543829449 718934990400559907872087)
                ·
                  refine ⟨1078402485600839861808131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 718934990400559907872087 1078402485600839861808131)
                  ·
                    refine ⟨1617603728401259792712197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1078402485600839861808131 1617603728401259792712197)
                    ·
                      refine ⟨303300699075236211133537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1617603728401259792712197 303300699075236211133537)
                      ·
                        rfl

theorem cell23_590676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 2, 1, 1, 4].length) (baseStart_590676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_590676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_590676 prefixEnd_590676 := by exact prefixLift 590676
  have htrace : WordTrace (prefixWord ++ tailWord_590676) baseStart_590676 baseEnd_590676 := by
    simpa [prefixWord, tailWord_590676, baseEnd_590676] using wordTrace_append hprefix tailTrace_590676
  have hstable : (prefixWord ++ tailWord_590676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590676).length < 2 ^ (prefixWord ++ tailWord_590676).sum := by decide
  have hdescent : baseEnd_590676 < baseStart_590676 := by decide
  rcases family_descends (prefixWord ++ tailWord_590676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590679 : List Nat := [1, 1, 3, 2, 4, 3, 1, 2, 1, 2, 3]
def baseStart_590679 : Nat := 118140960795 + 590679 * 2 ^ 59
def prefixEnd_590679 : Nat := 4983230072969 + 3 ^ 40 * 590679 * 2
def baseEnd_590679 : Nat := 303302239517199699396023

theorem tailTrace_590679 : CollatzResearch.WordTrace tailWord_590679 prefixEnd_590679 303302239517199699396023 := by
  unfold tailWord_590679
  simp only [CollatzResearch.WordTrace]
  refine ⟨21543833027078337786847091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14362555351385558524564727 21543833027078337786847091)
  ·
    refine ⟨32315749540617506680270637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21543833027078337786847091 32315749540617506680270637)
    ·
      refine ⟨12118406077731565005101489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32315749540617506680270637 12118406077731565005101489)
      ·
        refine ⟨9088804558298673753826117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12118406077731565005101489 9088804558298673753826117)
        ·
          refine ⟨1704150854681001328842397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9088804558298673753826117 1704150854681001328842397)
          ·
            refine ⟨639056570505375498315899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1704150854681001328842397 639056570505375498315899)
            ·
              refine ⟨958584855758063247473849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 639056570505375498315899 958584855758063247473849)
              ·
                refine ⟨718938641818547435605387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 958584855758063247473849 718938641818547435605387)
                ·
                  refine ⟨1078407962727821153408081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 718938641818547435605387 1078407962727821153408081)
                  ·
                    refine ⟨808805972045865865056061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1078407962727821153408081 808805972045865865056061)
                    ·
                      refine ⟨303302239517199699396023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 808805972045865865056061 303302239517199699396023)
                      ·
                        rfl

theorem cell23_590679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 2, 1, 2, 3].length) (baseStart_590679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_590679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_590679 prefixEnd_590679 := by exact prefixLift 590679
  have htrace : WordTrace (prefixWord ++ tailWord_590679) baseStart_590679 baseEnd_590679 := by
    simpa [prefixWord, tailWord_590679, baseEnd_590679] using wordTrace_append hprefix tailTrace_590679
  have hstable : (prefixWord ++ tailWord_590679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590679).length < 2 ^ (prefixWord ++ tailWord_590679).sum := by decide
  have hdescent : baseEnd_590679 < baseStart_590679 := by decide
  rcases family_descends (prefixWord ++ tailWord_590679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590692 : List Nat := [2, 3, 1, 1, 4, 2, 1, 2, 1, 3, 3]
def baseStart_590692 : Nat := 118140960795 + 590692 * 2 ^ 59
def prefixEnd_590692 : Nat := 4983230072969 + 3 ^ 40 * 590692 * 2
def baseEnd_590692 : Nat := 303308914765708148533463

theorem tailTrace_590692 : CollatzResearch.WordTrace tailWord_590692 prefixEnd_590692 303308914765708148533463 := by
  unfold tailWord_590692
  simp only [CollatzResearch.WordTrace]
  refine ⟨10772153588015620503535165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14362871450687494004713553 10772153588015620503535165)
  ·
    refine ⟨4039557595505857688825687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10772153588015620503535165 4039557595505857688825687)
    ·
      refine ⟨6059336393258786533238531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4039557595505857688825687 6059336393258786533238531)
      ·
        refine ⟨9089004589888179799857797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6059336393258786533238531 9089004589888179799857797)
        ·
          refine ⟨1704188360604033712473337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9089004589888179799857797 1704188360604033712473337)
          ·
            refine ⟨1278141270453025284355003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1704188360604033712473337 1278141270453025284355003)
            ·
              refine ⟨1917211905679537926532505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1278141270453025284355003 1917211905679537926532505)
              ·
                refine ⟨1437908929259653444899379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1917211905679537926532505 1437908929259653444899379)
                ·
                  refine ⟨2156863393889480167349069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1437908929259653444899379 2156863393889480167349069)
                  ·
                    refine ⟨808823772708555062755901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2156863393889480167349069 808823772708555062755901)
                    ·
                      refine ⟨303308914765708148533463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 808823772708555062755901 303308914765708148533463)
                      ·
                        rfl

theorem cell23_590692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 2, 1, 3, 3].length) (baseStart_590692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_590692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_590692 prefixEnd_590692 := by exact prefixLift 590692
  have htrace : WordTrace (prefixWord ++ tailWord_590692) baseStart_590692 baseEnd_590692 := by
    simpa [prefixWord, tailWord_590692, baseEnd_590692] using wordTrace_append hprefix tailTrace_590692
  have hstable : (prefixWord ++ tailWord_590692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590692).length < 2 ^ (prefixWord ++ tailWord_590692).sum := by decide
  have hdescent : baseEnd_590692 < baseStart_590692 := by decide
  rcases family_descends (prefixWord ++ tailWord_590692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590709 : List Nat := [1, 3, 4, 1, 1, 2, 1, 4, 2, 1, 3]
def baseStart_590709 : Nat := 118140960795 + 590709 * 2 ^ 59
def prefixEnd_590709 : Nat := 4983230072969 + 3 ^ 40 * 590709 * 2
def baseEnd_590709 : Nat := 303317643936834582020885

theorem tailTrace_590709 : CollatzResearch.WordTrace tailWord_590709 prefixEnd_590709 303317643936834582020885 := by
  unfold tailWord_590709
  simp only [CollatzResearch.WordTrace]
  refine ⟨21544927216969652910439181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14363284811313101940292787 21544927216969652910439181)
  ·
    refine ⟨8079347706363619841414693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21544927216969652910439181 8079347706363619841414693)
    ·
      refine ⟨1514877694943178720265255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8079347706363619841414693 1514877694943178720265255)
      ·
        refine ⟨2272316542414768080397883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1514877694943178720265255 2272316542414768080397883)
        ·
          refine ⟨3408474813622152120596825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2272316542414768080397883 3408474813622152120596825)
          ·
            refine ⟨2556356110216614090447619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3408474813622152120596825 2556356110216614090447619)
            ·
              refine ⟨3834534165324921135671429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2556356110216614090447619 3834534165324921135671429)
              ·
                refine ⟨718975155998422712938393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3834534165324921135671429 718975155998422712938393)
                ·
                  refine ⟨539231366998817034703795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 718975155998422712938393 539231366998817034703795)
                  ·
                    refine ⟨808847050498225552055693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 539231366998817034703795 808847050498225552055693)
                    ·
                      refine ⟨303317643936834582020885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 808847050498225552055693 303317643936834582020885)
                      ·
                        rfl

theorem cell23_590709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_590709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_590709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_590709 prefixEnd_590709 := by exact prefixLift 590709
  have htrace : WordTrace (prefixWord ++ tailWord_590709) baseStart_590709 baseEnd_590709 := by
    simpa [prefixWord, tailWord_590709, baseEnd_590709] using wordTrace_append hprefix tailTrace_590709
  have hstable : (prefixWord ++ tailWord_590709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590709).length < 2 ^ (prefixWord ++ tailWord_590709).sum := by decide
  have hdescent : baseEnd_590709 < baseStart_590709 := by decide
  rcases family_descends (prefixWord ++ tailWord_590709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590710 : List Nat := [5, 1, 1, 3, 1, 1, 4, 2, 1, 2, 2]
def baseStart_590710 : Nat := 118140960795 + 590710 * 2 ^ 59
def prefixEnd_590710 : Nat := 4983230072969 + 3 ^ 40 * 590710 * 2
def baseEnd_590710 : Nat := 303318157417489078108381

theorem tailTrace_590710 : CollatzResearch.WordTrace tailWord_590710 prefixEnd_590710 303318157417489078108381 := by
  unfold tailWord_590710
  simp only [CollatzResearch.WordTrace]
  refine ⟨1346560230622876880076599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14363309126644020054150389 1346560230622876880076599)
  ·
    refine ⟨2019840345934315320114899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1346560230622876880076599 2019840345934315320114899)
    ·
      refine ⟨3029760518901472980172349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2019840345934315320114899 3029760518901472980172349)
      ·
        refine ⟨1136160194588052367564631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3029760518901472980172349 1136160194588052367564631)
        ·
          refine ⟨1704240291882078551346947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1136160194588052367564631 1704240291882078551346947)
          ·
            refine ⟨2556360437823117827020421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1704240291882078551346947 2556360437823117827020421)
            ·
              refine ⟨479317582091834592566329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2556360437823117827020421 479317582091834592566329)
              ·
                refine ⟨359488186568875944424747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 479317582091834592566329 359488186568875944424747)
                ·
                  refine ⟨539232279853313916637121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 359488186568875944424747 539232279853313916637121)
                  ·
                    refine ⟨404424209889985437477841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 539232279853313916637121 404424209889985437477841)
                    ·
                      refine ⟨303318157417489078108381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 404424209889985437477841 303318157417489078108381)
                      ·
                        rfl

theorem cell23_590710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_590710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_590710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_590710 prefixEnd_590710 := by exact prefixLift 590710
  have htrace : WordTrace (prefixWord ++ tailWord_590710) baseStart_590710 baseEnd_590710 := by
    simpa [prefixWord, tailWord_590710, baseEnd_590710] using wordTrace_append hprefix tailTrace_590710
  have hstable : (prefixWord ++ tailWord_590710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590710).length < 2 ^ (prefixWord ++ tailWord_590710).sum := by decide
  have hdescent : baseEnd_590710 < baseStart_590710 := by decide
  rcases family_descends (prefixWord ++ tailWord_590710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590725 : List Nat := [1, 3, 1, 1, 3, 4, 1, 1, 2, 6]
def baseStart_590725 : Nat := 118140960795 + 590725 * 2 ^ 59
def prefixEnd_590725 : Nat := 4983230072969 + 3 ^ 40 * 590725 * 2
def baseEnd_590725 : Nat := 101108619875768839806937

theorem tailTrace_590725 : CollatzResearch.WordTrace tailWord_590725 prefixEnd_590725 101108619875768839806937 := by
  unfold tailWord_590725
  simp only [CollatzResearch.WordTrace]
  refine ⟨21545510784911687643021629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14363673856607791762014419 21545510784911687643021629)
  ·
    refine ⟨8079566544341882866133111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21545510784911687643021629 8079566544341882866133111)
    ·
      refine ⟨12119349816512824299199667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8079566544341882866133111 12119349816512824299199667)
      ·
        refine ⟨18179024724769236448799501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12119349816512824299199667 18179024724769236448799501)
        ·
          refine ⟨6817134271788463668299813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18179024724769236448799501 6817134271788463668299813)
          ·
            refine ⟨1278212675960336937806215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6817134271788463668299813 1278212675960336937806215)
            ·
              refine ⟨1917319013940505406709323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1278212675960336937806215 1917319013940505406709323)
              ·
                refine ⟨2875978520910758110063985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1917319013940505406709323 2875978520910758110063985)
                ·
                  refine ⟨2156983890683068582547989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2875978520910758110063985 2156983890683068582547989)
                  ·
                    refine ⟨101108619875768839806937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2156983890683068582547989 101108619875768839806937)
                    ·
                      rfl

theorem cell23_590725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 2, 6].length) (baseStart_590725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_590725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_590725 prefixEnd_590725 := by exact prefixLift 590725
  have htrace : WordTrace (prefixWord ++ tailWord_590725) baseStart_590725 baseEnd_590725 := by
    simpa [prefixWord, tailWord_590725, baseEnd_590725] using wordTrace_append hprefix tailTrace_590725
  have hstable : (prefixWord ++ tailWord_590725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590725).length < 2 ^ (prefixWord ++ tailWord_590725).sum := by decide
  have hdescent : baseEnd_590725 < baseStart_590725 := by decide
  rcases family_descends (prefixWord ++ tailWord_590725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590732 : List Nat := [2, 2, 1, 2, 1, 2, 3, 3, 1, 4, 2]
def baseStart_590732 : Nat := 118140960795 + 590732 * 2 ^ 59
def prefixEnd_590732 : Nat := 4983230072969 + 3 ^ 40 * 590732 * 2
def baseEnd_590732 : Nat := 303329453991887992033279

theorem tailTrace_590732 : CollatzResearch.WordTrace tailWord_590732 prefixEnd_590732 303329453991887992033279 := by
  unfold tailWord_590732
  simp only [CollatzResearch.WordTrace]
  refine ⟨10772883047943163919263225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14363844063924218559017633 10772883047943163919263225)
  ·
    refine ⟨8079662285957372939447419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10772883047943163919263225 8079662285957372939447419)
    ·
      refine ⟨12119493428936059409171129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8079662285957372939447419 12119493428936059409171129)
      ·
        refine ⟨9089620071702044556878347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12119493428936059409171129 9089620071702044556878347)
        ·
          refine ⟨13634430107553066835317521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9089620071702044556878347 13634430107553066835317521)
          ·
            refine ⟨10225822580664800126488141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13634430107553066835317521 10225822580664800126488141)
            ·
              refine ⟨3834683467749300047433053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10225822580664800126488141 3834683467749300047433053)
              ·
                refine ⟨1438006300405987517787395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3834683467749300047433053 1438006300405987517787395)
                ·
                  refine ⟨2157009450608981276681093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1438006300405987517787395 2157009450608981276681093)
                  ·
                    refine ⟨404439271989183989377705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2157009450608981276681093 404439271989183989377705)
                    ·
                      refine ⟨303329453991887992033279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 404439271989183989377705 303329453991887992033279)
                      ·
                        rfl

theorem cell23_590732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 3, 1, 4, 2].length) (baseStart_590732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_590732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_590732 prefixEnd_590732 := by exact prefixLift 590732
  have htrace : WordTrace (prefixWord ++ tailWord_590732) baseStart_590732 baseEnd_590732 := by
    simpa [prefixWord, tailWord_590732, baseEnd_590732] using wordTrace_append hprefix tailTrace_590732
  have hstable : (prefixWord ++ tailWord_590732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590732).length < 2 ^ (prefixWord ++ tailWord_590732).sum := by decide
  have hdescent : baseEnd_590732 < baseStart_590732 := by decide
  rcases family_descends (prefixWord ++ tailWord_590732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590749 : List Nat := [1, 4, 2, 1, 2, 1, 2, 2, 4, 2, 2]
def baseStart_590749 : Nat := 118140960795 + 590749 * 2 ^ 59
def prefixEnd_590749 : Nat := 4983230072969 + 3 ^ 40 * 590749 * 2
def baseEnd_590749 : Nat := 303338183163014425520701

theorem tailTrace_590749 : CollatzResearch.WordTrace tailWord_590749 prefixEnd_590749 303338183163014425520701 := by
  unfold tailWord_590749
  simp only [CollatzResearch.WordTrace]
  refine ⟨21546386136824739741895301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14364257424549826494596867 21546386136824739741895301)
  ·
    refine ⟨4039947400654638701605369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21546386136824739741895301 4039947400654638701605369)
    ·
      refine ⟨3029960550490979026204027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4039947400654638701605369 3029960550490979026204027)
      ·
        refine ⟨4544940825736468539306041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3029960550490979026204027 4544940825736468539306041)
        ·
          refine ⟨3408705619302351404479531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4544940825736468539306041 3408705619302351404479531)
          ·
            refine ⟨5113058428953527106719297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3408705619302351404479531 5113058428953527106719297)
            ·
              refine ⟨3834793821715145330039473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5113058428953527106719297 3834793821715145330039473)
              ·
                refine ⟨2876095366286358997529605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3834793821715145330039473 2876095366286358997529605)
                ·
                  refine ⟨539267881178692312036801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2876095366286358997529605 539267881178692312036801)
                  ·
                    refine ⟨404450910884019234027601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 539267881178692312036801 404450910884019234027601)
                    ·
                      refine ⟨303338183163014425520701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 404450910884019234027601 303338183163014425520701)
                      ·
                        rfl

theorem cell23_590749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 4, 2, 2].length) (baseStart_590749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_590749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_590749 prefixEnd_590749 := by exact prefixLift 590749
  have htrace : WordTrace (prefixWord ++ tailWord_590749) baseStart_590749 baseEnd_590749 := by
    simpa [prefixWord, tailWord_590749, baseEnd_590749] using wordTrace_append hprefix tailTrace_590749
  have hstable : (prefixWord ++ tailWord_590749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590749).length < 2 ^ (prefixWord ++ tailWord_590749).sum := by decide
  have hdescent : baseEnd_590749 < baseStart_590749 := by decide
  rcases family_descends (prefixWord ++ tailWord_590749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590753 : List Nat := [1, 2, 3, 4, 1, 3, 2, 1, 1, 3, 2]
def baseStart_590753 : Nat := 118140960795 + 590753 * 2 ^ 59
def prefixEnd_590753 : Nat := 4983230072969 + 3 ^ 40 * 590753 * 2
def baseEnd_590753 : Nat := 303340237085632409870683

theorem tailTrace_590753 : CollatzResearch.WordTrace tailWord_590753 prefixEnd_590753 303340237085632409870683 := by
  unfold tailWord_590753
  simp only [CollatzResearch.WordTrace]
  refine ⟨21546532028810248425040913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14364354685873498950027275 21546532028810248425040913)
  ·
    refine ⟨16159899021607686318780685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21546532028810248425040913 16159899021607686318780685)
    ·
      refine ⟨6059962133102882369542757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16159899021607686318780685 6059962133102882369542757)
      ·
        refine ⟨1136242899956790444289267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6059962133102882369542757 1136242899956790444289267)
        ·
          refine ⟨1704364349935185666433901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1136242899956790444289267 1704364349935185666433901)
          ·
            refine ⟨639136631225694624912713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1704364349935185666433901 639136631225694624912713)
            ·
              refine ⟨479352473419270968684535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 639136631225694624912713 479352473419270968684535)
              ·
                refine ⟨719028710128906453026803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 479352473419270968684535 719028710128906453026803)
                ·
                  refine ⟨1078543065193359679540205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 719028710128906453026803 1078543065193359679540205)
                  ·
                    refine ⟨404453649447509879827577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1078543065193359679540205 404453649447509879827577)
                    ·
                      refine ⟨303340237085632409870683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 404453649447509879827577 303340237085632409870683)
                      ·
                        rfl

theorem cell23_590753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_590753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_590753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_590753 prefixEnd_590753 := by exact prefixLift 590753
  have htrace : WordTrace (prefixWord ++ tailWord_590753) baseStart_590753 baseEnd_590753 := by
    simpa [prefixWord, tailWord_590753, baseEnd_590753] using wordTrace_append hprefix tailTrace_590753
  have hstable : (prefixWord ++ tailWord_590753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590753).length < 2 ^ (prefixWord ++ tailWord_590753).sum := by decide
  have hdescent : baseEnd_590753 < baseStart_590753 := by decide
  rcases family_descends (prefixWord ++ tailWord_590753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590782 : List Nat := [4, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3]
def baseStart_590782 : Nat := 118140960795 + 590782 * 2 ^ 59
def prefixEnd_590782 : Nat := 4983230072969 + 3 ^ 40 * 590782 * 2
def baseEnd_590782 : Nat := 303355128024612796408049

theorem tailTrace_590782 : CollatzResearch.WordTrace tailWord_590782 prefixEnd_590782 303355128024612796408049 := by
  unfold tailWord_590782
  simp only [CollatzResearch.WordTrace]
  refine ⟨2693448718213148297230825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14365059830470124251897733 2693448718213148297230825)
  ·
    refine ⟨2020086538659861222923119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2693448718213148297230825 2020086538659861222923119)
    ·
      refine ⟨3030129807989791834384679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2020086538659861222923119 3030129807989791834384679)
      ·
        refine ⟨4545194711984687751577019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3030129807989791834384679 4545194711984687751577019)
        ·
          refine ⟨6817792067977031627365529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4545194711984687751577019 6817792067977031627365529)
          ·
            refine ⟨5113344050982773720524147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6817792067977031627365529 5113344050982773720524147)
            ·
              refine ⟨7670016076474160580786221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5113344050982773720524147 7670016076474160580786221)
              ·
                refine ⟨2876256028677810217794833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7670016076474160580786221 2876256028677810217794833)
                ·
                  refine ⟨2157192021508357663346125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2876256028677810217794833 2157192021508357663346125)
                  ·
                    refine ⟨808947008065634123754797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2157192021508357663346125 808947008065634123754797)
                    ·
                      refine ⟨303355128024612796408049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 808947008065634123754797 303355128024612796408049)
                      ·
                        rfl

theorem cell23_590782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3].length) (baseStart_590782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_590782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_590782 prefixEnd_590782 := by exact prefixLift 590782
  have htrace : WordTrace (prefixWord ++ tailWord_590782) baseStart_590782 baseEnd_590782 := by
    simpa [prefixWord, tailWord_590782, baseEnd_590782] using wordTrace_append hprefix tailTrace_590782
  have hstable : (prefixWord ++ tailWord_590782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590782).length < 2 ^ (prefixWord ++ tailWord_590782).sum := by decide
  have hdescent : baseEnd_590782 < baseStart_590782 := by decide
  rcases family_descends (prefixWord ++ tailWord_590782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590802 : List Nat := [3, 2, 2, 3, 1, 1, 2, 1, 1, 7]
def baseStart_590802 : Nat := 118140960795 + 590802 * 2 ^ 59
def prefixEnd_590802 : Nat := 4983230072969 + 3 ^ 40 * 590802 * 2
def baseEnd_590802 : Nat := 101121799212567572719319

theorem tailTrace_590802 : CollatzResearch.WordTrace tailWord_590802 prefixEnd_590802 101121799212567572719319 := by
  unfold tailWord_590802
  simp only [CollatzResearch.WordTrace]
  refine ⟨5387079801408182448393665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14365546137088486529049773 5387079801408182448393665)
  ·
    refine ⟨4040309851056136836295249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5387079801408182448393665 4040309851056136836295249)
    ·
      refine ⟨3030232388292102627221437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4040309851056136836295249 3030232388292102627221437)
      ·
        refine ⟨1136337145609538485208039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3030232388292102627221437 1136337145609538485208039)
        ·
          refine ⟨1704505718414307727812059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1136337145609538485208039 1704505718414307727812059)
          ·
            refine ⟨2556758577621461591718089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1704505718414307727812059 2556758577621461591718089)
            ·
              refine ⟨1917568933216096193788567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2556758577621461591718089 1917568933216096193788567)
              ·
                refine ⟨2876353399824144290682851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1917568933216096193788567 2876353399824144290682851)
                ·
                  refine ⟨4314530099736216436024277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2876353399824144290682851 4314530099736216436024277)
                  ·
                    refine ⟨101121799212567572719319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4314530099736216436024277 101121799212567572719319)
                    ·
                      rfl

theorem cell23_590802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_590802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_590802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_590802 prefixEnd_590802 := by exact prefixLift 590802
  have htrace : WordTrace (prefixWord ++ tailWord_590802) baseStart_590802 baseEnd_590802 := by
    simpa [prefixWord, tailWord_590802, baseEnd_590802] using wordTrace_append hprefix tailTrace_590802
  have hstable : (prefixWord ++ tailWord_590802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590802).length < 2 ^ (prefixWord ++ tailWord_590802).sum := by decide
  have hdescent : baseEnd_590802 < baseStart_590802 := by decide
  rcases family_descends (prefixWord ++ tailWord_590802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590806 : List Nat := [5, 2, 1, 1, 2, 1, 3, 3, 5]
def baseStart_590806 : Nat := 118140960795 + 590806 * 2 ^ 59
def prefixEnd_590806 : Nat := 4983230072969 + 3 ^ 40 * 590806 * 2
def baseEnd_590806 : Nat := 33707494617813411389771

theorem tailTrace_590806 : CollatzResearch.WordTrace tailWord_590806 prefixEnd_590806 33707494617813411389771 := by
  unfold tailWord_590806
  simp only [CollatzResearch.WordTrace]
  refine ⟨1346779068601139904795017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14365643398412158984480181 1346779068601139904795017)
  ·
    refine ⟨1010084301450854928596263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1346779068601139904795017 1010084301450854928596263)
    ·
      refine ⟨1515126452176282392894395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1010084301450854928596263 1515126452176282392894395)
      ·
        refine ⟨2272689678264423589341593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1515126452176282392894395 2272689678264423589341593)
        ·
          refine ⟨1704517258698317692006195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2272689678264423589341593 1704517258698317692006195)
          ·
            refine ⟨2556775888047476538009293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1704517258698317692006195 2556775888047476538009293)
            ·
              refine ⟨958790958017803701753485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2556775888047476538009293 958790958017803701753485)
              ·
                refine ⟨359546609256676388157557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 958790958017803701753485 359546609256676388157557)
                ·
                  refine ⟨33707494617813411389771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 359546609256676388157557 33707494617813411389771)
                  ·
                    rfl

theorem cell23_590806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_590806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_590806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_590806 prefixEnd_590806 := by exact prefixLift 590806
  have htrace : WordTrace (prefixWord ++ tailWord_590806) baseStart_590806 baseEnd_590806 := by
    simpa [prefixWord, tailWord_590806, baseEnd_590806] using wordTrace_append hprefix tailTrace_590806
  have hstable : (prefixWord ++ tailWord_590806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590806).length < 2 ^ (prefixWord ++ tailWord_590806).sum := by decide
  have hdescent : baseEnd_590806 < baseStart_590806 := by decide
  rcases family_descends (prefixWord ++ tailWord_590806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590825 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 2, 8, 3]
def baseStart_590825 : Nat := 118140960795 + 590825 * 2 ^ 59
def prefixEnd_590825 : Nat := 4983230072969 + 3 ^ 40 * 590825 * 2
def baseEnd_590825 : Nat := 303377207692756128170351

theorem tailTrace_590825 : CollatzResearch.WordTrace tailWord_590825 prefixEnd_590825 303377207692756128170351 := by
  unfold tailWord_590825
  simp only [CollatzResearch.WordTrace]
  refine ⟨21549158084549404721661929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14366105389699603147774619 21549158084549404721661929)
  ·
    refine ⟨16161868563412053541246447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21549158084549404721661929 16161868563412053541246447)
    ·
      refine ⟨24242802845118080311869671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16161868563412053541246447 24242802845118080311869671)
      ·
        refine ⟨36364204267677120467804507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24242802845118080311869671 36364204267677120467804507)
        ·
          refine ⟨54546306401515680701706761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36364204267677120467804507 54546306401515680701706761)
          ·
            refine ⟨40909729801136760526280071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54546306401515680701706761 40909729801136760526280071)
            ·
              refine ⟨61364594701705140789420107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40909729801136760526280071 61364594701705140789420107)
              ·
                refine ⟨92046892052557711184130161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61364594701705140789420107 92046892052557711184130161)
                ·
                  refine ⟨69035169039418283388097621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 92046892052557711184130161 69035169039418283388097621)
                  ·
                    refine ⟨809005887180683008454269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 69035169039418283388097621 809005887180683008454269)
                    ·
                      refine ⟨303377207692756128170351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 809005887180683008454269 303377207692756128170351)
                      ·
                        rfl

theorem cell23_590825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 8, 3].length) (baseStart_590825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_590825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_590825 prefixEnd_590825 := by exact prefixLift 590825
  have htrace : WordTrace (prefixWord ++ tailWord_590825) baseStart_590825 baseEnd_590825 := by
    simpa [prefixWord, tailWord_590825, baseEnd_590825] using wordTrace_append hprefix tailTrace_590825
  have hstable : (prefixWord ++ tailWord_590825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590825).length < 2 ^ (prefixWord ++ tailWord_590825).sum := by decide
  have hdescent : baseEnd_590825 < baseStart_590825 := by decide
  rcases family_descends (prefixWord ++ tailWord_590825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590859 : List Nat := [1, 1, 1, 1, 6, 3, 2, 1, 2, 2, 3]
def baseStart_590859 : Nat := 118140960795 + 590859 * 2 ^ 59
def prefixEnd_590859 : Nat := 4983230072969 + 3 ^ 40 * 590859 * 2
def baseEnd_590859 : Nat := 303394666035008995145195

theorem tailTrace_590859 : CollatzResearch.WordTrace tailWord_590859 prefixEnd_590859 303394666035008995145195 := by
  unfold tailWord_590859
  simp only [CollatzResearch.WordTrace]
  refine ⟨21550398166426228528399631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14366932110950819018933087 21550398166426228528399631)
  ·
    refine ⟨32325597249639342792599447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21550398166426228528399631 32325597249639342792599447)
    ·
      refine ⟨48488395874459014188899171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32325597249639342792599447 48488395874459014188899171)
      ·
        refine ⟨72732593811688521283348757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48488395874459014188899171 72732593811688521283348757)
        ·
          refine ⟨3409340334922899435156973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 72732593811688521283348757 3409340334922899435156973)
          ·
            refine ⟨1278502625596087288183865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3409340334922899435156973 1278502625596087288183865)
            ·
              refine ⟨958876969197065466137899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1278502625596087288183865 958876969197065466137899)
              ·
                refine ⟨1438315453795598199206849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 958876969197065466137899 1438315453795598199206849)
                ·
                  refine ⟨1078736590346698649405137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1438315453795598199206849 1078736590346698649405137)
                  ·
                    refine ⟨809052442760023987053853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1078736590346698649405137 809052442760023987053853)
                    ·
                      refine ⟨303394666035008995145195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 809052442760023987053853 303394666035008995145195)
                      ·
                        rfl

theorem cell23_590859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 1, 2, 2, 3].length) (baseStart_590859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_590859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_590859 prefixEnd_590859 := by exact prefixLift 590859
  have htrace : WordTrace (prefixWord ++ tailWord_590859) baseStart_590859 baseEnd_590859 := by
    simpa [prefixWord, tailWord_590859, baseEnd_590859] using wordTrace_append hprefix tailTrace_590859
  have hstable : (prefixWord ++ tailWord_590859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590859).length < 2 ^ (prefixWord ++ tailWord_590859).sum := by decide
  have hdescent : baseEnd_590859 < baseStart_590859 := by decide
  rcases family_descends (prefixWord ++ tailWord_590859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590883 : List Nat := [1, 1, 1, 4, 3, 4, 2, 2, 1, 4]
def baseStart_590883 : Nat := 118140960795 + 590883 * 2 ^ 59
def prefixEnd_590883 : Nat := 4983230072969 + 3 ^ 40 * 590883 * 2
def baseEnd_590883 : Nat := 101135663190238967081695

theorem tailTrace_590883 : CollatzResearch.WordTrace tailWord_590883 prefixEnd_590883 101135663190238967081695 := by
  unfold tailWord_590883
  simp only [CollatzResearch.WordTrace]
  refine ⟨21551273518339280627273303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14367515678892853751515535 21551273518339280627273303)
  ·
    refine ⟨32326910277508920940909955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21551273518339280627273303 32326910277508920940909955)
    ·
      refine ⟨48490365416263381411364933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32326910277508920940909955 48490365416263381411364933)
      ·
        refine ⟨9091943515549384014630925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48490365416263381411364933 9091943515549384014630925)
        ·
          refine ⟨3409478818331019005486597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9091943515549384014630925 3409478818331019005486597)
          ·
            refine ⟨639277278437066063528737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3409478818331019005486597 639277278437066063528737)
            ·
              refine ⟨479457958827799547646553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 639277278437066063528737 479457958827799547646553)
              ·
                refine ⟨359593469120849660734915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 479457958827799547646553 359593469120849660734915)
                ·
                  refine ⟨539390203681274491102373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 359593469120849660734915 539390203681274491102373)
                  ·
                    refine ⟨101135663190238967081695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 539390203681274491102373 101135663190238967081695)
                    ·
                      rfl

theorem cell23_590883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 2, 2, 1, 4].length) (baseStart_590883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_590883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_590883 prefixEnd_590883 := by exact prefixLift 590883
  have htrace : WordTrace (prefixWord ++ tailWord_590883) baseStart_590883 baseEnd_590883 := by
    simpa [prefixWord, tailWord_590883, baseEnd_590883] using wordTrace_append hprefix tailTrace_590883
  have hstable : (prefixWord ++ tailWord_590883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590883).length < 2 ^ (prefixWord ++ tailWord_590883).sum := by decide
  have hdescent : baseEnd_590883 < baseStart_590883 := by decide
  rcases family_descends (prefixWord ++ tailWord_590883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590912 : List Nat := [2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 4]
def baseStart_590912 : Nat := 118140960795 + 590912 * 2 ^ 59
def prefixEnd_590912 : Nat := 4983230072969 + 3 ^ 40 * 590912 * 2
def baseEnd_590912 : Nat := 303421880509697287782451

theorem tailTrace_590912 : CollatzResearch.WordTrace tailWord_590912 prefixEnd_590912 303421880509697287782451 := by
  unfold tailWord_590912
  simp only [CollatzResearch.WordTrace]
  refine ⟨10776165617617109290039495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14368220823489479053385993 10776165617617109290039495)
  ·
    refine ⟨16164248426425663935059243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10776165617617109290039495 16164248426425663935059243)
    ·
      refine ⟨24246372639638495902588865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16164248426425663935059243 24246372639638495902588865)
      ·
        refine ⟨18184779479728871926941649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24246372639638495902588865 18184779479728871926941649)
        ·
          refine ⟨13638584609796653945206237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18184779479728871926941649 13638584609796653945206237)
          ·
            refine ⟨5114469228673745229452339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13638584609796653945206237 5114469228673745229452339)
            ·
              refine ⟨7671703843010617844178509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5114469228673745229452339 7671703843010617844178509)
              ·
                refine ⟨2876888941128981691566941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7671703843010617844178509 2876888941128981691566941)
                ·
                  refine ⟨1078833352923368134337603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2876888941128981691566941 1078833352923368134337603)
                  ·
                    refine ⟨1618250029385052201506405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1078833352923368134337603 1618250029385052201506405)
                    ·
                      refine ⟨303421880509697287782451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1618250029385052201506405 303421880509697287782451)
                      ·
                        rfl

theorem cell23_590912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 4].length) (baseStart_590912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_590912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_590912 prefixEnd_590912 := by exact prefixLift 590912
  have htrace : WordTrace (prefixWord ++ tailWord_590912) baseStart_590912 baseEnd_590912 := by
    simpa [prefixWord, tailWord_590912, baseEnd_590912] using wordTrace_append hprefix tailTrace_590912
  have hstable : (prefixWord ++ tailWord_590912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590912).length < 2 ^ (prefixWord ++ tailWord_590912).sum := by decide
  have hdescent : baseEnd_590912 < baseStart_590912 := by decide
  rcases family_descends (prefixWord ++ tailWord_590912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590922 : List Nat := [3, 1, 2, 1, 1, 2, 4, 2, 1, 6]
def baseStart_590922 : Nat := 118140960795 + 590922 * 2 ^ 59
def prefixEnd_590922 : Nat := 4983230072969 + 3 ^ 40 * 590922 * 2
def baseEnd_590922 : Nat := 101142338438747416219135

theorem tailTrace_590922 : CollatzResearch.WordTrace tailWord_590922 prefixEnd_590922 101142338438747416219135 := by
  unfold tailWord_590922
  simp only [CollatzResearch.WordTrace]
  refine ⟨5388173991299497571985755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14368463976798660191962013 5388173991299497571985755)
  ·
    refine ⟨8082260986949246357978633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5388173991299497571985755 8082260986949246357978633)
    ·
      refine ⟨6061695740211934768483975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8082260986949246357978633 6061695740211934768483975)
      ·
        refine ⟨9092543610317902152725963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6061695740211934768483975 9092543610317902152725963)
        ·
          refine ⟨13638815415476853229088945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9092543610317902152725963 13638815415476853229088945)
          ·
            refine ⟨10229111561607639921816709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13638815415476853229088945 10229111561607639921816709)
            ·
              refine ⟨1917958417801432485340633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10229111561607639921816709 1917958417801432485340633)
              ·
                refine ⟨1438468813351074364005475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1917958417801432485340633 1438468813351074364005475)
                ·
                  refine ⟨2157703220026611546008213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1438468813351074364005475 2157703220026611546008213)
                  ·
                    refine ⟨101142338438747416219135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2157703220026611546008213 101142338438747416219135)
                    ·
                      rfl

theorem cell23_590922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 2, 1, 6].length) (baseStart_590922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_590922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_590922 prefixEnd_590922 := by exact prefixLift 590922
  have htrace : WordTrace (prefixWord ++ tailWord_590922) baseStart_590922 baseEnd_590922 := by
    simpa [prefixWord, tailWord_590922, baseEnd_590922] using wordTrace_append hprefix tailTrace_590922
  have hstable : (prefixWord ++ tailWord_590922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590922).length < 2 ^ (prefixWord ++ tailWord_590922).sum := by decide
  have hdescent : baseEnd_590922 < baseStart_590922 := by decide
  rcases family_descends (prefixWord ++ tailWord_590922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590956 : List Nat := [2, 2, 1, 1, 3, 2, 5, 1, 2, 4]
def baseStart_590956 : Nat := 118140960795 + 590956 * 2 ^ 59
def prefixEnd_590956 : Nat := 4983230072969 + 3 ^ 40 * 590956 * 2
def baseEnd_590956 : Nat := 101148157886165038544083

theorem tailTrace_590956 : CollatzResearch.WordTrace tailWord_590956 prefixEnd_590956 101148157886165038544083 := by
  unfold tailWord_590956
  simp only [CollatzResearch.WordTrace]
  refine ⟨10776968023537407047340361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14369290698049876063120481 10776968023537407047340361)
  ·
    refine ⟨8082726017653055285505271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10776968023537407047340361 8082726017653055285505271)
    ·
      refine ⟨12124089026479582928257907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8082726017653055285505271 12124089026479582928257907)
      ·
        refine ⟨18186133539719374392386861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12124089026479582928257907 18186133539719374392386861)
        ·
          refine ⟨6819800077394765397145073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18186133539719374392386861 6819800077394765397145073)
          ·
            refine ⟨5114850058046074047858805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6819800077394765397145073 5114850058046074047858805)
            ·
              refine ⟨479517192941819441986763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5114850058046074047858805 479517192941819441986763)
              ·
                refine ⟨719275789412729162980145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 479517192941819441986763 719275789412729162980145)
                ·
                  refine ⟨539456842059546872235109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 719275789412729162980145 539456842059546872235109)
                  ·
                    refine ⟨101148157886165038544083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 539456842059546872235109 101148157886165038544083)
                    ·
                      rfl

theorem cell23_590956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 4].length) (baseStart_590956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_590956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_590956 prefixEnd_590956 := by exact prefixLift 590956
  have htrace : WordTrace (prefixWord ++ tailWord_590956) baseStart_590956 baseEnd_590956 := by
    simpa [prefixWord, tailWord_590956, baseEnd_590956] using wordTrace_append hprefix tailTrace_590956
  have hstable : (prefixWord ++ tailWord_590956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590956).length < 2 ^ (prefixWord ++ tailWord_590956).sum := by decide
  have hdescent : baseEnd_590956 < baseStart_590956 := by decide
  rcases family_descends (prefixWord ++ tailWord_590956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590979 : List Nat := [1, 1, 1, 3, 3, 2, 1, 1, 6, 1, 3]
def baseStart_590979 : Nat := 118140960795 + 590979 * 2 ^ 59
def prefixEnd_590979 : Nat := 4983230072969 + 3 ^ 40 * 590979 * 2
def baseEnd_590979 : Nat := 303456283713548525644643

theorem tailTrace_590979 : CollatzResearch.WordTrace tailWord_590979 prefixEnd_590979 303456283713548525644643 := by
  unfold tailWord_590979
  simp only [CollatzResearch.WordTrace]
  refine ⟨21554774925991489022767991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14369849950660992681845327 21554774925991489022767991)
  ·
    refine ⟨32332162388987233534151987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21554774925991489022767991 32332162388987233534151987)
    ·
      refine ⟨48498243583480850301227981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32332162388987233534151987 48498243583480850301227981)
      ·
        refine ⟨18186841343805318862960493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48498243583480850301227981 18186841343805318862960493)
        ·
          refine ⟨6820065503926994573610185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18186841343805318862960493 6820065503926994573610185)
          ·
            refine ⟨5115049127945245930207639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6820065503926994573610185 5115049127945245930207639)
            ·
              refine ⟨7672573691917868895311459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5115049127945245930207639 7672573691917868895311459)
              ·
                refine ⟨11508860537876803342967189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7672573691917868895311459 11508860537876803342967189)
                ·
                  refine ⟨539477837712975156701587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 11508860537876803342967189 539477837712975156701587)
                  ·
                    refine ⟨809216756569462735052381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 539477837712975156701587 809216756569462735052381)
                    ·
                      refine ⟨303456283713548525644643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 809216756569462735052381 303456283713548525644643)
                      ·
                        rfl

theorem cell23_590979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 6, 1, 3].length) (baseStart_590979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_590979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_590979 prefixEnd_590979 := by exact prefixLift 590979
  have htrace : WordTrace (prefixWord ++ tailWord_590979) baseStart_590979 baseEnd_590979 := by
    simpa [prefixWord, tailWord_590979, baseEnd_590979] using wordTrace_append hprefix tailTrace_590979
  have hstable : (prefixWord ++ tailWord_590979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590979).length < 2 ^ (prefixWord ++ tailWord_590979).sum := by decide
  have hdescent : baseEnd_590979 < baseStart_590979 := by decide
  rcases family_descends (prefixWord ++ tailWord_590979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590980 : List Nat := [2, 3, 2, 1, 2, 2, 3, 3, 1, 2, 2]
def baseStart_590980 : Nat := 118140960795 + 590980 * 2 ^ 59
def prefixEnd_590980 : Nat := 4983230072969 + 3 ^ 40 * 590980 * 2
def baseEnd_590980 : Nat := 303456797194203021732139

theorem tailTrace_590980 : CollatzResearch.WordTrace tailWord_590980 prefixEnd_590980 303456797194203021732139 := by
  unfold tailWord_590980
  simp only [CollatzResearch.WordTrace]
  refine ⟨10777405699493933096777197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14369874265991910795702929 10777405699493933096777197)
  ·
    refine ⟨4041527137310224911291449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10777405699493933096777197 4041527137310224911291449)
    ·
      refine ⟨3031145352982668683468587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4041527137310224911291449 3031145352982668683468587)
      ·
        refine ⟨4546718029474003025202881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3031145352982668683468587 4546718029474003025202881)
        ·
          refine ⟨3410038522105502268902161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4546718029474003025202881 3410038522105502268902161)
          ·
            refine ⟨2557528891579126701676621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3410038522105502268902161 2557528891579126701676621)
            ·
              refine ⟨959073334342172513128733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2557528891579126701676621 959073334342172513128733)
              ·
                refine ⟨359652500378314692423275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 959073334342172513128733 359652500378314692423275)
                ·
                  refine ⟨539478750567472038634913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 359652500378314692423275 539478750567472038634913)
                  ·
                    refine ⟨404609062925604028976185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 539478750567472038634913 404609062925604028976185)
                    ·
                      refine ⟨303456797194203021732139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 404609062925604028976185 303456797194203021732139)
                      ·
                        rfl

theorem cell23_590980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 3, 1, 2, 2].length) (baseStart_590980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_590980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_590980 prefixEnd_590980 := by exact prefixLift 590980
  have htrace : WordTrace (prefixWord ++ tailWord_590980) baseStart_590980 baseEnd_590980 := by
    simpa [prefixWord, tailWord_590980, baseEnd_590980] using wordTrace_append hprefix tailTrace_590980
  have hstable : (prefixWord ++ tailWord_590980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590980).length < 2 ^ (prefixWord ++ tailWord_590980).sum := by decide
  have hdescent : baseEnd_590980 < baseStart_590980 := by decide
  rcases family_descends (prefixWord ++ tailWord_590980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591013 : List Nat := [1, 3, 1, 2, 1, 4, 4, 1, 2, 1, 3]
def baseStart_591013 : Nat := 118140960795 + 591013 * 2 ^ 59
def prefixEnd_591013 : Nat := 4983230072969 + 3 ^ 40 * 591013 * 2
def baseEnd_591013 : Nat := 303473742055801392619487

theorem tailTrace_591013 : CollatzResearch.WordTrace tailWord_591013 prefixEnd_591013 303473742055801392619487 := by
  unfold tailWord_591013
  simp only [CollatzResearch.WordTrace]
  refine ⟨21556015007868312829505693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14370676671912208553003795 21556015007868312829505693)
  ·
    refine ⟨8083505627950617311064635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21556015007868312829505693 8083505627950617311064635)
    ·
      refine ⟨12125258441925925966596953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8083505627950617311064635 12125258441925925966596953)
      ·
        refine ⟨9093943831444444474947715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12125258441925925966596953 9093943831444444474947715)
        ·
          refine ⟨13640915747166666712421573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9093943831444444474947715 13640915747166666712421573)
          ·
            refine ⟨2557671702593750008579045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13640915747166666712421573 2557671702593750008579045)
            ·
              refine ⟨479563444236328126608571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2557671702593750008579045 479563444236328126608571)
              ·
                refine ⟨719345166354492189912857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 479563444236328126608571 719345166354492189912857)
                ·
                  refine ⟨539508874765869142434643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 719345166354492189912857 539508874765869142434643)
                  ·
                    refine ⟨809263312148803713651965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 539508874765869142434643 809263312148803713651965)
                    ·
                      refine ⟨303473742055801392619487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 809263312148803713651965 303473742055801392619487)
                      ·
                        rfl

theorem cell23_591013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 4, 1, 2, 1, 3].length) (baseStart_591013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_591013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_591013 prefixEnd_591013 := by exact prefixLift 591013
  have htrace : WordTrace (prefixWord ++ tailWord_591013) baseStart_591013 baseEnd_591013 := by
    simpa [prefixWord, tailWord_591013, baseEnd_591013] using wordTrace_append hprefix tailTrace_591013
  have hstable : (prefixWord ++ tailWord_591013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591013).length < 2 ^ (prefixWord ++ tailWord_591013).sum := by decide
  have hdescent : baseEnd_591013 < baseStart_591013 := by decide
  rcases family_descends (prefixWord ++ tailWord_591013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591030 : List Nat := [5, 1, 3, 2, 1, 1, 1, 2, 1, 3, 3]
def baseStart_591030 : Nat := 118140960795 + 591030 * 2 ^ 59
def prefixEnd_591030 : Nat := 4983230072969 + 3 ^ 40 * 591030 * 2
def baseEnd_591030 : Nat := 303482471226927826106909

theorem tailTrace_591030 : CollatzResearch.WordTrace tailWord_591030 prefixEnd_591030 303482471226927826106909 := by
  unfold tailWord_591030
  simp only [CollatzResearch.WordTrace]
  refine ⟨1347289690550420295804659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14371090032537816488583029 1347289690550420295804659)
  ·
    refine ⟨2020934535825630443706989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1347289690550420295804659 2020934535825630443706989)
    ·
      refine ⟨757850450934611416390121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2020934535825630443706989 757850450934611416390121)
      ·
        refine ⟨568387838200958562292591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 757850450934611416390121 568387838200958562292591)
        ·
          refine ⟨852581757301437843438887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 568387838200958562292591 852581757301437843438887)
          ·
            refine ⟨1278872635952156765158331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 852581757301437843438887 1278872635952156765158331)
            ·
              refine ⟨1918308953928235147737497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1278872635952156765158331 1918308953928235147737497)
              ·
                refine ⟨1438731715446176360803123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1918308953928235147737497 1438731715446176360803123)
                ·
                  refine ⟨2158097573169264541204685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1438731715446176360803123 2158097573169264541204685)
                  ·
                    refine ⟨809286589938474202951757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2158097573169264541204685 809286589938474202951757)
                    ·
                      refine ⟨303482471226927826106909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 809286589938474202951757 303482471226927826106909)
                      ·
                        rfl

theorem cell23_591030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_591030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_591030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_591030 prefixEnd_591030 := by exact prefixLift 591030
  have htrace : WordTrace (prefixWord ++ tailWord_591030) baseStart_591030 baseEnd_591030 := by
    simpa [prefixWord, tailWord_591030, baseEnd_591030] using wordTrace_append hprefix tailTrace_591030
  have hstable : (prefixWord ++ tailWord_591030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591030).length < 2 ^ (prefixWord ++ tailWord_591030).sum := by decide
  have hdescent : baseEnd_591030 < baseStart_591030 := by decide
  rcases family_descends (prefixWord ++ tailWord_591030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591032 : List Nat := [2, 1, 2, 1, 2, 1, 2, 1, 3, 4, 4]
def baseStart_591032 : Nat := 118140960795 + 591032 * 2 ^ 59
def prefixEnd_591032 : Nat := 4983230072969 + 3 ^ 40 * 591032 * 2
def baseEnd_591032 : Nat := 303483498188236818281899

theorem tailTrace_591032 : CollatzResearch.WordTrace tailWord_591032 prefixEnd_591032 303483498188236818281899 := by
  unfold tailWord_591032
  simp only [CollatzResearch.WordTrace]
  refine ⟨10778353997399739537223675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14371138663199652716298233 10778353997399739537223675)
  ·
    refine ⟨16167530996099609305835513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10778353997399739537223675 16167530996099609305835513)
    ·
      refine ⟨12125648247074706979376635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16167530996099609305835513 12125648247074706979376635)
      ·
        refine ⟨18188472370612060469064953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12125648247074706979376635 18188472370612060469064953)
        ·
          refine ⟨13641354277959045351798715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18188472370612060469064953 13641354277959045351798715)
          ·
            refine ⟨20462031416938568027698073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13641354277959045351798715 20462031416938568027698073)
            ·
              refine ⟨15346523562703926020773555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20462031416938568027698073 15346523562703926020773555)
              ·
                refine ⟨23019785344055889031160333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15346523562703926020773555 23019785344055889031160333)
                ·
                  refine ⟨8632419504020958386685125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23019785344055889031160333 8632419504020958386685125)
                  ·
                    refine ⟨1618578657003929697503461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8632419504020958386685125 1618578657003929697503461)
                    ·
                      refine ⟨303483498188236818281899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1618578657003929697503461 303483498188236818281899)
                      ·
                        rfl

theorem cell23_591032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 3, 4, 4].length) (baseStart_591032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_591032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_591032 prefixEnd_591032 := by exact prefixLift 591032
  have htrace : WordTrace (prefixWord ++ tailWord_591032) baseStart_591032 baseEnd_591032 := by
    simpa [prefixWord, tailWord_591032, baseEnd_591032] using wordTrace_append hprefix tailTrace_591032
  have hstable : (prefixWord ++ tailWord_591032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591032).length < 2 ^ (prefixWord ++ tailWord_591032).sum := by decide
  have hdescent : baseEnd_591032 < baseStart_591032 := by decide
  rcases family_descends (prefixWord ++ tailWord_591032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591036 : List Nat := [2, 2, 2, 3, 2, 1, 1, 1, 3, 4, 2]
def baseStart_591036 : Nat := 118140960795 + 591036 * 2 ^ 59
def prefixEnd_591036 : Nat := 4983230072969 + 3 ^ 40 * 591036 * 2
def baseEnd_591036 : Nat := 303485552110854802631881

theorem tailTrace_591036 : CollatzResearch.WordTrace tailWord_591036 prefixEnd_591036 303485552110854802631881 := by
  unfold tailWord_591036
  simp only [CollatzResearch.WordTrace]
  refine ⟨10778426943392493878796481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14371235924523325171728641 10778426943392493878796481)
  ·
    refine ⟨8083820207544370409097361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10778426943392493878796481 8083820207544370409097361)
    ·
      refine ⟨6062865155658277806823021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8083820207544370409097361 6062865155658277806823021)
      ·
        refine ⟨2273574433371854177558633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6062865155658277806823021 2273574433371854177558633)
        ·
          refine ⟨1705180825028890633168975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2273574433371854177558633 1705180825028890633168975)
          ·
            refine ⟨2557771237543335949753463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1705180825028890633168975 2557771237543335949753463)
            ·
              refine ⟨3836656856315003924630195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2557771237543335949753463 3836656856315003924630195)
              ·
                refine ⟨5754985284472505886945293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3836656856315003924630195 5754985284472505886945293)
                ·
                  refine ⟨2158119481677189707604485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5754985284472505886945293 2158119481677189707604485)
                  ·
                    refine ⟨404647402814473070175841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2158119481677189707604485 404647402814473070175841)
                    ·
                      refine ⟨303485552110854802631881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 404647402814473070175841 303485552110854802631881)
                      ·
                        rfl

theorem cell23_591036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 3, 4, 2].length) (baseStart_591036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_591036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_591036 prefixEnd_591036 := by exact prefixLift 591036
  have htrace : WordTrace (prefixWord ++ tailWord_591036) baseStart_591036 baseEnd_591036 := by
    simpa [prefixWord, tailWord_591036, baseEnd_591036] using wordTrace_append hprefix tailTrace_591036
  have hstable : (prefixWord ++ tailWord_591036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591036).length < 2 ^ (prefixWord ++ tailWord_591036).sum := by decide
  have hdescent : baseEnd_591036 < baseStart_591036 := by decide
  rcases family_descends (prefixWord ++ tailWord_591036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591040 : List Nat := [2, 1, 1, 2, 6, 1, 3, 1, 1, 3, 2]
def baseStart_591040 : Nat := 118140960795 + 591040 * 2 ^ 59
def prefixEnd_591040 : Nat := 4983230072969 + 3 ^ 40 * 591040 * 2
def baseEnd_591040 : Nat := 303487606033472786981863

theorem tailTrace_591040 : CollatzResearch.WordTrace tailWord_591040 prefixEnd_591040 303487606033472786981863 := by
  unfold tailWord_591040
  simp only [CollatzResearch.WordTrace]
  refine ⟨10778499889385248220369287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14371333185846997627159049 10778499889385248220369287)
  ·
    refine ⟨16167749834077872330553931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10778499889385248220369287 16167749834077872330553931)
    ·
      refine ⟨24251624751116808495830897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16167749834077872330553931 24251624751116808495830897)
      ·
        refine ⟨18188718563337606371873173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24251624751116808495830897 18188718563337606371873173)
        ·
          refine ⟨852596182656450298681555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 18188718563337606371873173 852596182656450298681555)
          ·
            refine ⟨1278894273984675448022333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 852596182656450298681555 1278894273984675448022333)
            ·
              refine ⟨479585352744253293008375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1278894273984675448022333 479585352744253293008375)
              ·
                refine ⟨719378029116379939512563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 479585352744253293008375 719378029116379939512563)
                ·
                  refine ⟨1079067043674569909268845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 719378029116379939512563 1079067043674569909268845)
                  ·
                    refine ⟨404650141377963715975817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1079067043674569909268845 404650141377963715975817)
                    ·
                      refine ⟨303487606033472786981863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 404650141377963715975817 303487606033472786981863)
                      ·
                        rfl

theorem cell23_591040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 3, 1, 1, 3, 2].length) (baseStart_591040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_591040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_591040 prefixEnd_591040 := by exact prefixLift 591040
  have htrace : WordTrace (prefixWord ++ tailWord_591040) baseStart_591040 baseEnd_591040 := by
    simpa [prefixWord, tailWord_591040, baseEnd_591040] using wordTrace_append hprefix tailTrace_591040
  have hstable : (prefixWord ++ tailWord_591040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591040).length < 2 ^ (prefixWord ++ tailWord_591040).sum := by decide
  have hdescent : baseEnd_591040 < baseStart_591040 := by decide
  rcases family_descends (prefixWord ++ tailWord_591040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591059 : List Nat := [1, 1, 1, 2, 1, 1, 1, 10, 5]
def baseStart_591059 : Nat := 118140960795 + 591059 * 2 ^ 59
def prefixEnd_591059 : Nat := 4983230072969 + 3 ^ 40 * 591059 * 2
def baseEnd_591059 : Nat := 33721929129545356960475

theorem tailTrace_591059 : CollatzResearch.WordTrace tailWord_591059 prefixEnd_591059 33721929129545356960475 := by
  unfold tailWord_591059
  simp only [CollatzResearch.WordTrace]
  refine ⟨21557692765701662685680231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14371795177134441790453487 21557692765701662685680231)
  ·
    refine ⟨32336539148552494028520347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21557692765701662685680231 32336539148552494028520347)
    ·
      refine ⟨48504808722828741042780521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32336539148552494028520347 48504808722828741042780521)
      ·
        refine ⟨36378606542121555782085391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48504808722828741042780521 36378606542121555782085391)
        ·
          refine ⟨54567909813182333673128087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36378606542121555782085391 54567909813182333673128087)
          ·
            refine ⟨81851864719773500509692131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54567909813182333673128087 81851864719773500509692131)
            ·
              refine ⟨122777797079660250764538197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81851864719773500509692131 122777797079660250764538197)
              ·
                refine ⟨359700577381817140911733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 122777797079660250764538197 359700577381817140911733)
                ·
                  refine ⟨33721929129545356960475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 359700577381817140911733 33721929129545356960475)
                  ·
                    rfl

theorem cell23_591059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 10, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 10, 5].length) (baseStart_591059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_591059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_591059 prefixEnd_591059 := by exact prefixLift 591059
  have htrace : WordTrace (prefixWord ++ tailWord_591059) baseStart_591059 baseEnd_591059 := by
    simpa [prefixWord, tailWord_591059, baseEnd_591059] using wordTrace_append hprefix tailTrace_591059
  have hstable : (prefixWord ++ tailWord_591059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591059).length < 2 ^ (prefixWord ++ tailWord_591059).sum := by decide
  have hdescent : baseEnd_591059 < baseStart_591059 := by decide
  rcases family_descends (prefixWord ++ tailWord_591059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591109 : List Nat := [1, 3, 1, 1, 2, 1, 4, 1, 4, 1, 4]
def baseStart_591109 : Nat := 118140960795 + 591109 * 2 ^ 59
def prefixEnd_591109 : Nat := 4983230072969 + 3 ^ 40 * 591109 * 2
def baseEnd_591109 : Nat := 303523036198633017019045

theorem tailTrace_591109 : CollatzResearch.WordTrace tailWord_591109 prefixEnd_591109 303523036198633017019045 := by
  unfold tailWord_591109
  simp only [CollatzResearch.WordTrace]
  refine ⟨21559516415520521225000381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14373010943680347483333587 21559516415520521225000381)
  ·
    refine ⟨8084818655820195459375143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21559516415520521225000381 8084818655820195459375143)
    ·
      refine ⟨12127227983730293189062715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8084818655820195459375143 12127227983730293189062715)
      ·
        refine ⟨18190841975595439783594073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12127227983730293189062715 18190841975595439783594073)
        ·
          refine ⟨13643131481696579837695555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18190841975595439783594073 13643131481696579837695555)
          ·
            refine ⟨20464697222544869756543333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13643131481696579837695555 20464697222544869756543333)
            ·
              refine ⟨3837130729227163079351875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20464697222544869756543333 3837130729227163079351875)
              ·
                refine ⟨5755696093840744619027813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3837130729227163079351875 5755696093840744619027813)
                ·
                  refine ⟨1079193017595139616067715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5755696093840744619027813 1079193017595139616067715)
                  ·
                    refine ⟨1618789526392709424101573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1079193017595139616067715 1618789526392709424101573)
                    ·
                      refine ⟨303523036198633017019045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1618789526392709424101573 303523036198633017019045)
                      ·
                        rfl

theorem cell23_591109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 4, 1, 4].length) (baseStart_591109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_591109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_591109 prefixEnd_591109 := by exact prefixLift 591109
  have htrace : WordTrace (prefixWord ++ tailWord_591109) baseStart_591109 baseEnd_591109 := by
    simpa [prefixWord, tailWord_591109, baseEnd_591109] using wordTrace_append hprefix tailTrace_591109
  have hstable : (prefixWord ++ tailWord_591109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591109).length < 2 ^ (prefixWord ++ tailWord_591109).sum := by decide
  have hdescent : baseEnd_591109 < baseStart_591109 := by decide
  rcases family_descends (prefixWord ++ tailWord_591109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591166 : List Nat := [4, 2, 1, 2, 1, 1, 2, 4, 6]
def baseStart_591166 : Nat := 118140960795 + 591166 * 2 ^ 59
def prefixEnd_591166 : Nat := 4983230072969 + 3 ^ 40 * 591166 * 2
def baseEnd_591166 : Nat := 33728033843993254889587

theorem tailTrace_591166 : CollatzResearch.WordTrace tailWord_591166 prefixEnd_591166 33728033843993254889587 := by
  unfold tailWord_591166
  simp only [CollatzResearch.WordTrace]
  refine ⟨2695199422039252494978169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14374396917542679973216901 2695199422039252494978169)
  ·
    refine ⟨2021399566529439371233627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2695199422039252494978169 2021399566529439371233627)
    ·
      refine ⟨3032099349794159056850441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2021399566529439371233627 3032099349794159056850441)
      ·
        refine ⟨2274074512345619292637831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3032099349794159056850441 2274074512345619292637831)
        ·
          refine ⟨3411111768518428938956747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2274074512345619292637831 3411111768518428938956747)
          ·
            refine ⟨5116667652777643408435121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3411111768518428938956747 5116667652777643408435121)
            ·
              refine ⟨3837500739583232556326341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5116667652777643408435121 3837500739583232556326341)
              ·
                refine ⟨719531388671856104311189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3837500739583232556326341 719531388671856104311189)
                ·
                  refine ⟨33728033843993254889587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 719531388671856104311189 33728033843993254889587)
                  ·
                    rfl

theorem cell23_591166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 4, 6].length) (baseStart_591166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_591166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_591166 prefixEnd_591166 := by exact prefixLift 591166
  have htrace : WordTrace (prefixWord ++ tailWord_591166) baseStart_591166 baseEnd_591166 := by
    simpa [prefixWord, tailWord_591166, baseEnd_591166] using wordTrace_append hprefix tailTrace_591166
  have hstable : (prefixWord ++ tailWord_591166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591166).length < 2 ^ (prefixWord ++ tailWord_591166).sum := by decide
  have hdescent : baseEnd_591166 < baseStart_591166 := by decide
  rcases family_descends (prefixWord ++ tailWord_591166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591203 : List Nat := [1, 1, 1, 5, 2, 2, 1, 3, 2, 3, 2]
def baseStart_591203 : Nat := 118140960795 + 591203 * 2 ^ 59
def prefixEnd_591203 : Nat := 4983230072969 + 3 ^ 40 * 591203 * 2
def baseEnd_591203 : Nat := 303571303380155649243613

theorem tailTrace_591203 : CollatzResearch.WordTrace tailWord_591203 prefixEnd_591203 303571303380155649243613 := by
  unfold tailWord_591203
  simp only [CollatzResearch.WordTrace]
  refine ⟨21562944877179975278922263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14375296584786650185948175 21562944877179975278922263)
  ·
    refine ⟨32344417315769962918383395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21562944877179975278922263 32344417315769962918383395)
    ·
      refine ⟨48516625973654944377575093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32344417315769962918383395 48516625973654944377575093)
      ·
        refine ⟨4548433685030151035397665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48516625973654944377575093 4548433685030151035397665)
        ·
          refine ⟨3411325263772613276548249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4548433685030151035397665 3411325263772613276548249)
          ·
            refine ⟨2558493947829459957411187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3411325263772613276548249 2558493947829459957411187)
            ·
              refine ⟨3837740921744189936116781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2558493947829459957411187 3837740921744189936116781)
              ·
                refine ⟨1439152845654071226043793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3837740921744189936116781 1439152845654071226043793)
                ·
                  refine ⟨1079364634240553419532845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1439152845654071226043793 1079364634240553419532845)
                  ·
                    refine ⟨404761737840207532324817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1079364634240553419532845 404761737840207532324817)
                    ·
                      refine ⟨303571303380155649243613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 404761737840207532324817 303571303380155649243613)
                      ·
                        rfl

theorem cell23_591203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 3, 2, 3, 2].length) (baseStart_591203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_591203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_591203 prefixEnd_591203 := by exact prefixLift 591203
  have htrace : WordTrace (prefixWord ++ tailWord_591203) baseStart_591203 baseEnd_591203 := by
    simpa [prefixWord, tailWord_591203, baseEnd_591203] using wordTrace_append hprefix tailTrace_591203
  have hstable : (prefixWord ++ tailWord_591203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591203).length < 2 ^ (prefixWord ++ tailWord_591203).sum := by decide
  have hdescent : baseEnd_591203 < baseStart_591203 := by decide
  rcases family_descends (prefixWord ++ tailWord_591203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591267 : List Nat := [1, 1, 1, 4, 1, 3, 4, 3, 1, 2, 2]
def baseStart_591267 : Nat := 118140960795 + 591267 * 2 ^ 59
def prefixEnd_591267 : Nat := 4983230072969 + 3 ^ 40 * 591267 * 2
def baseEnd_591267 : Nat := 303604166142043398843319

theorem tailTrace_591267 : CollatzResearch.WordTrace tailWord_591267 prefixEnd_591267 303604166142043398843319 := by
  unfold tailWord_591267
  simp only [CollatzResearch.WordTrace]
  refine ⟨21565279148948114209252055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14376852765965409472834703 21565279148948114209252055)
  ·
    refine ⟨32347918723422171313878083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21565279148948114209252055 32347918723422171313878083)
    ·
      refine ⟨48521878085133256970817125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32347918723422171313878083 48521878085133256970817125)
      ·
        refine ⟨9097852140962485682028211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48521878085133256970817125 9097852140962485682028211)
        ·
          refine ⟨13646778211443728523042317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9097852140962485682028211 13646778211443728523042317)
          ·
            refine ⟨5117541829291398196140869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13646778211443728523042317 5117541829291398196140869)
            ·
              refine ⟨959539092992137161776413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5117541829291398196140869 959539092992137161776413)
              ·
                refine ⟨359827159872051435666155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 959539092992137161776413 359827159872051435666155)
                ·
                  refine ⟨539740739808077153499233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 359827159872051435666155 539740739808077153499233)
                  ·
                    refine ⟨404805554856057865124425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 539740739808077153499233 404805554856057865124425)
                    ·
                      refine ⟨303604166142043398843319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 404805554856057865124425 303604166142043398843319)
                      ·
                        rfl

theorem cell23_591267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 3, 1, 2, 2].length) (baseStart_591267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_591267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_591267 prefixEnd_591267 := by exact prefixLift 591267
  have htrace : WordTrace (prefixWord ++ tailWord_591267) baseStart_591267 baseEnd_591267 := by
    simpa [prefixWord, tailWord_591267, baseEnd_591267] using wordTrace_append hprefix tailTrace_591267
  have hstable : (prefixWord ++ tailWord_591267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591267).length < 2 ^ (prefixWord ++ tailWord_591267).sum := by decide
  have hdescent : baseEnd_591267 < baseStart_591267 := by decide
  rcases family_descends (prefixWord ++ tailWord_591267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591269 : List Nat := [1, 3, 1, 2, 1, 1, 2, 2, 1, 9]
def baseStart_591269 : Nat := 118140960795 + 591269 * 2 ^ 59
def prefixEnd_591269 : Nat := 4983230072969 + 3 ^ 40 * 591269 * 2
def baseEnd_591269 : Nat := 101201731034450797006103

theorem tailTrace_591269 : CollatzResearch.WordTrace tailWord_591269 prefixEnd_591269 101201731034450797006103 := by
  unfold tailWord_591269
  simp only [CollatzResearch.WordTrace]
  refine ⟨21565352094940868550824861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14376901396627245700549907 21565352094940868550824861)
  ·
    refine ⟨8087007035602825706559323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21565352094940868550824861 8087007035602825706559323)
    ·
      refine ⟨12130510553404238559838985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8087007035602825706559323 12130510553404238559838985)
      ·
        refine ⟨9097882915053178919879239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12130510553404238559838985 9097882915053178919879239)
        ·
          refine ⟨13646824372579768379818859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9097882915053178919879239 13646824372579768379818859)
          ·
            refine ⟨20470236558869652569728289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13646824372579768379818859 20470236558869652569728289)
            ·
              refine ⟨15352677419152239427296217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20470236558869652569728289 15352677419152239427296217)
              ·
                refine ⟨11514508064364179570472163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15352677419152239427296217 11514508064364179570472163)
                ·
                  refine ⟨17271762096546269355708245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11514508064364179570472163 17271762096546269355708245)
                  ·
                    refine ⟨101201731034450797006103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 17271762096546269355708245 101201731034450797006103)
                    ·
                      rfl

theorem cell23_591269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 9].length) (baseStart_591269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_591269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_591269 prefixEnd_591269 := by exact prefixLift 591269
  have htrace : WordTrace (prefixWord ++ tailWord_591269) baseStart_591269 baseEnd_591269 := by
    simpa [prefixWord, tailWord_591269, baseEnd_591269] using wordTrace_append hprefix tailTrace_591269
  have hstable : (prefixWord ++ tailWord_591269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591269).length < 2 ^ (prefixWord ++ tailWord_591269).sum := by decide
  have hdescent : baseEnd_591269 < baseStart_591269 := by decide
  rcases family_descends (prefixWord ++ tailWord_591269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591277 : List Nat := [1, 5, 2, 2, 1, 3, 1, 2, 2, 4]
def baseStart_591277 : Nat := 118140960795 + 591277 * 2 ^ 59
def prefixEnd_591277 : Nat := 4983230072969 + 3 ^ 40 * 591277 * 2
def baseEnd_591277 : Nat := 101203100316196119906091

theorem tailTrace_591277 : CollatzResearch.WordTrace tailWord_591277 prefixEnd_591277 101203100316196119906091 := by
  unfold tailWord_591277
  simp only [CollatzResearch.WordTrace]
  refine ⟨21565643878911885917116085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14377095919274590611410723 21565643878911885917116085)
  ·
    refine ⟨2021779113647989304729633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21565643878911885917116085 2021779113647989304729633)
    ·
      refine ⟨1516334335235991978547225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2021779113647989304729633 1516334335235991978547225)
      ·
        refine ⟨1137250751426993983910419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1516334335235991978547225 1137250751426993983910419)
        ·
          refine ⟨1705876127140490975865629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1137250751426993983910419 1705876127140490975865629)
          ·
            refine ⟨639703547677684115949611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1705876127140490975865629 639703547677684115949611)
            ·
              refine ⟨959555321516526173924417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 639703547677684115949611 959555321516526173924417)
              ·
                refine ⟨719666491137394630443313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 959555321516526173924417 719666491137394630443313)
                ·
                  refine ⟨539749868353045972832485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 719666491137394630443313 539749868353045972832485)
                  ·
                    refine ⟨101203100316196119906091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 539749868353045972832485 101203100316196119906091)
                    ·
                      rfl

theorem cell23_591277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_591277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_591277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_591277 prefixEnd_591277 := by exact prefixLift 591277
  have htrace : WordTrace (prefixWord ++ tailWord_591277) baseStart_591277 baseEnd_591277 := by
    simpa [prefixWord, tailWord_591277, baseEnd_591277] using wordTrace_append hprefix tailTrace_591277
  have hstable : (prefixWord ++ tailWord_591277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591277).length < 2 ^ (prefixWord ++ tailWord_591277).sum := by decide
  have hdescent : baseEnd_591277 < baseStart_591277 := by decide
  rcases family_descends (prefixWord ++ tailWord_591277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591300 : List Nat := [2, 3, 3, 2, 1, 1, 3, 1, 1, 3, 3]
def baseStart_591300 : Nat := 118140960795 + 591300 * 2 ^ 59
def prefixEnd_591300 : Nat := 4983230072969 + 3 ^ 40 * 591300 * 2
def baseEnd_591300 : Nat := 303621111003641769730667

theorem tailTrace_591300 : CollatzResearch.WordTrace tailWord_591300 prefixEnd_591300 303621111003641769730667 := by
  unfold tailWord_591300
  simp only [CollatzResearch.WordTrace]
  refine ⟨10783241378914280422601677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14377655171885707230135569 10783241378914280422601677)
  ·
    refine ⟨4043715517092855158475629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10783241378914280422601677 4043715517092855158475629)
    ·
      refine ⟨1516393318909820684428361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4043715517092855158475629 1516393318909820684428361)
      ·
        refine ⟨1137294989182365513321271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1516393318909820684428361 1137294989182365513321271)
        ·
          refine ⟨1705942483773548269981907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1137294989182365513321271 1705942483773548269981907)
          ·
            refine ⟨2558913725660322404972861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1705942483773548269981907 2558913725660322404972861)
            ·
              refine ⟨959592647122620901864823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2558913725660322404972861 959592647122620901864823)
              ·
                refine ⟨1439388970683931352797235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 959592647122620901864823 1439388970683931352797235)
                ·
                  refine ⟨2159083456025897029195853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1439388970683931352797235 2159083456025897029195853)
                  ·
                    refine ⟨809656296009711385948445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2159083456025897029195853 809656296009711385948445)
                    ·
                      refine ⟨303621111003641769730667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 809656296009711385948445 303621111003641769730667)
                      ·
                        rfl

theorem cell23_591300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_591300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_591300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_591300 prefixEnd_591300 := by exact prefixLift 591300
  have htrace : WordTrace (prefixWord ++ tailWord_591300) baseStart_591300 baseEnd_591300 := by
    simpa [prefixWord, tailWord_591300, baseEnd_591300] using wordTrace_append hprefix tailTrace_591300
  have hstable : (prefixWord ++ tailWord_591300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591300).length < 2 ^ (prefixWord ++ tailWord_591300).sum := by decide
  have hdescent : baseEnd_591300 < baseStart_591300 := by decide
  rcases family_descends (prefixWord ++ tailWord_591300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591310 : List Nat := [4, 1, 1, 1, 2, 1, 3, 4, 1, 3, 2]
def baseStart_591310 : Nat := 118140960795 + 591310 * 2 ^ 59
def prefixEnd_591310 : Nat := 4983230072969 + 3 ^ 40 * 591310 * 2
def baseEnd_591310 : Nat := 303626245810186730605621

theorem tailTrace_591310 : CollatzResearch.WordTrace tailWord_591310 prefixEnd_591310 303626245810186730605621 := by
  unfold tailWord_591310
  simp only [CollatzResearch.WordTrace]
  refine ⟨2695855935974041569133423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14377898325194888368711589 2695855935974041569133423)
  ·
    refine ⟨4043783903961062353700135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2695855935974041569133423 4043783903961062353700135)
    ·
      refine ⟨6065675855941593530550203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4043783903961062353700135 6065675855941593530550203)
      ·
        refine ⟨9098513783912390295825305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6065675855941593530550203 9098513783912390295825305)
        ·
          refine ⟨6823885337934292721868979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9098513783912390295825305 6823885337934292721868979)
          ·
            refine ⟨10235828006901439082803469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6823885337934292721868979 10235828006901439082803469)
            ·
              refine ⟨3838435502588039656051301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10235828006901439082803469 3838435502588039656051301)
              ·
                refine ⟨719706656735257435509619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3838435502588039656051301 719706656735257435509619)
                ·
                  refine ⟨1079559985102886153264429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 719706656735257435509619 1079559985102886153264429)
                  ·
                    refine ⟨404834994413582307474161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1079559985102886153264429 404834994413582307474161)
                    ·
                      refine ⟨303626245810186730605621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 404834994413582307474161 303626245810186730605621)
                      ·
                        rfl

theorem cell23_591310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 4, 1, 3, 2].length) (baseStart_591310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_591310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_591310 prefixEnd_591310 := by exact prefixLift 591310
  have htrace : WordTrace (prefixWord ++ tailWord_591310) baseStart_591310 baseEnd_591310 := by
    simpa [prefixWord, tailWord_591310, baseEnd_591310] using wordTrace_append hprefix tailTrace_591310
  have hstable : (prefixWord ++ tailWord_591310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591310).length < 2 ^ (prefixWord ++ tailWord_591310).sum := by decide
  have hdescent : baseEnd_591310 < baseStart_591310 := by decide
  rcases family_descends (prefixWord ++ tailWord_591310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591357 : List Nat := [1, 4, 1, 1, 1, 5, 1, 3, 2, 2, 2]
def baseStart_591357 : Nat := 118140960795 + 591357 * 2 ^ 59
def prefixEnd_591357 : Nat := 4983230072969 + 3 ^ 40 * 591357 * 2
def baseEnd_591357 : Nat := 303650379400948046717905

theorem tailTrace_591357 : CollatzResearch.WordTrace tailWord_591357 prefixEnd_591357 303650379400948046717905 := by
  unfold tailWord_591357
  simp only [CollatzResearch.WordTrace]
  refine ⟨21568561718622059580028325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14379041145748039720018883 21568561718622059580028325)
  ·
    refine ⟨4044105322241636171255311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21568561718622059580028325 4044105322241636171255311)
    ·
      refine ⟨6066157983362454256882967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4044105322241636171255311 6066157983362454256882967)
      ·
        refine ⟨9099236975043681385324451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6066157983362454256882967 9099236975043681385324451)
        ·
          refine ⟨13648855462565522077986677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9099236975043681385324451 13648855462565522077986677)
          ·
            refine ⟨1279580199615517694811251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13648855462565522077986677 1279580199615517694811251)
            ·
              refine ⟨1919370299423276542216877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1279580199615517694811251 1919370299423276542216877)
              ·
                refine ⟨719763862283728703331329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1919370299423276542216877 719763862283728703331329)
                ·
                  refine ⟨539822896712796527498497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 719763862283728703331329 539822896712796527498497)
                  ·
                    refine ⟨404867172534597395623873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 539822896712796527498497 404867172534597395623873)
                    ·
                      refine ⟨303650379400948046717905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 404867172534597395623873 303650379400948046717905)
                      ·
                        rfl

theorem cell23_591357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 3, 2, 2, 2].length) (baseStart_591357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_591357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_591357 prefixEnd_591357 := by exact prefixLift 591357
  have htrace : WordTrace (prefixWord ++ tailWord_591357) baseStart_591357 baseEnd_591357 := by
    simpa [prefixWord, tailWord_591357, baseEnd_591357] using wordTrace_append hprefix tailTrace_591357
  have hstable : (prefixWord ++ tailWord_591357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591357).length < 2 ^ (prefixWord ++ tailWord_591357).sum := by decide
  have hdescent : baseEnd_591357 < baseStart_591357 := by decide
  rcases family_descends (prefixWord ++ tailWord_591357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591393 : List Nat := [1, 2, 3, 2, 2, 2, 2, 2, 2, 5]
def baseStart_591393 : Nat := 118140960795 + 591393 * 2 ^ 59
def prefixEnd_591393 : Nat := 4983230072969 + 3 ^ 40 * 591393 * 2
def baseEnd_591393 : Nat := 101222954901503301955913

theorem tailTrace_591393 : CollatzResearch.WordTrace tailWord_591393 prefixEnd_591393 101222954901503301955913 := by
  unfold tailWord_591393
  simp only [CollatzResearch.WordTrace]
  refine ⟨21569874746491637728338833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14379916497661091818892555 21569874746491637728338833)
  ·
    refine ⟨16177406059868728296254125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21569874746491637728338833 16177406059868728296254125)
    ·
      refine ⟨6066527272450773111095297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16177406059868728296254125 6066527272450773111095297)
      ·
        refine ⟨4549895454338079833321473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6066527272450773111095297 4549895454338079833321473)
        ·
          refine ⟨3412421590753559874991105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4549895454338079833321473 3412421590753559874991105)
          ·
            refine ⟨2559316193065169906243329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3412421590753559874991105 2559316193065169906243329)
            ·
              refine ⟨1919487144798877429682497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2559316193065169906243329 1919487144798877429682497)
              ·
                refine ⟨1439615358599158072261873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1919487144798877429682497 1439615358599158072261873)
                ·
                  refine ⟨1079711518949368554196405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1439615358599158072261873 1079711518949368554196405)
                  ·
                    refine ⟨101222954901503301955913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1079711518949368554196405 101222954901503301955913)
                    ·
                      rfl

theorem cell23_591393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 2, 2, 5].length) (baseStart_591393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_591393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_591393 prefixEnd_591393 := by exact prefixLift 591393
  have htrace : WordTrace (prefixWord ++ tailWord_591393) baseStart_591393 baseEnd_591393 := by
    simpa [prefixWord, tailWord_591393, baseEnd_591393] using wordTrace_append hprefix tailTrace_591393
  have hstable : (prefixWord ++ tailWord_591393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591393).length < 2 ^ (prefixWord ++ tailWord_591393).sum := by decide
  have hdescent : baseEnd_591393 < baseStart_591393 := by decide
  rcases family_descends (prefixWord ++ tailWord_591393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591423 : List Nat := [1, 1, 2, 2, 3, 3, 1, 1, 5, 4]
def baseStart_591423 : Nat := 118140960795 + 591423 * 2 ^ 59
def prefixEnd_591423 : Nat := 4983230072969 + 3 ^ 40 * 591423 * 2
def baseEnd_591423 : Nat := 101228089708048262830867

theorem tailTrace_591423 : CollatzResearch.WordTrace tailWord_591423 prefixEnd_591423 101228089708048262830867 := by
  unfold tailWord_591423
  simp only [CollatzResearch.WordTrace]
  refine ⟨21570968936382952851930923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14380645957588635234620615 21570968936382952851930923)
  ·
    refine ⟨32356453404574429277896385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21570968936382952851930923 32356453404574429277896385)
    ·
      refine ⟨24267340053430821958422289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32356453404574429277896385 24267340053430821958422289)
      ·
        refine ⟨18200505040073116468816717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24267340053430821958422289 18200505040073116468816717)
        ·
          refine ⟨6825189390027418675806269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18200505040073116468816717 6825189390027418675806269)
          ·
            refine ⟨2559446021260282003427351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6825189390027418675806269 2559446021260282003427351)
            ·
              refine ⟨3839169031890423005141027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2559446021260282003427351 3839169031890423005141027)
              ·
                refine ⟨5758753547835634507711541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3839169031890423005141027 5758753547835634507711541)
                ·
                  refine ⟨539883145109590735097957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5758753547835634507711541 539883145109590735097957)
                  ·
                    refine ⟨101228089708048262830867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 539883145109590735097957 101228089708048262830867)
                    ·
                      rfl

theorem cell23_591423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 5, 4].length) (baseStart_591423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_591423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_591423 prefixEnd_591423 := by exact prefixLift 591423
  have htrace : WordTrace (prefixWord ++ tailWord_591423) baseStart_591423 baseEnd_591423 := by
    simpa [prefixWord, tailWord_591423, baseEnd_591423] using wordTrace_append hprefix tailTrace_591423
  have hstable : (prefixWord ++ tailWord_591423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591423).length < 2 ^ (prefixWord ++ tailWord_591423).sum := by decide
  have hdescent : baseEnd_591423 < baseStart_591423 := by decide
  rcases family_descends (prefixWord ++ tailWord_591423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591523 : List Nat := [1, 1, 1, 4, 1, 1, 3, 4, 1, 1, 5]
def baseStart_591523 : Nat := 118140960795 + 591523 * 2 ^ 59
def prefixEnd_591523 : Nat := 4983230072969 + 3 ^ 40 * 591523 * 2
def baseEnd_591523 : Nat := 303735617189594397242141

theorem tailTrace_591523 : CollatzResearch.WordTrace tailWord_591523 prefixEnd_591523 303735617189594397242141 := by
  unfold tailWord_591523
  simp only [CollatzResearch.WordTrace]
  refine ⟨21574616236020669930571223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14383077490680446620380815 21574616236020669930571223)
  ·
    refine ⟨32361924354031004895856835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21574616236020669930571223 32361924354031004895856835)
    ·
      refine ⟨48542886531046507343785253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32361924354031004895856835 48542886531046507343785253)
      ·
        refine ⟨9101791224571220126959735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48542886531046507343785253 9101791224571220126959735)
        ·
          refine ⟨13652686836856830190439603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9101791224571220126959735 13652686836856830190439603)
          ·
            refine ⟨20479030255285245285659405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13652686836856830190439603 20479030255285245285659405)
            ·
              refine ⟨7679636345731966982122277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20479030255285245285659405 7679636345731966982122277)
              ·
                refine ⟨1439931814824743809147927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7679636345731966982122277 1439931814824743809147927)
                ·
                  refine ⟨2159897722237115713721891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1439931814824743809147927 2159897722237115713721891)
                  ·
                    refine ⟨3239846583355673570582837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2159897722237115713721891 3239846583355673570582837)
                    ·
                      refine ⟨303735617189594397242141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3239846583355673570582837 303735617189594397242141)
                      ·
                        rfl

theorem cell23_591523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 4, 1, 1, 5].length) (baseStart_591523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_591523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_591523 prefixEnd_591523 := by exact prefixLift 591523
  have htrace : WordTrace (prefixWord ++ tailWord_591523) baseStart_591523 baseEnd_591523 := by
    simpa [prefixWord, tailWord_591523, baseEnd_591523] using wordTrace_append hprefix tailTrace_591523
  have hstable : (prefixWord ++ tailWord_591523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591523).length < 2 ^ (prefixWord ++ tailWord_591523).sum := by decide
  have hdescent : baseEnd_591523 < baseStart_591523 := by decide
  rcases family_descends (prefixWord ++ tailWord_591523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591543 : List Nat := [1, 1, 3, 1, 5, 1, 2, 9]
def baseStart_591543 : Nat := 118140960795 + 591543 * 2 ^ 59
def prefixEnd_591543 : Nat := 4983230072969 + 3 ^ 40 * 591543 * 2
def baseEnd_591543 : Nat := 11249847659358678481187

theorem tailTrace_591543 : CollatzResearch.WordTrace tailWord_591543 prefixEnd_591543 11249847659358678481187 := by
  unfold tailWord_591543
  simp only [CollatzResearch.WordTrace]
  refine ⟨21575345695948213346299283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14383563797298808897532855 21575345695948213346299283)
  ·
    refine ⟨32363018543922320019448925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21575345695948213346299283 32363018543922320019448925)
    ·
      refine ⟨12136131953970870007293347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32363018543922320019448925 12136131953970870007293347)
      ·
        refine ⟨18204197930956305010940021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12136131953970870007293347 18204197930956305010940021)
        ·
          refine ⟨1706643556027153594775627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18204197930956305010940021 1706643556027153594775627)
          ·
            refine ⟨2559965334040730392163441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1706643556027153594775627 2559965334040730392163441)
            ·
              refine ⟨1919974000530547794122581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2559965334040730392163441 1919974000530547794122581)
              ·
                refine ⟨11249847659358678481187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1919974000530547794122581 11249847659358678481187)
                ·
                  rfl

theorem cell23_591543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 9].length) (baseStart_591543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_591543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_591543 prefixEnd_591543 := by exact prefixLift 591543
  have htrace : WordTrace (prefixWord ++ tailWord_591543) baseStart_591543 baseEnd_591543 := by
    simpa [prefixWord, tailWord_591543, baseEnd_591543] using wordTrace_append hprefix tailTrace_591543
  have hstable : (prefixWord ++ tailWord_591543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591543).length < 2 ^ (prefixWord ++ tailWord_591543).sum := by decide
  have hdescent : baseEnd_591543 < baseStart_591543 := by decide
  rcases family_descends (prefixWord ++ tailWord_591543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591550 : List Nat := [4, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4]
def baseStart_591550 : Nat := 118140960795 + 591550 * 2 ^ 59
def prefixEnd_591550 : Nat := 4983230072969 + 3 ^ 40 * 591550 * 2
def baseEnd_591550 : Nat := 303749481167265791604517

theorem tailTrace_591550 : CollatzResearch.WordTrace tailWord_591550 prefixEnd_591550 303749481167265791604517 := by
  unfold tailWord_591550
  simp only [CollatzResearch.WordTrace]
  refine ⟨2696950125865356692725513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14383734004615235694536069 2696950125865356692725513)
  ·
    refine ⟨2022712594399017519544135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2696950125865356692725513 2022712594399017519544135)
    ·
      refine ⟨3034068891598526279316203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2022712594399017519544135 3034068891598526279316203)
      ·
        refine ⟨4551103337397789418974305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3034068891598526279316203 4551103337397789418974305)
        ·
          refine ⟨3413327503048342064230729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4551103337397789418974305 3413327503048342064230729)
          ·
            refine ⟨2559995627286256548173047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3413327503048342064230729 2559995627286256548173047)
            ·
              refine ⟨3839993440929384822259571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2559995627286256548173047 3839993440929384822259571)
              ·
                refine ⟨5759990161394077233389357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3839993440929384822259571 5759990161394077233389357)
                ·
                  refine ⟨2159996310522778962521009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5759990161394077233389357 2159996310522778962521009)
                  ·
                    refine ⟨1619997232892084221890757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2159996310522778962521009 1619997232892084221890757)
                    ·
                      refine ⟨303749481167265791604517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1619997232892084221890757 303749481167265791604517)
                      ·
                        rfl

theorem cell23_591550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_591550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_591550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_591550 prefixEnd_591550 := by exact prefixLift 591550
  have htrace : WordTrace (prefixWord ++ tailWord_591550) baseStart_591550 baseEnd_591550 := by
    simpa [prefixWord, tailWord_591550, baseEnd_591550] using wordTrace_append hprefix tailTrace_591550
  have hstable : (prefixWord ++ tailWord_591550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591550).length < 2 ^ (prefixWord ++ tailWord_591550).sum := by decide
  have hdescent : baseEnd_591550 < baseStart_591550 := by decide
  rcases family_descends (prefixWord ++ tailWord_591550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591564 : List Nat := [2, 2, 1, 5, 2, 1, 2, 2, 2, 4]
def baseStart_591564 : Nat := 118140960795 + 591564 * 2 ^ 59
def prefixEnd_591564 : Nat := 4983230072969 + 3 ^ 40 * 591564 * 2
def baseEnd_591564 : Nat := 101252223298809578943151

theorem tailTrace_591564 : CollatzResearch.WordTrace tailWord_591564 prefixEnd_591564 101252223298809578943151 := by
  unfold tailWord_591564
  simp only [CollatzResearch.WordTrace]
  refine ⟨10788055814436066966406873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14384074419248089288542497 10788055814436066966406873)
  ·
    refine ⟨8091041860827050224805155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10788055814436066966406873 8091041860827050224805155)
    ·
      refine ⟨12136562791240575337207733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8091041860827050224805155 12136562791240575337207733)
      ·
        refine ⟨1137802761678803937863225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12136562791240575337207733 1137802761678803937863225)
        ·
          refine ⟨853352071259102953397419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1137802761678803937863225 853352071259102953397419)
          ·
            refine ⟨1280028106888654430096129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 853352071259102953397419 1280028106888654430096129)
            ·
              refine ⟨960021080166490822572097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1280028106888654430096129 960021080166490822572097)
              ·
                refine ⟨720015810124868116929073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 960021080166490822572097 720015810124868116929073)
                ·
                  refine ⟨540011857593651087696805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 720015810124868116929073 540011857593651087696805)
                  ·
                    refine ⟨101252223298809578943151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 540011857593651087696805 101252223298809578943151)
                    ·
                      rfl

theorem cell23_591564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 2, 2, 4].length) (baseStart_591564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_591564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_591564 prefixEnd_591564 := by exact prefixLift 591564
  have htrace : WordTrace (prefixWord ++ tailWord_591564) baseStart_591564 baseEnd_591564 := by
    simpa [prefixWord, tailWord_591564, baseEnd_591564] using wordTrace_append hprefix tailTrace_591564
  have hstable : (prefixWord ++ tailWord_591564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591564).length < 2 ^ (prefixWord ++ tailWord_591564).sum := by decide
  have hdescent : baseEnd_591564 < baseStart_591564 := by decide
  rcases family_descends (prefixWord ++ tailWord_591564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591565 : List Nat := [1, 6, 2, 1, 1, 3, 2, 2, 1, 1, 3]
def baseStart_591565 : Nat := 118140960795 + 591565 * 2 ^ 59
def prefixEnd_591565 : Nat := 4983230072969 + 3 ^ 40 * 591565 * 2
def baseEnd_591565 : Nat := 303757183377083232916949

theorem tailTrace_591565 : CollatzResearch.WordTrace tailWord_591565 prefixEnd_591565 303757183377083232916949 := by
  unfold tailWord_591565
  simp only [CollatzResearch.WordTrace]
  refine ⟨21576148101868511103600149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14384098734579007402400099 21576148101868511103600149)
  ·
    refine ⟨1011381942275086457981257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 21576148101868511103600149 1011381942275086457981257)
    ·
      refine ⟨758536456706314843485943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1011381942275086457981257 758536456706314843485943)
      ·
        refine ⟨1137804685059472265228915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 758536456706314843485943 1137804685059472265228915)
        ·
          refine ⟨1706707027589208397843373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1137804685059472265228915 1706707027589208397843373)
          ·
            refine ⟨640015135345953149191265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1706707027589208397843373 640015135345953149191265)
            ·
              refine ⟨480011351509464861893449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 640015135345953149191265 480011351509464861893449)
              ·
                refine ⟨360008513632098646420087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 480011351509464861893449 360008513632098646420087)
                ·
                  refine ⟨540012770448147969630131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 360008513632098646420087 540012770448147969630131)
                  ·
                    refine ⟨810019155672221954445197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 540012770448147969630131 810019155672221954445197)
                    ·
                      refine ⟨303757183377083232916949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 810019155672221954445197 303757183377083232916949)
                      ·
                        rfl

theorem cell23_591565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_591565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_591565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_591565 prefixEnd_591565 := by exact prefixLift 591565
  have htrace : WordTrace (prefixWord ++ tailWord_591565) baseStart_591565 baseEnd_591565 := by
    simpa [prefixWord, tailWord_591565, baseEnd_591565] using wordTrace_append hprefix tailTrace_591565
  have hstable : (prefixWord ++ tailWord_591565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591565).length < 2 ^ (prefixWord ++ tailWord_591565).sum := by decide
  have hdescent : baseEnd_591565 < baseStart_591565 := by decide
  rcases family_descends (prefixWord ++ tailWord_591565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591593 : List Nat := [1, 2, 1, 1, 1, 2, 3, 1, 4, 3, 4]
def baseStart_591593 : Nat := 118140960795 + 591593 * 2 ^ 59
def prefixEnd_591593 : Nat := 4983230072969 + 3 ^ 40 * 591593 * 2
def baseEnd_591593 : Nat := 303771560835409123366819

theorem tailTrace_591593 : CollatzResearch.WordTrace tailWord_591593 prefixEnd_591593 303771560835409123366819 := by
  unfold tailWord_591593
  simp only [CollatzResearch.WordTrace]
  refine ⟨21577169345767071885619433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14384779563844714590412955 21577169345767071885619433)
  ·
    refine ⟨16182877009325303914214575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21577169345767071885619433 16182877009325303914214575)
    ·
      refine ⟨24274315513987955871321863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16182877009325303914214575 24274315513987955871321863)
      ·
        refine ⟨36411473270981933806982795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24274315513987955871321863 36411473270981933806982795)
        ·
          refine ⟨54617209906472900710474193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36411473270981933806982795 54617209906472900710474193)
          ·
            refine ⟨40962907429854675532855645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54617209906472900710474193 40962907429854675532855645)
            ·
              refine ⟨15361090286195503324820867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40962907429854675532855645 15361090286195503324820867)
              ·
                refine ⟨23041635429293254987231301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15361090286195503324820867 23041635429293254987231301)
                ·
                  refine ⟨4320306642992485310105869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23041635429293254987231301 4320306642992485310105869)
                  ·
                    refine ⟨1620114991122181991289701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4320306642992485310105869 1620114991122181991289701)
                    ·
                      refine ⟨303771560835409123366819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1620114991122181991289701 303771560835409123366819)
                      ·
                        rfl

theorem cell23_591593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 3, 4].length) (baseStart_591593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_591593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_591593 prefixEnd_591593 := by exact prefixLift 591593
  have htrace : WordTrace (prefixWord ++ tailWord_591593) baseStart_591593 baseEnd_591593 := by
    simpa [prefixWord, tailWord_591593, baseEnd_591593] using wordTrace_append hprefix tailTrace_591593
  have hstable : (prefixWord ++ tailWord_591593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591593).length < 2 ^ (prefixWord ++ tailWord_591593).sum := by decide
  have hdescent : baseEnd_591593 < baseStart_591593 := by decide
  rcases family_descends (prefixWord ++ tailWord_591593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591620 : List Nat := [2, 3, 2, 2, 1, 2, 1, 2, 2, 6]
def baseStart_591620 : Nat := 118140960795 + 591620 * 2 ^ 59
def prefixEnd_591620 : Nat := 4983230072969 + 3 ^ 40 * 591620 * 2
def baseEnd_591620 : Nat := 101261808271026839243065

theorem tailTrace_591620 : CollatzResearch.WordTrace tailWord_591620 prefixEnd_591620 101261808271026839243065 := by
  unfold tailWord_591620
  simp only [CollatzResearch.WordTrace]
  refine ⟨10789077058334627748426157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14385436077779503664568209 10789077058334627748426157)
  ·
    refine ⟨4045903896875485405659809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10789077058334627748426157 4045903896875485405659809)
    ·
      refine ⟨3034427922656614054244857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4045903896875485405659809 3034427922656614054244857)
      ·
        refine ⟨2275820941992460540683643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3034427922656614054244857 2275820941992460540683643)
        ·
          refine ⟨3413731412988690811025465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2275820941992460540683643 3413731412988690811025465)
          ·
            refine ⟨2560298559741518108269099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3413731412988690811025465 2560298559741518108269099)
            ·
              refine ⟨3840447839612277162403649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2560298559741518108269099 3840447839612277162403649)
              ·
                refine ⟨2880335879709207871802737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3840447839612277162403649 2880335879709207871802737)
                ·
                  refine ⟨2160251909781905903852053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2880335879709207871802737 2160251909781905903852053)
                  ·
                    refine ⟨101261808271026839243065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2160251909781905903852053 101261808271026839243065)
                    ·
                      rfl

theorem cell23_591620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_591620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_591620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_591620 prefixEnd_591620 := by exact prefixLift 591620
  have htrace : WordTrace (prefixWord ++ tailWord_591620) baseStart_591620 baseEnd_591620 := by
    simpa [prefixWord, tailWord_591620, baseEnd_591620] using wordTrace_append hprefix tailTrace_591620
  have hstable : (prefixWord ++ tailWord_591620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591620).length < 2 ^ (prefixWord ++ tailWord_591620).sum := by decide
  have hdescent : baseEnd_591620 < baseStart_591620 := by decide
  rcases family_descends (prefixWord ++ tailWord_591620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591630 : List Nat := [4, 1, 1, 2, 1, 1, 2, 1, 1, 6, 3]
def baseStart_591630 : Nat := 118140960795 + 591630 * 2 ^ 59
def prefixEnd_591630 : Nat := 4983230072969 + 3 ^ 40 * 591630 * 2
def baseEnd_591630 : Nat := 303790559619625478604149

theorem tailTrace_591630 : CollatzResearch.WordTrace tailWord_591630 prefixEnd_591630 303790559619625478604149 := by
  unfold tailWord_591630
  simp only [CollatzResearch.WordTrace]
  refine ⟨2697314855829128400589543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14385679231088684803144229 2697314855829128400589543)
  ·
    refine ⟨4045972283743692600884315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2697314855829128400589543 4045972283743692600884315)
    ·
      refine ⟨6068958425615538901326473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4045972283743692600884315 6068958425615538901326473)
      ·
        refine ⟨4551718819211654175994855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6068958425615538901326473 4551718819211654175994855)
        ·
          refine ⟨6827578228817481263992283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4551718819211654175994855 6827578228817481263992283)
          ·
            refine ⟨10241367343226221895988425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6827578228817481263992283 10241367343226221895988425)
            ·
              refine ⟨7681025507419666421991319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10241367343226221895988425 7681025507419666421991319)
              ·
                refine ⟨11521538261129499632986979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7681025507419666421991319 11521538261129499632986979)
                ·
                  refine ⟨17282307391694249449480469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11521538261129499632986979 17282307391694249449480469)
                  ·
                    refine ⟨810108158985667942944397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17282307391694249449480469 810108158985667942944397)
                    ·
                      refine ⟨303790559619625478604149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 810108158985667942944397 303790559619625478604149)
                      ·
                        rfl

theorem cell23_591630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 1, 6, 3].length) (baseStart_591630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_591630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_591630 prefixEnd_591630 := by exact prefixLift 591630
  have htrace : WordTrace (prefixWord ++ tailWord_591630) baseStart_591630 baseEnd_591630 := by
    simpa [prefixWord, tailWord_591630, baseEnd_591630] using wordTrace_append hprefix tailTrace_591630
  have hstable : (prefixWord ++ tailWord_591630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591630).length < 2 ^ (prefixWord ++ tailWord_591630).sum := by decide
  have hdescent : baseEnd_591630 < baseStart_591630 := by decide
  rcases family_descends (prefixWord ++ tailWord_591630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591640 : List Nat := [2, 1, 2, 3, 1, 1, 4, 1, 2, 2, 4]
def baseStart_591640 : Nat := 118140960795 + 591640 * 2 ^ 59
def prefixEnd_591640 : Nat := 4983230072969 + 3 ^ 40 * 591640 * 2
def baseEnd_591640 : Nat := 303795694426170439479103

theorem tailTrace_591640 : CollatzResearch.WordTrace tailWord_591640 prefixEnd_591640 303795694426170439479103 := by
  unfold tailWord_591640
  simp only [CollatzResearch.WordTrace]
  refine ⟨10789441788298399456290187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14385922384397865941720249 10789441788298399456290187)
  ·
    refine ⟨16184162682447599184435281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10789441788298399456290187 16184162682447599184435281)
    ·
      refine ⟨12138122011835699388326461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16184162682447599184435281 12138122011835699388326461)
      ·
        refine ⟨4551795754438387270622423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12138122011835699388326461 4551795754438387270622423)
        ·
          refine ⟨6827693631657580905933635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4551795754438387270622423 6827693631657580905933635)
          ·
            refine ⟨10241540447486371358900453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6827693631657580905933635 10241540447486371358900453)
            ·
              refine ⟨1920288833903694629793835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10241540447486371358900453 1920288833903694629793835)
              ·
                refine ⟨2880433250855541944690753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1920288833903694629793835 2880433250855541944690753)
                ·
                  refine ⟨2160324938141656458518065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2880433250855541944690753 2160324938141656458518065)
                  ·
                    refine ⟨1620243703606242343888549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2160324938141656458518065 1620243703606242343888549)
                    ·
                      refine ⟨303795694426170439479103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1620243703606242343888549 303795694426170439479103)
                      ·
                        rfl

theorem cell23_591640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_591640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_591640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_591640 prefixEnd_591640 := by exact prefixLift 591640
  have htrace : WordTrace (prefixWord ++ tailWord_591640) baseStart_591640 baseEnd_591640 := by
    simpa [prefixWord, tailWord_591640, baseEnd_591640] using wordTrace_append hprefix tailTrace_591640
  have hstable : (prefixWord ++ tailWord_591640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591640).length < 2 ^ (prefixWord ++ tailWord_591640).sum := by decide
  have hdescent : baseEnd_591640 < baseStart_591640 := by decide
  rcases family_descends (prefixWord ++ tailWord_591640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591650 : List Nat := [3, 3, 1, 1, 2, 1, 1, 4, 7]
def baseStart_591650 : Nat := 118140960795 + 591650 * 2 ^ 59
def prefixEnd_591650 : Nat := 4983230072969 + 3 ^ 40 * 591650 * 2
def baseEnd_591650 : Nat := 33755647692523933372673

theorem tailTrace_591650 : CollatzResearch.WordTrace tailWord_591650 prefixEnd_591650 33755647692523933372673 := by
  unfold tailWord_591650
  simp only [CollatzResearch.WordTrace]
  refine ⟨5394812076640142655111101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14386165537707047080296269 5394812076640142655111101)
  ·
    refine ⟨2023054528740053495666663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5394812076640142655111101 2023054528740053495666663)
    ·
      refine ⟨3034581793110080243499995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2023054528740053495666663 3034581793110080243499995)
      ·
        refine ⟨4551872689665120365249993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3034581793110080243499995 4551872689665120365249993)
        ·
          refine ⟨3413904517248840273937495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4551872689665120365249993 3413904517248840273937495)
          ·
            refine ⟨5120856775873260410906243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3413904517248840273937495 5120856775873260410906243)
            ·
              refine ⟨7681285163809890616359365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5120856775873260410906243 7681285163809890616359365)
              ·
                refine ⟨1440240968214354490567381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7681285163809890616359365 1440240968214354490567381)
                ·
                  refine ⟨33755647692523933372673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1440240968214354490567381 33755647692523933372673)
                  ·
                    rfl

theorem cell23_591650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 4, 7].length) (baseStart_591650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_591650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_591650 prefixEnd_591650 := by exact prefixLift 591650
  have htrace : WordTrace (prefixWord ++ tailWord_591650) baseStart_591650 baseEnd_591650 := by
    simpa [prefixWord, tailWord_591650, baseEnd_591650] using wordTrace_append hprefix tailTrace_591650
  have hstable : (prefixWord ++ tailWord_591650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591650).length < 2 ^ (prefixWord ++ tailWord_591650).sum := by decide
  have hdescent : baseEnd_591650 < baseStart_591650 := by decide
  rcases family_descends (prefixWord ++ tailWord_591650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591690 : List Nat := [3, 1, 2, 1, 1, 1, 5, 1, 1, 2, 5]
def baseStart_591690 : Nat := 118140960795 + 591690 * 2 ^ 59
def prefixEnd_591690 : Nat := 4983230072969 + 3 ^ 40 * 591690 * 2
def baseEnd_591690 : Nat := 303821368458895243853873

theorem tailTrace_591690 : CollatzResearch.WordTrace tailWord_591690 prefixEnd_591690 303821368458895243853873 := by
  unfold tailWord_591690
  simp only [CollatzResearch.WordTrace]
  refine ⟨5395176806603914362975131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14387138150943771634600349 5395176806603914362975131)
  ·
    refine ⟨8092765209905871544462697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5395176806603914362975131 8092765209905871544462697)
    ·
      refine ⟨6069573907429403658347023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8092765209905871544462697 6069573907429403658347023)
      ·
        refine ⟨9104360861144105487520535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6069573907429403658347023 9104360861144105487520535)
        ·
          refine ⟨13656541291716158231280803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9104360861144105487520535 13656541291716158231280803)
          ·
            refine ⟨20484811937574237346921205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13656541291716158231280803 20484811937574237346921205)
            ·
              refine ⟨1920451119147584751273863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20484811937574237346921205 1920451119147584751273863)
              ·
                refine ⟨2880676678721377126910795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1920451119147584751273863 2880676678721377126910795)
                ·
                  refine ⟨4321015018082065690366193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2880676678721377126910795 4321015018082065690366193)
                  ·
                    refine ⟨3240761263561549267774645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4321015018082065690366193 3240761263561549267774645)
                    ·
                      refine ⟨303821368458895243853873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3240761263561549267774645 303821368458895243853873)
                      ·
                        rfl

theorem cell23_591690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 1, 2, 5].length) (baseStart_591690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_591690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_591690 prefixEnd_591690 := by exact prefixLift 591690
  have htrace : WordTrace (prefixWord ++ tailWord_591690) baseStart_591690 baseEnd_591690 := by
    simpa [prefixWord, tailWord_591690, baseEnd_591690] using wordTrace_append hprefix tailTrace_591690
  have hstable : (prefixWord ++ tailWord_591690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591690).length < 2 ^ (prefixWord ++ tailWord_591690).sum := by decide
  have hdescent : baseEnd_591690 < baseStart_591690 := by decide
  rcases family_descends (prefixWord ++ tailWord_591690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591714 : List Nat := [3, 3, 2, 1, 2, 2, 2, 1, 2, 5]
def baseStart_591714 : Nat := 118140960795 + 591714 * 2 ^ 59
def prefixEnd_591714 : Nat := 4983230072969 + 3 ^ 40 * 591714 * 2
def baseEnd_591714 : Nat := 101277897331534383317921

theorem tailTrace_591714 : CollatzResearch.WordTrace tailWord_591714 prefixEnd_591714 101277897331534383317921 := by
  unfold tailWord_591714
  simp only [CollatzResearch.WordTrace]
  refine ⟨5395395644582177387693549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14387721718885806367182797 5395395644582177387693549)
  ·
    refine ⟨2023273366718316520385081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5395395644582177387693549 2023273366718316520385081)
    ·
      refine ⟨1517455025038737390288811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2023273366718316520385081 1517455025038737390288811)
      ·
        refine ⟨2276182537558106085433217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1517455025038737390288811 2276182537558106085433217)
        ·
          refine ⟨1707136903168579564074913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2276182537558106085433217 1707136903168579564074913)
          ·
            refine ⟨1280352677376434673056185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1707136903168579564074913 1280352677376434673056185)
            ·
              refine ⟨960264508032326004792139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1280352677376434673056185 960264508032326004792139)
              ·
                refine ⟨1440396762048489007188209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 960264508032326004792139 1440396762048489007188209)
                ·
                  refine ⟨1080297571536366755391157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1440396762048489007188209 1080297571536366755391157)
                  ·
                    refine ⟨101277897331534383317921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1080297571536366755391157 101277897331534383317921)
                    ·
                      rfl

theorem cell23_591714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_591714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_591714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_591714 prefixEnd_591714 := by exact prefixLift 591714
  have htrace : WordTrace (prefixWord ++ tailWord_591714) baseStart_591714 baseEnd_591714 := by
    simpa [prefixWord, tailWord_591714, baseEnd_591714] using wordTrace_append hprefix tailTrace_591714
  have hstable : (prefixWord ++ tailWord_591714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591714).length < 2 ^ (prefixWord ++ tailWord_591714).sum := by decide
  have hdescent : baseEnd_591714 < baseStart_591714 := by decide
  rcases family_descends (prefixWord ++ tailWord_591714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591717 : List Nat := [1, 3, 1, 3, 1, 1, 1, 2, 4, 4, 2]
def baseStart_591717 : Nat := 118140960795 + 591717 * 2 ^ 59
def prefixEnd_591717 : Nat := 4983230072969 + 3 ^ 40 * 591717 * 2
def baseEnd_591717 : Nat := 303835232436566638216249

theorem tailTrace_591717 : CollatzResearch.WordTrace tailWord_591717 prefixEnd_591717 303835232436566638216249 := by
  unfold tailWord_591717
  simp only [CollatzResearch.WordTrace]
  refine ⟨21581691997317841063133405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14387794664878560708755603 21581691997317841063133405)
  ·
    refine ⟨8093134498994190398675027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21581691997317841063133405 8093134498994190398675027)
    ·
      refine ⟨12139701748491285598012541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8093134498994190398675027 12139701748491285598012541)
      ·
        refine ⟨4552388155684232099254703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12139701748491285598012541 4552388155684232099254703)
        ·
          refine ⟨6828582233526348148882055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4552388155684232099254703 6828582233526348148882055)
          ·
            refine ⟨10242873350289522223323083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6828582233526348148882055 10242873350289522223323083)
            ·
              refine ⟨15364310025434283334984625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10242873350289522223323083 15364310025434283334984625)
              ·
                refine ⟨11523232519075712501238469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15364310025434283334984625 11523232519075712501238469)
                ·
                  refine ⟨2160606097326696093982213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11523232519075712501238469 2160606097326696093982213)
                  ·
                    refine ⟨405113643248755517621665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2160606097326696093982213 405113643248755517621665)
                    ·
                      refine ⟨303835232436566638216249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 405113643248755517621665 303835232436566638216249)
                      ·
                        rfl

theorem cell23_591717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 4, 4, 2].length) (baseStart_591717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_591717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_591717 prefixEnd_591717 := by exact prefixLift 591717
  have htrace : WordTrace (prefixWord ++ tailWord_591717) baseStart_591717 baseEnd_591717 := by
    simpa [prefixWord, tailWord_591717, baseEnd_591717] using wordTrace_append hprefix tailTrace_591717
  have hstable : (prefixWord ++ tailWord_591717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591717).length < 2 ^ (prefixWord ++ tailWord_591717).sum := by decide
  have hdescent : baseEnd_591717 < baseStart_591717 := by decide
  rcases family_descends (prefixWord ++ tailWord_591717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591730 : List Nat := [3, 2, 1, 2, 1, 1, 1, 3, 2, 1, 6]
def baseStart_591730 : Nat := 118140960795 + 591730 * 2 ^ 59
def prefixEnd_591730 : Nat := 4983230072969 + 3 ^ 40 * 591730 * 2
def baseEnd_591730 : Nat := 303841907685075087353689

theorem tailTrace_591730 : CollatzResearch.WordTrace tailWord_591730 prefixEnd_591730 303841907685075087353689 := by
  unfold tailWord_591730
  simp only [CollatzResearch.WordTrace]
  refine ⟨5395541536567686070839161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14388110764180496188904429 5395541536567686070839161)
  ·
    refine ⟨4046656152425764553129371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5395541536567686070839161 4046656152425764553129371)
    ·
      refine ⟨6069984228638646829694057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4046656152425764553129371 6069984228638646829694057)
      ·
        refine ⟨4552488171478985122270543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6069984228638646829694057 4552488171478985122270543)
        ·
          refine ⟨6828732257218477683405815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4552488171478985122270543 6828732257218477683405815)
          ·
            refine ⟨10243098385827716525108723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6828732257218477683405815 10243098385827716525108723)
            ·
              refine ⟨15364647578741574787663085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10243098385827716525108723 15364647578741574787663085)
              ·
                refine ⟨5761742842028090545373657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15364647578741574787663085 5761742842028090545373657)
                ·
                  refine ⟨4321307131521067909030243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5761742842028090545373657 4321307131521067909030243)
                  ·
                    refine ⟨6481960697281601863545365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4321307131521067909030243 6481960697281601863545365)
                    ·
                      refine ⟨303841907685075087353689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6481960697281601863545365 303841907685075087353689)
                      ·
                        rfl

theorem cell23_591730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_591730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_591730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_591730 prefixEnd_591730 := by exact prefixLift 591730
  have htrace : WordTrace (prefixWord ++ tailWord_591730) baseStart_591730 baseEnd_591730 := by
    simpa [prefixWord, tailWord_591730, baseEnd_591730] using wordTrace_append hprefix tailTrace_591730
  have hstable : (prefixWord ++ tailWord_591730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591730).length < 2 ^ (prefixWord ++ tailWord_591730).sum := by decide
  have hdescent : baseEnd_591730 < baseStart_591730 := by decide
  rcases family_descends (prefixWord ++ tailWord_591730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591737 : List Nat := [1, 2, 1, 3, 2, 2, 1, 4, 2, 2, 3]
def baseStart_591737 : Nat := 118140960795 + 591737 * 2 ^ 59
def prefixEnd_591737 : Nat := 4983230072969 + 3 ^ 40 * 591737 * 2
def baseEnd_591737 : Nat := 303845502049656559966157

theorem tailTrace_591737 : CollatzResearch.WordTrace tailWord_591737 prefixEnd_591737 303845502049656559966157 := by
  unfold tailWord_591737
  simp only [CollatzResearch.WordTrace]
  refine ⟨21582421457245384478861465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14388280971496922985907643 21582421457245384478861465)
  ·
    refine ⟨16186816092934038359146099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21582421457245384478861465 16186816092934038359146099)
    ·
      refine ⟨24280224139401057538719149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16186816092934038359146099 24280224139401057538719149)
      ·
        refine ⟨9105084052275396577019681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24280224139401057538719149 9105084052275396577019681)
        ·
          refine ⟨6828813039206547432764761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9105084052275396577019681 6828813039206547432764761)
          ·
            refine ⟨5121609779404910574573571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6828813039206547432764761 5121609779404910574573571)
            ·
              refine ⟨7682414669107365861860357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5121609779404910574573571 7682414669107365861860357)
              ·
                refine ⟨1440452750457631099098817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7682414669107365861860357 1440452750457631099098817)
                ·
                  refine ⟨1080339562843223324324113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1440452750457631099098817 1080339562843223324324113)
                  ·
                    refine ⟨810254672132417493243085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1080339562843223324324113 810254672132417493243085)
                    ·
                      refine ⟨303845502049656559966157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 810254672132417493243085 303845502049656559966157)
                      ·
                        rfl

theorem cell23_591737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 4, 2, 2, 3].length) (baseStart_591737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_591737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_591737 prefixEnd_591737 := by exact prefixLift 591737
  have htrace : WordTrace (prefixWord ++ tailWord_591737) baseStart_591737 baseEnd_591737 := by
    simpa [prefixWord, tailWord_591737, baseEnd_591737] using wordTrace_append hprefix tailTrace_591737
  have hstable : (prefixWord ++ tailWord_591737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591737).length < 2 ^ (prefixWord ++ tailWord_591737).sum := by decide
  have hdescent : baseEnd_591737 < baseStart_591737 := by decide
  rcases family_descends (prefixWord ++ tailWord_591737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591744 : List Nat := [2, 1, 1, 2, 1, 2, 5, 4, 1, 4]
def baseStart_591744 : Nat := 118140960795 + 591744 * 2 ^ 59
def prefixEnd_591744 : Nat := 4983230072969 + 3 ^ 40 * 591744 * 2
def baseEnd_591744 : Nat := 101283032138079344192875

theorem tailTrace_591744 : CollatzResearch.WordTrace tailWord_591744 prefixEnd_591744 101283032138079344192875 := by
  unfold tailWord_591744
  simp only [CollatzResearch.WordTrace]
  refine ⟨10791338384110012337183143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14388451178813349782910857 10791338384110012337183143)
  ·
    refine ⟨16187007576165018505774715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10791338384110012337183143 16187007576165018505774715)
    ·
      refine ⟨24280511364247527758662073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16187007576165018505774715 24280511364247527758662073)
      ·
        refine ⟨18210383523185645818996555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24280511364247527758662073 18210383523185645818996555)
        ·
          refine ⟨27315575284778468728494833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18210383523185645818996555 27315575284778468728494833)
          ·
            refine ⟨20486681463583851546371125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27315575284778468728494833 20486681463583851546371125)
            ·
              refine ⟨1920626387210986082472293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20486681463583851546371125 1920626387210986082472293)
              ·
                refine ⟨360117447602059890463555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1920626387210986082472293 360117447602059890463555)
                ·
                  refine ⟨540176171403089835695333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 360117447602059890463555 540176171403089835695333)
                  ·
                    refine ⟨101283032138079344192875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 540176171403089835695333 101283032138079344192875)
                    ·
                      rfl

theorem cell23_591744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 4, 1, 4].length) (baseStart_591744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_591744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_591744 prefixEnd_591744 := by exact prefixLift 591744
  have htrace : WordTrace (prefixWord ++ tailWord_591744) baseStart_591744 baseEnd_591744 := by
    simpa [prefixWord, tailWord_591744, baseEnd_591744] using wordTrace_append hprefix tailTrace_591744
  have hstable : (prefixWord ++ tailWord_591744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591744).length < 2 ^ (prefixWord ++ tailWord_591744).sum := by decide
  have hdescent : baseEnd_591744 < baseStart_591744 := by decide
  rcases family_descends (prefixWord ++ tailWord_591744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591768 : List Nat := [2, 1, 2, 6, 2, 1, 1, 1, 2, 1, 4]
def baseStart_591768 : Nat := 118140960795 + 591768 * 2 ^ 59
def prefixEnd_591768 : Nat := 4983230072969 + 3 ^ 40 * 591768 * 2
def baseEnd_591768 : Nat := 303861419949945938678515

theorem tailTrace_591768 : CollatzResearch.WordTrace tailWord_591768 prefixEnd_591768 303861419949945938678515 := by
  unfold tailWord_591768
  simp only [CollatzResearch.WordTrace]
  refine ⟨10791776060066538386619979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14389034746755384515493305 10791776060066538386619979)
  ·
    refine ⟨16187664090099807579929969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10791776060066538386619979 16187664090099807579929969)
    ·
      refine ⟨12140748067574855684947477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16187664090099807579929969 12140748067574855684947477)
      ·
        refine ⟨569097565667571360231913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 12140748067574855684947477 569097565667571360231913)
        ·
          refine ⟨426823174250678520173935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 569097565667571360231913 426823174250678520173935)
          ·
            refine ⟨640234761376017780260903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 426823174250678520173935 640234761376017780260903)
            ·
              refine ⟨960352142064026670391355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 640234761376017780260903 960352142064026670391355)
              ·
                refine ⟨1440528213096040005587033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 960352142064026670391355 1440528213096040005587033)
                ·
                  refine ⟨1080396159822030004190275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1440528213096040005587033 1080396159822030004190275)
                  ·
                    refine ⟨1620594239733045006285413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1080396159822030004190275 1620594239733045006285413)
                    ·
                      refine ⟨303861419949945938678515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1620594239733045006285413 303861419949945938678515)
                      ·
                        rfl

theorem cell23_591768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_591768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_591768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_591768 prefixEnd_591768 := by exact prefixLift 591768
  have htrace : WordTrace (prefixWord ++ tailWord_591768) baseStart_591768 baseEnd_591768 := by
    simpa [prefixWord, tailWord_591768, baseEnd_591768] using wordTrace_append hprefix tailTrace_591768
  have hstable : (prefixWord ++ tailWord_591768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591768).length < 2 ^ (prefixWord ++ tailWord_591768).sum := by decide
  have hdescent : baseEnd_591768 < baseStart_591768 := by decide
  rcases family_descends (prefixWord ++ tailWord_591768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591778 : List Nat := [3, 3, 1, 2, 3, 1, 2, 3, 1, 4]
def baseStart_591778 : Nat := 118140960795 + 591778 * 2 ^ 59
def prefixEnd_591778 : Nat := 4983230072969 + 3 ^ 40 * 591778 * 2
def baseEnd_591778 : Nat := 101288851585496966517823

theorem tailTrace_591778 : CollatzResearch.WordTrace tailWord_591778 prefixEnd_591778 101288851585496966517823 := by
  unfold tailWord_591778
  simp only [CollatzResearch.WordTrace]
  refine ⟨5395979212524212120275997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14389277900064565654069325 5395979212524212120275997)
  ·
    refine ⟨2023492204696579545103499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5395979212524212120275997 2023492204696579545103499)
    ·
      refine ⟨3035238307044869317655249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2023492204696579545103499 3035238307044869317655249)
      ·
        refine ⟨2276428730283651988241437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3035238307044869317655249 2276428730283651988241437)
        ·
          refine ⟨853660773856369495590539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2276428730283651988241437 853660773856369495590539)
          ·
            refine ⟨1280491160784554243385809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 853660773856369495590539 1280491160784554243385809)
            ·
              refine ⟨960368370588415682539357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1280491160784554243385809 960368370588415682539357)
              ·
                refine ⟨360138138970655880952259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 960368370588415682539357 360138138970655880952259)
                ·
                  refine ⟨540207208455983821428389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 360138138970655880952259 540207208455983821428389)
                  ·
                    refine ⟨101288851585496966517823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 540207208455983821428389 101288851585496966517823)
                    ·
                      rfl

theorem cell23_591778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 3, 1, 4].length) (baseStart_591778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_591778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_591778 prefixEnd_591778 := by exact prefixLift 591778
  have htrace : WordTrace (prefixWord ++ tailWord_591778) baseStart_591778 baseEnd_591778 := by
    simpa [prefixWord, tailWord_591778, baseEnd_591778] using wordTrace_append hprefix tailTrace_591778
  have hstable : (prefixWord ++ tailWord_591778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591778).length < 2 ^ (prefixWord ++ tailWord_591778).sum := by decide
  have hdescent : baseEnd_591778 < baseStart_591778 := by decide
  rcases family_descends (prefixWord ++ tailWord_591778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591794 : List Nat := [3, 2, 1, 1, 1, 1, 1, 6, 2, 3, 2]
def baseStart_591794 : Nat := 118140960795 + 591794 * 2 ^ 59
def prefixEnd_591794 : Nat := 4983230072969 + 3 ^ 40 * 591794 * 2
def baseEnd_591794 : Nat := 303874770446962836953395

theorem tailTrace_591794 : CollatzResearch.WordTrace tailWord_591794 prefixEnd_591794 303874770446962836953395 := by
  unfold tailWord_591794
  simp only [CollatzResearch.WordTrace]
  refine ⟨5396125104509720803421609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14389666945359255475790957 5396125104509720803421609)
  ·
    refine ⟨4047093828382290602566207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5396125104509720803421609 4047093828382290602566207)
    ·
      refine ⟨6070640742573435903849311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4047093828382290602566207 6070640742573435903849311)
      ·
        refine ⟨9105961113860153855773967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6070640742573435903849311 9105961113860153855773967)
        ·
          refine ⟨13658941670790230783660951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9105961113860153855773967 13658941670790230783660951)
          ·
            refine ⟨20488412506185346175491427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13658941670790230783660951 20488412506185346175491427)
            ·
              refine ⟨30732618759278019263237141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20488412506185346175491427 30732618759278019263237141)
              ·
                refine ⟨1440591504341157152964241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30732618759278019263237141 1440591504341157152964241)
                ·
                  refine ⟨1080443628255867864723181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1440591504341157152964241 1080443628255867864723181)
                  ·
                    refine ⟨405166360595950449271193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1080443628255867864723181 405166360595950449271193)
                    ·
                      refine ⟨303874770446962836953395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 405166360595950449271193 303874770446962836953395)
                      ·
                        rfl

theorem cell23_591794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 6, 2, 3, 2].length) (baseStart_591794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_591794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_591794 prefixEnd_591794 := by exact prefixLift 591794
  have htrace : WordTrace (prefixWord ++ tailWord_591794) baseStart_591794 baseEnd_591794 := by
    simpa [prefixWord, tailWord_591794, baseEnd_591794] using wordTrace_append hprefix tailTrace_591794
  have hstable : (prefixWord ++ tailWord_591794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591794).length < 2 ^ (prefixWord ++ tailWord_591794).sum := by decide
  have hdescent : baseEnd_591794 < baseStart_591794 := by decide
  rcases family_descends (prefixWord ++ tailWord_591794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591801 : List Nat := [1, 2, 1, 4, 2, 1, 1, 6, 1, 1, 3]
def baseStart_591801 : Nat := 118140960795 + 591801 * 2 ^ 59
def prefixEnd_591801 : Nat := 4983230072969 + 3 ^ 40 * 591801 * 2
def baseEnd_591801 : Nat := 303878364811544309565863

theorem tailTrace_591801 : CollatzResearch.WordTrace tailWord_591801 prefixEnd_591801 303878364811544309565863 := by
  unfold tailWord_591801
  simp only [CollatzResearch.WordTrace]
  refine ⟨21584755729013523409191257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14389837152675682272794171 21584755729013523409191257)
  ·
    refine ⟨16188566796760142556893443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21584755729013523409191257 16188566796760142556893443)
    ·
      refine ⟨24282850195140213835340165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16188566796760142556893443 24282850195140213835340165)
      ·
        refine ⟨4553034411588790094126281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24282850195140213835340165 4553034411588790094126281)
        ·
          refine ⟨3414775808691592570594711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4553034411588790094126281 3414775808691592570594711)
          ·
            refine ⟨5122163713037388855892067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3414775808691592570594711 5122163713037388855892067)
            ·
              refine ⟨7683245569556083283838101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5122163713037388855892067 7683245569556083283838101)
              ·
                refine ⟨360152136072941403929911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7683245569556083283838101 360152136072941403929911)
                ·
                  refine ⟨540228204109412105894867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 360152136072941403929911 540228204109412105894867)
                  ·
                    refine ⟨810342306164118158842301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 540228204109412105894867 810342306164118158842301)
                    ·
                      refine ⟨303878364811544309565863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 810342306164118158842301 303878364811544309565863)
                      ·
                        rfl

theorem cell23_591801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 6, 1, 1, 3].length) (baseStart_591801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_591801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_591801 prefixEnd_591801 := by exact prefixLift 591801
  have htrace : WordTrace (prefixWord ++ tailWord_591801) baseStart_591801 baseEnd_591801 := by
    simpa [prefixWord, tailWord_591801, baseEnd_591801] using wordTrace_append hprefix tailTrace_591801
  have hstable : (prefixWord ++ tailWord_591801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591801).length < 2 ^ (prefixWord ++ tailWord_591801).sum := by decide
  have hdescent : baseEnd_591801 < baseStart_591801 := by decide
  rcases family_descends (prefixWord ++ tailWord_591801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591844 : List Nat := [2, 3, 1, 1, 1, 1, 3, 5, 1, 2, 3]
def baseStart_591844 : Nat := 118140960795 + 591844 * 2 ^ 59
def prefixEnd_591844 : Nat := 4983230072969 + 3 ^ 40 * 591844 * 2
def baseEnd_591844 : Nat := 303900444479687641328165

theorem tailTrace_591844 : CollatzResearch.WordTrace tailWord_591844 prefixEnd_591844 303900444479687641328165 := by
  unfold tailWord_591844
  simp only [CollatzResearch.WordTrace]
  refine ⟨10793162033928870876503293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14390882711905161168671057 10793162033928870876503293)
  ·
    refine ⟨4047435762723326578688735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10793162033928870876503293 4047435762723326578688735)
    ·
      refine ⟨6071153644084989868033103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4047435762723326578688735 6071153644084989868033103)
      ·
        refine ⟨9106730466127484802049655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6071153644084989868033103 9106730466127484802049655)
        ·
          refine ⟨13660095699191227203074483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9106730466127484802049655 13660095699191227203074483)
          ·
            refine ⟨20490143548786840804611725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13660095699191227203074483 20490143548786840804611725)
            ·
              refine ⟨7683803830795065301729397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20490143548786840804611725 7683803830795065301729397)
              ·
                refine ⟨720356609137037372037131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7683803830795065301729397 720356609137037372037131)
                ·
                  refine ⟨1080534913705556058055697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 720356609137037372037131 1080534913705556058055697)
                  ·
                    refine ⟨810401185279167043541773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1080534913705556058055697 810401185279167043541773)
                    ·
                      refine ⟨303900444479687641328165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 810401185279167043541773 303900444479687641328165)
                      ·
                        rfl

theorem cell23_591844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 5, 1, 2, 3].length) (baseStart_591844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_591844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_591844 prefixEnd_591844 := by exact prefixLift 591844
  have htrace : WordTrace (prefixWord ++ tailWord_591844) baseStart_591844 baseEnd_591844 := by
    simpa [prefixWord, tailWord_591844, baseEnd_591844] using wordTrace_append hprefix tailTrace_591844
  have hstable : (prefixWord ++ tailWord_591844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591844).length < 2 ^ (prefixWord ++ tailWord_591844).sum := by decide
  have hdescent : baseEnd_591844 < baseStart_591844 := by decide
  rcases family_descends (prefixWord ++ tailWord_591844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591907 : List Nat := [1, 1, 1, 4, 3, 1, 2, 2, 2, 6]
def baseStart_591907 : Nat := 118140960795 + 591907 * 2 ^ 59
def prefixEnd_591907 : Nat := 4983230072969 + 3 ^ 40 * 591907 * 2
def baseEnd_591907 : Nat := 101310931253640298280125

theorem tailTrace_591907 : CollatzResearch.WordTrace tailWord_591907 prefixEnd_591907 101310931253640298280125 := by
  unfold tailWord_591907
  simp only [CollatzResearch.WordTrace]
  refine ⟨21588621866629503512549975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14392414577753002341699983 21588621866629503512549975)
  ·
    refine ⟨32382932799944255268824963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21588621866629503512549975 32382932799944255268824963)
    ·
      refine ⟨48574399199916382903237445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32382932799944255268824963 48574399199916382903237445)
      ·
        refine ⟨9107699849984321794357021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48574399199916382903237445 9107699849984321794357021)
        ·
          refine ⟨3415387443744120672883883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9107699849984321794357021 3415387443744120672883883)
          ·
            refine ⟨5123081165616181009325825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3415387443744120672883883 5123081165616181009325825)
            ·
              refine ⟨3842310874212135756994369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5123081165616181009325825 3842310874212135756994369)
              ·
                refine ⟨2881733155659101817745777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3842310874212135756994369 2881733155659101817745777)
                ·
                  refine ⟨2161299866744326363309333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2881733155659101817745777 2161299866744326363309333)
                  ·
                    refine ⟨101310931253640298280125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2161299866744326363309333 101310931253640298280125)
                    ·
                      rfl

theorem cell23_591907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 2, 6].length) (baseStart_591907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_591907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_591907 prefixEnd_591907 := by exact prefixLift 591907
  have htrace : WordTrace (prefixWord ++ tailWord_591907) baseStart_591907 baseEnd_591907 := by
    simpa [prefixWord, tailWord_591907, baseEnd_591907] using wordTrace_append hprefix tailTrace_591907
  have hstable : (prefixWord ++ tailWord_591907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591907).length < 2 ^ (prefixWord ++ tailWord_591907).sum := by decide
  have hdescent : baseEnd_591907 < baseStart_591907 := by decide
  rcases family_descends (prefixWord ++ tailWord_591907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591914 : List Nat := [3, 1, 4, 1, 2, 1, 1, 1, 2, 3, 4]
def baseStart_591914 : Nat := 118140960795 + 591914 * 2 ^ 59
def prefixEnd_591914 : Nat := 4983230072969 + 3 ^ 40 * 591914 * 2
def baseEnd_591914 : Nat := 303936388125502367452843

theorem tailTrace_591914 : CollatzResearch.WordTrace tailWord_591914 prefixEnd_591914 303936388125502367452843 := by
  unfold tailWord_591914
  simp only [CollatzResearch.WordTrace]
  refine ⟨5397219294401035927013699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14392584785069429138703197 5397219294401035927013699)
  ·
    refine ⟨8095828941601553890520549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5397219294401035927013699 8095828941601553890520549)
    ·
      refine ⟨1517967926550291354472603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8095828941601553890520549 1517967926550291354472603)
      ·
        refine ⟨2276951889825437031708905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1517967926550291354472603 2276951889825437031708905)
        ·
          refine ⟨1707713917369077773781679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2276951889825437031708905 1707713917369077773781679)
          ·
            refine ⟨2561570876053616660672519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1707713917369077773781679 2561570876053616660672519)
            ·
              refine ⟨3842356314080424991008779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2561570876053616660672519 3842356314080424991008779)
              ·
                refine ⟨5763534471120637486513169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3842356314080424991008779 5763534471120637486513169)
                ·
                  refine ⟨4322650853340478114884877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5763534471120637486513169 4322650853340478114884877)
                  ·
                    refine ⟨1620994070002679293081829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4322650853340478114884877 1620994070002679293081829)
                    ·
                      refine ⟨303936388125502367452843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1620994070002679293081829 303936388125502367452843)
                      ·
                        rfl

theorem cell23_591914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_591914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_591914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_591914 prefixEnd_591914 := by exact prefixLift 591914
  have htrace : WordTrace (prefixWord ++ tailWord_591914) baseStart_591914 baseEnd_591914 := by
    simpa [prefixWord, tailWord_591914, baseEnd_591914] using wordTrace_append hprefix tailTrace_591914
  have hstable : (prefixWord ++ tailWord_591914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591914).length < 2 ^ (prefixWord ++ tailWord_591914).sum := by decide
  have hdescent : baseEnd_591914 < baseStart_591914 := by decide
  rcases family_descends (prefixWord ++ tailWord_591914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591927 : List Nat := [1, 1, 3, 1, 2, 2, 3, 1, 1, 4, 4]
def baseStart_591927 : Nat := 118140960795 + 591927 * 2 ^ 59
def prefixEnd_591927 : Nat := 4983230072969 + 3 ^ 40 * 591927 * 2
def baseEnd_591927 : Nat := 303943063374010816590283

theorem tailTrace_591927 : CollatzResearch.WordTrace tailWord_591927 prefixEnd_591927 303943063374010816590283 := by
  unfold tailWord_591927
  simp only [CollatzResearch.WordTrace]
  refine ⟨21589351326557046928278035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14392900884371364618852023 21589351326557046928278035)
  ·
    refine ⟨32384026989835570392417053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21589351326557046928278035 32384026989835570392417053)
    ·
      refine ⟨12144010121188338897156395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32384026989835570392417053 12144010121188338897156395)
      ·
        refine ⟨18216015181782508345734593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12144010121188338897156395 18216015181782508345734593)
        ·
          refine ⟨13662011386336881259300945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18216015181782508345734593 13662011386336881259300945)
          ·
            refine ⟨10246508539752660944475709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13662011386336881259300945 10246508539752660944475709)
            ·
              refine ⟨3842440702407247854178391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10246508539752660944475709 3842440702407247854178391)
              ·
                refine ⟨5763661053610871781267587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3842440702407247854178391 5763661053610871781267587)
                ·
                  refine ⟨8645491580416307671901381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5763661053610871781267587 8645491580416307671901381)
                  ·
                    refine ⟨1621029671328057688481509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8645491580416307671901381 1621029671328057688481509)
                    ·
                      refine ⟨303943063374010816590283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1621029671328057688481509 303943063374010816590283)
                      ·
                        rfl

theorem cell23_591927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 4, 4].length) (baseStart_591927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_591927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_591927 prefixEnd_591927 := by exact prefixLift 591927
  have htrace : WordTrace (prefixWord ++ tailWord_591927) baseStart_591927 baseEnd_591927 := by
    simpa [prefixWord, tailWord_591927, baseEnd_591927] using wordTrace_append hprefix tailTrace_591927
  have hstable : (prefixWord ++ tailWord_591927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591927).length < 2 ^ (prefixWord ++ tailWord_591927).sum := by decide
  have hdescent : baseEnd_591927 < baseStart_591927 := by decide
  rcases family_descends (prefixWord ++ tailWord_591927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591965 : List Nat := [1, 4, 4, 1, 1, 2, 1, 1, 4, 2, 2]
def baseStart_591965 : Nat := 118140960795 + 591965 * 2 ^ 59
def prefixEnd_591965 : Nat := 4983230072969 + 3 ^ 40 * 591965 * 2
def baseEnd_591965 : Nat := 303962575638881667915109

theorem tailTrace_591965 : CollatzResearch.WordTrace tailWord_591965 prefixEnd_591965 303962575638881667915109 := by
  unfold tailWord_591965
  simp only [CollatzResearch.WordTrace]
  refine ⟨21590737300419379418161349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14393824866946252945440899 21590737300419379418161349)
  ·
    refine ⟨4048263243828633640905253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21590737300419379418161349 4048263243828633640905253)
    ·
      refine ⟨759049358217868807669735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4048263243828633640905253 759049358217868807669735)
      ·
        refine ⟨1138574037326803211504603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 759049358217868807669735 1138574037326803211504603)
        ·
          refine ⟨1707861055990204817256905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1138574037326803211504603 1707861055990204817256905)
          ·
            refine ⟨1280895791992653612942679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1707861055990204817256905 1280895791992653612942679)
            ·
              refine ⟨1921343687988980419414019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1280895791992653612942679 1921343687988980419414019)
              ·
                refine ⟨2882015531983470629121029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1921343687988980419414019 2882015531983470629121029)
                ·
                  refine ⟨540377912246900742960193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2882015531983470629121029 540377912246900742960193)
                  ·
                    refine ⟨405283434185175557220145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 540377912246900742960193 405283434185175557220145)
                    ·
                      refine ⟨303962575638881667915109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 405283434185175557220145 303962575638881667915109)
                      ·
                        rfl

theorem cell23_591965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_591965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_591965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_591965 prefixEnd_591965 := by exact prefixLift 591965
  have htrace : WordTrace (prefixWord ++ tailWord_591965) baseStart_591965 baseEnd_591965 := by
    simpa [prefixWord, tailWord_591965, baseEnd_591965] using wordTrace_append hprefix tailTrace_591965
  have hstable : (prefixWord ++ tailWord_591965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591965).length < 2 ^ (prefixWord ++ tailWord_591965).sum := by decide
  have hdescent : baseEnd_591965 < baseStart_591965 := by decide
  rcases family_descends (prefixWord ++ tailWord_591965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591977 : List Nat := [1, 2, 1, 1, 1, 5, 2, 1, 1, 1, 7]
def baseStart_591977 : Nat := 118140960795 + 591977 * 2 ^ 59
def prefixEnd_591977 : Nat := 4983230072969 + 3 ^ 40 * 591977 * 2
def baseEnd_591977 : Nat := 303968737406735620965053

theorem tailTrace_591977 : CollatzResearch.WordTrace tailWord_591977 prefixEnd_591977 303968737406735620965053 := by
  unfold tailWord_591977
  simp only [CollatzResearch.WordTrace]
  refine ⟨21591174976375905467598185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14394116650917270311732123 21591174976375905467598185)
  ·
    refine ⟨16193381232281929100698639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21591174976375905467598185 16193381232281929100698639)
    ·
      refine ⟨24290071848422893651047959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16193381232281929100698639 24290071848422893651047959)
      ·
        refine ⟨36435107772634340476571939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24290071848422893651047959 36435107772634340476571939)
        ·
          refine ⟨54652661658951510714857909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36435107772634340476571939 54652661658951510714857909)
          ·
            refine ⟨5123687030526704129517929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54652661658951510714857909 5123687030526704129517929)
            ·
              refine ⟨3842765272895028097138447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5123687030526704129517929 3842765272895028097138447)
              ·
                refine ⟨5764147909342542145707671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3842765272895028097138447 5764147909342542145707671)
                ·
                  refine ⟨8646221864013813218561507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5764147909342542145707671 8646221864013813218561507)
                  ·
                    refine ⟨12969332796020719827842261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8646221864013813218561507 12969332796020719827842261)
                    ·
                      refine ⟨303968737406735620965053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 12969332796020719827842261 303968737406735620965053)
                      ·
                        rfl

theorem cell23_591977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 1, 7].length) (baseStart_591977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_591977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_591977 prefixEnd_591977 := by exact prefixLift 591977
  have htrace : WordTrace (prefixWord ++ tailWord_591977) baseStart_591977 baseEnd_591977 := by
    simpa [prefixWord, tailWord_591977, baseEnd_591977] using wordTrace_append hprefix tailTrace_591977
  have hstable : (prefixWord ++ tailWord_591977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591977).length < 2 ^ (prefixWord ++ tailWord_591977).sum := by decide
  have hdescent : baseEnd_591977 < baseStart_591977 := by decide
  rcases family_descends (prefixWord ++ tailWord_591977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592004 : List Nat := [2, 3, 2, 1, 2, 1, 1, 3, 1, 3, 4]
def baseStart_592004 : Nat := 118140960795 + 592004 * 2 ^ 59
def prefixEnd_592004 : Nat := 4983230072969 + 3 ^ 40 * 592004 * 2
def baseEnd_592004 : Nat := 303982601384407015327429

theorem tailTrace_592004 : CollatzResearch.WordTrace tailWord_592004 prefixEnd_592004 303982601384407015327429 := by
  unfold tailWord_592004
  simp only [CollatzResearch.WordTrace]
  refine ⟨10796079873639044539415533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14394773164852059385887377 10796079873639044539415533)
  ·
    refine ⟨4048529952614641702280825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10796079873639044539415533 4048529952614641702280825)
    ·
      refine ⟨3036397464460981276710619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4048529952614641702280825 3036397464460981276710619)
      ·
        refine ⟨4554596196691471915065929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3036397464460981276710619 4554596196691471915065929)
        ·
          refine ⟨3415947147518603936299447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4554596196691471915065929 3415947147518603936299447)
          ·
            refine ⟨5123920721277905904449171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3415947147518603936299447 5123920721277905904449171)
            ·
              refine ⟨7685881081916858856673757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5123920721277905904449171 7685881081916858856673757)
              ·
                refine ⟨2882205405718822071252659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7685881081916858856673757 2882205405718822071252659)
                ·
                  refine ⟨4323308108578233106878989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2882205405718822071252659 4323308108578233106878989)
                  ·
                    refine ⟨1621240540716837415079621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4323308108578233106878989 1621240540716837415079621)
                    ·
                      refine ⟨303982601384407015327429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1621240540716837415079621 303982601384407015327429)
                      ·
                        rfl

theorem cell23_592004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_592004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_592004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_592004 prefixEnd_592004 := by exact prefixLift 592004
  have htrace : WordTrace (prefixWord ++ tailWord_592004) baseStart_592004 baseEnd_592004 := by
    simpa [prefixWord, tailWord_592004, baseEnd_592004] using wordTrace_append hprefix tailTrace_592004
  have hstable : (prefixWord ++ tailWord_592004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592004).length < 2 ^ (prefixWord ++ tailWord_592004).sum := by decide
  have hdescent : baseEnd_592004 < baseStart_592004 := by decide
  rcases family_descends (prefixWord ++ tailWord_592004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592027 : List Nat := [1, 1, 1, 1, 1, 1, 2, 7, 8]
def baseStart_592027 : Nat := 118140960795 + 592027 * 2 ^ 59
def prefixEnd_592027 : Nat := 4983230072969 + 3 ^ 40 * 592027 * 2
def baseEnd_592027 : Nat := 33777156826606713926647

theorem tailTrace_592027 : CollatzResearch.WordTrace tailWord_592027 prefixEnd_592027 33777156826606713926647 := by
  unfold tailWord_592027
  simp only [CollatzResearch.WordTrace]
  refine ⟨21592998626194764006918335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14395332417463176004612223 21592998626194764006918335)
  ·
    refine ⟨32389497939292146010377503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21592998626194764006918335 32389497939292146010377503)
    ·
      refine ⟨48584246908938219015566255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32389497939292146010377503 48584246908938219015566255)
      ·
        refine ⟨72876370363407328523349383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48584246908938219015566255 72876370363407328523349383)
        ·
          refine ⟨109314555545110992785024075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72876370363407328523349383 109314555545110992785024075)
          ·
            refine ⟨163971833317666489177536113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109314555545110992785024075 163971833317666489177536113)
            ·
              refine ⟨122978874988249866883152085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 163971833317666489177536113 122978874988249866883152085)
              ·
                refine ⟨2882317382537106255073877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 122978874988249866883152085 2882317382537106255073877)
                ·
                  refine ⟨33777156826606713926647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2882317382537106255073877 33777156826606713926647)
                  ·
                    rfl

theorem cell23_592027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 8].length) (baseStart_592027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_592027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_592027 prefixEnd_592027 := by exact prefixLift 592027
  have htrace : WordTrace (prefixWord ++ tailWord_592027) baseStart_592027 baseEnd_592027 := by
    simpa [prefixWord, tailWord_592027, baseEnd_592027] using wordTrace_append hprefix tailTrace_592027
  have hstable : (prefixWord ++ tailWord_592027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592027).length < 2 ^ (prefixWord ++ tailWord_592027).sum := by decide
  have hdescent : baseEnd_592027 < baseStart_592027 := by decide
  rcases family_descends (prefixWord ++ tailWord_592027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592052 : List Nat := [2, 5, 3, 1, 1, 1, 2, 1, 2, 5]
def baseStart_592052 : Nat := 118140960795 + 592052 * 2 ^ 59
def prefixEnd_592052 : Nat := 4983230072969 + 3 ^ 40 * 592052 * 2
def baseEnd_592052 : Nat := 101335749485274275842403

theorem tailTrace_592052 : CollatzResearch.WordTrace tailWord_592052 prefixEnd_592052 101335749485274275842403 := by
  unfold tailWord_592052
  simp only [CollatzResearch.WordTrace]
  refine ⟨10796955225552096638289205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14395940300736128851052273 10796955225552096638289205)
  ·
    refine ⟨1012214552395509059839613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10796955225552096638289205 1012214552395509059839613)
    ·
      refine ⟨379580457148315897439855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1012214552395509059839613 379580457148315897439855)
      ·
        refine ⟨569370685722473846159783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 379580457148315897439855 569370685722473846159783)
        ·
          refine ⟨854056028583710769239675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 569370685722473846159783 854056028583710769239675)
          ·
            refine ⟨1281084042875566153859513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 854056028583710769239675 1281084042875566153859513)
            ·
              refine ⟨960813032156674615394635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1281084042875566153859513 960813032156674615394635)
              ·
                refine ⟨1441219548235011923091953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 960813032156674615394635 1441219548235011923091953)
                ·
                  refine ⟨1080914661176258942318965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1441219548235011923091953 1080914661176258942318965)
                  ·
                    refine ⟨101335749485274275842403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1080914661176258942318965 101335749485274275842403)
                    ·
                      rfl

theorem cell23_592052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_592052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_592052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_592052 prefixEnd_592052 := by exact prefixLift 592052
  have htrace : WordTrace (prefixWord ++ tailWord_592052) baseStart_592052 baseEnd_592052 := by
    simpa [prefixWord, tailWord_592052, baseEnd_592052] using wordTrace_append hprefix tailTrace_592052
  have hstable : (prefixWord ++ tailWord_592052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592052).length < 2 ^ (prefixWord ++ tailWord_592052).sum := by decide
  have hdescent : baseEnd_592052 < baseStart_592052 := by decide
  rcases family_descends (prefixWord ++ tailWord_592052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592082 : List Nat := [3, 2, 2, 2, 1, 4, 2, 2, 1, 4]
def baseStart_592082 : Nat := 118140960795 + 592082 * 2 ^ 59
def prefixEnd_592082 : Nat := 4983230072969 + 3 ^ 40 * 592082 * 2
def baseEnd_592082 : Nat := 101340884291819236717357

theorem tailTrace_592082 : CollatzResearch.WordTrace tailWord_592082 prefixEnd_592082 101340884291819236717357 := by
  unfold tailWord_592082
  simp only [CollatzResearch.WordTrace]
  refine ⟨5398751160248877100042625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14396669760663672266780333 5398751160248877100042625)
  ·
    refine ⟨4049063370186657825031969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5398751160248877100042625 4049063370186657825031969)
    ·
      refine ⟨3036797527639993368773977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4049063370186657825031969 3036797527639993368773977)
      ·
        refine ⟨2277598145729995026580483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3036797527639993368773977 2277598145729995026580483)
        ·
          refine ⟨3416397218594992539870725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2277598145729995026580483 3416397218594992539870725)
          ·
            refine ⟨640574478486561101225761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3416397218594992539870725 640574478486561101225761)
            ·
              refine ⟨480430858864920825919321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 640574478486561101225761 480430858864920825919321)
              ·
                refine ⟨360323144148690619439491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 480430858864920825919321 360323144148690619439491)
                ·
                  refine ⟨540484716223035929159237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 360323144148690619439491 540484716223035929159237)
                  ·
                    refine ⟨101340884291819236717357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 540484716223035929159237 101340884291819236717357)
                    ·
                      rfl

theorem cell23_592082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 2, 2, 1, 4].length) (baseStart_592082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_592082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_592082 prefixEnd_592082 := by exact prefixLift 592082
  have htrace : WordTrace (prefixWord ++ tailWord_592082) baseStart_592082 baseEnd_592082 := by
    simpa [prefixWord, tailWord_592082, baseEnd_592082] using wordTrace_append hprefix tailTrace_592082
  have hstable : (prefixWord ++ tailWord_592082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592082).length < 2 ^ (prefixWord ++ tailWord_592082).sum := by decide
  have hdescent : baseEnd_592082 < baseStart_592082 := by decide
  rcases family_descends (prefixWord ++ tailWord_592082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592111 : List Nat := [1, 1, 2, 1, 6, 1, 2, 1, 3, 1, 4]
def baseStart_592111 : Nat := 118140960795 + 592111 * 2 ^ 59
def prefixEnd_592111 : Nat := 4983230072969 + 3 ^ 40 * 592111 * 2
def baseEnd_592111 : Nat := 304037543814438096689437

theorem tailTrace_592111 : CollatzResearch.WordTrace tailWord_592111 prefixEnd_592111 304037543814438096689437 := by
  unfold tailWord_592111
  simp only [CollatzResearch.WordTrace]
  refine ⟨21596062357890446352976187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14397374905260297568650791 21596062357890446352976187)
  ·
    refine ⟨32394093536835669529464281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21596062357890446352976187 32394093536835669529464281)
    ·
      refine ⟨24295570152626752147098211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32394093536835669529464281 24295570152626752147098211)
      ·
        refine ⟨36443355228940128220647317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24295570152626752147098211 36443355228940128220647317)
        ·
          refine ⟨1708282276356568510342843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 36443355228940128220647317 1708282276356568510342843)
          ·
            refine ⟨2562423414534852765514265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1708282276356568510342843 2562423414534852765514265)
            ·
              refine ⟨1921817560901139574135699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2562423414534852765514265 1921817560901139574135699)
              ·
                refine ⟨2882726341351709361203549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1921817560901139574135699 2882726341351709361203549)
                ·
                  refine ⟨1081022378006891010451331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2882726341351709361203549 1081022378006891010451331)
                  ·
                    refine ⟨1621533567010336515676997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1081022378006891010451331 1621533567010336515676997)
                    ·
                      refine ⟨304037543814438096689437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1621533567010336515676997 304037543814438096689437)
                      ·
                        rfl

theorem cell23_592111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 3, 1, 4].length) (baseStart_592111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_592111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_592111 prefixEnd_592111 := by exact prefixLift 592111
  have htrace : WordTrace (prefixWord ++ tailWord_592111) baseStart_592111 baseEnd_592111 := by
    simpa [prefixWord, tailWord_592111, baseEnd_592111] using wordTrace_append hprefix tailTrace_592111
  have hstable : (prefixWord ++ tailWord_592111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592111).length < 2 ^ (prefixWord ++ tailWord_592111).sum := by decide
  have hdescent : baseEnd_592111 < baseStart_592111 := by decide
  rcases family_descends (prefixWord ++ tailWord_592111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592128 : List Nat := [2, 1, 1, 2, 1, 1, 8, 1, 1, 1, 4]
def baseStart_592128 : Nat := 118140960795 + 592128 * 2 ^ 59
def prefixEnd_592128 : Nat := 4983230072969 + 3 ^ 40 * 592128 * 2
def baseEnd_592128 : Nat := 304046272985564530176859

theorem tailTrace_592128 : CollatzResearch.WordTrace tailWord_592128 prefixEnd_592128 304046272985564530176859 := by
  unfold tailWord_592128
  simp only [CollatzResearch.WordTrace]
  refine ⟨10798341199414429128172519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14397788265885905504230025 10798341199414429128172519)
  ·
    refine ⟨16197511799121643692258779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10798341199414429128172519 16197511799121643692258779)
    ·
      refine ⟨24296267698682465538388169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16197511799121643692258779 24296267698682465538388169)
      ·
        refine ⟨18222200774011849153791127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24296267698682465538388169 18222200774011849153791127)
        ·
          refine ⟨27333301161017773730686691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18222200774011849153791127 27333301161017773730686691)
          ·
            refine ⟨40999951741526660596030037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27333301161017773730686691 40999951741526660596030037)
            ·
              refine ⟨480468184471015553859727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 40999951741526660596030037 480468184471015553859727)
              ·
                refine ⟨720702276706523330789591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 480468184471015553859727 720702276706523330789591)
                ·
                  refine ⟨1081053415059784996184387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 720702276706523330789591 1081053415059784996184387)
                  ·
                    refine ⟨1621580122589677494276581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1081053415059784996184387 1621580122589677494276581)
                    ·
                      refine ⟨304046272985564530176859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1621580122589677494276581 304046272985564530176859)
                      ·
                        rfl

theorem cell23_592128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 8, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 8, 1, 1, 1, 4].length) (baseStart_592128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_592128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_592128 prefixEnd_592128 := by exact prefixLift 592128
  have htrace : WordTrace (prefixWord ++ tailWord_592128) baseStart_592128 baseEnd_592128 := by
    simpa [prefixWord, tailWord_592128, baseEnd_592128] using wordTrace_append hprefix tailTrace_592128
  have hstable : (prefixWord ++ tailWord_592128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592128).length < 2 ^ (prefixWord ++ tailWord_592128).sum := by decide
  have hdescent : baseEnd_592128 < baseStart_592128 := by decide
  rcases family_descends (prefixWord ++ tailWord_592128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592138 : List Nat := [3, 1, 2, 2, 1, 1, 5, 2, 2, 4]
def baseStart_592138 : Nat := 118140960795 + 592138 * 2 ^ 59
def prefixEnd_592138 : Nat := 4983230072969 + 3 ^ 40 * 592138 * 2
def baseEnd_592138 : Nat := 101350469264036497017271

theorem tailTrace_592138 : CollatzResearch.WordTrace tailWord_592138 prefixEnd_592138 101350469264036497017271 := by
  unfold tailWord_592138
  simp only [CollatzResearch.WordTrace]
  refine ⟨5399261782198157491052267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14398031419195086642806045 5399261782198157491052267)
  ·
    refine ⟨8098892673297236236578401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5399261782198157491052267 8098892673297236236578401)
    ·
      refine ⟨6074169504972927177433801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8098892673297236236578401 6074169504972927177433801)
      ·
        refine ⟨4555627128729695383075351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6074169504972927177433801 4555627128729695383075351)
        ·
          refine ⟨6833440693094543074613027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4555627128729695383075351 6833440693094543074613027)
          ·
            refine ⟨10250161039641814611919541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6833440693094543074613027 10250161039641814611919541)
            ·
              refine ⟨960952597466420119867457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10250161039641814611919541 960952597466420119867457)
              ·
                refine ⟨720714448099815089900593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 960952597466420119867457 720714448099815089900593)
                ·
                  refine ⟨540535836074861317425445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 720714448099815089900593 540535836074861317425445)
                  ·
                    refine ⟨101350469264036497017271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 540535836074861317425445 101350469264036497017271)
                    ·
                      rfl

theorem cell23_592138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 2, 2, 4].length) (baseStart_592138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_592138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_592138 prefixEnd_592138 := by exact prefixLift 592138
  have htrace : WordTrace (prefixWord ++ tailWord_592138) baseStart_592138 baseEnd_592138 := by
    simpa [prefixWord, tailWord_592138, baseEnd_592138] using wordTrace_append hprefix tailTrace_592138
  have hstable : (prefixWord ++ tailWord_592138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592138).length < 2 ^ (prefixWord ++ tailWord_592138).sum := by decide
  have hdescent : baseEnd_592138 < baseStart_592138 := by decide
  rcases family_descends (prefixWord ++ tailWord_592138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592145 : List Nat := [1, 2, 2, 1, 1, 6, 2, 1, 3, 2, 2]
def baseStart_592145 : Nat := 118140960795 + 592145 * 2 ^ 59
def prefixEnd_592145 : Nat := 4983230072969 + 3 ^ 40 * 592145 * 2
def baseEnd_592145 : Nat := 304055002156690963664281

theorem tailTrace_592145 : CollatzResearch.WordTrace tailWord_592145 prefixEnd_592145 304055002156690963664281 := by
  unfold tailWord_592145
  simp only [CollatzResearch.WordTrace]
  refine ⟨21597302439767270159713889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14398201626511513439809259 21597302439767270159713889)
  ·
    refine ⟨16197976829825452619785417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21597302439767270159713889 16197976829825452619785417)
    ·
      refine ⟨12148482622369089464839063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16197976829825452619785417 12148482622369089464839063)
      ·
        refine ⟨18222723933553634197258595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12148482622369089464839063 18222723933553634197258595)
        ·
          refine ⟨27334085900330451295887893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18222723933553634197258595 27334085900330451295887893)
          ·
            refine ⟨1281285276577989904494745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 27334085900330451295887893 1281285276577989904494745)
            ·
              refine ⟨960963957433492428371059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1281285276577989904494745 960963957433492428371059)
              ·
                refine ⟨1441445936150238642556589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 960963957433492428371059 1441445936150238642556589)
                ·
                  refine ⟨540542226056339490958721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1441445936150238642556589 540542226056339490958721)
                  ·
                    refine ⟨405406669542254618219041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 540542226056339490958721 405406669542254618219041)
                    ·
                      refine ⟨304055002156690963664281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 405406669542254618219041 304055002156690963664281)
                      ·
                        rfl

theorem cell23_592145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 1, 3, 2, 2].length) (baseStart_592145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_592145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_592145 prefixEnd_592145 := by exact prefixLift 592145
  have htrace : WordTrace (prefixWord ++ tailWord_592145) baseStart_592145 baseEnd_592145 := by
    simpa [prefixWord, tailWord_592145, baseEnd_592145] using wordTrace_append hprefix tailTrace_592145
  have hstable : (prefixWord ++ tailWord_592145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592145).length < 2 ^ (prefixWord ++ tailWord_592145).sum := by decide
  have hdescent : baseEnd_592145 < baseStart_592145 := by decide
  rcases family_descends (prefixWord ++ tailWord_592145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592165 : List Nat := [1, 3, 1, 2, 5, 1, 2, 2, 1, 2, 3]
def baseStart_592165 : Nat := 118140960795 + 592165 * 2 ^ 59
def prefixEnd_592165 : Nat := 4983230072969 + 3 ^ 40 * 592165 * 2
def baseEnd_592165 : Nat := 304065271769780885414189

theorem tailTrace_592165 : CollatzResearch.WordTrace tailWord_592165 prefixEnd_592165 304065271769780885414189 := by
  unfold tailWord_592165
  simp only [CollatzResearch.WordTrace]
  refine ⟨21598031899694813575441949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14398687933129875716961299 21598031899694813575441949)
  ·
    refine ⟨8099261962385555090790731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21598031899694813575441949 8099261962385555090790731)
    ·
      refine ⟨12148892943578332636186097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8099261962385555090790731 12148892943578332636186097)
      ·
        refine ⟨9111669707683749477139573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12148892943578332636186097 9111669707683749477139573)
        ·
          refine ⟨854219035095351513481835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9111669707683749477139573 854219035095351513481835)
          ·
            refine ⟨1281328552643027270222753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 854219035095351513481835 1281328552643027270222753)
            ·
              refine ⟨960996414482270452667065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1281328552643027270222753 960996414482270452667065)
              ·
                refine ⟨720747310861702839500299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 960996414482270452667065 720747310861702839500299)
                ·
                  refine ⟨1081120966292554259250449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 720747310861702839500299 1081120966292554259250449)
                  ·
                    refine ⟨810840724719415694437837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1081120966292554259250449 810840724719415694437837)
                    ·
                      refine ⟨304065271769780885414189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 810840724719415694437837 304065271769780885414189)
                      ·
                        rfl

theorem cell23_592165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 2, 1, 2, 3].length) (baseStart_592165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_592165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_592165 prefixEnd_592165 := by exact prefixLift 592165
  have htrace : WordTrace (prefixWord ++ tailWord_592165) baseStart_592165 baseEnd_592165 := by
    simpa [prefixWord, tailWord_592165, baseEnd_592165] using wordTrace_append hprefix tailTrace_592165
  have hstable : (prefixWord ++ tailWord_592165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592165).length < 2 ^ (prefixWord ++ tailWord_592165).sum := by decide
  have hdescent : baseEnd_592165 < baseStart_592165 := by decide
  rcases family_descends (prefixWord ++ tailWord_592165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592196 : List Nat := [2, 3, 4, 1, 3, 1, 1, 1, 3, 2, 2]
def baseStart_592196 : Nat := 118140960795 + 592196 * 2 ^ 59
def prefixEnd_592196 : Nat := 4983230072969 + 3 ^ 40 * 592196 * 2
def baseEnd_592196 : Nat := 304081189670070264126547

theorem tailTrace_592196 : CollatzResearch.WordTrace tailWord_592196 prefixEnd_592196 304081189670070264126547 := by
  unfold tailWord_592196
  simp only [CollatzResearch.WordTrace]
  refine ⟨10799581281291252934910221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14399441708388337246546961 10799581281291252934910221)
  ·
    refine ⟨4049842980484219850591333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10799581281291252934910221 4049842980484219850591333)
    ·
      refine ⟨759345558840791221985875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4049842980484219850591333 759345558840791221985875)
      ·
        refine ⟨1139018338261186832978813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 759345558840791221985875 1139018338261186832978813)
        ·
          refine ⟨427131876847945062367055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1139018338261186832978813 427131876847945062367055)
          ·
            refine ⟨640697815271917593550583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 427131876847945062367055 640697815271917593550583)
            ·
              refine ⟨961046722907876390325875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 640697815271917593550583 961046722907876390325875)
              ·
                refine ⟨1441570084361814585488813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 961046722907876390325875 1441570084361814585488813)
                ·
                  refine ⟨540588781635680469558305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1441570084361814585488813 540588781635680469558305)
                  ·
                    refine ⟨405441586226760352168729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 540588781635680469558305 405441586226760352168729)
                    ·
                      refine ⟨304081189670070264126547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 405441586226760352168729 304081189670070264126547)
                      ·
                        rfl

theorem cell23_592196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_592196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_592196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_592196 prefixEnd_592196 := by exact prefixLift 592196
  have htrace : WordTrace (prefixWord ++ tailWord_592196) baseStart_592196 baseEnd_592196 := by
    simpa [prefixWord, tailWord_592196, baseEnd_592196] using wordTrace_append hprefix tailTrace_592196
  have hstable : (prefixWord ++ tailWord_592196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592196).length < 2 ^ (prefixWord ++ tailWord_592196).sum := by decide
  have hdescent : baseEnd_592196 < baseStart_592196 := by decide
  rcases family_descends (prefixWord ++ tailWord_592196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592212 : List Nat := [2, 4, 1, 1, 2, 2, 4, 1, 2, 1, 3]
def baseStart_592212 : Nat := 118140960795 + 592212 * 2 ^ 59
def prefixEnd_592212 : Nat := 4983230072969 + 3 ^ 40 * 592212 * 2
def baseEnd_592212 : Nat := 304089405360542201526473

theorem tailTrace_592212 : CollatzResearch.WordTrace tailWord_592212 prefixEnd_592212 304089405360542201526473 := by
  unfold tailWord_592212
  simp only [CollatzResearch.WordTrace]
  refine ⟨10799873065262270301201445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14399830753683027068268593 10799873065262270301201445)
  ·
    refine ⟨2024976199736675681475271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10799873065262270301201445 2024976199736675681475271)
    ·
      refine ⟨3037464299605013522212907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2024976199736675681475271 3037464299605013522212907)
      ·
        refine ⟨4556196449407520283319361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3037464299605013522212907 4556196449407520283319361)
        ·
          refine ⟨3417147337055640212489521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4556196449407520283319361 3417147337055640212489521)
          ·
            refine ⟨2562860502791730159367141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3417147337055640212489521 2562860502791730159367141)
            ·
              refine ⟨480536344273449404881339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2562860502791730159367141 480536344273449404881339)
              ·
                refine ⟨720804516410174107322009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 480536344273449404881339 720804516410174107322009)
                ·
                  refine ⟨540603387307630580491507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 720804516410174107322009 540603387307630580491507)
                  ·
                    refine ⟨810905080961445870737261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 540603387307630580491507 810905080961445870737261)
                    ·
                      refine ⟨304089405360542201526473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 810905080961445870737261 304089405360542201526473)
                      ·
                        rfl

theorem cell23_592212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 4, 1, 2, 1, 3].length) (baseStart_592212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_592212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_592212 prefixEnd_592212 := by exact prefixLift 592212
  have htrace : WordTrace (prefixWord ++ tailWord_592212) baseStart_592212 baseEnd_592212 := by
    simpa [prefixWord, tailWord_592212, baseEnd_592212] using wordTrace_append hprefix tailTrace_592212
  have hstable : (prefixWord ++ tailWord_592212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592212).length < 2 ^ (prefixWord ++ tailWord_592212).sum := by decide
  have hdescent : baseEnd_592212 < baseStart_592212 := by decide
  rcases family_descends (prefixWord ++ tailWord_592212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592218 : List Nat := [3, 1, 1, 2, 1, 2, 1, 5, 1, 4, 2]
def baseStart_592218 : Nat := 118140960795 + 592218 * 2 ^ 59
def prefixEnd_592218 : Nat := 4983230072969 + 3 ^ 40 * 592218 * 2
def baseEnd_592218 : Nat := 304092486244469178051445

theorem tailTrace_592218 : CollatzResearch.WordTrace tailWord_592218 prefixEnd_592218 304092486244469178051445 := by
  unfold tailWord_592218
  simp only [CollatzResearch.WordTrace]
  refine ⟨5399991242125700906780327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14399976645668535751414205 5399991242125700906780327)
  ·
    refine ⟨8099986863188551360170491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5399991242125700906780327 8099986863188551360170491)
    ·
      refine ⟨12149980294782827040255737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8099986863188551360170491 12149980294782827040255737)
      ·
        refine ⟨9112485221087120280191803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12149980294782827040255737 9112485221087120280191803)
        ·
          refine ⟨13668727831630680420287705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9112485221087120280191803 13668727831630680420287705)
          ·
            refine ⟨10251545873723010315215779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13668727831630680420287705 10251545873723010315215779)
            ·
              refine ⟨15377318810584515472823669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10251545873723010315215779 15377318810584515472823669)
              ·
                refine ⟨1441623638492298325577219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15377318810584515472823669 1441623638492298325577219)
                ·
                  refine ⟨2162435457738447488365829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1441623638492298325577219 2162435457738447488365829)
                  ·
                    refine ⟨405456648325958904068593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2162435457738447488365829 405456648325958904068593)
                    ·
                      refine ⟨304092486244469178051445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 405456648325958904068593 304092486244469178051445)
                      ·
                        rfl

theorem cell23_592218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 5, 1, 4, 2].length) (baseStart_592218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_592218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_592218 prefixEnd_592218 := by exact prefixLift 592218
  have htrace : WordTrace (prefixWord ++ tailWord_592218) baseStart_592218 baseEnd_592218 := by
    simpa [prefixWord, tailWord_592218, baseEnd_592218] using wordTrace_append hprefix tailTrace_592218
  have hstable : (prefixWord ++ tailWord_592218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592218).length < 2 ^ (prefixWord ++ tailWord_592218).sum := by decide
  have hdescent : baseEnd_592218 < baseStart_592218 := by decide
  rcases family_descends (prefixWord ++ tailWord_592218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592268 : List Nat := [2, 2, 1, 2, 1, 5, 1, 1, 2, 3, 3]
def baseStart_592268 : Nat := 118140960795 + 592268 * 2 ^ 59
def prefixEnd_592268 : Nat := 4983230072969 + 3 ^ 40 * 592268 * 2
def baseEnd_592268 : Nat := 304118160277193982426215

theorem tailTrace_592268 : CollatzResearch.WordTrace tailWord_592268 prefixEnd_592268 304118160277193982426215 := by
  unfold tailWord_592268
  simp only [CollatzResearch.WordTrace]
  refine ⟨10800894309160831083220729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14401192412214441444294305 10800894309160831083220729)
  ·
    refine ⟨8100670731870623312415547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10800894309160831083220729 8100670731870623312415547)
    ·
      refine ⟨12151006097805934968623321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8100670731870623312415547 12151006097805934968623321)
      ·
        refine ⟨9113254573354451226467491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12151006097805934968623321 9113254573354451226467491)
        ·
          refine ⟨13669881860031676839701237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9113254573354451226467491 13669881860031676839701237)
          ·
            refine ⟨1281551424377969703721991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13669881860031676839701237 1281551424377969703721991)
            ·
              refine ⟨1922327136566954555582987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1281551424377969703721991 1922327136566954555582987)
              ·
                refine ⟨2883490704850431833374481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1922327136566954555582987 2883490704850431833374481)
                ·
                  refine ⟨2162618028637823875030861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2883490704850431833374481 2162618028637823875030861)
                  ·
                    refine ⟨810981760739183953136573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2162618028637823875030861 810981760739183953136573)
                    ·
                      refine ⟨304118160277193982426215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 810981760739183953136573 304118160277193982426215)
                      ·
                        rfl

theorem cell23_592268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 2, 3, 3].length) (baseStart_592268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_592268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_592268 prefixEnd_592268 := by exact prefixLift 592268
  have htrace : WordTrace (prefixWord ++ tailWord_592268) baseStart_592268 baseEnd_592268 := by
    simpa [prefixWord, tailWord_592268, baseEnd_592268] using wordTrace_append hprefix tailTrace_592268
  have hstable : (prefixWord ++ tailWord_592268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592268).length < 2 ^ (prefixWord ++ tailWord_592268).sum := by decide
  have hdescent : baseEnd_592268 < baseStart_592268 := by decide
  rcases family_descends (prefixWord ++ tailWord_592268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592288 : List Nat := [2, 1, 1, 4, 1, 3, 3, 1, 2, 5]
def baseStart_592288 : Nat := 118140960795 + 592288 * 2 ^ 59
def prefixEnd_592288 : Nat := 4983230072969 + 3 ^ 40 * 592288 * 2
def baseEnd_592288 : Nat := 101376143296761301392041

theorem tailTrace_592288 : CollatzResearch.WordTrace tailWord_592288 prefixEnd_592288 101376143296761301392041 := by
  unfold tailWord_592288
  simp only [CollatzResearch.WordTrace]
  refine ⟨10801259039124602791084759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14401678718832803721446345 10801259039124602791084759)
  ·
    refine ⟨16201888558686904186627139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10801259039124602791084759 16201888558686904186627139)
    ·
      refine ⟨24302832838030356279940709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16201888558686904186627139 24302832838030356279940709)
      ·
        refine ⟨4556781157130691802488883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24302832838030356279940709 4556781157130691802488883)
        ·
          refine ⟨6835171735696037703733325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4556781157130691802488883 6835171735696037703733325)
          ·
            refine ⟨2563189400886014138899997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6835171735696037703733325 2563189400886014138899997)
            ·
              refine ⟨961196025332255302087499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2563189400886014138899997 961196025332255302087499)
              ·
                refine ⟨1441794037998382953131249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 961196025332255302087499 1441794037998382953131249)
                ·
                  refine ⟨1081345528498787214848437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1441794037998382953131249 1081345528498787214848437)
                  ·
                    refine ⟨101376143296761301392041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1081345528498787214848437 101376143296761301392041)
                    ·
                      rfl

theorem cell23_592288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 1, 2, 5].length) (baseStart_592288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_592288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_592288 prefixEnd_592288 := by exact prefixLift 592288
  have htrace : WordTrace (prefixWord ++ tailWord_592288) baseStart_592288 baseEnd_592288 := by
    simpa [prefixWord, tailWord_592288, baseEnd_592288] using wordTrace_append hprefix tailTrace_592288
  have hstable : (prefixWord ++ tailWord_592288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592288).length < 2 ^ (prefixWord ++ tailWord_592288).sum := by decide
  have hdescent : baseEnd_592288 < baseStart_592288 := by decide
  rcases family_descends (prefixWord ++ tailWord_592288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592328 : List Nat := [2, 1, 3, 1, 3, 2, 1, 2, 1, 4, 3]
def baseStart_592328 : Nat := 118140960795 + 592328 * 2 ^ 59
def prefixEnd_592328 : Nat := 4983230072969 + 3 ^ 40 * 592328 * 2
def baseEnd_592328 : Nat := 304148969116463747675939

theorem tailTrace_592328 : CollatzResearch.WordTrace tailWord_592328 prefixEnd_592328 304148969116463747675939 := by
  unfold tailWord_592328
  simp only [CollatzResearch.WordTrace]
  refine ⟨10801988499052146206812819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14402651332069528275750425 10801988499052146206812819)
  ·
    refine ⟨16202982748578219310219229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10801988499052146206812819 16202982748578219310219229)
    ·
      refine ⟨6076118530716832241332211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16202982748578219310219229 6076118530716832241332211)
      ·
        refine ⟨9114177796075248361998317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6076118530716832241332211 9114177796075248361998317)
        ·
          refine ⟨3417816673528218135749369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9114177796075248361998317 3417816673528218135749369)
          ·
            refine ⟨2563362505146163601812027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3417816673528218135749369 2563362505146163601812027)
            ·
              refine ⟨3845043757719245402718041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2563362505146163601812027 3845043757719245402718041)
              ·
                refine ⟨2883782818289434052038531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3845043757719245402718041 2883782818289434052038531)
                ·
                  refine ⟨4325674227434151078057797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2883782818289434052038531 4325674227434151078057797)
                  ·
                    refine ⟨811063917643903327135837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4325674227434151078057797 811063917643903327135837)
                    ·
                      refine ⟨304148969116463747675939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 811063917643903327135837 304148969116463747675939)
                      ·
                        rfl

theorem cell23_592328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 1, 4, 3].length) (baseStart_592328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_592328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_592328 prefixEnd_592328 := by exact prefixLift 592328
  have htrace : WordTrace (prefixWord ++ tailWord_592328) baseStart_592328 baseEnd_592328 := by
    simpa [prefixWord, tailWord_592328, baseEnd_592328] using wordTrace_append hprefix tailTrace_592328
  have hstable : (prefixWord ++ tailWord_592328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592328).length < 2 ^ (prefixWord ++ tailWord_592328).sum := by decide
  have hdescent : baseEnd_592328 < baseStart_592328 := by decide
  rcases family_descends (prefixWord ++ tailWord_592328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592395 : List Nat := [1, 1, 1, 1, 7, 1, 3, 2, 1, 5]
def baseStart_592395 : Nat := 118140960795 + 592395 * 2 ^ 59
def prefixEnd_592395 : Nat := 4983230072969 + 3 ^ 40 * 592395 * 2
def baseEnd_592395 : Nat := 101394457440104995179377

theorem tailTrace_592395 : CollatzResearch.WordTrace tailWord_592395 prefixEnd_592395 101394457440104995179377 := by
  unfold tailWord_592395
  simp only [CollatzResearch.WordTrace]
  refine ⟨21606420688861562856314639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14404280459241041904209759 21606420688861562856314639)
  ·
    refine ⟨32409631033292344284471959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21606420688861562856314639 32409631033292344284471959)
    ·
      refine ⟨48614446549938516426707939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32409631033292344284471959 48614446549938516426707939)
      ·
        refine ⟨72921669824907774640061909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48614446549938516426707939 72921669824907774640061909)
        ·
          refine ⟨1709101636521275968126451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 72921669824907774640061909 1709101636521275968126451)
          ·
            refine ⟨2563652454781913952189677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1709101636521275968126451 2563652454781913952189677)
            ·
              refine ⟨961369670543217732071129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2563652454781913952189677 961369670543217732071129)
              ·
                refine ⟨721027252907413299053347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 961369670543217732071129 721027252907413299053347)
                ·
                  refine ⟨1081540879361119948580021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 721027252907413299053347 1081540879361119948580021)
                  ·
                    refine ⟨101394457440104995179377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1081540879361119948580021 101394457440104995179377)
                    ·
                      rfl

theorem cell23_592395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 2, 1, 5].length) (baseStart_592395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_592395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_592395 prefixEnd_592395 := by exact prefixLift 592395
  have htrace : WordTrace (prefixWord ++ tailWord_592395) baseStart_592395 baseEnd_592395 := by
    simpa [prefixWord, tailWord_592395, baseEnd_592395] using wordTrace_append hprefix tailTrace_592395
  have hstable : (prefixWord ++ tailWord_592395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592395).length < 2 ^ (prefixWord ++ tailWord_592395).sum := by decide
  have hdescent : baseEnd_592395 < baseStart_592395 := by decide
  rcases family_descends (prefixWord ++ tailWord_592395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592408 : List Nat := [2, 1, 2, 3, 3, 1, 1, 1, 3, 6]
def baseStart_592408 : Nat := 118140960795 + 592408 * 2 ^ 59
def prefixEnd_592408 : Nat := 4983230072969 + 3 ^ 40 * 592408 * 2
def baseEnd_592408 : Nat := 101396682522941144891857

theorem tailTrace_592408 : CollatzResearch.WordTrace tailWord_592408 prefixEnd_592408 101396682522941144891857 := by
  unfold tailWord_592408
  simp only [CollatzResearch.WordTrace]
  refine ⟨10803447418907233038268939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14404596558542977384358585 10803447418907233038268939)
  ·
    refine ⟨16205171128360849557403409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10803447418907233038268939 16205171128360849557403409)
    ·
      refine ⟨12153878346270637168052557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16205171128360849557403409 12153878346270637168052557)
      ·
        refine ⟨4557704379851488938019709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12153878346270637168052557 4557704379851488938019709)
        ·
          refine ⟨1709139142444308351757391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4557704379851488938019709 1709139142444308351757391)
          ·
            refine ⟨2563708713666462527636087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1709139142444308351757391 2563708713666462527636087)
            ·
              refine ⟨3845563070499693791454131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2563708713666462527636087 3845563070499693791454131)
              ·
                refine ⟨5768344605749540687181197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3845563070499693791454131 5768344605749540687181197)
                ·
                  refine ⟨2163129227156077757692949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5768344605749540687181197 2163129227156077757692949)
                  ·
                    refine ⟨101396682522941144891857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2163129227156077757692949 101396682522941144891857)
                    ·
                      rfl

theorem cell23_592408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 3, 6].length) (baseStart_592408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_592408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_592408 prefixEnd_592408 := by exact prefixLift 592408
  have htrace : WordTrace (prefixWord ++ tailWord_592408) baseStart_592408 baseEnd_592408 := by
    simpa [prefixWord, tailWord_592408, baseEnd_592408] using wordTrace_append hprefix tailTrace_592408
  have hstable : (prefixWord ++ tailWord_592408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592408).length < 2 ^ (prefixWord ++ tailWord_592408).sum := by decide
  have hdescent : baseEnd_592408 < baseStart_592408 := by decide
  rcases family_descends (prefixWord ++ tailWord_592408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592411 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 6]
def baseStart_592411 : Nat := 118140960795 + 592411 * 2 ^ 59
def prefixEnd_592411 : Nat := 4983230072969 + 3 ^ 40 * 592411 * 2
def baseEnd_592411 : Nat := 304191588010786922938057

theorem tailTrace_592411 : CollatzResearch.WordTrace tailWord_592411 prefixEnd_592411 304191588010786922938057 := by
  unfold tailWord_592411
  simp only [CollatzResearch.WordTrace]
  refine ⟨21607004256803597588897087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14404669504535731725931391 21607004256803597588897087)
  ·
    refine ⟨32410506385205396383345631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21607004256803597588897087 32410506385205396383345631)
    ·
      refine ⟨48615759577808094575018447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32410506385205396383345631 48615759577808094575018447)
      ·
        refine ⟨72923639366712141862527671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48615759577808094575018447 72923639366712141862527671)
        ·
          refine ⟨109385459050068212793791507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72923639366712141862527671 109385459050068212793791507)
          ·
            refine ⟨164078188575102319190687261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109385459050068212793791507 164078188575102319190687261)
            ·
              refine ⟨61529320715663369696507723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 164078188575102319190687261 61529320715663369696507723)
              ·
                refine ⟨92293981073495054544761585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61529320715663369696507723 92293981073495054544761585)
                ·
                  refine ⟨69220485805121290908571189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 92293981073495054544761585 69220485805121290908571189)
                  ·
                    refine ⟨6489420544230121022678549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 69220485805121290908571189 6489420544230121022678549)
                    ·
                      refine ⟨304191588010786922938057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6489420544230121022678549 304191588010786922938057)
                      ·
                        rfl

theorem cell23_592411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 6].length) (baseStart_592411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_592411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_592411 prefixEnd_592411 := by exact prefixLift 592411
  have htrace : WordTrace (prefixWord ++ tailWord_592411) baseStart_592411 baseEnd_592411 := by
    simpa [prefixWord, tailWord_592411, baseEnd_592411] using wordTrace_append hprefix tailTrace_592411
  have hstable : (prefixWord ++ tailWord_592411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592411).length < 2 ^ (prefixWord ++ tailWord_592411).sum := by decide
  have hdescent : baseEnd_592411 < baseStart_592411 := by decide
  rcases family_descends (prefixWord ++ tailWord_592411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592412 : List Nat := [2, 2, 3, 1, 2, 3, 3, 1, 1, 5]
def baseStart_592412 : Nat := 118140960795 + 592412 * 2 ^ 59
def prefixEnd_592412 : Nat := 4983230072969 + 3 ^ 40 * 592412 * 2
def baseEnd_592412 : Nat := 101397367163813806341851

theorem tailTrace_592412 : CollatzResearch.WordTrace tailWord_592412 prefixEnd_592412 101397367163813806341851 := by
  unfold tailWord_592412
  simp only [CollatzResearch.WordTrace]
  refine ⟨10803520364899987379841745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14404693819866649839788993 10803520364899987379841745)
  ·
    refine ⟨8102640273674990534881309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10803520364899987379841745 8102640273674990534881309)
    ·
      refine ⟨3038490102628121450580491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8102640273674990534881309 3038490102628121450580491)
      ·
        refine ⟨4557735153942182175870737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3038490102628121450580491 4557735153942182175870737)
        ·
          refine ⟨3418301365456636631903053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4557735153942182175870737 3418301365456636631903053)
          ·
            refine ⟨1281863012046238736963645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3418301365456636631903053 1281863012046238736963645)
            ·
              refine ⟨480698629517339526361367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1281863012046238736963645 480698629517339526361367)
              ·
                refine ⟨721047944276009289542051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 480698629517339526361367 721047944276009289542051)
                ·
                  refine ⟨1081571916414013934313077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 721047944276009289542051 1081571916414013934313077)
                  ·
                    refine ⟨101397367163813806341851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1081571916414013934313077 101397367163813806341851)
                    ·
                      rfl

theorem cell23_592412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 3, 1, 1, 5].length) (baseStart_592412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_592412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_592412 prefixEnd_592412 := by exact prefixLift 592412
  have htrace : WordTrace (prefixWord ++ tailWord_592412) baseStart_592412 baseEnd_592412 := by
    simpa [prefixWord, tailWord_592412, baseEnd_592412] using wordTrace_append hprefix tailTrace_592412
  have hstable : (prefixWord ++ tailWord_592412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592412).length < 2 ^ (prefixWord ++ tailWord_592412).sum := by decide
  have hdescent : baseEnd_592412 < baseStart_592412 := by decide
  rcases family_descends (prefixWord ++ tailWord_592412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592426 : List Nat := [3, 1, 4, 1, 1, 2, 4, 2, 1, 1, 3]
def baseStart_592426 : Nat := 118140960795 + 592426 * 2 ^ 59
def prefixEnd_592426 : Nat := 4983230072969 + 3 ^ 40 * 592426 * 2
def baseEnd_592426 : Nat := 304199290220604364250489

theorem tailTrace_592426 : CollatzResearch.WordTrace tailWord_592426 prefixEnd_592426 304199290220604364250489 := by
  unfold tailWord_592426
  simp only [CollatzResearch.WordTrace]
  refine ⟨5401887837937313787673283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14405034234499503433795421 5401887837937313787673283)
  ·
    refine ⟨8102831756905970681509925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5401887837937313787673283 8102831756905970681509925)
    ·
      refine ⟨1519280954419869502783111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8102831756905970681509925 1519280954419869502783111)
      ·
        refine ⟨2278921431629804254174667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1519280954419869502783111 2278921431629804254174667)
        ·
          refine ⟨3418382147444706381262001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2278921431629804254174667 3418382147444706381262001)
          ·
            refine ⟨2563786610583529785946501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3418382147444706381262001 2563786610583529785946501)
            ·
              refine ⟨480709989484411834864969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2563786610583529785946501 480709989484411834864969)
              ·
                refine ⟨360532492113308876148727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 480709989484411834864969 360532492113308876148727)
                ·
                  refine ⟨540798738169963314223091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 360532492113308876148727 540798738169963314223091)
                  ·
                    refine ⟨811198107254944971334637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 540798738169963314223091 811198107254944971334637)
                    ·
                      refine ⟨304199290220604364250489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 811198107254944971334637 304199290220604364250489)
                      ·
                        rfl

theorem cell23_592426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 4, 2, 1, 1, 3].length) (baseStart_592426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_592426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_592426 prefixEnd_592426 := by exact prefixLift 592426
  have htrace : WordTrace (prefixWord ++ tailWord_592426) baseStart_592426 baseEnd_592426 := by
    simpa [prefixWord, tailWord_592426, baseEnd_592426] using wordTrace_append hprefix tailTrace_592426
  have hstable : (prefixWord ++ tailWord_592426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592426).length < 2 ^ (prefixWord ++ tailWord_592426).sum := by decide
  have hdescent : baseEnd_592426 < baseStart_592426 := by decide
  rcases family_descends (prefixWord ++ tailWord_592426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
