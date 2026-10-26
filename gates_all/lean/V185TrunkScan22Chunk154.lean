import V185TrunkScan22Chunk153

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1376463 : List Nat := [1, 1, 2, 1, 1, 3, 3, 1, 1, 8]
def baseStart_1376463 : Nat := 118140960795 + 1376463 * 2 ^ 59
def prefixEnd_1376463 : Nat := 4983230072969 + 3 ^ 40 * 1376463 * 2
def baseEnd_1376463 : Nat := 471191414753168877254845

theorem tailTrace_1376463 : CollatzResearch.WordTrace tailWord_1376463 prefixEnd_1376463 471191414753168877254845 := by
  unfold tailWord_1376463
  simp only [CollatzResearch.WordTrace]
  refine ⟨50203730012317107009742043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33469153341544738006494695 50203730012317107009742043)
  ·
    refine ⟨75305595018475660514613065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50203730012317107009742043 75305595018475660514613065)
    ·
      refine ⟨56479196263856745385959799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75305595018475660514613065 56479196263856745385959799)
      ·
        refine ⟨84718794395785118078939699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56479196263856745385959799 84718794395785118078939699)
        ·
          refine ⟨127078191593677677118409549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84718794395785118078939699 127078191593677677118409549)
          ·
            refine ⟨47654321847629128919403581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127078191593677677118409549 47654321847629128919403581)
            ·
              refine ⟨17870370692860923344776343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47654321847629128919403581 17870370692860923344776343)
              ·
                refine ⟨26805556039291385017164515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17870370692860923344776343 26805556039291385017164515)
                ·
                  refine ⟨40208334058937077525746773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26805556039291385017164515 40208334058937077525746773)
                  ·
                    refine ⟨471191414753168877254845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 40208334058937077525746773 471191414753168877254845)
                    ·
                      rfl

theorem cell22_1376463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 8].length) (baseStart_1376463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1376463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1376463 prefixEnd_1376463 := by exact prefixLift 1376463
  have htrace : WordTrace (prefixWord ++ tailWord_1376463) baseStart_1376463 baseEnd_1376463 := by
    simpa [prefixWord, tailWord_1376463, baseEnd_1376463] using wordTrace_append hprefix tailTrace_1376463
  have hstable : (prefixWord ++ tailWord_1376463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376463).length < 2 ^ (prefixWord ++ tailWord_1376463).sum := by decide
  have hdescent : baseEnd_1376463 < baseStart_1376463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376499 : List Nat := [1, 1, 1, 2, 2, 4, 4, 3, 1, 3]
def baseStart_1376499 : Nat := 118140960795 + 1376499 * 2 ^ 59
def prefixEnd_1376499 : Nat := 4983230072969 + 3 ^ 40 * 1376499 * 2
def baseEnd_1376499 : Nat := 471203738288876783354735

theorem tailTrace_1376499 : CollatzResearch.WordTrace tailWord_1376499 prefixEnd_1376499 471203738288876783354735 := by
  unfold tailWord_1376499
  simp only [CollatzResearch.WordTrace]
  refine ⟨50205043040186685158052551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33470028693457790105368367 50205043040186685158052551)
  ·
    refine ⟨75307564560280027737078827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50205043040186685158052551 75307564560280027737078827)
    ·
      refine ⟨112961346840420041605618241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75307564560280027737078827 112961346840420041605618241)
      ·
        refine ⟨84721010130315031204213681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112961346840420041605618241 84721010130315031204213681)
        ·
          refine ⟨63540757597736273403160261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84721010130315031204213681 63540757597736273403160261)
          ·
            refine ⟨11913892049575551263092549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63540757597736273403160261 11913892049575551263092549)
            ·
              refine ⟨2233854759295415861829853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11913892049575551263092549 2233854759295415861829853)
              ·
                refine ⟨837695534735780948186195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2233854759295415861829853 837695534735780948186195)
                ·
                  refine ⟨1256543302103671422279293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 837695534735780948186195 1256543302103671422279293)
                  ·
                    refine ⟨471203738288876783354735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1256543302103671422279293 471203738288876783354735)
                    ·
                      rfl

theorem cell22_1376499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 3, 1, 3].length) (baseStart_1376499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1376499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1376499 prefixEnd_1376499 := by exact prefixLift 1376499
  have htrace : WordTrace (prefixWord ++ tailWord_1376499) baseStart_1376499 baseEnd_1376499 := by
    simpa [prefixWord, tailWord_1376499, baseEnd_1376499] using wordTrace_append hprefix tailTrace_1376499
  have hstable : (prefixWord ++ tailWord_1376499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376499).length < 2 ^ (prefixWord ++ tailWord_1376499).sum := by decide
  have hdescent : baseEnd_1376499 < baseStart_1376499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376572 : List Nat := [2, 2, 2, 2, 1, 2, 1, 3, 4, 3]
def baseStart_1376572 : Nat := 118140960795 + 1376572 * 2 ^ 59
def prefixEnd_1376572 : Nat := 4983230072969 + 3 ^ 40 * 1376572 * 2
def baseEnd_1376572 : Nat := 471228727680728926279511

theorem tailTrace_1376572 : CollatzResearch.WordTrace tailWord_1376572 prefixEnd_1376572 471228727680728926279511 := by
  unfold tailWord_1376572
  simp only [CollatzResearch.WordTrace]
  refine ⟨25103852784461109312729985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33471803712614812416973313 25103852784461109312729985)
  ·
    refine ⟨18827889588345831984547489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25103852784461109312729985 18827889588345831984547489)
    ·
      refine ⟨14120917191259373988410617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18827889588345831984547489 14120917191259373988410617)
      ·
        refine ⟨10590687893444530491307963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14120917191259373988410617 10590687893444530491307963)
        ·
          refine ⟨15886031840166795736961945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10590687893444530491307963 15886031840166795736961945)
          ·
            refine ⟨11914523880125096802721459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15886031840166795736961945 11914523880125096802721459)
            ·
              refine ⟨17871785820187645204082189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11914523880125096802721459 17871785820187645204082189)
              ·
                refine ⟨6701919682570366951530821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17871785820187645204082189 6701919682570366951530821)
                ·
                  refine ⟨1256609940481943803412029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6701919682570366951530821 1256609940481943803412029)
                  ·
                    refine ⟨471228727680728926279511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1256609940481943803412029 471228727680728926279511)
                    ·
                      rfl

theorem cell22_1376572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 4, 3].length) (baseStart_1376572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1376572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1376572 prefixEnd_1376572 := by exact prefixLift 1376572
  have htrace : WordTrace (prefixWord ++ tailWord_1376572) baseStart_1376572 baseEnd_1376572 := by
    simpa [prefixWord, tailWord_1376572, baseEnd_1376572] using wordTrace_append hprefix tailTrace_1376572
  have hstable : (prefixWord ++ tailWord_1376572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376572).length < 2 ^ (prefixWord ++ tailWord_1376572).sum := by decide
  have hdescent : baseEnd_1376572 < baseStart_1376572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376574 : List Nat := [4, 2, 1, 2, 1, 4, 1, 1, 6]
def baseStart_1376574 : Nat := 118140960795 + 1376574 * 2 ^ 59
def prefixEnd_1376574 : Nat := 4983230072969 + 3 ^ 40 * 1376574 * 2
def baseEnd_1376574 : Nat := 157076470773867195909835

theorem tailTrace_1376574 : CollatzResearch.WordTrace tailWord_1376574 prefixEnd_1376574 157076470773867195909835 := by
  unfold tailWord_1376574
  simp only [CollatzResearch.WordTrace]
  refine ⟨6275972314364371620879097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33471852343276648644688517 6275972314364371620879097)
  ·
    refine ⟨4706979235773278715659323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6275972314364371620879097 4706979235773278715659323)
    ·
      refine ⟨7060468853659918073488985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4706979235773278715659323 7060468853659918073488985)
      ·
        refine ⟨5295351640244938555116739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7060468853659918073488985 5295351640244938555116739)
        ·
          refine ⟨7943027460367407832675109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5295351640244938555116739 7943027460367407832675109)
          ·
            refine ⟨1489317648818888968626583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7943027460367407832675109 1489317648818888968626583)
            ·
              refine ⟨2233976473228333452939875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1489317648818888968626583 2233976473228333452939875)
              ·
                refine ⟨3350964709842500179409813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2233976473228333452939875 3350964709842500179409813)
                ·
                  refine ⟨157076470773867195909835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3350964709842500179409813 157076470773867195909835)
                  ·
                    rfl

theorem cell22_1376574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 1, 6].length) (baseStart_1376574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1376574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1376574 prefixEnd_1376574 := by exact prefixLift 1376574
  have htrace : WordTrace (prefixWord ++ tailWord_1376574) baseStart_1376574 baseEnd_1376574 := by
    simpa [prefixWord, tailWord_1376574, baseEnd_1376574] using wordTrace_append hprefix tailTrace_1376574
  have hstable : (prefixWord ++ tailWord_1376574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376574).length < 2 ^ (prefixWord ++ tailWord_1376574).sum := by decide
  have hdescent : baseEnd_1376574 < baseStart_1376574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376647 : List Nat := [1, 1, 4, 2, 2, 1, 1, 5, 5]
def baseStart_1376647 : Nat := 118140960795 + 1376647 * 2 ^ 59
def prefixEnd_1376647 : Nat := 4983230072969 + 3 ^ 40 * 1376647 * 2
def baseEnd_1376647 : Nat := 157084800571151243551427

theorem tailTrace_1376647 : CollatzResearch.WordTrace tailWord_1376647 prefixEnd_1376647 157084800571151243551427 := by
  unfold tailWord_1376647
  simp only [CollatzResearch.WordTrace]
  refine ⟨50210441043650506434440195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33473627362433670956293463 50210441043650506434440195)
  ·
    refine ⟨75315661565475759651660293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50210441043650506434440195 75315661565475759651660293)
    ·
      refine ⟨14121686543526704934686305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75315661565475759651660293 14121686543526704934686305)
      ·
        refine ⟨10591264907645028701014729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14121686543526704934686305 10591264907645028701014729)
        ·
          refine ⟨7943448680733771525761047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10591264907645028701014729 7943448680733771525761047)
          ·
            refine ⟨11915173021100657288641571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7943448680733771525761047 11915173021100657288641571)
            ·
              refine ⟨17872759531650985932962357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11915173021100657288641571 17872759531650985932962357)
              ·
                refine ⟨1675571206092279931215221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17872759531650985932962357 1675571206092279931215221)
                ·
                  refine ⟨157084800571151243551427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1675571206092279931215221 157084800571151243551427)
                  ·
                    rfl

theorem cell22_1376647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 5, 5].length) (baseStart_1376647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1376647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1376647 prefixEnd_1376647 := by exact prefixLift 1376647
  have htrace : WordTrace (prefixWord ++ tailWord_1376647) baseStart_1376647 baseEnd_1376647 := by
    simpa [prefixWord, tailWord_1376647, baseEnd_1376647] using wordTrace_append hprefix tailTrace_1376647
  have hstable : (prefixWord ++ tailWord_1376647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376647).length < 2 ^ (prefixWord ++ tailWord_1376647).sum := by decide
  have hdescent : baseEnd_1376647 < baseStart_1376647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376803 : List Nat := [1, 1, 1, 4, 4, 2, 1, 4, 1, 3]
def baseStart_1376803 : Nat := 118140960795 + 1376803 * 2 ^ 59
def prefixEnd_1376803 : Nat := 4983230072969 + 3 ^ 40 * 1376803 * 2
def baseEnd_1376803 : Nat := 471307803701521323753803

theorem tailTrace_1376803 : CollatzResearch.WordTrace tailWord_1376803 prefixEnd_1376803 471307803701521323753803 := by
  unfold tailWord_1376803
  simp only [CollatzResearch.WordTrace]
  refine ⟨50216130831085345077119063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33477420554056896718079375 50216130831085345077119063)
  ·
    refine ⟨75324196246628017615678595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50216130831085345077119063 75324196246628017615678595)
    ·
      refine ⟨112986294369942026423517893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75324196246628017615678595 112986294369942026423517893)
      ·
        refine ⟨21184930194364129954409605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112986294369942026423517893 21184930194364129954409605)
        ·
          refine ⟨3972174411443274366451801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21184930194364129954409605 3972174411443274366451801)
          ·
            refine ⟨2979130808582455774838851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3972174411443274366451801 2979130808582455774838851)
            ·
              refine ⟨4468696212873683662258277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2979130808582455774838851 4468696212873683662258277)
              ·
                refine ⟨837880539913815686673427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4468696212873683662258277 837880539913815686673427)
                ·
                  refine ⟨1256820809870723530010141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 837880539913815686673427 1256820809870723530010141)
                  ·
                    refine ⟨471307803701521323753803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1256820809870723530010141 471307803701521323753803)
                    ·
                      rfl

theorem cell22_1376803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 4, 1, 3].length) (baseStart_1376803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1376803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1376803 prefixEnd_1376803 := by exact prefixLift 1376803
  have htrace : WordTrace (prefixWord ++ tailWord_1376803) baseStart_1376803 baseEnd_1376803 := by
    simpa [prefixWord, tailWord_1376803, baseEnd_1376803] using wordTrace_append hprefix tailTrace_1376803
  have hstable : (prefixWord ++ tailWord_1376803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376803).length < 2 ^ (prefixWord ++ tailWord_1376803).sum := by decide
  have hdescent : baseEnd_1376803 < baseStart_1376803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376820 : List Nat := [2, 5, 1, 3, 1, 1, 1, 2, 3, 3]
def baseStart_1376820 : Nat := 118140960795 + 1376820 * 2 ^ 59
def prefixEnd_1376820 : Nat := 4983230072969 + 3 ^ 40 * 1376820 * 2
def baseEnd_1376820 : Nat := 471313623148938946078751

theorem tailTrace_1376820 : CollatzResearch.WordTrace tailWord_1376820 prefixEnd_1376820 471313623148938946078751 := by
  unfold tailWord_1376820
  simp only [CollatzResearch.WordTrace]
  refine ⟨25108375436011878490243957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33477833914682504653658609 25108375436011878490243957)
  ·
    refine ⟨2353910197126113608460371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25108375436011878490243957 2353910197126113608460371)
    ·
      refine ⟨3530865295689170412690557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2353910197126113608460371 3530865295689170412690557)
      ·
        refine ⟨1324074485883438904758959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3530865295689170412690557 1324074485883438904758959)
        ·
          refine ⟨1986111728825158357138439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1324074485883438904758959 1986111728825158357138439)
          ·
            refine ⟨2979167593237737535707659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1986111728825158357138439 2979167593237737535707659)
            ·
              refine ⟨4468751389856606303561489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2979167593237737535707659 4468751389856606303561489)
              ·
                refine ⟨3351563542392454727671117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4468751389856606303561489 3351563542392454727671117)
                ·
                  refine ⟨1256836328397170522876669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3351563542392454727671117 1256836328397170522876669)
                  ·
                    refine ⟨471313623148938946078751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1256836328397170522876669 471313623148938946078751)
                    ·
                      rfl

theorem cell22_1376820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_1376820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1376820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1376820 prefixEnd_1376820 := by exact prefixLift 1376820
  have htrace : WordTrace (prefixWord ++ tailWord_1376820) baseStart_1376820 baseEnd_1376820 := by
    simpa [prefixWord, tailWord_1376820, baseEnd_1376820] using wordTrace_append hprefix tailTrace_1376820
  have hstable : (prefixWord ++ tailWord_1376820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376820).length < 2 ^ (prefixWord ++ tailWord_1376820).sum := by decide
  have hdescent : baseEnd_1376820 < baseStart_1376820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376874 : List Nat := [3, 1, 3, 2, 1, 1, 1, 1, 3, 6]
def baseStart_1376874 : Nat := 118140960795 + 1376874 * 2 ^ 59
def prefixEnd_1376874 : Nat := 4983230072969 + 3 ^ 40 * 1376874 * 2
def baseEnd_1376874 : Nat := 471332108452500805228585

theorem tailTrace_1376874 : CollatzResearch.WordTrace tailWord_1376874 prefixEnd_1376874 471332108452500805228585 := by
  unfold tailWord_1376874
  simp only [CollatzResearch.WordTrace]
  refine ⟨12554680103457031050738419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33479146942552082801969117 12554680103457031050738419)
  ·
    refine ⟨18832020155185546576107629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12554680103457031050738419 18832020155185546576107629)
    ·
      refine ⟨7062007558194579966040361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18832020155185546576107629 7062007558194579966040361)
      ·
        refine ⟨5296505668645934974530271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7062007558194579966040361 5296505668645934974530271)
        ·
          refine ⟨7944758502968902461795407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5296505668645934974530271 7944758502968902461795407)
          ·
            refine ⟨11917137754453353692693111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7944758502968902461795407 11917137754453353692693111)
            ·
              refine ⟨17875706631680030539039667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11917137754453353692693111 17875706631680030539039667)
              ·
                refine ⟨26813559947520045808559501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17875706631680030539039667 26813559947520045808559501)
                ·
                  refine ⟨10055084980320017178209813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26813559947520045808559501 10055084980320017178209813)
                  ·
                    refine ⟨471332108452500805228585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10055084980320017178209813 471332108452500805228585)
                    ·
                      rfl

theorem cell22_1376874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_1376874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1376874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1376874 prefixEnd_1376874 := by exact prefixLift 1376874
  have htrace : WordTrace (prefixWord ++ tailWord_1376874) baseStart_1376874 baseEnd_1376874 := by
    simpa [prefixWord, tailWord_1376874, baseEnd_1376874] using wordTrace_append hprefix tailTrace_1376874
  have hstable : (prefixWord ++ tailWord_1376874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376874).length < 2 ^ (prefixWord ++ tailWord_1376874).sum := by decide
  have hdescent : baseEnd_1376874 < baseStart_1376874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376876 : List Nat := [2, 2, 1, 1, 3, 1, 2, 5, 2, 3]
def baseStart_1376876 : Nat := 118140960795 + 1376876 * 2 ^ 59
def prefixEnd_1376876 : Nat := 4983230072969 + 3 ^ 40 * 1376876 * 2
def baseEnd_1376876 : Nat := 471332793093373466678579

theorem tailTrace_1376876 : CollatzResearch.WordTrace tailWord_1376876 prefixEnd_1376876 471332793093373466678579 := by
  unfold tailWord_1376876
  simp only [CollatzResearch.WordTrace]
  refine ⟨25109396679910439272263241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33479195573213919029684321 25109396679910439272263241)
  ·
    refine ⟨18832047509932829454197431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25109396679910439272263241 18832047509932829454197431)
    ·
      refine ⟨28248071264899244181296147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18832047509932829454197431 28248071264899244181296147)
      ·
        refine ⟨42372106897348866271944221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28248071264899244181296147 42372106897348866271944221)
        ·
          refine ⟨15889540086505824851979083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42372106897348866271944221 15889540086505824851979083)
          ·
            refine ⟨23834310129758737277968625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15889540086505824851979083 23834310129758737277968625)
            ·
              refine ⟨17875732597319052958476469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23834310129758737277968625 17875732597319052958476469)
              ·
                refine ⟨1675849930998661214857169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17875732597319052958476469 1675849930998661214857169)
                ·
                  refine ⟨1256887448248995911142877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1675849930998661214857169 1256887448248995911142877)
                  ·
                    refine ⟨471332793093373466678579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1256887448248995911142877 471332793093373466678579)
                    ·
                      rfl

theorem cell22_1376876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 3].length) (baseStart_1376876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1376876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1376876 prefixEnd_1376876 := by exact prefixLift 1376876
  have htrace : WordTrace (prefixWord ++ tailWord_1376876) baseStart_1376876 baseEnd_1376876 := by
    simpa [prefixWord, tailWord_1376876, baseEnd_1376876] using wordTrace_append hprefix tailTrace_1376876
  have hstable : (prefixWord ++ tailWord_1376876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376876).length < 2 ^ (prefixWord ++ tailWord_1376876).sum := by decide
  have hdescent : baseEnd_1376876 < baseStart_1376876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376889 : List Nat := [1, 2, 1, 3, 3, 3, 1, 8]
def baseStart_1376889 : Nat := 118140960795 + 1376889 * 2 ^ 59
def prefixEnd_1376889 : Nat := 4983230072969 + 3 ^ 40 * 1376889 * 2
def baseEnd_1376889 : Nat := 52370804806560640678171

theorem tailTrace_1376889 : CollatzResearch.WordTrace tailWord_1376889 prefixEnd_1376889 52370804806560640678171 := by
  unfold tailWord_1376889
  simp only [CollatzResearch.WordTrace]
  refine ⟨50219267508773781764749721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33479511672515854509833147 50219267508773781764749721)
  ·
    refine ⟨37664450631580336323562291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50219267508773781764749721 37664450631580336323562291)
    ·
      refine ⟨56496675947370504485343437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37664450631580336323562291 56496675947370504485343437)
      ·
        refine ⟨21186253480263939182003789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56496675947370504485343437 21186253480263939182003789)
        ·
          refine ⟨7944845055098977193251421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21186253480263939182003789 7944845055098977193251421)
          ·
            refine ⟨2979316895662116447469283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7944845055098977193251421 2979316895662116447469283)
            ·
              refine ⟨4468975343493174671203925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2979316895662116447469283 4468975343493174671203925)
              ·
                refine ⟨52370804806560640678171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4468975343493174671203925 52370804806560640678171)
                ·
                  rfl

theorem cell22_1376889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 8].length) (baseStart_1376889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1376889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1376889 prefixEnd_1376889 := by exact prefixLift 1376889
  have htrace : WordTrace (prefixWord ++ tailWord_1376889) baseStart_1376889 baseEnd_1376889 := by
    simpa [prefixWord, tailWord_1376889, baseEnd_1376889] using wordTrace_append hprefix tailTrace_1376889
  have hstable : (prefixWord ++ tailWord_1376889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376889).length < 2 ^ (prefixWord ++ tailWord_1376889).sum := by decide
  have hdescent : baseEnd_1376889 < baseStart_1376889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376906 : List Nat := [3, 1, 2, 3, 3, 2, 8]
def baseStart_1376906 : Nat := 118140960795 + 1376906 * 2 ^ 59
def prefixEnd_1376906 : Nat := 4983230072969 + 3 ^ 40 * 1376906 * 2
def baseEnd_1376906 : Nat := 17457150470609755126981

theorem tailTrace_1376906 : CollatzResearch.WordTrace tailWord_1376906 prefixEnd_1376906 17457150470609755126981 := by
  unfold tailWord_1376906
  simp only [CollatzResearch.WordTrace]
  refine ⟨12554971887428048417029643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33479925033141462445412381 12554971887428048417029643)
  ·
    refine ⟨18832457831142072625544465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12554971887428048417029643 18832457831142072625544465)
    ·
      refine ⟨14124343373356554469158349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18832457831142072625544465 14124343373356554469158349)
      ·
        refine ⟨5296628765008707925934381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14124343373356554469158349 5296628765008707925934381)
        ·
          refine ⟨1986235786878265472225393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5296628765008707925934381 1986235786878265472225393)
          ·
            refine ⟨1489676840158699104169045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1986235786878265472225393 1489676840158699104169045)
            ·
              refine ⟨17457150470609755126981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1489676840158699104169045 17457150470609755126981)
              ·
                rfl

theorem cell22_1376906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 8].length) (baseStart_1376906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1376906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1376906 prefixEnd_1376906 := by exact prefixLift 1376906
  have htrace : WordTrace (prefixWord ++ tailWord_1376906) baseStart_1376906 baseEnd_1376906 := by
    simpa [prefixWord, tailWord_1376906, baseEnd_1376906] using wordTrace_append hprefix tailTrace_1376906
  have hstable : (prefixWord ++ tailWord_1376906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376906).length < 2 ^ (prefixWord ++ tailWord_1376906).sum := by decide
  have hdescent : baseEnd_1376906 < baseStart_1376906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376919 : List Nat := [1, 1, 3, 3, 2, 1, 2, 1, 2, 6]
def baseStart_1376919 : Nat := 118140960795 + 1376919 * 2 ^ 59
def prefixEnd_1376919 : Nat := 4983230072969 + 3 ^ 40 * 1376919 * 2
def baseEnd_1376919 : Nat := 471347512872135687853447

theorem tailTrace_1376919 : CollatzResearch.WordTrace tailWord_1376919 prefixEnd_1376919 471347512872135687853447 := by
  unfold tailWord_1376919
  simp only [CollatzResearch.WordTrace]
  refine ⟨50220361698665096888341811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33480241132443397925561207 50220361698665096888341811)
  ·
    refine ⟨75330542547997645332512717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50220361698665096888341811 75330542547997645332512717)
    ·
      refine ⟨28248953455499116999692269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75330542547997645332512717 28248953455499116999692269)
      ·
        refine ⟨10593357545812168874884601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28248953455499116999692269 10593357545812168874884601)
        ·
          refine ⟨7945018159359126656163451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10593357545812168874884601 7945018159359126656163451)
          ·
            refine ⟨11917527239038689984245177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7945018159359126656163451 11917527239038689984245177)
            ·
              refine ⟨8938145429279017488183883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11917527239038689984245177 8938145429279017488183883)
              ·
                refine ⟨13407218143918526232275825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8938145429279017488183883 13407218143918526232275825)
                ·
                  refine ⟨10055413607938894674206869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13407218143918526232275825 10055413607938894674206869)
                  ·
                    refine ⟨471347512872135687853447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10055413607938894674206869 471347512872135687853447)
                    ·
                      rfl

theorem cell22_1376919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 6].length) (baseStart_1376919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1376919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1376919 prefixEnd_1376919 := by exact prefixLift 1376919
  have htrace : WordTrace (prefixWord ++ tailWord_1376919) baseStart_1376919 baseEnd_1376919 := by
    simpa [prefixWord, tailWord_1376919, baseEnd_1376919] using wordTrace_append hprefix tailTrace_1376919
  have hstable : (prefixWord ++ tailWord_1376919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376919).length < 2 ^ (prefixWord ++ tailWord_1376919).sum := by decide
  have hdescent : baseEnd_1376919 < baseStart_1376919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376972 : List Nat := [2, 2, 1, 5, 1, 1, 4, 2, 1, 3]
def baseStart_1376972 : Nat := 118140960795 + 1376972 * 2 ^ 59
def prefixEnd_1376972 : Nat := 4983230072969 + 3 ^ 40 * 1376972 * 2
def baseEnd_1376972 : Nat := 471365655855261216278285

theorem tailTrace_1376972 : CollatzResearch.WordTrace tailWord_1376972 prefixEnd_1376972 471365655855261216278285 := by
  unfold tailWord_1376972
  simp only [CollatzResearch.WordTrace]
  refine ⟨25111147383736543470010585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33481529844982057960014113 25111147383736543470010585)
  ·
    refine ⟨18833360537802407602507939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25111147383736543470010585 18833360537802407602507939)
    ·
      refine ⟨28250040806703611403761909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18833360537802407602507939 28250040806703611403761909)
      ·
        refine ⟨2648441325628463569102679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28250040806703611403761909 2648441325628463569102679)
        ·
          refine ⟨3972661988442695353654019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2648441325628463569102679 3972661988442695353654019)
          ·
            refine ⟨5958992982664043030481029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3972661988442695353654019 5958992982664043030481029)
            ·
              refine ⟨1117311184249508068215193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5958992982664043030481029 1117311184249508068215193)
              ·
                refine ⟨837983388187131051161395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1117311184249508068215193 837983388187131051161395)
                ·
                  refine ⟨1256975082280696576742093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 837983388187131051161395 1256975082280696576742093)
                  ·
                    refine ⟨471365655855261216278285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1256975082280696576742093 471365655855261216278285)
                    ·
                      rfl

theorem cell22_1376972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 4, 2, 1, 3].length) (baseStart_1376972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1376972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1376972 prefixEnd_1376972 := by exact prefixLift 1376972
  have htrace : WordTrace (prefixWord ++ tailWord_1376972) baseStart_1376972 baseEnd_1376972 := by
    simpa [prefixWord, tailWord_1376972, baseEnd_1376972] using wordTrace_append hprefix tailTrace_1376972
  have hstable : (prefixWord ++ tailWord_1376972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376972).length < 2 ^ (prefixWord ++ tailWord_1376972).sum := by decide
  have hdescent : baseEnd_1376972 < baseStart_1376972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376996 : List Nat := [2, 3, 1, 1, 1, 5, 1, 2, 6]
def baseStart_1376996 : Nat := 118140960795 + 1376996 * 2 ^ 59
def prefixEnd_1376996 : Nat := 4983230072969 + 3 ^ 40 * 1376996 * 2
def baseEnd_1376996 : Nat := 157124623848577717892737

theorem tailTrace_1376996 : CollatzResearch.WordTrace tailWord_1376996 prefixEnd_1376996 157124623848577717892737 := by
  unfold tailWord_1376996
  simp only [CollatzResearch.WordTrace]
  refine ⟨25111585059693069519447421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33482113412924092692596561 25111585059693069519447421)
  ·
    refine ⟨9416844397384901069792783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25111585059693069519447421 9416844397384901069792783)
    ·
      refine ⟨14125266596077351604689175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9416844397384901069792783 14125266596077351604689175)
      ·
        refine ⟨21187899894116027407033763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14125266596077351604689175 21187899894116027407033763)
        ·
          refine ⟨31781849841174041110550645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21187899894116027407033763 31781849841174041110550645)
          ·
            refine ⟨2979548422610066354114123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31781849841174041110550645 2979548422610066354114123)
            ·
              refine ⟨4469322633915099531171185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2979548422610066354114123 4469322633915099531171185)
              ·
                refine ⟨3351991975436324648378389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4469322633915099531171185 3351991975436324648378389)
                ·
                  refine ⟨157124623848577717892737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3351991975436324648378389 157124623848577717892737)
                  ·
                    rfl

theorem cell22_1376996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 2, 6].length) (baseStart_1376996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1376996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1376996 prefixEnd_1376996 := by exact prefixLift 1376996
  have htrace : WordTrace (prefixWord ++ tailWord_1376996) baseStart_1376996 baseEnd_1376996 := by
    simpa [prefixWord, tailWord_1376996, baseEnd_1376996] using wordTrace_append hprefix tailTrace_1376996
  have hstable : (prefixWord ++ tailWord_1376996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376996).length < 2 ^ (prefixWord ++ tailWord_1376996).sum := by decide
  have hdescent : baseEnd_1376996 < baseStart_1376996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377011 : List Nat := [1, 1, 1, 2, 2, 3, 1, 4, 4, 3]
def baseStart_1377011 : Nat := 118140960795 + 1377011 * 2 ^ 59
def prefixEnd_1377011 : Nat := 4983230072969 + 3 ^ 40 * 1377011 * 2
def baseEnd_1377011 : Nat := 471379006352278114553165

theorem tailTrace_1377011 : CollatzResearch.WordTrace tailWord_1377011 prefixEnd_1377011 471379006352278114553165 := by
  unfold tailWord_1377011
  simp only [CollatzResearch.WordTrace]
  refine ⟨50223717214331796600690887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33482478142887864400460591 50223717214331796600690887)
  ·
    refine ⟨75335575821497694901036331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50223717214331796600690887 75335575821497694901036331)
    ·
      refine ⟨113003363732246542351554497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75335575821497694901036331 113003363732246542351554497)
      ·
        refine ⟨84752522799184906763665873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113003363732246542351554497 84752522799184906763665873)
        ·
          refine ⟨63564392099388680072749405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84752522799184906763665873 63564392099388680072749405)
          ·
            refine ⟨23836647037270755027281027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63564392099388680072749405 23836647037270755027281027)
            ·
              refine ⟨35754970555906132540921541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23836647037270755027281027 35754970555906132540921541)
              ·
                refine ⟨6704056979232399851422789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35754970555906132540921541 6704056979232399851422789)
                ·
                  refine ⟨1257010683606074972141773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6704056979232399851422789 1257010683606074972141773)
                  ·
                    refine ⟨471379006352278114553165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1257010683606074972141773 471379006352278114553165)
                    ·
                      rfl

theorem cell22_1377011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 4, 3].length) (baseStart_1377011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1377011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1377011 prefixEnd_1377011 := by exact prefixLift 1377011
  have htrace : WordTrace (prefixWord ++ tailWord_1377011) baseStart_1377011 baseEnd_1377011 := by
    simpa [prefixWord, tailWord_1377011, baseEnd_1377011] using wordTrace_append hprefix tailTrace_1377011
  have hstable : (prefixWord ++ tailWord_1377011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377011).length < 2 ^ (prefixWord ++ tailWord_1377011).sum := by decide
  have hdescent : baseEnd_1377011 < baseStart_1377011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377028 : List Nat := [2, 3, 2, 2, 1, 1, 3, 1, 4, 3]
def baseStart_1377028 : Nat := 118140960795 + 1377028 * 2 ^ 59
def prefixEnd_1377028 : Nat := 4983230072969 + 3 ^ 40 * 1377028 * 2
def baseEnd_1377028 : Nat := 471384825799695736878113

theorem tailTrace_1377028 : CollatzResearch.WordTrace tailWord_1377028 prefixEnd_1377028 471384825799695736878113 := by
  unfold tailWord_1377028
  simp only [CollatzResearch.WordTrace]
  refine ⟨25112168627635104252029869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33482891503513472336039825 25112168627635104252029869)
  ·
    refine ⟨9417063235363164094511201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25112168627635104252029869 9417063235363164094511201)
    ·
      refine ⟨7062797426522373070883401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9417063235363164094511201 7062797426522373070883401)
      ·
        refine ⟨5297098069891779803162551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7062797426522373070883401 5297098069891779803162551)
        ·
          refine ⟨7945647104837669704743827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5297098069891779803162551 7945647104837669704743827)
          ·
            refine ⟨11918470657256504557115741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7945647104837669704743827 11918470657256504557115741)
            ·
              refine ⟨4469426496471189208918403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11918470657256504557115741 4469426496471189208918403)
              ·
                refine ⟨6704139744706783813377605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4469426496471189208918403 6704139744706783813377605)
                ·
                  refine ⟨1257026202132521965008301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6704139744706783813377605 1257026202132521965008301)
                  ·
                    refine ⟨471384825799695736878113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1257026202132521965008301 471384825799695736878113)
                    ·
                      rfl

theorem cell22_1377028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 4, 3].length) (baseStart_1377028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1377028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1377028 prefixEnd_1377028 := by exact prefixLift 1377028
  have htrace : WordTrace (prefixWord ++ tailWord_1377028) baseStart_1377028 baseEnd_1377028 := by
    simpa [prefixWord, tailWord_1377028, baseEnd_1377028] using wordTrace_append hprefix tailTrace_1377028
  have hstable : (prefixWord ++ tailWord_1377028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377028).length < 2 ^ (prefixWord ++ tailWord_1377028).sum := by decide
  have hdescent : baseEnd_1377028 < baseStart_1377028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377045 : List Nat := [1, 3, 2, 1, 2, 2, 5, 1, 2, 3]
def baseStart_1377045 : Nat := 118140960795 + 1377045 * 2 ^ 59
def prefixEnd_1377045 : Nat := 4983230072969 + 3 ^ 40 * 1377045 * 2
def baseEnd_1377045 : Nat := 471390645247113359203061

theorem tailTrace_1377045 : CollatzResearch.WordTrace tailWord_1377045 prefixEnd_1377045 471390645247113359203061 := by
  unfold tailWord_1377045
  simp only [CollatzResearch.WordTrace]
  refine ⟨50224957296208620407428589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33483304864139080271619059 50224957296208620407428589)
  ·
    refine ⟨18834358986078232652785721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50224957296208620407428589 18834358986078232652785721)
    ·
      refine ⟨14125769239558674489589291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18834358986078232652785721 14125769239558674489589291)
      ·
        refine ⟨21188653859338011734383937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14125769239558674489589291 21188653859338011734383937)
        ·
          refine ⟨15891490394503508800787953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21188653859338011734383937 15891490394503508800787953)
          ·
            refine ⟨11918617795877631600590965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15891490394503508800787953 11918617795877631600590965)
            ·
              refine ⟨1117370418363527962555403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11918617795877631600590965 1117370418363527962555403)
              ·
                refine ⟨1676055627545291943833105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1117370418363527962555403 1676055627545291943833105)
                ·
                  refine ⟨1257041720658968957874829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1676055627545291943833105 1257041720658968957874829)
                  ·
                    refine ⟨471390645247113359203061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1257041720658968957874829 471390645247113359203061)
                    ·
                      rfl

theorem cell22_1377045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 5, 1, 2, 3].length) (baseStart_1377045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1377045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1377045 prefixEnd_1377045 := by exact prefixLift 1377045
  have htrace : WordTrace (prefixWord ++ tailWord_1377045) baseStart_1377045 baseEnd_1377045 := by
    simpa [prefixWord, tailWord_1377045, baseEnd_1377045] using wordTrace_append hprefix tailTrace_1377045
  have hstable : (prefixWord ++ tailWord_1377045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377045).length < 2 ^ (prefixWord ++ tailWord_1377045).sum := by decide
  have hdescent : baseEnd_1377045 < baseStart_1377045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377058 : List Nat := [3, 3, 1, 1, 2, 2, 4, 6]
def baseStart_1377058 : Nat := 118140960795 + 1377058 * 2 ^ 59
def prefixEnd_1377058 : Nat := 4983230072969 + 3 ^ 40 * 1377058 * 2
def baseEnd_1377058 : Nat := 52377232823642850958669

theorem tailTrace_1377058 : CollatzResearch.WordTrace tailWord_1377058 prefixEnd_1377058 52377232823642850958669 := by
  unfold tailWord_1377058
  simp only [CollatzResearch.WordTrace]
  refine ⟨12556357861290380906912957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33483620963441015751767885 12556357861290380906912957)
  ·
    refine ⟨4708634197983892840092359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12556357861290380906912957 4708634197983892840092359)
    ·
      refine ⟨7062951296975839260138539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4708634197983892840092359 7062951296975839260138539)
      ·
        refine ⟨10594426945463758890207809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7062951296975839260138539 10594426945463758890207809)
        ·
          refine ⟨7945820209097819167655857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10594426945463758890207809 7945820209097819167655857)
          ·
            refine ⟨5959365156823364375741893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7945820209097819167655857 5959365156823364375741893)
            ·
              refine ⟨1117380966904380820451605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5959365156823364375741893 1117380966904380820451605)
              ·
                refine ⟨52377232823642850958669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1117380966904380820451605 52377232823642850958669)
                ·
                  rfl

theorem cell22_1377058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 4, 6].length) (baseStart_1377058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1377058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1377058 prefixEnd_1377058 := by exact prefixLift 1377058
  have htrace : WordTrace (prefixWord ++ tailWord_1377058) baseStart_1377058 baseEnd_1377058 := by
    simpa [prefixWord, tailWord_1377058, baseEnd_1377058] using wordTrace_append hprefix tailTrace_1377058
  have hstable : (prefixWord ++ tailWord_1377058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377058).length < 2 ^ (prefixWord ++ tailWord_1377058).sum := by decide
  have hdescent : baseEnd_1377058 < baseStart_1377058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377146 : List Nat := [3, 1, 1, 1, 1, 1, 3, 1, 5, 5]
def baseStart_1377146 : Nat := 118140960795 + 1377146 * 2 ^ 59
def prefixEnd_1377146 : Nat := 4983230072969 + 3 ^ 40 * 1377146 * 2
def baseEnd_1377146 : Nat := 471425219611182762427751

theorem tailTrace_1377146 : CollatzResearch.WordTrace tailWord_1377146 prefixEnd_1377146 471425219611182762427751 := by
  unfold tailWord_1377146
  simp only [CollatzResearch.WordTrace]
  refine ⟨12557160267210678664213823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33485760712561809771236861 12557160267210678664213823)
  ·
    refine ⟨18835740400816017996320735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12557160267210678664213823 18835740400816017996320735)
    ·
      refine ⟨28253610601224026994481103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18835740400816017996320735 28253610601224026994481103)
      ·
        refine ⟨42380415901836040491721655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28253610601224026994481103 42380415901836040491721655)
        ·
          refine ⟨63570623852754060737582483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42380415901836040491721655 63570623852754060737582483)
          ·
            refine ⟨95355935779131091106373725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63570623852754060737582483 95355935779131091106373725)
            ·
              refine ⟨35758475917174159164890147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95355935779131091106373725 35758475917174159164890147)
              ·
                refine ⟨53637713875761238747335221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35758475917174159164890147 53637713875761238747335221)
                ·
                  refine ⟨5028535675852616132562677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53637713875761238747335221 5028535675852616132562677)
                  ·
                    refine ⟨471425219611182762427751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5028535675852616132562677 471425219611182762427751)
                    ·
                      rfl

theorem cell22_1377146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 5, 5].length) (baseStart_1377146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1377146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1377146 prefixEnd_1377146 := by exact prefixLift 1377146
  have htrace : WordTrace (prefixWord ++ tailWord_1377146) baseStart_1377146 baseEnd_1377146 := by
    simpa [prefixWord, tailWord_1377146, baseEnd_1377146] using wordTrace_append hprefix tailTrace_1377146
  have hstable : (prefixWord ++ tailWord_1377146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377146).length < 2 ^ (prefixWord ++ tailWord_1377146).sum := by decide
  have hdescent : baseEnd_1377146 < baseStart_1377146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377332 : List Nat := [2, 5, 1, 2, 1, 1, 1, 3, 1, 5]
def baseStart_1377332 : Nat := 118140960795 + 1377332 * 2 ^ 59
def prefixEnd_1377332 : Nat := 4983230072969 + 3 ^ 40 * 1377332 * 2
def baseEnd_1377332 : Nat := 471488891212340277277181

theorem tailTrace_1377332 : CollatzResearch.WordTrace tailWord_1377332 prefixEnd_1377332 471488891212340277277181 := by
  unfold tailWord_1377332
  simp only [CollatzResearch.WordTrace]
  refine ⟨25117712523084434211563125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33490283364112578948750833 25117712523084434211563125)
  ·
    refine ⟨2354785549039165707334043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25117712523084434211563125 2354785549039165707334043)
    ·
      refine ⟨3532178323558748561001065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2354785549039165707334043 3532178323558748561001065)
      ·
        refine ⟨2649133742669061420750799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3532178323558748561001065 2649133742669061420750799)
        ·
          refine ⟨3973700614003592131126199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2649133742669061420750799 3973700614003592131126199)
          ·
            refine ⟨5960550921005388196689299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3973700614003592131126199 5960550921005388196689299)
            ·
              refine ⟨8940826381508082295033949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5960550921005388196689299 8940826381508082295033949)
              ·
                refine ⟨3352809893065530860637731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8940826381508082295033949 3352809893065530860637731)
                ·
                  refine ⟨5029214839598296290956597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3352809893065530860637731 5029214839598296290956597)
                  ·
                    refine ⟨471488891212340277277181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5029214839598296290956597 471488891212340277277181)
                    ·
                      rfl

theorem cell22_1377332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_1377332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1377332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1377332 prefixEnd_1377332 := by exact prefixLift 1377332
  have htrace : WordTrace (prefixWord ++ tailWord_1377332) baseStart_1377332 baseEnd_1377332 := by
    simpa [prefixWord, tailWord_1377332, baseEnd_1377332] using wordTrace_append hprefix tailTrace_1377332
  have hstable : (prefixWord ++ tailWord_1377332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377332).length < 2 ^ (prefixWord ++ tailWord_1377332).sum := by decide
  have hdescent : baseEnd_1377332 < baseStart_1377332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377366 : List Nat := [5, 2, 2, 1, 2, 1, 1, 1, 4, 3]
def baseStart_1377366 : Nat := 118140960795 + 1377366 * 2 ^ 59
def prefixEnd_1377366 : Nat := 4983230072969 + 3 ^ 40 * 1377366 * 2
def baseEnd_1377366 : Nat := 471500530107175521927077

theorem tailTrace_1377366 : CollatzResearch.WordTrace tailWord_1377366 prefixEnd_1377366 471500530107175521927077 := by
  unfold tailWord_1377366
  simp only [CollatzResearch.WordTrace]
  refine ⟨3139791570502855764366497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33491110085363794819909301 3139791570502855764366497)
  ·
    refine ⟨2354843677877141823274873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3139791570502855764366497 2354843677877141823274873)
    ·
      refine ⟨1766132758407856367456155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2354843677877141823274873 1766132758407856367456155)
      ·
        refine ⟨2649199137611784551184233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1766132758407856367456155 2649199137611784551184233)
        ·
          refine ⟨1986899353208838413388175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2649199137611784551184233 1986899353208838413388175)
          ·
            refine ⟨2980349029813257620082263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1986899353208838413388175 2980349029813257620082263)
            ·
              refine ⟨4470523544719886430123395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2980349029813257620082263 4470523544719886430123395)
              ·
                refine ⟨6705785317079829645185093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4470523544719886430123395 6705785317079829645185093)
                ·
                  refine ⟨1257334746952468058472205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6705785317079829645185093 1257334746952468058472205)
                  ·
                    refine ⟨471500530107175521927077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1257334746952468058472205 471500530107175521927077)
                    ·
                      rfl

theorem cell22_1377366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_1377366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1377366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1377366 prefixEnd_1377366 := by exact prefixLift 1377366
  have htrace : WordTrace (prefixWord ++ tailWord_1377366) baseStart_1377366 baseEnd_1377366 := by
    simpa [prefixWord, tailWord_1377366, baseEnd_1377366] using wordTrace_append hprefix tailTrace_1377366
  have hstable : (prefixWord ++ tailWord_1377366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377366).length < 2 ^ (prefixWord ++ tailWord_1377366).sum := by decide
  have hdescent : baseEnd_1377366 < baseStart_1377366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377403 : List Nat := [1, 1, 1, 1, 1, 4, 1, 2, 2, 8]
def baseStart_1377403 : Nat := 118140960795 + 1377403 * 2 ^ 59
def prefixEnd_1377403 : Nat := 4983230072969 + 3 ^ 40 * 1377403 * 2
def baseEnd_1377403 : Nat := 471513195963319758751963

theorem tailTrace_1377403 : CollatzResearch.WordTrace tailWord_1377403 prefixEnd_1377403 471513195963319758751963 := by
  unfold tailWord_1377403
  simp only [CollatzResearch.WordTrace]
  refine ⟨50238014628911647548960863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33492009752607765032640575 50238014628911647548960863)
  ·
    refine ⟨75357021943367471323441295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50238014628911647548960863 75357021943367471323441295)
    ·
      refine ⟨113035532915051206985161943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75357021943367471323441295 113035532915051206985161943)
      ·
        refine ⟨169553299372576810477742915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113035532915051206985161943 169553299372576810477742915)
        ·
          refine ⟨254329949058865215716614373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169553299372576810477742915 254329949058865215716614373)
          ·
            refine ⟨47686865448537227946865195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 254329949058865215716614373 47686865448537227946865195)
            ·
              refine ⟨71530298172805841920297793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47686865448537227946865195 71530298172805841920297793)
              ·
                refine ⟨53647723629604381440223345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71530298172805841920297793 53647723629604381440223345)
                ·
                  refine ⟨40235792722203286080167509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53647723629604381440223345 40235792722203286080167509)
                  ·
                    refine ⟨471513195963319758751963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 40235792722203286080167509 471513195963319758751963)
                    ·
                      rfl

theorem cell22_1377403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 8].length) (baseStart_1377403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1377403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1377403 prefixEnd_1377403 := by exact prefixLift 1377403
  have htrace : WordTrace (prefixWord ++ tailWord_1377403) baseStart_1377403 baseEnd_1377403 := by
    simpa [prefixWord, tailWord_1377403, baseEnd_1377403] using wordTrace_append hprefix tailTrace_1377403
  have hstable : (prefixWord ++ tailWord_1377403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377403).length < 2 ^ (prefixWord ++ tailWord_1377403).sum := by decide
  have hdescent : baseEnd_1377403 < baseStart_1377403 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377482 : List Nat := [3, 1, 2, 1, 3, 2, 2, 2, 2, 4]
def baseStart_1377482 : Nat := 118140960795 + 1377482 * 2 ^ 59
def prefixEnd_1377482 : Nat := 4983230072969 + 3 ^ 40 * 1377482 * 2
def baseEnd_1377482 : Nat := 471540239277789886026721

theorem tailTrace_1377482 : CollatzResearch.WordTrace tailWord_1377482 prefixEnd_1377482 471540239277789886026721 := by
  unfold tailWord_1377482
  simp only [CollatzResearch.WordTrace]
  refine ⟨12560223998906361010271675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33493930663750296027391133 12560223998906361010271675)
  ·
    refine ⟨18840335998359541515407513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12560223998906361010271675 18840335998359541515407513)
    ·
      refine ⟨14130251998769656136555635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18840335998359541515407513 14130251998769656136555635)
      ·
        refine ⟨21195377998154484204833453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14130251998769656136555635 21195377998154484204833453)
        ·
          refine ⟨7948266749307931576812545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21195377998154484204833453 7948266749307931576812545)
          ·
            refine ⟨5961200061980948682609409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7948266749307931576812545 5961200061980948682609409)
            ·
              refine ⟨4470900046485711511957057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5961200061980948682609409 4470900046485711511957057)
              ·
                refine ⟨3353175034864283633967793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4470900046485711511957057 3353175034864283633967793)
                ·
                  refine ⟨2514881276148212725475845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3353175034864283633967793 2514881276148212725475845)
                  ·
                    refine ⟨471540239277789886026721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2514881276148212725475845 471540239277789886026721)
                    ·
                      rfl

theorem cell22_1377482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 2, 2, 4].length) (baseStart_1377482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1377482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1377482 prefixEnd_1377482 := by exact prefixLift 1377482
  have htrace : WordTrace (prefixWord ++ tailWord_1377482) baseStart_1377482 baseEnd_1377482 := by
    simpa [prefixWord, tailWord_1377482, baseEnd_1377482] using wordTrace_append hprefix tailTrace_1377482
  have hstable : (prefixWord ++ tailWord_1377482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377482).length < 2 ^ (prefixWord ++ tailWord_1377482).sum := by decide
  have hdescent : baseEnd_1377482 < baseStart_1377482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377559 : List Nat := [1, 1, 3, 4, 1, 1, 5, 1, 5]
def baseStart_1377559 : Nat := 118140960795 + 1377559 * 2 ^ 59
def prefixEnd_1377559 : Nat := 4983230072969 + 3 ^ 40 * 1377559 * 2
def baseEnd_1377559 : Nat := 157188865983795783950495

theorem tailTrace_1377559 : CollatzResearch.WordTrace tailWord_1377559 prefixEnd_1377559 157188865983795783950495 := by
  unfold tailWord_1377559
  simp only [CollatzResearch.WordTrace]
  refine ⟨50243704416346486191639731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33495802944230990794426487 50243704416346486191639731)
  ·
    refine ⟨75365556624519729287459597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50243704416346486191639731 75365556624519729287459597)
    ·
      refine ⟨28262083734194898482797349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75365556624519729287459597 28262083734194898482797349)
      ·
        refine ⟨5299140700161543465524503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28262083734194898482797349 5299140700161543465524503)
        ·
          refine ⟨7948711050242315198286755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5299140700161543465524503 7948711050242315198286755)
          ·
            refine ⟨11923066575363472797430133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7948711050242315198286755 11923066575363472797430133)
            ·
              refine ⟨1117787491440325574759075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11923066575363472797430133 1117787491440325574759075)
              ·
                refine ⟨1676681237160488362138613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1117787491440325574759075 1676681237160488362138613)
                ·
                  refine ⟨157188865983795783950495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1676681237160488362138613 157188865983795783950495)
                  ·
                    rfl

theorem cell22_1377559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 5, 1, 5].length) (baseStart_1377559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1377559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1377559 prefixEnd_1377559 := by exact prefixLift 1377559
  have htrace : WordTrace (prefixWord ++ tailWord_1377559) baseStart_1377559 baseEnd_1377559 := by
    simpa [prefixWord, tailWord_1377559, baseEnd_1377559] using wordTrace_append hprefix tailTrace_1377559
  have hstable : (prefixWord ++ tailWord_1377559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377559).length < 2 ^ (prefixWord ++ tailWord_1377559).sum := by decide
  have hdescent : baseEnd_1377559 < baseStart_1377559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377589 : List Nat := [1, 3, 3, 1, 2, 2, 2, 3, 1, 4]
def baseStart_1377589 : Nat := 118140960795 + 1377589 * 2 ^ 59
def prefixEnd_1377589 : Nat := 4983230072969 + 3 ^ 40 * 1377589 * 2
def baseEnd_1377589 : Nat := 471576867564477273601393

theorem tailTrace_1377589 : CollatzResearch.WordTrace tailWord_1377589 prefixEnd_1377589 471576867564477273601393 := by
  unfold tailWord_1377589
  simp only [CollatzResearch.WordTrace]
  refine ⟨50244798606237801315231821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33496532404158534210154547 50244798606237801315231821)
  ·
    refine ⟨18841799477339175493211933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50244798606237801315231821 18841799477339175493211933)
    ·
      refine ⟨7065674804002190809954475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18841799477339175493211933 7065674804002190809954475)
      ·
        refine ⟨10598512206003286214931713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7065674804002190809954475 10598512206003286214931713)
        ·
          refine ⟨7948884154502464661198785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10598512206003286214931713 7948884154502464661198785)
          ·
            refine ⟨5961663115876848495899089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7948884154502464661198785 5961663115876848495899089)
            ·
              refine ⟨4471247336907636371924317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5961663115876848495899089 4471247336907636371924317)
              ·
                refine ⟨1676717751340363639471619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4471247336907636371924317 1676717751340363639471619)
                ·
                  refine ⟨2515076627010545459207429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1676717751340363639471619 2515076627010545459207429)
                  ·
                    refine ⟨471576867564477273601393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2515076627010545459207429 471576867564477273601393)
                    ·
                      rfl

theorem cell22_1377589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_1377589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1377589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1377589 prefixEnd_1377589 := by exact prefixLift 1377589
  have htrace : WordTrace (prefixWord ++ tailWord_1377589) baseStart_1377589 baseEnd_1377589 := by
    simpa [prefixWord, tailWord_1377589, baseEnd_1377589] using wordTrace_append hprefix tailTrace_1377589
  have hstable : (prefixWord ++ tailWord_1377589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377589).length < 2 ^ (prefixWord ++ tailWord_1377589).sum := by decide
  have hdescent : baseEnd_1377589 < baseStart_1377589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377617 : List Nat := [1, 2, 2, 1, 4, 1, 1, 2, 4, 4]
def baseStart_1377617 : Nat := 118140960795 + 1377617 * 2 ^ 59
def prefixEnd_1377617 : Nat := 4983230072969 + 3 ^ 40 * 1377617 * 2
def baseEnd_1377617 : Nat := 471586452536694533901307

theorem tailTrace_1377617 : CollatzResearch.WordTrace tailWord_1377617 prefixEnd_1377617 471586452536694533901307 := by
  unfold tailWord_1377617
  simp only [CollatzResearch.WordTrace]
  refine ⟨50245819850136362097251105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33497213233424241398167403 50245819850136362097251105)
  ·
    refine ⟨37684364887602271572938329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50245819850136362097251105 37684364887602271572938329)
    ·
      refine ⟨28263273665701703679703747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37684364887602271572938329 28263273665701703679703747)
      ·
        refine ⟨42394910498552555519555621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28263273665701703679703747 42394910498552555519555621)
        ·
          refine ⟨7949045718478604159916679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42394910498552555519555621 7949045718478604159916679)
          ·
            refine ⟨11923568577717906239875019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7949045718478604159916679 11923568577717906239875019)
            ·
              refine ⟨17885352866576859359812529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11923568577717906239875019 17885352866576859359812529)
              ·
                refine ⟨13414014649932644519859397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17885352866576859359812529 13414014649932644519859397)
                ·
                  refine ⟨2515127746862370847473637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13414014649932644519859397 2515127746862370847473637)
                  ·
                    refine ⟨471586452536694533901307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2515127746862370847473637 471586452536694533901307)
                    ·
                      rfl

theorem cell22_1377617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 4, 4].length) (baseStart_1377617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1377617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1377617 prefixEnd_1377617 := by exact prefixLift 1377617
  have htrace : WordTrace (prefixWord ++ tailWord_1377617) baseStart_1377617 baseEnd_1377617 := by
    simpa [prefixWord, tailWord_1377617, baseEnd_1377617] using wordTrace_append hprefix tailTrace_1377617
  have hstable : (prefixWord ++ tailWord_1377617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377617).length < 2 ^ (prefixWord ++ tailWord_1377617).sum := by decide
  have hdescent : baseEnd_1377617 < baseStart_1377617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377619 : List Nat := [1, 1, 1, 2, 1, 1, 7, 3, 2, 3]
def baseStart_1377619 : Nat := 118140960795 + 1377619 * 2 ^ 59
def prefixEnd_1377619 : Nat := 4983230072969 + 3 ^ 40 * 1377619 * 2
def baseEnd_1377619 : Nat := 471587137177567195351301

theorem tailTrace_1377619 : CollatzResearch.WordTrace tailWord_1377619 prefixEnd_1377619 471587137177567195351301 := by
  unfold tailWord_1377619
  simp only [CollatzResearch.WordTrace]
  refine ⟨50245892796129116438823911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33497261864086077625882607 50245892796129116438823911)
  ·
    refine ⟨75368839194193674658235867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50245892796129116438823911 75368839194193674658235867)
    ·
      refine ⟨113053258791290511987353801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75368839194193674658235867 113053258791290511987353801)
      ·
        refine ⟨84789944093467883990515351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113053258791290511987353801 84789944093467883990515351)
        ·
          refine ⟨127184916140201825985773027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84789944093467883990515351 127184916140201825985773027)
          ·
            refine ⟨190777374210302738978659541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127184916140201825985773027 190777374210302738978659541)
            ·
              refine ⟨4471344708053970444812333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 190777374210302738978659541 4471344708053970444812333)
              ·
                refine ⟨1676754265520238916804625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4471344708053970444812333 1676754265520238916804625)
                ·
                  refine ⟨1257565699140179187603469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1676754265520238916804625 1257565699140179187603469)
                  ·
                    refine ⟨471587137177567195351301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1257565699140179187603469 471587137177567195351301)
                    ·
                      rfl

theorem cell22_1377619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 3, 2, 3].length) (baseStart_1377619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1377619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1377619 prefixEnd_1377619 := by exact prefixLift 1377619
  have htrace : WordTrace (prefixWord ++ tailWord_1377619) baseStart_1377619 baseEnd_1377619 := by
    simpa [prefixWord, tailWord_1377619, baseEnd_1377619] using wordTrace_append hprefix tailTrace_1377619
  have hstable : (prefixWord ++ tailWord_1377619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377619).length < 2 ^ (prefixWord ++ tailWord_1377619).sum := by decide
  have hdescent : baseEnd_1377619 < baseStart_1377619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377632 : List Nat := [2, 1, 1, 3, 4, 1, 2, 8]
def baseStart_1377632 : Nat := 118140960795 + 1377632 * 2 ^ 59
def prefixEnd_1377632 : Nat := 4983230072969 + 3 ^ 40 * 1377632 * 2
def baseEnd_1377632 : Nat := 52399065260359943864029

theorem tailTrace_1377632 : CollatzResearch.WordTrace tailWord_1377632 prefixEnd_1377632 52399065260359943864029 := by
  unfold tailWord_1377632
  simp only [CollatzResearch.WordTrace]
  refine ⟨25123183472541009829523575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33497577963388013106031433 25123183472541009829523575)
  ·
    refine ⟨37684775208811514744285363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25123183472541009829523575 37684775208811514744285363)
    ·
      refine ⟨56527162813217272116428045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37684775208811514744285363 56527162813217272116428045)
      ·
        refine ⟨21197686054956477043660517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56527162813217272116428045 21197686054956477043660517)
        ·
          refine ⟨3974566135304339445686347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21197686054956477043660517 3974566135304339445686347)
          ·
            refine ⟨5961849202956509168529521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3974566135304339445686347 5961849202956509168529521)
            ·
              refine ⟨4471386902217381876397141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5961849202956509168529521 4471386902217381876397141)
              ·
                refine ⟨52399065260359943864029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4471386902217381876397141 52399065260359943864029)
                ·
                  rfl

theorem cell22_1377632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 8].length) (baseStart_1377632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1377632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1377632 prefixEnd_1377632 := by exact prefixLift 1377632
  have htrace : WordTrace (prefixWord ++ tailWord_1377632) baseStart_1377632 baseEnd_1377632 := by
    simpa [prefixWord, tailWord_1377632, baseEnd_1377632] using wordTrace_append hprefix tailTrace_1377632
  have hstable : (prefixWord ++ tailWord_1377632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377632).length < 2 ^ (prefixWord ++ tailWord_1377632).sum := by decide
  have hdescent : baseEnd_1377632 < baseStart_1377632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377653 : List Nat := [1, 3, 4, 1, 3, 1, 2, 2, 2, 3]
def baseStart_1377653 : Nat := 118140960795 + 1377653 * 2 ^ 59
def prefixEnd_1377653 : Nat := 4983230072969 + 3 ^ 40 * 1377653 * 2
def baseEnd_1377653 : Nat := 471598776072402440001197

theorem tailTrace_1377653 : CollatzResearch.WordTrace tailWord_1377653 prefixEnd_1377653 471598776072402440001197 := by
  unfold tailWord_1377653
  simp only [CollatzResearch.WordTrace]
  refine ⟨50247132878005940245561613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33498088585337293497041075 50247132878005940245561613)
  ·
    refine ⟨18842674829252227592085605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50247132878005940245561613 18842674829252227592085605)
    ·
      refine ⟨3533001530484792673516051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18842674829252227592085605 3533001530484792673516051)
      ·
        refine ⟨5299502295727189010274077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3533001530484792673516051 5299502295727189010274077)
        ·
          refine ⟨1987313360897695878852779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5299502295727189010274077 1987313360897695878852779)
          ·
            refine ⟨2980970041346543818279169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1987313360897695878852779 2980970041346543818279169)
            ·
              refine ⟨2235727531009907863709377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2980970041346543818279169 2235727531009907863709377)
              ·
                refine ⟨1676795648257430897782033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2235727531009907863709377 1676795648257430897782033)
                ·
                  refine ⟨1257596736193073173336525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1676795648257430897782033 1257596736193073173336525)
                  ·
                    refine ⟨471598776072402440001197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1257596736193073173336525 471598776072402440001197)
                    ·
                      rfl

theorem cell22_1377653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_1377653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1377653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1377653 prefixEnd_1377653 := by exact prefixLift 1377653
  have htrace : WordTrace (prefixWord ++ tailWord_1377653) baseStart_1377653 baseEnd_1377653 := by
    simpa [prefixWord, tailWord_1377653, baseEnd_1377653] using wordTrace_append hprefix tailTrace_1377653
  have hstable : (prefixWord ++ tailWord_1377653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377653).length < 2 ^ (prefixWord ++ tailWord_1377653).sum := by decide
  have hdescent : baseEnd_1377653 < baseStart_1377653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377666 : List Nat := [3, 4, 2, 1, 1, 1, 3, 7]
def baseStart_1377666 : Nat := 118140960795 + 1377666 * 2 ^ 59
def prefixEnd_1377666 : Nat := 4983230072969 + 3 ^ 40 * 1377666 * 2
def baseEnd_1377666 : Nat := 52400358470897193269573

theorem tailTrace_1377666 : CollatzResearch.WordTrace tailWord_1377666 prefixEnd_1377666 52400358470897193269573 := by
  unfold tailWord_1377666
  simp only [CollatzResearch.WordTrace]
  refine ⟨12561901756739710866446213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33498404684639228977189901 12561901756739710866446213)
  ·
    refine ⟨2355356579388695787458665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12561901756739710866446213 2355356579388695787458665)
    ·
      refine ⟨1766517434541521840593999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2355356579388695787458665 1766517434541521840593999)
      ·
        refine ⟨2649776151812282760890999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1766517434541521840593999 2649776151812282760890999)
        ·
          refine ⟨3974664227718424141336499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2649776151812282760890999 3974664227718424141336499)
          ·
            refine ⟨5961996341577636212004749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3974664227718424141336499 5961996341577636212004749)
            ·
              refine ⟨2235748628091613579501781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5961996341577636212004749 2235748628091613579501781)
              ·
                refine ⟨52400358470897193269573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2235748628091613579501781 52400358470897193269573)
                ·
                  rfl

theorem cell22_1377666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 7].length) (baseStart_1377666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1377666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1377666 prefixEnd_1377666 := by exact prefixLift 1377666
  have htrace : WordTrace (prefixWord ++ tailWord_1377666) baseStart_1377666 baseEnd_1377666 := by
    simpa [prefixWord, tailWord_1377666, baseEnd_1377666] using wordTrace_append hprefix tailTrace_1377666
  have hstable : (prefixWord ++ tailWord_1377666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377666).length < 2 ^ (prefixWord ++ tailWord_1377666).sum := by decide
  have hdescent : baseEnd_1377666 < baseStart_1377666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377698 : List Nat := [3, 3, 1, 2, 1, 2, 1, 5, 1, 3]
def baseStart_1377698 : Nat := 118140960795 + 1377698 * 2 ^ 59
def prefixEnd_1377698 : Nat := 4983230072969 + 3 ^ 40 * 1377698 * 2
def baseEnd_1377698 : Nat := 471614180492037322626059

theorem tailTrace_1377698 : CollatzResearch.WordTrace tailWord_1377698 prefixEnd_1377698 471614180492037322626059 := by
  unfold tailWord_1377698
  simp only [CollatzResearch.WordTrace]
  refine ⟨12562193540710728232737437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33499182775228608620633165 12562193540710728232737437)
  ·
    refine ⟨4710822577766523087276539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12562193540710728232737437 4710822577766523087276539)
    ·
      refine ⟨7066233866649784630914809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4710822577766523087276539 7066233866649784630914809)
      ·
        refine ⟨5299675399987338473186107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7066233866649784630914809 5299675399987338473186107)
        ·
          refine ⟨7949513099981007709779161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5299675399987338473186107 7949513099981007709779161)
          ·
            refine ⟨5962134824985755782334371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7949513099981007709779161 5962134824985755782334371)
            ·
              refine ⟨8943202237478633673501557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5962134824985755782334371 8943202237478633673501557)
              ·
                refine ⟨838425209763621906890771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8943202237478633673501557 838425209763621906890771)
                ·
                  refine ⟨1257637814645432860336157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 838425209763621906890771 1257637814645432860336157)
                  ·
                    refine ⟨471614180492037322626059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1257637814645432860336157 471614180492037322626059)
                    ·
                      rfl

theorem cell22_1377698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 5, 1, 3].length) (baseStart_1377698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1377698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1377698 prefixEnd_1377698 := by exact prefixLift 1377698
  have htrace : WordTrace (prefixWord ++ tailWord_1377698) baseStart_1377698 baseEnd_1377698 := by
    simpa [prefixWord, tailWord_1377698, baseEnd_1377698] using wordTrace_append hprefix tailTrace_1377698
  have hstable : (prefixWord ++ tailWord_1377698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377698).length < 2 ^ (prefixWord ++ tailWord_1377698).sum := by decide
  have hdescent : baseEnd_1377698 < baseStart_1377698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377773 : List Nat := [1, 5, 1, 3, 2, 2, 1, 1, 6]
def baseStart_1377773 : Nat := 118140960795 + 1377773 * 2 ^ 59
def prefixEnd_1377773 : Nat := 4983230072969 + 3 ^ 40 * 1377773 * 2
def baseEnd_1377773 : Nat := 157213284841587375666943

theorem tailTrace_1377773 : CollatzResearch.WordTrace tailWord_1377773 prefixEnd_1377773 157213284841587375666943 := by
  unfold tailWord_1377773
  simp only [CollatzResearch.WordTrace]
  refine ⟨50251509637571200739929973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33501006425047467159953315 50251509637571200739929973)
  ·
    refine ⟨4711079028522300069368435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50251509637571200739929973 4711079028522300069368435)
    ·
      refine ⟨7066618542783450104052653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4711079028522300069368435 7066618542783450104052653)
      ·
        refine ⟨2649981953543793789019745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7066618542783450104052653 2649981953543793789019745)
        ·
          refine ⟨1987486465157845341764809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2649981953543793789019745 1987486465157845341764809)
          ·
            refine ⟨1490614848868384006323607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1987486465157845341764809 1490614848868384006323607)
            ·
              refine ⟨2235922273302576009485411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1490614848868384006323607 2235922273302576009485411)
              ·
                refine ⟨3353883409953864014228117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2235922273302576009485411 3353883409953864014228117)
                ·
                  refine ⟨157213284841587375666943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3353883409953864014228117 157213284841587375666943)
                  ·
                    rfl

theorem cell22_1377773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 1, 6].length) (baseStart_1377773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1377773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1377773 prefixEnd_1377773 := by exact prefixLift 1377773
  have htrace : WordTrace (prefixWord ++ tailWord_1377773) baseStart_1377773 baseEnd_1377773 := by
    simpa [prefixWord, tailWord_1377773, baseEnd_1377773] using wordTrace_append hprefix tailTrace_1377773
  have hstable : (prefixWord ++ tailWord_1377773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377773).length < 2 ^ (prefixWord ++ tailWord_1377773).sum := by decide
  have hdescent : baseEnd_1377773 < baseStart_1377773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377784 : List Nat := [2, 1, 2, 1, 1, 6, 2, 7]
def baseStart_1377784 : Nat := 118140960795 + 1377784 * 2 ^ 59
def prefixEnd_1377784 : Nat := 4983230072969 + 3 ^ 40 * 1377784 * 2
def baseEnd_1377784 : Nat := 52404846672173529441755

theorem tailTrace_1377784 : CollatzResearch.WordTrace tailWord_1377784 prefixEnd_1377784 52404846672173529441755 := by
  unfold tailWord_1377784
  simp only [CollatzResearch.WordTrace]
  refine ⟨25125955420265674809290203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33501273893687566412386937 25125955420265674809290203)
  ·
    refine ⟨37688933130398512213935305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25125955420265674809290203 37688933130398512213935305)
    ·
      refine ⟨28266699847798884160451479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37688933130398512213935305 28266699847798884160451479)
      ·
        refine ⟨42400049771698326240677219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28266699847798884160451479 42400049771698326240677219)
        ·
          refine ⟨63600074657547489361015829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42400049771698326240677219 63600074657547489361015829)
          ·
            refine ⟨2981253499572538563797617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 63600074657547489361015829 2981253499572538563797617)
            ·
              refine ⟨2235940124679403922848213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2981253499572538563797617 2235940124679403922848213)
              ·
                refine ⟨52404846672173529441755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2235940124679403922848213 52404846672173529441755)
                ·
                  rfl

theorem cell22_1377784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 7].length) (baseStart_1377784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1377784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1377784 prefixEnd_1377784 := by exact prefixLift 1377784
  have htrace : WordTrace (prefixWord ++ tailWord_1377784) baseStart_1377784 baseEnd_1377784 := by
    simpa [prefixWord, tailWord_1377784, baseEnd_1377784] using wordTrace_append hprefix tailTrace_1377784
  have hstable : (prefixWord ++ tailWord_1377784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377784).length < 2 ^ (prefixWord ++ tailWord_1377784).sum := by decide
  have hdescent : baseEnd_1377784 < baseStart_1377784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377788 : List Nat := [2, 2, 2, 1, 2, 1, 6, 1, 2, 3]
def baseStart_1377788 : Nat := 118140960795 + 1377788 * 2 ^ 59
def prefixEnd_1377788 : Nat := 4983230072969 + 3 ^ 40 * 1377788 * 2
def baseEnd_1377788 : Nat := 471644989331307087875783

theorem tailTrace_1377788 : CollatzResearch.WordTrace tailWord_1377788 prefixEnd_1377788 471644989331307087875783 := by
  unfold tailWord_1377788
  simp only [CollatzResearch.WordTrace]
  refine ⟨25126028366258429150863009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33501371155011238867817345 25126028366258429150863009)
  ·
    refine ⟨18844521274693821863147257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25126028366258429150863009 18844521274693821863147257)
    ·
      refine ⟨14133390956020366397360443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18844521274693821863147257 14133390956020366397360443)
      ·
        refine ⟨21200086434030549596040665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14133390956020366397360443 21200086434030549596040665)
        ·
          refine ⟨15900064825522912197030499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21200086434030549596040665 15900064825522912197030499)
          ·
            refine ⟨23850097238284368295545749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15900064825522912197030499 23850097238284368295545749)
            ·
              refine ⟨1117973308044579763853707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 23850097238284368295545749 1117973308044579763853707)
              ·
                refine ⟨1676959962066869645780561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1117973308044579763853707 1676959962066869645780561)
                ·
                  refine ⟨1257719971550152234335421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1676959962066869645780561 1257719971550152234335421)
                  ·
                    refine ⟨471644989331307087875783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1257719971550152234335421 471644989331307087875783)
                    ·
                      rfl

theorem cell22_1377788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 6, 1, 2, 3].length) (baseStart_1377788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1377788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1377788 prefixEnd_1377788 := by exact prefixLift 1377788
  have htrace : WordTrace (prefixWord ++ tailWord_1377788) baseStart_1377788 baseEnd_1377788 := by
    simpa [prefixWord, tailWord_1377788, baseEnd_1377788] using wordTrace_append hprefix tailTrace_1377788
  have hstable : (prefixWord ++ tailWord_1377788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377788).length < 2 ^ (prefixWord ++ tailWord_1377788).sum := by decide
  have hdescent : baseEnd_1377788 < baseStart_1377788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377805 : List Nat := [1, 7, 1, 1, 2, 1, 1, 2, 1, 5]
def baseStart_1377805 : Nat := 118140960795 + 1377805 * 2 ^ 59
def prefixEnd_1377805 : Nat := 4983230072969 + 3 ^ 40 * 1377805 * 2
def baseEnd_1377805 : Nat := 471650808778724710200731

theorem tailTrace_1377805 : CollatzResearch.WordTrace tailWord_1377805 prefixEnd_1377805 471650808778724710200731 := by
  unfold tailWord_1377805
  simp only [CollatzResearch.WordTrace]
  refine ⟨50252676773455270205094869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33501784515636846803396579 50252676773455270205094869)
  ·
    refine ⟨1177797111877857895431911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 50252676773455270205094869 1177797111877857895431911)
    ·
      refine ⟨1766695667816786843147867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1177797111877857895431911 1766695667816786843147867)
      ·
        refine ⟨2650043501725180264721801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1766695667816786843147867 2650043501725180264721801)
        ·
          refine ⟨1987532626293885198541351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2650043501725180264721801 1987532626293885198541351)
          ·
            refine ⟨2981298939440827797812027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1987532626293885198541351 2981298939440827797812027)
            ·
              refine ⟨4471948409161241696718041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2981298939440827797812027 4471948409161241696718041)
              ·
                refine ⟨3353961306870931272538531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4471948409161241696718041 3353961306870931272538531)
                ·
                  refine ⟨5030941960306396908807797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3353961306870931272538531 5030941960306396908807797)
                  ·
                    refine ⟨471650808778724710200731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5030941960306396908807797 471650808778724710200731)
                    ·
                      rfl

theorem cell22_1377805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_1377805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1377805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1377805 prefixEnd_1377805 := by exact prefixLift 1377805
  have htrace : WordTrace (prefixWord ++ tailWord_1377805) baseStart_1377805 baseEnd_1377805 := by
    simpa [prefixWord, tailWord_1377805, baseEnd_1377805] using wordTrace_append hprefix tailTrace_1377805
  have hstable : (prefixWord ++ tailWord_1377805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377805).length < 2 ^ (prefixWord ++ tailWord_1377805).sum := by decide
  have hdescent : baseEnd_1377805 < baseStart_1377805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377891 : List Nat := [1, 1, 1, 5, 1, 4, 2, 1, 6]
def baseStart_1377891 : Nat := 118140960795 + 1377891 * 2 ^ 59
def prefixEnd_1377891 : Nat := 4983230072969 + 3 ^ 40 * 1377891 * 2
def baseEnd_1377891 : Nat := 157226749445416384183489

theorem tailTrace_1377891 : CollatzResearch.WordTrace tailWord_1377891 prefixEnd_1377891 157226749445416384183489 := by
  unfold tailWord_1377891
  simp only [CollatzResearch.WordTrace]
  refine ⟨50255813451143706892725527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33503875634095804595150351 50255813451143706892725527)
  ·
    refine ⟨75383720176715560339088291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50255813451143706892725527 75383720176715560339088291)
    ·
      refine ⟨113075580265073340508632437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75383720176715560339088291 113075580265073340508632437)
      ·
        refine ⟨10600835649850625672684291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 113075580265073340508632437 10600835649850625672684291)
        ·
          refine ⟨15901253474775938509026437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10600835649850625672684291 15901253474775938509026437)
          ·
            refine ⟨2981485026520488470442457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15901253474775938509026437 2981485026520488470442457)
            ·
              refine ⟨2236113769890366352831843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2981485026520488470442457 2236113769890366352831843)
              ·
                refine ⟨3354170654835549529247765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2236113769890366352831843 3354170654835549529247765)
                ·
                  refine ⟨157226749445416384183489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3354170654835549529247765 157226749445416384183489)
                  ·
                    rfl

theorem cell22_1377891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 1, 6].length) (baseStart_1377891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1377891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1377891 prefixEnd_1377891 := by exact prefixLift 1377891
  have htrace : WordTrace (prefixWord ++ tailWord_1377891) baseStart_1377891 baseEnd_1377891 := by
    simpa [prefixWord, tailWord_1377891, baseEnd_1377891] using wordTrace_append hprefix tailTrace_1377891
  have hstable : (prefixWord ++ tailWord_1377891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377891).length < 2 ^ (prefixWord ++ tailWord_1377891).sum := by decide
  have hdescent : baseEnd_1377891 < baseStart_1377891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377910 : List Nat := [5, 1, 1, 2, 2, 2, 2, 2, 1, 4]
def baseStart_1377910 : Nat := 118140960795 + 1377910 * 2 ^ 59
def prefixEnd_1377910 : Nat := 4983230072969 + 3 ^ 40 * 1377910 * 2
def baseEnd_1377910 : Nat := 471686752424539436325409

theorem tailTrace_1377910 : CollatzResearch.WordTrace tailWord_1377910 prefixEnd_1377910 471686752424539436325409 := by
  unfold tailWord_1377910
  simp only [CollatzResearch.WordTrace]
  refine ⟨3141031652379679571104199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33504337625383248758444789 3141031652379679571104199)
  ·
    refine ⟨4711547478569519356656299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3141031652379679571104199 4711547478569519356656299)
    ·
      refine ⟨7067321217854279034984449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4711547478569519356656299 7067321217854279034984449)
      ·
        refine ⟨5300490913390709276238337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7067321217854279034984449 5300490913390709276238337)
        ·
          refine ⟨3975368185043031957178753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5300490913390709276238337 3975368185043031957178753)
          ·
            refine ⟨2981526138782273967884065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3975368185043031957178753 2981526138782273967884065)
            ·
              refine ⟨2236144604086705475913049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2981526138782273967884065 2236144604086705475913049)
              ·
                refine ⟨1677108453065029106934787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2236144604086705475913049 1677108453065029106934787)
                ·
                  refine ⟨2515662679597543660402181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1677108453065029106934787 2515662679597543660402181)
                  ·
                    refine ⟨471686752424539436325409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2515662679597543660402181 471686752424539436325409)
                    ·
                      rfl

theorem cell22_1377910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_1377910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1377910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1377910 prefixEnd_1377910 := by exact prefixLift 1377910
  have htrace : WordTrace (prefixWord ++ tailWord_1377910) baseStart_1377910 baseEnd_1377910 := by
    simpa [prefixWord, tailWord_1377910, baseEnd_1377910] using wordTrace_append hprefix tailTrace_1377910
  have hstable : (prefixWord ++ tailWord_1377910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377910).length < 2 ^ (prefixWord ++ tailWord_1377910).sum := by decide
  have hdescent : baseEnd_1377910 < baseStart_1377910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377921 : List Nat := [1, 2, 4, 2, 1, 2, 2, 1, 1, 6]
def baseStart_1377921 : Nat := 118140960795 + 1377921 * 2 ^ 59
def prefixEnd_1377921 : Nat := 4983230072969 + 3 ^ 40 * 1377921 * 2
def baseEnd_1377921 : Nat := 471690517949339074300375

theorem tailTrace_1377921 : CollatzResearch.WordTrace tailWord_1377921 prefixEnd_1377921 471690517949339074300375 := by
  unfold tailWord_1377921
  simp only [CollatzResearch.WordTrace]
  refine ⟨50256907641035022016317617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33504605094023348010878411 50256907641035022016317617)
  ·
    refine ⟨37692680730776266512238213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50256907641035022016317617 37692680730776266512238213)
    ·
      refine ⟨7067377637020549971044665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37692680730776266512238213 7067377637020549971044665)
      ·
        refine ⟨5300533227765412478283499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7067377637020549971044665 5300533227765412478283499)
        ·
          refine ⟨7950799841648118717425249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5300533227765412478283499 7950799841648118717425249)
          ·
            refine ⟨5963099881236089038068937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7950799841648118717425249 5963099881236089038068937)
            ·
              refine ⟨4472324910927066778551703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5963099881236089038068937 4472324910927066778551703)
              ·
                refine ⟨6708487366390600167827555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4472324910927066778551703 6708487366390600167827555)
                ·
                  refine ⟨10062731049585900251741333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6708487366390600167827555 10062731049585900251741333)
                  ·
                    refine ⟨471690517949339074300375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10062731049585900251741333 471690517949339074300375)
                    ·
                      rfl

theorem cell22_1377921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_1377921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1377921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1377921 prefixEnd_1377921 := by exact prefixLift 1377921
  have htrace : WordTrace (prefixWord ++ tailWord_1377921) baseStart_1377921 baseEnd_1377921 := by
    simpa [prefixWord, tailWord_1377921, baseEnd_1377921] using wordTrace_append hprefix tailTrace_1377921
  have hstable : (prefixWord ++ tailWord_1377921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377921).length < 2 ^ (prefixWord ++ tailWord_1377921).sum := by decide
  have hdescent : baseEnd_1377921 < baseStart_1377921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1377998 : List Nat := [4, 1, 1, 1, 3, 1, 4, 2, 5]
def baseStart_1377998 : Nat := 118140960795 + 1377998 * 2 ^ 59
def prefixEnd_1377998 : Nat := 4983230072969 + 3 ^ 40 * 1377998 * 2
def baseEnd_1377998 : Nat := 157238958874312180041713

theorem tailTrace_1377998 : CollatzResearch.WordTrace tailWord_1377998 prefixEnd_1377998 157238958874312180041713 := by
  unfold tailWord_1377998
  simp only [CollatzResearch.WordTrace]
  refine ⟨6282464507719508020858831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33506477374504042777913765 6282464507719508020858831)
  ·
    refine ⟨9423696761579262031288247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6282464507719508020858831 9423696761579262031288247)
    ·
      refine ⟨14135545142368893046932371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9423696761579262031288247 14135545142368893046932371)
      ·
        refine ⟨21203317713553339570398557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14135545142368893046932371 21203317713553339570398557)
        ·
          refine ⟨7951244142582502338899459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21203317713553339570398557 7951244142582502338899459)
          ·
            refine ⟨11926866213873753508349189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7951244142582502338899459 11926866213873753508349189)
            ·
              refine ⟨2236287415101328782815473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11926866213873753508349189 2236287415101328782815473)
              ·
                refine ⟨1677215561325996587111605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2236287415101328782815473 1677215561325996587111605)
                ·
                  refine ⟨157238958874312180041713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1677215561325996587111605 157238958874312180041713)
                  ·
                    rfl

theorem cell22_1377998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 2, 5].length) (baseStart_1377998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1377998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1377998 prefixEnd_1377998 := by exact prefixLift 1377998
  have htrace : WordTrace (prefixWord ++ tailWord_1377998) baseStart_1377998 baseEnd_1377998 := by
    simpa [prefixWord, tailWord_1377998, baseEnd_1377998] using wordTrace_append hprefix tailTrace_1377998
  have hstable : (prefixWord ++ tailWord_1377998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1377998).length < 2 ^ (prefixWord ++ tailWord_1377998).sum := by decide
  have hdescent : baseEnd_1377998 < baseStart_1377998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1377998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378002 : List Nat := [3, 2, 2, 2, 2, 2, 1, 4, 1, 3]
def baseStart_1378002 : Nat := 118140960795 + 1378002 * 2 ^ 59
def prefixEnd_1378002 : Nat := 4983230072969 + 3 ^ 40 * 1378002 * 2
def baseEnd_1378002 : Nat := 471718245904681863025127

theorem tailTrace_1378002 : CollatzResearch.WordTrace tailWord_1378002 prefixEnd_1378002 471718245904681863025127 := by
  unfold tailWord_1378002
  simp only [CollatzResearch.WordTrace]
  refine ⟨12564965488435393212504065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33506574635827715233344173 12564965488435393212504065)
  ·
    refine ⟨9423724116326544909378049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12564965488435393212504065 9423724116326544909378049)
    ·
      refine ⟨7067793087244908682033537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9423724116326544909378049 7067793087244908682033537)
      ·
        refine ⟨5300844815433681511525153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7067793087244908682033537 5300844815433681511525153)
        ·
          refine ⟨3975633611575261133643865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5300844815433681511525153 3975633611575261133643865)
          ·
            refine ⟨2981725208681445850232899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3975633611575261133643865 2981725208681445850232899)
            ·
              refine ⟨4472587813022168775349349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2981725208681445850232899 4472587813022168775349349)
              ·
                refine ⟨838610214941656645378003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4472587813022168775349349 838610214941656645378003)
                ·
                  refine ⟨1257915322412484968067005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 838610214941656645378003 1257915322412484968067005)
                  ·
                    refine ⟨471718245904681863025127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1257915322412484968067005 471718245904681863025127)
                    ·
                      rfl

theorem cell22_1378002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 4, 1, 3].length) (baseStart_1378002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1378002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1378002 prefixEnd_1378002 := by exact prefixLift 1378002
  have htrace : WordTrace (prefixWord ++ tailWord_1378002) baseStart_1378002 baseEnd_1378002 := by
    simpa [prefixWord, tailWord_1378002, baseEnd_1378002] using wordTrace_append hprefix tailTrace_1378002
  have hstable : (prefixWord ++ tailWord_1378002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378002).length < 2 ^ (prefixWord ++ tailWord_1378002).sum := by decide
  have hdescent : baseEnd_1378002 < baseStart_1378002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378026 : List Nat := [3, 1, 3, 1, 1, 1, 3, 1, 8]
def baseStart_1378026 : Nat := 118140960795 + 1378026 * 2 ^ 59
def prefixEnd_1378026 : Nat := 4983230072969 + 3 ^ 40 * 1378026 * 2
def baseEnd_1378026 : Nat := 157242153865051266808351

theorem tailTrace_1378026 : CollatzResearch.WordTrace tailWord_1378026 prefixEnd_1378026 157242153865051266808351 := by
  unfold tailWord_1378026
  simp only [CollatzResearch.WordTrace]
  refine ⟨12565184326413656237222483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33507158203769749965926621 12565184326413656237222483)
  ·
    refine ⟨18847776489620484355833725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12565184326413656237222483 18847776489620484355833725)
    ·
      refine ⟨7067916183607681633437647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18847776489620484355833725 7067916183607681633437647)
      ·
        refine ⟨10601874275411522450156471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7067916183607681633437647 10601874275411522450156471)
        ·
          refine ⟨15902811413117283675234707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10601874275411522450156471 15902811413117283675234707)
          ·
            refine ⟨23854217119675925512852061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15902811413117283675234707 23854217119675925512852061)
            ·
              refine ⟨8945331419878472067319523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23854217119675925512852061 8945331419878472067319523)
              ·
                refine ⟨13417997129817708100979285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8945331419878472067319523 13417997129817708100979285)
                ·
                  refine ⟨157242153865051266808351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13417997129817708100979285 157242153865051266808351)
                  ·
                    rfl

theorem cell22_1378026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 8].length) (baseStart_1378026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1378026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1378026 prefixEnd_1378026 := by exact prefixLift 1378026
  have htrace : WordTrace (prefixWord ++ tailWord_1378026) baseStart_1378026 baseEnd_1378026 := by
    simpa [prefixWord, tailWord_1378026, baseEnd_1378026] using wordTrace_append hprefix tailTrace_1378026
  have hstable : (prefixWord ++ tailWord_1378026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378026).length < 2 ^ (prefixWord ++ tailWord_1378026).sum := by decide
  have hdescent : baseEnd_1378026 < baseStart_1378026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378036 : List Nat := [2, 6, 1, 1, 1, 2, 2, 3, 1, 3]
def baseStart_1378036 : Nat := 118140960795 + 1378036 * 2 ^ 59
def prefixEnd_1378036 : Nat := 4983230072969 + 3 ^ 40 * 1378036 * 2
def baseEnd_1378036 : Nat := 471729884799517107675023

theorem tailTrace_1378036 : CollatzResearch.WordTrace tailWord_1378036 prefixEnd_1378036 471729884799517107675023 := by
  unfold tailWord_1378036
  simp only [CollatzResearch.WordTrace]
  refine ⟨25130551017809198328376981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33507401357078931104502641 25130551017809198328376981)
  ·
    refine ⟨1177994578959806171642671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 25130551017809198328376981 1177994578959806171642671)
    ·
      refine ⟨1766991868439709257464007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1177994578959806171642671 1766991868439709257464007)
      ·
        refine ⟨2650487802659563886196011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1766991868439709257464007 2650487802659563886196011)
        ·
          refine ⟨3975731703989345829294017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2650487802659563886196011 3975731703989345829294017)
          ·
            refine ⟨2981798777992009371970513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3975731703989345829294017 2981798777992009371970513)
            ·
              refine ⟨2236349083494007028977885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2981798777992009371970513 2236349083494007028977885)
              ·
                refine ⟨838630906310252635866707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2236349083494007028977885 838630906310252635866707)
                ·
                  refine ⟨1257946359465378953800061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 838630906310252635866707 1257946359465378953800061)
                  ·
                    refine ⟨471729884799517107675023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1257946359465378953800061 471729884799517107675023)
                    ·
                      rfl

theorem cell22_1378036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_1378036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1378036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1378036 prefixEnd_1378036 := by exact prefixLift 1378036
  have htrace : WordTrace (prefixWord ++ tailWord_1378036) baseStart_1378036 baseEnd_1378036 := by
    simpa [prefixWord, tailWord_1378036, baseEnd_1378036] using wordTrace_append hprefix tailTrace_1378036
  have hstable : (prefixWord ++ tailWord_1378036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378036).length < 2 ^ (prefixWord ++ tailWord_1378036).sum := by decide
  have hdescent : baseEnd_1378036 < baseStart_1378036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378088 : List Nat := [2, 1, 5, 1, 1, 3, 1, 8]
def baseStart_1378088 : Nat := 118140960795 + 1378088 * 2 ^ 59
def prefixEnd_1378088 : Nat := 4983230072969 + 3 ^ 40 * 1378088 * 2
def baseEnd_1378088 : Nat := 52416409495800700597207

theorem tailTrace_1378088 : CollatzResearch.WordTrace tailWord_1378088 prefixEnd_1378088 52416409495800700597207 := by
  unfold tailWord_1378088
  simp only [CollatzResearch.WordTrace]
  refine ⟨25131499315715004768823459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33508665754286673025097945 25131499315715004768823459)
  ·
    refine ⟨37697248973572507153235189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25131499315715004768823459 37697248973572507153235189)
    ·
      refine ⟨3534117091272422545615799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37697248973572507153235189 3534117091272422545615799)
      ·
        refine ⟨5301175636908633818423699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3534117091272422545615799 5301175636908633818423699)
        ·
          refine ⟨7951763455362950727635549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5301175636908633818423699 7951763455362950727635549)
          ·
            refine ⟨2981911295761106522863331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7951763455362950727635549 2981911295761106522863331)
            ·
              refine ⟨4472866943641659784294997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2981911295761106522863331 4472866943641659784294997)
              ·
                refine ⟨52416409495800700597207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4472866943641659784294997 52416409495800700597207)
                ·
                  rfl

theorem cell22_1378088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 8].length) (baseStart_1378088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1378088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1378088 prefixEnd_1378088 := by exact prefixLift 1378088
  have htrace : WordTrace (prefixWord ++ tailWord_1378088) baseStart_1378088 baseEnd_1378088 := by
    simpa [prefixWord, tailWord_1378088, baseEnd_1378088] using wordTrace_append hprefix tailTrace_1378088
  have hstable : (prefixWord ++ tailWord_1378088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378088).length < 2 ^ (prefixWord ++ tailWord_1378088).sum := by decide
  have hdescent : baseEnd_1378088 < baseStart_1378088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378094 : List Nat := [4, 1, 3, 2, 2, 2, 1, 3, 4]
def baseStart_1378094 : Nat := 118140960795 + 1378094 * 2 ^ 59
def prefixEnd_1378094 : Nat := 4983230072969 + 3 ^ 40 * 1378094 * 2
def baseEnd_1378094 : Nat := 157249913128274763241615

theorem tailTrace_1378094 : CollatzResearch.WordTrace tailWord_1378094 prefixEnd_1378094 157249913128274763241615 := by
  unfold tailWord_1378094
  simp only [CollatzResearch.WordTrace]
  refine ⟨6282902183676034070295667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33508811646272181708243557 6282902183676034070295667)
  ·
    refine ⟨9424353275514051105443501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6282902183676034070295667 9424353275514051105443501)
    ·
      refine ⟨3534132478317769164541313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9424353275514051105443501 3534132478317769164541313)
      ·
        refine ⟨2650599358738326873405985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3534132478317769164541313 2650599358738326873405985)
        ·
          refine ⟨1987949519053745155054489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2650599358738326873405985 1987949519053745155054489)
          ·
            refine ⟨1490962139290308866290867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1987949519053745155054489 1490962139290308866290867)
            ·
              refine ⟨2236443208935463299436301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1490962139290308866290867 2236443208935463299436301)
              ·
                refine ⟨838666203350798737288613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2236443208935463299436301 838666203350798737288613)
                ·
                  refine ⟨157249913128274763241615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 838666203350798737288613 157249913128274763241615)
                  ·
                    rfl

theorem cell22_1378094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 3, 4].length) (baseStart_1378094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1378094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1378094 prefixEnd_1378094 := by exact prefixLift 1378094
  have htrace : WordTrace (prefixWord ++ tailWord_1378094) baseStart_1378094 baseEnd_1378094 := by
    simpa [prefixWord, tailWord_1378094, baseEnd_1378094] using wordTrace_append hprefix tailTrace_1378094
  have hstable : (prefixWord ++ tailWord_1378094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378094).length < 2 ^ (prefixWord ++ tailWord_1378094).sum := by decide
  have hdescent : baseEnd_1378094 < baseStart_1378094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378105 : List Nat := [1, 2, 1, 7, 1, 2, 8]
def baseStart_1378105 : Nat := 118140960795 + 1378105 * 2 ^ 59
def prefixEnd_1378105 : Nat := 4983230072969 + 3 ^ 40 * 1378105 * 2
def baseEnd_1378105 : Nat := 17472352033689775099993

theorem tailTrace_1378105 : CollatzResearch.WordTrace tailWord_1378105 prefixEnd_1378105 17472352033689775099993 := by
  unfold tailWord_1378105
  simp only [CollatzResearch.WordTrace]
  refine ⟨50263618672368421441015769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33509079114912280960677179 50263618672368421441015769)
  ·
    refine ⟨37697714004276316080761827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50263618672368421441015769 37697714004276316080761827)
    ·
      refine ⟨56546571006414474121142741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37697714004276316080761827 56546571006414474121142741)
      ·
        refine ⟨1325310257962839237214283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 56546571006414474121142741 1325310257962839237214283)
        ·
          refine ⟨1987965386944258855821425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1325310257962839237214283 1987965386944258855821425)
          ·
            refine ⟨1490974040208194141866069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1987965386944258855821425 1490974040208194141866069)
            ·
              refine ⟨17472352033689775099993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1490974040208194141866069 17472352033689775099993)
              ·
                rfl

theorem cell22_1378105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 8].length) (baseStart_1378105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1378105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1378105 prefixEnd_1378105 := by exact prefixLift 1378105
  have htrace : WordTrace (prefixWord ++ tailWord_1378105) baseStart_1378105 baseEnd_1378105 := by
    simpa [prefixWord, tailWord_1378105, baseEnd_1378105] using wordTrace_append hprefix tailTrace_1378105
  have hstable : (prefixWord ++ tailWord_1378105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378105).length < 2 ^ (prefixWord ++ tailWord_1378105).sum := by decide
  have hdescent : baseEnd_1378105 < baseStart_1378105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378120 : List Nat := [2, 1, 3, 1, 1, 4, 3, 1, 3, 3]
def baseStart_1378120 : Nat := 118140960795 + 1378120 * 2 ^ 59
def prefixEnd_1378120 : Nat := 4983230072969 + 3 ^ 40 * 1378120 * 2
def baseEnd_1378120 : Nat := 471758639716168888574765

theorem tailTrace_1378120 : CollatzResearch.WordTrace tailWord_1378120 prefixEnd_1378120 471758639716168888574765 := by
  unfold tailWord_1378120
  simp only [CollatzResearch.WordTrace]
  refine ⟨25132082883657039501405907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33509443844876052668541209 25132082883657039501405907)
  ·
    refine ⟨37698124325485559252108861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25132082883657039501405907 37698124325485559252108861)
    ·
      refine ⟨14136796622057084719540823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37698124325485559252108861 14136796622057084719540823)
      ·
        refine ⟨21205194933085627079311235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14136796622057084719540823 21205194933085627079311235)
        ·
          refine ⟨31807792399628440618966853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21205194933085627079311235 31807792399628440618966853)
          ·
            refine ⟨5963961074930332616056285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31807792399628440618966853 5963961074930332616056285)
            ·
              refine ⟨2236485403098874731021107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5963961074930332616056285 2236485403098874731021107)
              ·
                refine ⟨3354728104648312096531661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2236485403098874731021107 3354728104648312096531661)
                ·
                  refine ⟨1258023039243117036199373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3354728104648312096531661 1258023039243117036199373)
                  ·
                    refine ⟨471758639716168888574765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1258023039243117036199373 471758639716168888574765)
                    ·
                      rfl

theorem cell22_1378120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 1, 3, 3].length) (baseStart_1378120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1378120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1378120 prefixEnd_1378120 := by exact prefixLift 1378120
  have htrace : WordTrace (prefixWord ++ tailWord_1378120) baseStart_1378120 baseEnd_1378120 := by
    simpa [prefixWord, tailWord_1378120, baseEnd_1378120] using wordTrace_append hprefix tailTrace_1378120
  have hstable : (prefixWord ++ tailWord_1378120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378120).length < 2 ^ (prefixWord ++ tailWord_1378120).sum := by decide
  have hdescent : baseEnd_1378120 < baseStart_1378120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378193 : List Nat := [1, 2, 2, 1, 1, 1, 5, 3, 1, 5]
def baseStart_1378193 : Nat := 118140960795 + 1378193 * 2 ^ 59
def prefixEnd_1378193 : Nat := 4983230072969 + 3 ^ 40 * 1378193 * 2
def baseEnd_1378193 : Nat := 471783629108021031499541

theorem tailTrace_1378193 : CollatzResearch.WordTrace tailWord_1378193 prefixEnd_1378193 471783629108021031499541 := by
  unfold tailWord_1378193
  simp only [CollatzResearch.WordTrace]
  refine ⟨50266828296049612470219233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33511218864033074980146155 50266828296049612470219233)
  ·
    refine ⟨37700121222037209352664425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50266828296049612470219233 37700121222037209352664425)
    ·
      refine ⟨28275090916527907014498319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37700121222037209352664425 28275090916527907014498319)
      ·
        refine ⟨42412636374791860521747479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28275090916527907014498319 42412636374791860521747479)
        ·
          refine ⟨63618954562187790782621219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42412636374791860521747479 63618954562187790782621219)
          ·
            refine ⟨95428431843281686173931829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63618954562187790782621219 95428431843281686173931829)
            ·
              refine ⟨8946415485307658078806109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 95428431843281686173931829 8946415485307658078806109)
              ·
                refine ⟨3354905806990371779552291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8946415485307658078806109 3354905806990371779552291)
                ·
                  refine ⟨5032358710485557669328437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3354905806990371779552291 5032358710485557669328437)
                  ·
                    refine ⟨471783629108021031499541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5032358710485557669328437 471783629108021031499541)
                    ·
                      rfl

theorem cell22_1378193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 5].length) (baseStart_1378193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1378193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1378193 prefixEnd_1378193 := by exact prefixLift 1378193
  have htrace : WordTrace (prefixWord ++ tailWord_1378193) baseStart_1378193 baseEnd_1378193 := by
    simpa [prefixWord, tailWord_1378193, baseEnd_1378193] using wordTrace_append hprefix tailTrace_1378193
  have hstable : (prefixWord ++ tailWord_1378193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378193).length < 2 ^ (prefixWord ++ tailWord_1378193).sum := by decide
  have hdescent : baseEnd_1378193 < baseStart_1378193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378212 : List Nat := [2, 3, 1, 2, 1, 4, 2, 3, 4]
def baseStart_1378212 : Nat := 118140960795 + 1378212 * 2 ^ 59
def prefixEnd_1378212 : Nat := 4983230072969 + 3 ^ 40 * 1378212 * 2
def baseEnd_1378212 : Nat := 157263377732103771758161

theorem tailTrace_1378212 : CollatzResearch.WordTrace tailWord_1378212 prefixEnd_1378212 157263377732103771758161 := by
  unfold tailWord_1378212
  simp only [CollatzResearch.WordTrace]
  refine ⟨25133760641490389357580445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33511680855320519143440593 25133760641490389357580445)
  ·
    refine ⟨9425160240558896009092667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25133760641490389357580445 9425160240558896009092667)
    ·
      refine ⟨14137740360838344013639001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9425160240558896009092667 14137740360838344013639001)
      ·
        refine ⟨10603305270628758010229251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14137740360838344013639001 10603305270628758010229251)
        ·
          refine ⟨15904957905943137015343877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10603305270628758010229251 15904957905943137015343877)
          ·
            refine ⟨2982179607364338190376977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15904957905943137015343877 2982179607364338190376977)
            ·
              refine ⟨2236634705523253642782733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2982179607364338190376977 2236634705523253642782733)
              ·
                refine ⟨838738014571220116043525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2236634705523253642782733 838738014571220116043525)
                ·
                  refine ⟨157263377732103771758161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 838738014571220116043525 157263377732103771758161)
                  ·
                    rfl

theorem cell22_1378212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 3, 4].length) (baseStart_1378212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1378212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1378212 prefixEnd_1378212 := by exact prefixLift 1378212
  have htrace : WordTrace (prefixWord ++ tailWord_1378212) baseStart_1378212 baseEnd_1378212 := by
    simpa [prefixWord, tailWord_1378212, baseEnd_1378212] using wordTrace_append hprefix tailTrace_1378212
  have hstable : (prefixWord ++ tailWord_1378212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378212).length < 2 ^ (prefixWord ++ tailWord_1378212).sum := by decide
  have hdescent : baseEnd_1378212 < baseStart_1378212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378255 : List Nat := [1, 1, 2, 1, 1, 5, 1, 4, 3, 3]
def baseStart_1378255 : Nat := 118140960795 + 1378255 * 2 ^ 59
def prefixEnd_1378255 : Nat := 4983230072969 + 3 ^ 40 * 1378255 * 2
def baseEnd_1378255 : Nat := 471804852975073536449351

theorem tailTrace_1378255 : CollatzResearch.WordTrace tailWord_1378255 prefixEnd_1378255 471804852975073536449351 := by
  unfold tailWord_1378255
  simp only [CollatzResearch.WordTrace]
  refine ⟨50269089621824997058976219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33512726414549998039317479 50269089621824997058976219)
  ·
    refine ⟨75403634432737495588464329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50269089621824997058976219 75403634432737495588464329)
    ·
      refine ⟨56552725824553121691348247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75403634432737495588464329 56552725824553121691348247)
      ·
        refine ⟨84829088736829682537022371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56552725824553121691348247 84829088736829682537022371)
        ·
          refine ⟨127243633105244523805533557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84829088736829682537022371 127243633105244523805533557)
          ·
            refine ⟨11929090603616674106768771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 127243633105244523805533557 11929090603616674106768771)
            ·
              refine ⟨17893635905425011160153157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11929090603616674106768771 17893635905425011160153157)
              ·
                refine ⟨3355056732267189592528717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17893635905425011160153157 3355056732267189592528717)
                ·
                  refine ⟨1258146274600196097198269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3355056732267189592528717 1258146274600196097198269)
                  ·
                    refine ⟨471804852975073536449351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1258146274600196097198269 471804852975073536449351)
                    ·
                      rfl

theorem cell22_1378255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 4, 3, 3].length) (baseStart_1378255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1378255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1378255 prefixEnd_1378255 := by exact prefixLift 1378255
  have htrace : WordTrace (prefixWord ++ tailWord_1378255) baseStart_1378255 baseEnd_1378255 := by
    simpa [prefixWord, tailWord_1378255, baseEnd_1378255] using wordTrace_append hprefix tailTrace_1378255
  have hstable : (prefixWord ++ tailWord_1378255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378255).length < 2 ^ (prefixWord ++ tailWord_1378255).sum := by decide
  have hdescent : baseEnd_1378255 < baseStart_1378255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378274 : List Nat := [3, 3, 3, 1, 3, 1, 8]
def baseStart_1378274 : Nat := 118140960795 + 1378274 * 2 ^ 59
def prefixEnd_1378274 : Nat := 4983230072969 + 3 ^ 40 * 1378274 * 2
def baseEnd_1378274 : Nat := 17474494706050511860159

theorem tailTrace_1378274 : CollatzResearch.WordTrace tailWord_1378274 prefixEnd_1378274 17474494706050511860159 := by
  unfold tailWord_1378274
  simp only [CollatzResearch.WordTrace]
  refine ⟨12567445652189040825979469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33513188405837442202611917 12567445652189040825979469)
  ·
    refine ⟨4712792119570890309742301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12567445652189040825979469 4712792119570890309742301)
    ·
      refine ⟨1767297044839083866153363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4712792119570890309742301 1767297044839083866153363)
      ·
        refine ⟨2650945567258625799230045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1767297044839083866153363 2650945567258625799230045)
        ·
          refine ⟨994104587721984674711267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2650945567258625799230045 994104587721984674711267)
          ·
            refine ⟨1491156881582977012066901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 994104587721984674711267 1491156881582977012066901)
            ·
              refine ⟨17474494706050511860159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1491156881582977012066901 17474494706050511860159)
              ·
                rfl

theorem cell22_1378274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 8].length) (baseStart_1378274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1378274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1378274 prefixEnd_1378274 := by exact prefixLift 1378274
  have htrace : WordTrace (prefixWord ++ tailWord_1378274) baseStart_1378274 baseEnd_1378274 := by
    simpa [prefixWord, tailWord_1378274, baseEnd_1378274] using wordTrace_append hprefix tailTrace_1378274
  have hstable : (prefixWord ++ tailWord_1378274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378274).length < 2 ^ (prefixWord ++ tailWord_1378274).sum := by decide
  have hdescent : baseEnd_1378274 < baseStart_1378274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378283 : List Nat := [1, 1, 1, 1, 2, 3, 1, 3, 4, 5]
def baseStart_1378283 : Nat := 118140960795 + 1378283 * 2 ^ 59
def prefixEnd_1378283 : Nat := 4983230072969 + 3 ^ 40 * 1378283 * 2
def baseEnd_1378283 : Nat := 471814437947290796749265

theorem tailTrace_1378283 : CollatzResearch.WordTrace tailWord_1378283 prefixEnd_1378283 471814437947290796749265 := by
  unfold tailWord_1378283
  simp only [CollatzResearch.WordTrace]
  refine ⟨50270110865723557840995503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33513407243815705227330335 50270110865723557840995503)
  ·
    refine ⟨75405166298585336761493255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50270110865723557840995503 75405166298585336761493255)
    ·
      refine ⟨113107749447878005142239883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75405166298585336761493255 113107749447878005142239883)
      ·
        refine ⟨169661624171817007713359825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113107749447878005142239883 169661624171817007713359825)
        ·
          refine ⟨127246218128862755785019869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169661624171817007713359825 127246218128862755785019869)
          ·
            refine ⟨47717331798323533419382451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127246218128862755785019869 47717331798323533419382451)
            ·
              refine ⟨71575997697485300129073677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47717331798323533419382451 71575997697485300129073677)
              ·
                refine ⟨26840999136556987548402629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71575997697485300129073677 26840999136556987548402629)
                ·
                  refine ⟨5032687338104435165325493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26840999136556987548402629 5032687338104435165325493)
                  ·
                    refine ⟨471814437947290796749265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5032687338104435165325493 471814437947290796749265)
                    ·
                      rfl

theorem cell22_1378283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 4, 5].length) (baseStart_1378283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1378283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1378283 prefixEnd_1378283 := by exact prefixLift 1378283
  have htrace : WordTrace (prefixWord ++ tailWord_1378283) baseStart_1378283 baseEnd_1378283 := by
    simpa [prefixWord, tailWord_1378283, baseEnd_1378283] using wordTrace_append hprefix tailTrace_1378283
  have hstable : (prefixWord ++ tailWord_1378283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378283).length < 2 ^ (prefixWord ++ tailWord_1378283).sum := by decide
  have hdescent : baseEnd_1378283 < baseStart_1378283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378289 : List Nat := [1, 2, 2, 2, 5, 2, 1, 1, 3, 3]
def baseStart_1378289 : Nat := 118140960795 + 1378289 * 2 ^ 59
def prefixEnd_1378289 : Nat := 4983230072969 + 3 ^ 40 * 1378289 * 2
def baseEnd_1378289 : Nat := 471816491869908781099247

theorem tailTrace_1378289 : CollatzResearch.WordTrace tailWord_1378289 prefixEnd_1378289 471816491869908781099247 := by
  unfold tailWord_1378289
  simp only [CollatzResearch.WordTrace]
  refine ⟨50270329703701820865713921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33513553135801213910475947 50270329703701820865713921)
  ·
    refine ⟨37702747277776365649285441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50270329703701820865713921 37702747277776365649285441)
    ·
      refine ⟨28277060458332274236964081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37702747277776365649285441 28277060458332274236964081)
      ·
        refine ⟨21207795343749205677723061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28277060458332274236964081 21207795343749205677723061)
        ·
          refine ⟨1988230813476488032286537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21207795343749205677723061 1988230813476488032286537)
          ·
            refine ⟨1491173110107366024214903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1988230813476488032286537 1491173110107366024214903)
            ·
              refine ⟨2236759665161049036322355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1491173110107366024214903 2236759665161049036322355)
              ·
                refine ⟨3355139497741573554483533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2236759665161049036322355 3355139497741573554483533)
                ·
                  refine ⟨1258177311653090082931325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3355139497741573554483533 1258177311653090082931325)
                  ·
                    refine ⟨471816491869908781099247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1258177311653090082931325 471816491869908781099247)
                    ·
                      rfl

theorem cell22_1378289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 1, 3, 3].length) (baseStart_1378289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1378289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1378289 prefixEnd_1378289 := by exact prefixLift 1378289
  have htrace : WordTrace (prefixWord ++ tailWord_1378289) baseStart_1378289 baseEnd_1378289 := by
    simpa [prefixWord, tailWord_1378289, baseEnd_1378289] using wordTrace_append hprefix tailTrace_1378289
  have hstable : (prefixWord ++ tailWord_1378289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378289).length < 2 ^ (prefixWord ++ tailWord_1378289).sum := by decide
  have hdescent : baseEnd_1378289 < baseStart_1378289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378298 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 1, 10]
def baseStart_1378298 : Nat := 118140960795 + 1378298 * 2 ^ 59
def prefixEnd_1378298 : Nat := 4983230072969 + 3 ^ 40 * 1378298 * 2
def baseEnd_1378298 : Nat := 471819572753835757624219

theorem tailTrace_1378298 : CollatzResearch.WordTrace tailWord_1378298 prefixEnd_1378298 471819572753835757624219 := by
  unfold tailWord_1378298
  simp only [CollatzResearch.WordTrace]
  refine ⟨12567664490167303850697887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33513771973779476935194365 12567664490167303850697887)
  ·
    refine ⟨18851496735250955776046831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12567664490167303850697887 18851496735250955776046831)
    ·
      refine ⟨28277245102876433664070247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18851496735250955776046831 28277245102876433664070247)
      ·
        refine ⟨42415867654314650496105371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28277245102876433664070247 42415867654314650496105371)
        ·
          refine ⟨63623801481471975744158057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42415867654314650496105371 63623801481471975744158057)
          ·
            refine ⟨47717851111103981808118543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63623801481471975744158057 47717851111103981808118543)
            ·
              refine ⟨71576776666655972712177815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47717851111103981808118543 71576776666655972712177815)
              ·
                refine ⟨107365164999983959068266723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71576776666655972712177815 107365164999983959068266723)
                ·
                  refine ⟨161047747499975938602400085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107365164999983959068266723 161047747499975938602400085)
                  ·
                    refine ⟨471819572753835757624219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 161047747499975938602400085 471819572753835757624219)
                    ·
                      rfl

theorem cell22_1378298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 1, 10].length) (baseStart_1378298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1378298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1378298 prefixEnd_1378298 := by exact prefixLift 1378298
  have htrace : WordTrace (prefixWord ++ tailWord_1378298) baseStart_1378298 baseEnd_1378298 := by
    simpa [prefixWord, tailWord_1378298, baseEnd_1378298] using wordTrace_append hprefix tailTrace_1378298
  have hstable : (prefixWord ++ tailWord_1378298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378298).length < 2 ^ (prefixWord ++ tailWord_1378298).sum := by decide
  have hdescent : baseEnd_1378298 < baseStart_1378298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378315 : List Nat := [1, 1, 1, 1, 6, 1, 3, 1, 3, 4]
def baseStart_1378315 : Nat := 118140960795 + 1378315 * 2 ^ 59
def prefixEnd_1378315 : Nat := 4983230072969 + 3 ^ 40 * 1378315 * 2
def baseEnd_1378315 : Nat := 471825392201253379949167

theorem tailTrace_1378315 : CollatzResearch.WordTrace tailWord_1378315 prefixEnd_1378315 471825392201253379949167 := by
  unfold tailWord_1378315
  simp only [CollatzResearch.WordTrace]
  refine ⟨50271278001607627306160399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33514185334405084870773599 50271278001607627306160399)
  ·
    refine ⟨75406917002411440959240599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50271278001607627306160399 75406917002411440959240599)
    ·
      refine ⟨113110375503617161438860899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75406917002411440959240599 113110375503617161438860899)
      ·
        refine ⟨169665563255425742158291349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113110375503617161438860899 169665563255425742158291349)
        ·
          refine ⟨7953073277598081663669907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 169665563255425742158291349 7953073277598081663669907)
          ·
            refine ⟨11929609916397122495504861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7953073277598081663669907 11929609916397122495504861)
            ·
              refine ⟨4473603718648920935814323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11929609916397122495504861 4473603718648920935814323)
              ·
                refine ⟨6710405577973381403721485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4473603718648920935814323 6710405577973381403721485)
                ·
                  refine ⟨2516402091740018026395557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6710405577973381403721485 2516402091740018026395557)
                  ·
                    refine ⟨471825392201253379949167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2516402091740018026395557 471825392201253379949167)
                    ·
                      rfl

theorem cell22_1378315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 3, 4].length) (baseStart_1378315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1378315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1378315 prefixEnd_1378315 := by exact prefixLift 1378315
  have htrace : WordTrace (prefixWord ++ tailWord_1378315) baseStart_1378315 baseEnd_1378315 := by
    simpa [prefixWord, tailWord_1378315, baseEnd_1378315] using wordTrace_append hprefix tailTrace_1378315
  have hstable : (prefixWord ++ tailWord_1378315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378315).length < 2 ^ (prefixWord ++ tailWord_1378315).sum := by decide
  have hdescent : baseEnd_1378315 < baseStart_1378315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378340 : List Nat := [2, 3, 1, 4, 3, 1, 2, 2, 1, 3]
def baseStart_1378340 : Nat := 118140960795 + 1378340 * 2 ^ 59
def prefixEnd_1378340 : Nat := 4983230072969 + 3 ^ 40 * 1378340 * 2
def baseEnd_1378340 : Nat := 471833950212161648074091

theorem tailTrace_1378340 : CollatzResearch.WordTrace tailWord_1378340 prefixEnd_1378340 471833950212161648074091 := by
  unfold tailWord_1378340
  simp only [CollatzResearch.WordTrace]
  refine ⟨25136094913258528287910237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33514793217678037717213649 25136094913258528287910237)
  ·
    refine ⟨9426035592471948107966339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25136094913258528287910237 9426035592471948107966339)
    ·
      refine ⟨14139053388707922161949509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9426035592471948107966339 14139053388707922161949509)
      ·
        refine ⟨2651072510382735405365533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14139053388707922161949509 2651072510382735405365533)
        ·
          refine ⟨994152191393525777012075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2651072510382735405365533 994152191393525777012075)
          ·
            refine ⟨1491228287090288665518113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 994152191393525777012075 1491228287090288665518113)
            ·
              refine ⟨1118421215317716499138585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1491228287090288665518113 1118421215317716499138585)
              ·
                refine ⟨838815911488287374353939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1118421215317716499138585 838815911488287374353939)
                ·
                  refine ⟨1258223867232431061530909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 838815911488287374353939 1258223867232431061530909)
                  ·
                    refine ⟨471833950212161648074091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1258223867232431061530909 471833950212161648074091)
                    ·
                      rfl

theorem cell22_1378340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 2, 2, 1, 3].length) (baseStart_1378340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1378340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1378340 prefixEnd_1378340 := by exact prefixLift 1378340
  have htrace : WordTrace (prefixWord ++ tailWord_1378340) baseStart_1378340 baseEnd_1378340 := by
    simpa [prefixWord, tailWord_1378340, baseEnd_1378340] using wordTrace_append hprefix tailTrace_1378340
  have hstable : (prefixWord ++ tailWord_1378340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378340).length < 2 ^ (prefixWord ++ tailWord_1378340).sum := by decide
  have hdescent : baseEnd_1378340 < baseStart_1378340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378345 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 10, 3]
def baseStart_1378345 : Nat := 118140960795 + 1378345 * 2 ^ 59
def prefixEnd_1378345 : Nat := 4983230072969 + 3 ^ 40 * 1378345 * 2
def baseEnd_1378345 : Nat := 471835661814343301699075

theorem tailTrace_1378345 : CollatzResearch.WordTrace tailWord_1378345 prefixEnd_1378345 471835661814343301699075 := by
  unfold tailWord_1378345
  simp only [CollatzResearch.WordTrace]
  refine ⟨50272372191498942429752489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33514914794332628286501659 50272372191498942429752489)
  ·
    refine ⟨37704279143624206822314367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50272372191498942429752489 37704279143624206822314367)
    ·
      refine ⟨56556418715436310233471551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37704279143624206822314367 56556418715436310233471551)
      ·
        refine ⟨84834628073154465350207327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56556418715436310233471551 84834628073154465350207327)
        ·
          refine ⟨127251942109731698025310991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84834628073154465350207327 127251942109731698025310991)
          ·
            refine ⟨190877913164597547037966487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127251942109731698025310991 190877913164597547037966487)
            ·
              refine ⟨286316869746896320556949731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190877913164597547037966487 286316869746896320556949731)
              ·
                refine ⟨429475304620344480835424597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 286316869746896320556949731 429475304620344480835424597)
                ·
                  refine ⟨1258228431504915471197533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 429475304620344480835424597 1258228431504915471197533)
                  ·
                    refine ⟨471835661814343301699075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1258228431504915471197533 471835661814343301699075)
                    ·
                      rfl

theorem cell22_1378345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 10, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 10, 3].length) (baseStart_1378345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1378345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1378345 prefixEnd_1378345 := by exact prefixLift 1378345
  have htrace : WordTrace (prefixWord ++ tailWord_1378345) baseStart_1378345 baseEnd_1378345 := by
    simpa [prefixWord, tailWord_1378345, baseEnd_1378345] using wordTrace_append hprefix tailTrace_1378345
  have hstable : (prefixWord ++ tailWord_1378345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378345).length < 2 ^ (prefixWord ++ tailWord_1378345).sum := by decide
  have hdescent : baseEnd_1378345 < baseStart_1378345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378396 : List Nat := [2, 2, 4, 1, 1, 4, 1, 2, 2, 3]
def baseStart_1378396 : Nat := 118140960795 + 1378396 * 2 ^ 59
def prefixEnd_1378396 : Nat := 4983230072969 + 3 ^ 40 * 1378396 * 2
def baseEnd_1378396 : Nat := 471853120156596168673919

theorem tailTrace_1378396 : CollatzResearch.WordTrace tailWord_1378396 prefixEnd_1378396 471853120156596168673919 := by
  unfold tailWord_1378396
  simp only [CollatzResearch.WordTrace]
  refine ⟨25137116157157089069929521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33516154876209452093239361 25137116157157089069929521)
  ·
    refine ⟨18852837117867816802447141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25137116157157089069929521 18852837117867816802447141)
    ·
      refine ⟨3534906959600215650458839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18852837117867816802447141 3534906959600215650458839)
      ·
        refine ⟨5302360439400323475688259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3534906959600215650458839 5302360439400323475688259)
        ·
          refine ⟨7953540659100485213532389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5302360439400323475688259 7953540659100485213532389)
          ·
            refine ⟨1491288873581340977537323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7953540659100485213532389 1491288873581340977537323)
            ·
              refine ⟨2236933310372011466305985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1491288873581340977537323 2236933310372011466305985)
              ·
                refine ⟨1677699982779008599729489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2236933310372011466305985 1677699982779008599729489)
                ·
                  refine ⟨1258274987084256449797117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1677699982779008599729489 1258274987084256449797117)
                  ·
                    refine ⟨471853120156596168673919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1258274987084256449797117 471853120156596168673919)
                    ·
                      rfl

theorem cell22_1378396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_1378396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1378396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1378396 prefixEnd_1378396 := by exact prefixLift 1378396
  have htrace : WordTrace (prefixWord ++ tailWord_1378396) baseStart_1378396 baseEnd_1378396 := by
    simpa [prefixWord, tailWord_1378396, baseEnd_1378396] using wordTrace_append hprefix tailTrace_1378396
  have hstable : (prefixWord ++ tailWord_1378396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378396).length < 2 ^ (prefixWord ++ tailWord_1378396).sum := by decide
  have hdescent : baseEnd_1378396 < baseStart_1378396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378458 : List Nat := [3, 1, 1, 5, 3, 1, 1, 1, 3, 3]
def baseStart_1378458 : Nat := 118140960795 + 1378458 * 2 ^ 59
def prefixEnd_1378458 : Nat := 4983230072969 + 3 ^ 40 * 1378458 * 2
def baseEnd_1378458 : Nat := 471874344023648673623729

theorem tailTrace_1378458 : CollatzResearch.WordTrace tailWord_1378458 prefixEnd_1378458 471874344023648673623729 := by
  unfold tailWord_1378458
  simp only [CollatzResearch.WordTrace]
  refine ⟨12569123410022390682154007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33517662426726375152410685 12569123410022390682154007)
  ·
    refine ⟨18853685115033586023231011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12569123410022390682154007 18853685115033586023231011)
    ·
      refine ⟨28280527672550379034846517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18853685115033586023231011 28280527672550379034846517)
      ·
        refine ⟨2651299469301598034516861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28280527672550379034846517 2651299469301598034516861)
        ·
          refine ⟨994237300988099262943823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2651299469301598034516861 994237300988099262943823)
          ·
            refine ⟨1491355951482148894415735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 994237300988099262943823 1491355951482148894415735)
            ·
              refine ⟨2237033927223223341623603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1491355951482148894415735 2237033927223223341623603)
              ·
                refine ⟨3355550890834835012435405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2237033927223223341623603 3355550890834835012435405)
                ·
                  refine ⟨1258331584063063129663277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3355550890834835012435405 1258331584063063129663277)
                  ·
                    refine ⟨471874344023648673623729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1258331584063063129663277 471874344023648673623729)
                    ·
                      rfl

theorem cell22_1378458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 1, 3, 3].length) (baseStart_1378458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1378458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1378458 prefixEnd_1378458 := by exact prefixLift 1378458
  have htrace : WordTrace (prefixWord ++ tailWord_1378458) baseStart_1378458 baseEnd_1378458 := by
    simpa [prefixWord, tailWord_1378458, baseEnd_1378458] using wordTrace_append hprefix tailTrace_1378458
  have hstable : (prefixWord ++ tailWord_1378458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378458).length < 2 ^ (prefixWord ++ tailWord_1378458).sum := by decide
  have hdescent : baseEnd_1378458 < baseStart_1378458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378531 : List Nat := [1, 1, 1, 8, 1, 1, 2, 1, 1, 5]
def baseStart_1378531 : Nat := 118140960795 + 1378531 * 2 ^ 59
def prefixEnd_1378531 : Nat := 4983230072969 + 3 ^ 40 * 1378531 * 2
def baseEnd_1378531 : Nat := 471899333415500816548505

theorem tailTrace_1378531 : CollatzResearch.WordTrace tailWord_1378531 prefixEnd_1378531 471899333415500816548505 := by
  unfold tailWord_1378531
  simp only [CollatzResearch.WordTrace]
  refine ⟨50279156168825096196023447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33519437445883397464015631 50279156168825096196023447)
  ·
    refine ⟨75418734253237644294035171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50279156168825096196023447 75418734253237644294035171)
    ·
      refine ⟨113128101379856466441052757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75418734253237644294035171 113128101379856466441052757)
      ·
        refine ⟨1325719938045192966106087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 113128101379856466441052757 1325719938045192966106087)
        ·
          refine ⟨1988579907067789449159131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1325719938045192966106087 1988579907067789449159131)
          ·
            refine ⟨2982869860601684173738697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1988579907067789449159131 2982869860601684173738697)
            ·
              refine ⟨2237152395451263130304023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2982869860601684173738697 2237152395451263130304023)
              ·
                refine ⟨3355728593176894695456035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2237152395451263130304023 3355728593176894695456035)
                ·
                  refine ⟨5033592889765342043184053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3355728593176894695456035 5033592889765342043184053)
                  ·
                    refine ⟨471899333415500816548505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5033592889765342043184053 471899333415500816548505)
                    ·
                      rfl

theorem cell22_1378531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 1, 1, 5].length) (baseStart_1378531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1378531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1378531 prefixEnd_1378531 := by exact prefixLift 1378531
  have htrace : WordTrace (prefixWord ++ tailWord_1378531) baseStart_1378531 baseEnd_1378531 := by
    simpa [prefixWord, tailWord_1378531, baseEnd_1378531] using wordTrace_append hprefix tailTrace_1378531
  have hstable : (prefixWord ++ tailWord_1378531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378531).length < 2 ^ (prefixWord ++ tailWord_1378531).sum := by decide
  have hdescent : baseEnd_1378531 < baseStart_1378531 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378546 : List Nat := [3, 2, 1, 3, 2, 3, 1, 1, 2, 4]
def baseStart_1378546 : Nat := 118140960795 + 1378546 * 2 ^ 59
def prefixEnd_1378546 : Nat := 4983230072969 + 3 ^ 40 * 1378546 * 2
def baseEnd_1378546 : Nat := 471904468222045777423459

theorem tailTrace_1378546 : CollatzResearch.WordTrace tailWord_1378546 prefixEnd_1378546 471904468222045777423459 := by
  unfold tailWord_1378546
  simp only [CollatzResearch.WordTrace]
  refine ⟨12569925815942688439454873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33519802175847169171879661 12569925815942688439454873)
  ·
    refine ⟨9427444361957016329591155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12569925815942688439454873 9427444361957016329591155)
    ·
      refine ⟨14141166542935524494386733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9427444361957016329591155 14141166542935524494386733)
      ·
        refine ⟨5302937453600821685395025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14141166542935524494386733 5302937453600821685395025)
        ·
          refine ⟨3977203090200616264046269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5302937453600821685395025 3977203090200616264046269)
          ·
            refine ⟨1491451158825231099017351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3977203090200616264046269 1491451158825231099017351)
            ·
              refine ⟨2237176738237846648526027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1491451158825231099017351 2237176738237846648526027)
              ·
                refine ⟨3355765107356769972789041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2237176738237846648526027 3355765107356769972789041)
                ·
                  refine ⟨2516823830517577479591781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3355765107356769972789041 2516823830517577479591781)
                  ·
                    refine ⟨471904468222045777423459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2516823830517577479591781 471904468222045777423459)
                    ·
                      rfl

theorem cell22_1378546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 1, 2, 4].length) (baseStart_1378546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1378546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1378546 prefixEnd_1378546 := by exact prefixLift 1378546
  have htrace : WordTrace (prefixWord ++ tailWord_1378546) baseStart_1378546 baseEnd_1378546 := by
    simpa [prefixWord, tailWord_1378546, baseEnd_1378546] using wordTrace_append hprefix tailTrace_1378546
  have hstable : (prefixWord ++ tailWord_1378546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378546).length < 2 ^ (prefixWord ++ tailWord_1378546).sum := by decide
  have hdescent : baseEnd_1378546 < baseStart_1378546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378572 : List Nat := [2, 2, 1, 2, 2, 2, 3, 1, 7]
def baseStart_1378572 : Nat := 118140960795 + 1378572 * 2 ^ 59
def prefixEnd_1378572 : Nat := 4983230072969 + 3 ^ 40 * 1378572 * 2
def baseEnd_1378572 : Nat := 157304456184463458757793

theorem tailTrace_1378572 : CollatzResearch.WordTrace tailWord_1378572 prefixEnd_1378572 157304456184463458757793 := by
  unfold tailWord_1378572
  simp only [CollatzResearch.WordTrace]
  refine ⟨25140325780838280099132985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33520434374451040132177313 25140325780838280099132985)
  ·
    refine ⟨18855244335628710074349739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25140325780838280099132985 18855244335628710074349739)
    ·
      refine ⟨28282866503443065111524609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18855244335628710074349739 28282866503443065111524609)
      ·
        refine ⟨21212149877582298833643457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28282866503443065111524609 21212149877582298833643457)
        ·
          refine ⟨15909112408186724125232593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21212149877582298833643457 15909112408186724125232593)
          ·
            refine ⟨11931834306140043093924445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15909112408186724125232593 11931834306140043093924445)
            ·
              refine ⟨4474437864802516160221667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11931834306140043093924445 4474437864802516160221667)
              ·
                refine ⟨6711656797203774240332501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4474437864802516160221667 6711656797203774240332501)
                ·
                  refine ⟨157304456184463458757793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6711656797203774240332501 157304456184463458757793)
                  ·
                    rfl

theorem cell22_1378572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 7].length) (baseStart_1378572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1378572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1378572 prefixEnd_1378572 := by exact prefixLift 1378572
  have htrace : WordTrace (prefixWord ++ tailWord_1378572) baseStart_1378572 baseEnd_1378572 := by
    simpa [prefixWord, tailWord_1378572, baseEnd_1378572] using wordTrace_append hprefix tailTrace_1378572
  have hstable : (prefixWord ++ tailWord_1378572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378572).length < 2 ^ (prefixWord ++ tailWord_1378572).sum := by decide
  have hdescent : baseEnd_1378572 < baseStart_1378572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378587 : List Nat := [1, 1, 1, 1, 1, 1, 8, 1, 2, 5]
def baseStart_1378587 : Nat := 118140960795 + 1378587 * 2 ^ 59
def prefixEnd_1378587 : Nat := 4983230072969 + 3 ^ 40 * 1378587 * 2
def baseEnd_1378587 : Nat := 471918503359935337148333

theorem tailTrace_1378587 : CollatzResearch.WordTrace tailWord_1378587 prefixEnd_1378587 471918503359935337148333 := by
  unfold tailWord_1378587
  simp only [CollatzResearch.WordTrace]
  refine ⟨50281198656622217760062015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33520799104414811840041343 50281198656622217760062015)
  ·
    refine ⟨75421797984933326640093023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50281198656622217760062015 75421797984933326640093023)
    ·
      refine ⟨113132696977399989960139535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75421797984933326640093023 113132696977399989960139535)
      ·
        refine ⟨169699045466099984940209303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113132696977399989960139535 169699045466099984940209303)
        ·
          refine ⟨254548568199149977410313955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169699045466099984940209303 254548568199149977410313955)
          ·
            refine ⟨381822852298724966115470933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254548568199149977410313955 381822852298724966115470933)
            ·
              refine ⟨4474486550375683196665675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 381822852298724966115470933 4474486550375683196665675)
              ·
                refine ⟨6711729825563524794998513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4474486550375683196665675 6711729825563524794998513)
                ·
                  refine ⟨5033797369172643596248885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6711729825563524794998513 5033797369172643596248885)
                  ·
                    refine ⟨471918503359935337148333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5033797369172643596248885 471918503359935337148333)
                    ·
                      rfl

theorem cell22_1378587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 2, 5].length) (baseStart_1378587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1378587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1378587 prefixEnd_1378587 := by exact prefixLift 1378587
  have htrace : WordTrace (prefixWord ++ tailWord_1378587) baseStart_1378587 baseEnd_1378587 := by
    simpa [prefixWord, tailWord_1378587, baseEnd_1378587] using wordTrace_append hprefix tailTrace_1378587
  have hstable : (prefixWord ++ tailWord_1378587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378587).length < 2 ^ (prefixWord ++ tailWord_1378587).sum := by decide
  have hdescent : baseEnd_1378587 < baseStart_1378587 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378610 : List Nat := [3, 2, 1, 1, 5, 2, 1, 3, 1, 3]
def baseStart_1378610 : Nat := 118140960795 + 1378610 * 2 ^ 59
def prefixEnd_1378610 : Nat := 4983230072969 + 3 ^ 40 * 1378610 * 2
def baseEnd_1378610 : Nat := 471926376729970943823263

theorem tailTrace_1378610 : CollatzResearch.WordTrace tailWord_1378610 prefixEnd_1378610 471926376729970943823263 := by
  unfold tailWord_1378610
  simp only [CollatzResearch.WordTrace]
  refine ⟨12570509383884723172037321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33521358357025928458766189 12570509383884723172037321)
  ·
    refine ⟨9427882037913542379027991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12570509383884723172037321 9427882037913542379027991)
    ·
      refine ⟨14141823056870313568541987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9427882037913542379027991 14141823056870313568541987)
      ·
        refine ⟨21212734585305470352812981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14141823056870313568541987 21212734585305470352812981)
        ·
          refine ⟨1988693867372387845576217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21212734585305470352812981 1988693867372387845576217)
          ·
            refine ⟨1491520400529290884182163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1988693867372387845576217 1491520400529290884182163)
            ·
              refine ⟨2237280600793936326273245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1491520400529290884182163 2237280600793936326273245)
              ·
                refine ⟨838980225297726122352467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2237280600793936326273245 838980225297726122352467)
                ·
                  refine ⟨1258470337946589183528701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 838980225297726122352467 1258470337946589183528701)
                  ·
                    refine ⟨471926376729970943823263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1258470337946589183528701 471926376729970943823263)
                    ·
                      rfl

theorem cell22_1378610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 3, 1, 3].length) (baseStart_1378610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1378610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1378610 prefixEnd_1378610 := by exact prefixLift 1378610
  have htrace : WordTrace (prefixWord ++ tailWord_1378610) baseStart_1378610 baseEnd_1378610 := by
    simpa [prefixWord, tailWord_1378610, baseEnd_1378610] using wordTrace_append hprefix tailTrace_1378610
  have hstable : (prefixWord ++ tailWord_1378610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378610).length < 2 ^ (prefixWord ++ tailWord_1378610).sum := by decide
  have hdescent : baseEnd_1378610 < baseStart_1378610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378666 : List Nat := [3, 1, 3, 3, 1, 2, 1, 2, 1, 5]
def baseStart_1378666 : Nat := 118140960795 + 1378666 * 2 ^ 59
def prefixEnd_1378666 : Nat := 4983230072969 + 3 ^ 40 * 1378666 * 2
def baseEnd_1378666 : Nat := 471945546674405464423091

theorem tailTrace_1378666 : CollatzResearch.WordTrace tailWord_1378666 prefixEnd_1378666 471945546674405464423091 := by
  unfold tailWord_1378666
  simp only [CollatzResearch.WordTrace]
  refine ⟨12571020005834003563046963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33522720015557342834791901 12571020005834003563046963)
  ·
    refine ⟨18856530008751005344570445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12571020005834003563046963 18856530008751005344570445)
    ·
      refine ⟨7071198753281627004213917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18856530008751005344570445 7071198753281627004213917)
      ·
        refine ⟨2651699532480610126580219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7071198753281627004213917 2651699532480610126580219)
        ·
          refine ⟨3977549298720915189870329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2651699532480610126580219 3977549298720915189870329)
          ·
            refine ⟨2983161974040686392402747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3977549298720915189870329 2983161974040686392402747)
            ·
              refine ⟨4474742961061029588604121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2983161974040686392402747 4474742961061029588604121)
              ·
                refine ⟨3356057220795772191453091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4474742961061029588604121 3356057220795772191453091)
                ·
                  refine ⟨5034085831193658287179637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3356057220795772191453091 5034085831193658287179637)
                  ·
                    refine ⟨471945546674405464423091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5034085831193658287179637 471945546674405464423091)
                    ·
                      rfl

theorem cell22_1378666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_1378666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1378666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1378666 prefixEnd_1378666 := by exact prefixLift 1378666
  have htrace : WordTrace (prefixWord ++ tailWord_1378666) baseStart_1378666 baseEnd_1378666 := by
    simpa [prefixWord, tailWord_1378666, baseEnd_1378666] using wordTrace_append hprefix tailTrace_1378666
  have hstable : (prefixWord ++ tailWord_1378666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378666).length < 2 ^ (prefixWord ++ tailWord_1378666).sum := by decide
  have hdescent : baseEnd_1378666 < baseStart_1378666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378741 : List Nat := [1, 3, 3, 2, 3, 1, 1, 1, 7]
def baseStart_1378741 : Nat := 118140960795 + 1378741 * 2 ^ 59
def prefixEnd_1378741 : Nat := 4983230072969 + 3 ^ 40 * 1378741 * 2
def baseEnd_1378741 : Nat := 157323740235710089599287

theorem tailTrace_1378741 : CollatzResearch.WordTrace tailWord_1378741 prefixEnd_1378741 157323740235710089599287 := by
  unfold tailWord_1378741
  simp only [CollatzResearch.WordTrace]
  refine ⟨50286815498064302061168077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33524543665376201374112051 50286815498064302061168077)
  ·
    refine ⟨18857555811774113272938029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50286815498064302061168077 18857555811774113272938029)
    ·
      refine ⟨7071583429415292477351761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18857555811774113272938029 7071583429415292477351761)
      ·
        refine ⟨5303687572061469358013821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7071583429415292477351761 5303687572061469358013821)
        ·
          refine ⟨1988882839523051009255183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5303687572061469358013821 1988882839523051009255183)
          ·
            refine ⟨2983324259284576513882775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1988882839523051009255183 2983324259284576513882775)
            ·
              refine ⟨4474986388926864770824163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2983324259284576513882775 4474986388926864770824163)
              ·
                refine ⟨6712479583390297156236245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4474986388926864770824163 6712479583390297156236245)
                ·
                  refine ⟨157323740235710089599287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6712479583390297156236245 157323740235710089599287)
                  ·
                    rfl

theorem cell22_1378741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 7].length) (baseStart_1378741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1378741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1378741 prefixEnd_1378741 := by exact prefixLift 1378741
  have htrace : WordTrace (prefixWord ++ tailWord_1378741) baseStart_1378741 baseEnd_1378741 := by
    simpa [prefixWord, tailWord_1378741, baseEnd_1378741] using wordTrace_append hprefix tailTrace_1378741
  have hstable : (prefixWord ++ tailWord_1378741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378741).length < 2 ^ (prefixWord ++ tailWord_1378741).sum := by decide
  have hdescent : baseEnd_1378741 < baseStart_1378741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378784 : List Nat := [2, 1, 1, 3, 1, 1, 4, 1, 3, 5]
def baseStart_1378784 : Nat := 118140960795 + 1378784 * 2 ^ 59
def prefixEnd_1378784 : Nat := 4983230072969 + 3 ^ 40 * 1378784 * 2
def baseEnd_1378784 : Nat := 471985940485892489972729

theorem tailTrace_1378784 : CollatzResearch.WordTrace tailWord_1378784 prefixEnd_1378784 471985940485892489972729 := by
  unfold tailWord_1378784
  simp only [CollatzResearch.WordTrace]
  refine ⟨25144191918454260202491703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33525589224605680269988937 25144191918454260202491703)
  ·
    refine ⟨37716287877681390303737555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25144191918454260202491703 37716287877681390303737555)
    ·
      refine ⟨56574431816522085455606333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37716287877681390303737555 56574431816522085455606333)
      ·
        refine ⟨21215411931195782045852375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56574431816522085455606333 21215411931195782045852375)
        ·
          refine ⟨31823117896793673068778563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21215411931195782045852375 31823117896793673068778563)
          ·
            refine ⟨47734676845190509603167845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31823117896793673068778563 47734676845190509603167845)
            ·
              refine ⟨8950251908473220550593971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47734676845190509603167845 8950251908473220550593971)
              ·
                refine ⟨13425377862709830825890957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8950251908473220550593971 13425377862709830825890957)
                ·
                  refine ⟨5034516698516186559709109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13425377862709830825890957 5034516698516186559709109)
                  ·
                    refine ⟨471985940485892489972729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5034516698516186559709109 471985940485892489972729)
                    ·
                      rfl

theorem cell22_1378784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 3, 5].length) (baseStart_1378784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1378784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1378784 prefixEnd_1378784 := by exact prefixLift 1378784
  have htrace : WordTrace (prefixWord ++ tailWord_1378784) baseStart_1378784 baseEnd_1378784 := by
    simpa [prefixWord, tailWord_1378784, baseEnd_1378784] using wordTrace_append hprefix tailTrace_1378784
  have hstable : (prefixWord ++ tailWord_1378784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378784).length < 2 ^ (prefixWord ++ tailWord_1378784).sum := by decide
  have hdescent : baseEnd_1378784 < baseStart_1378784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378801 : List Nat := [1, 2, 2, 2, 3, 1, 1, 3, 4, 3]
def baseStart_1378801 : Nat := 118140960795 + 1378801 * 2 ^ 59
def prefixEnd_1378801 : Nat := 4983230072969 + 3 ^ 40 * 1378801 * 2
def baseEnd_1378801 : Nat := 471991759933310112297677

theorem tailTrace_1378801 : CollatzResearch.WordTrace tailWord_1378801 prefixEnd_1378801 471991759933310112297677 := by
  unfold tailWord_1378801
  simp only [CollatzResearch.WordTrace]
  refine ⟨50289003877846932308352257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33526002585231288205568171 50289003877846932308352257)
  ·
    refine ⟨37716752908385199231264193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50289003877846932308352257 37716752908385199231264193)
    ·
      refine ⟨28287564681288899423448145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37716752908385199231264193 28287564681288899423448145)
      ·
        refine ⟨21215673510966674567586109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28287564681288899423448145 21215673510966674567586109)
        ·
          refine ⟨7955877566612502962844791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21215673510966674567586109 7955877566612502962844791)
          ·
            refine ⟨11933816349918754444267187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7955877566612502962844791 11933816349918754444267187)
            ·
              refine ⟨17900724524878131666400781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11933816349918754444267187 17900724524878131666400781)
              ·
                refine ⟨6712771696829299374900293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17900724524878131666400781 6712771696829299374900293)
                ·
                  refine ⟨1258644693155493632793805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6712771696829299374900293 1258644693155493632793805)
                  ·
                    refine ⟨471991759933310112297677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1258644693155493632793805 471991759933310112297677)
                    ·
                      rfl

theorem cell22_1378801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 4, 3].length) (baseStart_1378801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1378801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1378801 prefixEnd_1378801 := by exact prefixLift 1378801
  have htrace : WordTrace (prefixWord ++ tailWord_1378801) baseStart_1378801 baseEnd_1378801 := by
    simpa [prefixWord, tailWord_1378801, baseEnd_1378801] using wordTrace_append hprefix tailTrace_1378801
  have hstable : (prefixWord ++ tailWord_1378801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378801).length < 2 ^ (prefixWord ++ tailWord_1378801).sum := by decide
  have hdescent : baseEnd_1378801 < baseStart_1378801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378803 : List Nat := [1, 1, 1, 2, 2, 2, 7, 2, 4]
def baseStart_1378803 : Nat := 118140960795 + 1378803 * 2 ^ 59
def prefixEnd_1378803 : Nat := 4983230072969 + 3 ^ 40 * 1378803 * 2
def baseEnd_1378803 : Nat := 157330814858060924582557

theorem tailTrace_1378803 : CollatzResearch.WordTrace tailWord_1378803 prefixEnd_1378803 157330814858060924582557 := by
  unfold tailWord_1378803
  simp only [CollatzResearch.WordTrace]
  refine ⟨50289076823839686649925063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33526051215893124433283375 50289076823839686649925063)
  ·
    refine ⟨75433615235759529974887595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50289076823839686649925063 75433615235759529974887595)
    ·
      refine ⟨113150422853639294962331393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75433615235759529974887595 113150422853639294962331393)
      ·
        refine ⟨84862817140229471221748545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113150422853639294962331393 84862817140229471221748545)
        ·
          refine ⟨63647112855172103416311409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84862817140229471221748545 63647112855172103416311409)
          ·
            refine ⟨47735334641379077562233557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63647112855172103416311409 47735334641379077562233557)
            ·
              refine ⟨1118796905657322130364849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 47735334641379077562233557 1118796905657322130364849)
              ·
                refine ⟨839097679242991597773637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1118796905657322130364849 839097679242991597773637)
                ·
                  refine ⟨157330814858060924582557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 839097679242991597773637 157330814858060924582557)
                  ·
                    rfl

theorem cell22_1378803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 7, 2, 4].length) (baseStart_1378803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1378803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1378803 prefixEnd_1378803 := by exact prefixLift 1378803
  have htrace : WordTrace (prefixWord ++ tailWord_1378803) baseStart_1378803 baseEnd_1378803 := by
    simpa [prefixWord, tailWord_1378803, baseEnd_1378803] using wordTrace_append hprefix tailTrace_1378803
  have hstable : (prefixWord ++ tailWord_1378803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378803).length < 2 ^ (prefixWord ++ tailWord_1378803).sum := by decide
  have hdescent : baseEnd_1378803 < baseStart_1378803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378822 : List Nat := [6, 2, 1, 1, 1, 2, 1, 1, 3, 4]
def baseStart_1378822 : Nat := 118140960795 + 1378822 * 2 ^ 59
def prefixEnd_1378822 : Nat := 4983230072969 + 3 ^ 40 * 1378822 * 2
def baseEnd_1378822 : Nat := 471998948662473057522613

theorem tailTrace_1378822 : CollatzResearch.WordTrace tailWord_1378822 prefixEnd_1378822 471998948662473057522613 := by
  unfold tailWord_1378822
  simp only [CollatzResearch.WordTrace]
  refine ⟨1571555306586589152964585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 33526513207180568596577813 1571555306586589152964585)
  ·
    refine ⟨1178666479939941864723439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1571555306586589152964585 1178666479939941864723439)
    ·
      refine ⟨1767999719909912797085159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1178666479939941864723439 1767999719909912797085159)
      ·
        refine ⟨2651999579864869195627739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1767999719909912797085159 2651999579864869195627739)
        ·
          refine ⟨3977999369797303793441609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2651999579864869195627739 3977999369797303793441609)
          ·
            refine ⟨2983499527347977845081207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3977999369797303793441609 2983499527347977845081207)
            ·
              refine ⟨4475249291021966767621811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2983499527347977845081207 4475249291021966767621811)
              ·
                refine ⟨6712873936532950151432717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4475249291021966767621811 6712873936532950151432717)
                ·
                  refine ⟨2517327726199856306787269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6712873936532950151432717 2517327726199856306787269)
                  ·
                    refine ⟨471998948662473057522613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2517327726199856306787269 471998948662473057522613)
                    ·
                      rfl

theorem cell22_1378822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_1378822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1378822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1378822 prefixEnd_1378822 := by exact prefixLift 1378822
  have htrace : WordTrace (prefixWord ++ tailWord_1378822) baseStart_1378822 baseEnd_1378822 := by
    simpa [prefixWord, tailWord_1378822, baseEnd_1378822] using wordTrace_append hprefix tailTrace_1378822
  have hstable : (prefixWord ++ tailWord_1378822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378822).length < 2 ^ (prefixWord ++ tailWord_1378822).sum := by decide
  have hdescent : baseEnd_1378822 < baseStart_1378822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378852 : List Nat := [2, 3, 1, 5, 1, 1, 2, 2, 2, 3]
def baseStart_1378852 : Nat := 118140960795 + 1378852 * 2 ^ 59
def prefixEnd_1378852 : Nat := 4983230072969 + 3 ^ 40 * 1378852 * 2
def baseEnd_1378852 : Nat := 472009218275562979272521

theorem tailTrace_1378852 : CollatzResearch.WordTrace tailWord_1378852 prefixEnd_1378852 472009218275562979272521 := by
  unfold tailWord_1378852
  simp only [CollatzResearch.WordTrace]
  refine ⟨25145432000331084009229405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33527242667108112012305873 25145432000331084009229405)
  ·
    refine ⟨9429537000124156503461027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25145432000331084009229405 9429537000124156503461027)
    ·
      refine ⟨14144305500186234755191541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9429537000124156503461027 14144305500186234755191541)
      ·
        refine ⟨1326028640642459508299207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14144305500186234755191541 1326028640642459508299207)
        ·
          refine ⟨1989042960963689262448811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1326028640642459508299207 1989042960963689262448811)
          ·
            refine ⟨2983564441445533893673217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1989042960963689262448811 2983564441445533893673217)
            ·
              refine ⟨2237673331084150420254913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2983564441445533893673217 2237673331084150420254913)
              ·
                refine ⟨1678254998313112815191185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2237673331084150420254913 1678254998313112815191185)
                ·
                  refine ⟨1258691248734834611393389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1678254998313112815191185 1258691248734834611393389)
                  ·
                    refine ⟨472009218275562979272521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1258691248734834611393389 472009218275562979272521)
                    ·
                      rfl

theorem cell22_1378852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 2, 2, 3].length) (baseStart_1378852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1378852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1378852 prefixEnd_1378852 := by exact prefixLift 1378852
  have htrace : WordTrace (prefixWord ++ tailWord_1378852) baseStart_1378852 baseEnd_1378852 := by
    simpa [prefixWord, tailWord_1378852, baseEnd_1378852] using wordTrace_append hprefix tailTrace_1378852
  have hstable : (prefixWord ++ tailWord_1378852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378852).length < 2 ^ (prefixWord ++ tailWord_1378852).sum := by decide
  have hdescent : baseEnd_1378852 < baseStart_1378852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378859 : List Nat := [1, 1, 1, 1, 2, 1, 3, 5, 7]
def baseStart_1378859 : Nat := 118140960795 + 1378859 * 2 ^ 59
def prefixEnd_1378859 : Nat := 4983230072969 + 3 ^ 40 * 1378859 * 2
def baseEnd_1378859 : Nat := 157337204839539098115833

theorem tailTrace_1378859 : CollatzResearch.WordTrace tailWord_1378859 prefixEnd_1378859 157337204839539098115833 := by
  unfold tailWord_1378859
  simp only [CollatzResearch.WordTrace]
  refine ⟨50291119311636808213963631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33527412874424538809309087 50291119311636808213963631)
  ·
    refine ⟨75436678967455212320945447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50291119311636808213963631 75436678967455212320945447)
    ·
      refine ⟨113155018451182818481418171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75436678967455212320945447 113155018451182818481418171)
      ·
        refine ⟨169732527676774227722127257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113155018451182818481418171 169732527676774227722127257)
        ·
          refine ⟨127299395757580670791595443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169732527676774227722127257 127299395757580670791595443)
          ·
            refine ⟨190949093636371006187393165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127299395757580670791595443 190949093636371006187393165)
            ·
              refine ⟨71605910113639127320272437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 190949093636371006187393165 71605910113639127320272437)
              ·
                refine ⟨6713054073153668186275541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71605910113639127320272437 6713054073153668186275541)
                ·
                  refine ⟨157337204839539098115833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6713054073153668186275541 157337204839539098115833)
                  ·
                    rfl

theorem cell22_1378859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 7].length) (baseStart_1378859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1378859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1378859 prefixEnd_1378859 := by exact prefixLift 1378859
  have htrace : WordTrace (prefixWord ++ tailWord_1378859) baseStart_1378859 baseEnd_1378859 := by
    simpa [prefixWord, tailWord_1378859, baseEnd_1378859] using wordTrace_append hprefix tailTrace_1378859
  have hstable : (prefixWord ++ tailWord_1378859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378859).length < 2 ^ (prefixWord ++ tailWord_1378859).sum := by decide
  have hdescent : baseEnd_1378859 < baseStart_1378859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378884 : List Nat := [2, 3, 5, 1, 1, 2, 1, 1, 2, 4]
def baseStart_1378884 : Nat := 118140960795 + 1378884 * 2 ^ 59
def prefixEnd_1378884 : Nat := 4983230072969 + 3 ^ 40 * 1378884 * 2
def baseEnd_1378884 : Nat := 472020172529525562472423

theorem tailTrace_1378884 : CollatzResearch.WordTrace tailWord_1378884 prefixEnd_1378884 472020172529525562472423 := by
  unfold tailWord_1378884
  simp only [CollatzResearch.WordTrace]
  refine ⟨25146015568273118741811853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33528020757697491655749137 25146015568273118741811853)
  ·
    refine ⟨9429755838102419528179445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25146015568273118741811853 9429755838102419528179445)
    ·
      refine ⟨884039609822101830766823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9429755838102419528179445 884039609822101830766823)
      ·
        refine ⟨1326059414733152746150235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 884039609822101830766823 1326059414733152746150235)
        ·
          refine ⟨1989089122099729119225353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1326059414733152746150235 1989089122099729119225353)
          ·
            refine ⟨1491816841574796839419015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1989089122099729119225353 1491816841574796839419015)
            ·
              refine ⟨2237725262362195259128523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1491816841574796839419015 2237725262362195259128523)
              ·
                refine ⟨3356587893543292888692785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2237725262362195259128523 3356587893543292888692785)
                ·
                  refine ⟨2517440920157469666519589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3356587893543292888692785 2517440920157469666519589)
                  ·
                    refine ⟨472020172529525562472423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2517440920157469666519589 472020172529525562472423)
                    ·
                      rfl

theorem cell22_1378884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_1378884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1378884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1378884 prefixEnd_1378884 := by exact prefixLift 1378884
  have htrace : WordTrace (prefixWord ++ tailWord_1378884) baseStart_1378884 baseEnd_1378884 := by
    simpa [prefixWord, tailWord_1378884, baseEnd_1378884] using wordTrace_append hprefix tailTrace_1378884
  have hstable : (prefixWord ++ tailWord_1378884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378884).length < 2 ^ (prefixWord ++ tailWord_1378884).sum := by decide
  have hdescent : baseEnd_1378884 < baseStart_1378884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378951 : List Nat := [1, 1, 4, 2, 1, 2, 1, 3, 1, 6]
def baseStart_1378951 : Nat := 118140960795 + 1378951 * 2 ^ 59
def prefixEnd_1378951 : Nat := 4983230072969 + 3 ^ 40 * 1378951 * 2
def baseEnd_1378951 : Nat := 472043107998759721047217

theorem tailTrace_1378951 : CollatzResearch.WordTrace tailWord_1378951 prefixEnd_1378951 472043107998759721047217 := by
  unfold tailWord_1378951
  simp only [CollatzResearch.WordTrace]
  refine ⟨50294474827303507926312707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33529649884869005284208471 50294474827303507926312707)
  ·
    refine ⟨75441712240955261889469061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50294474827303507926312707 75441712240955261889469061)
    ·
      refine ⟨14145321045179111604275449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75441712240955261889469061 14145321045179111604275449)
      ·
        refine ⟨10608990783884333703206587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14145321045179111604275449 10608990783884333703206587)
        ·
          refine ⟨15913486175826500554809881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10608990783884333703206587 15913486175826500554809881)
          ·
            refine ⟨11935114631869875416107411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15913486175826500554809881 11935114631869875416107411)
            ·
              refine ⟨17902671947804813124161117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11935114631869875416107411 17902671947804813124161117)
              ·
                refine ⟨6713501980426804921560419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17902671947804813124161117 6713501980426804921560419)
                ·
                  refine ⟨10070252970640207382340629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6713501980426804921560419 10070252970640207382340629)
                  ·
                    refine ⟨472043107998759721047217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10070252970640207382340629 472043107998759721047217)
                    ·
                      rfl

theorem cell22_1378951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_1378951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1378951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1378951 prefixEnd_1378951 := by exact prefixLift 1378951
  have htrace : WordTrace (prefixWord ++ tailWord_1378951) baseStart_1378951 baseEnd_1378951 := by
    simpa [prefixWord, tailWord_1378951, baseEnd_1378951] using wordTrace_append hprefix tailTrace_1378951
  have hstable : (prefixWord ++ tailWord_1378951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378951).length < 2 ^ (prefixWord ++ tailWord_1378951).sum := by decide
  have hdescent : baseEnd_1378951 < baseStart_1378951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378968 : List Nat := [2, 1, 2, 4, 1, 1, 3, 2, 2, 4]
def baseStart_1378968 : Nat := 118140960795 + 1378968 * 2 ^ 59
def prefixEnd_1378968 : Nat := 4983230072969 + 3 ^ 40 * 1378968 * 2
def baseEnd_1378968 : Nat := 472048927446177343372165

theorem tailTrace_1378968 : CollatzResearch.WordTrace tailWord_1378968 prefixEnd_1378968 472048927446177343372165 := by
  unfold tailWord_1378968
  simp only [CollatzResearch.WordTrace]
  refine ⟨25147547434120959914840779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33530063245494613219787705 25147547434120959914840779)
  ·
    refine ⟨37721321151181439872261169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25147547434120959914840779 37721321151181439872261169)
    ·
      refine ⟨28290990863386079904195877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37721321151181439872261169 28290990863386079904195877)
      ·
        refine ⟨5304560786884889982036727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28290990863386079904195877 5304560786884889982036727)
        ·
          refine ⟨7956841180327334973055091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5304560786884889982036727 7956841180327334973055091)
          ·
            refine ⟨11935261770491002459582637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7956841180327334973055091 11935261770491002459582637)
            ·
              refine ⟨4475723163934125922343489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11935261770491002459582637 4475723163934125922343489)
              ·
                refine ⟨3356792372950594441757617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4475723163934125922343489 3356792372950594441757617)
                ·
                  refine ⟨2517594279712945831318213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3356792372950594441757617 2517594279712945831318213)
                  ·
                    refine ⟨472048927446177343372165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2517594279712945831318213 472048927446177343372165)
                    ·
                      rfl

theorem cell22_1378968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 2, 2, 4].length) (baseStart_1378968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1378968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1378968 prefixEnd_1378968 := by exact prefixLift 1378968
  have htrace : WordTrace (prefixWord ++ tailWord_1378968) baseStart_1378968 baseEnd_1378968 := by
    simpa [prefixWord, tailWord_1378968, baseEnd_1378968] using wordTrace_append hprefix tailTrace_1378968
  have hstable : (prefixWord ++ tailWord_1378968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378968).length < 2 ^ (prefixWord ++ tailWord_1378968).sum := by decide
  have hdescent : baseEnd_1378968 < baseStart_1378968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378972 : List Nat := [2, 2, 3, 2, 2, 2, 3, 2, 4]
def baseStart_1378972 : Nat := 118140960795 + 1378972 * 2 ^ 59
def prefixEnd_1378972 : Nat := 4983230072969 + 3 ^ 40 * 1378972 * 2
def baseEnd_1378972 : Nat := 157350098909307555424051

theorem tailTrace_1378972 : CollatzResearch.WordTrace tailWord_1378972 prefixEnd_1378972 157350098909307555424051 := by
  unfold tailWord_1378972
  simp only [CollatzResearch.WordTrace]
  refine ⟨25147620380113714256413585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33530160506818285675218113 25147620380113714256413585)
  ·
    refine ⟨18860715285085285692310189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25147620380113714256413585 18860715285085285692310189)
    ·
      refine ⟨7072768231906982134616321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18860715285085285692310189 7072768231906982134616321)
      ·
        refine ⟨5304576173930236600962241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7072768231906982134616321 5304576173930236600962241)
        ·
          refine ⟨3978432130447677450721681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5304576173930236600962241 3978432130447677450721681)
          ·
            refine ⟨2983824097835758088041261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3978432130447677450721681 2983824097835758088041261)
            ·
              refine ⟨1118934036688409283015473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2983824097835758088041261 1118934036688409283015473)
              ·
                refine ⟨839200527516306962261605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1118934036688409283015473 839200527516306962261605)
                ·
                  refine ⟨157350098909307555424051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 839200527516306962261605 157350098909307555424051)
                  ·
                    rfl

theorem cell22_1378972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 3, 2, 4].length) (baseStart_1378972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1378972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1378972 prefixEnd_1378972 := by exact prefixLift 1378972
  have htrace : WordTrace (prefixWord ++ tailWord_1378972) baseStart_1378972 baseEnd_1378972 := by
    simpa [prefixWord, tailWord_1378972, baseEnd_1378972] using wordTrace_append hprefix tailTrace_1378972
  have hstable : (prefixWord ++ tailWord_1378972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378972).length < 2 ^ (prefixWord ++ tailWord_1378972).sum := by decide
  have hdescent : baseEnd_1378972 < baseStart_1378972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379032 : List Nat := [2, 1, 2, 2, 3, 3, 1, 4, 1, 3]
def baseStart_1379032 : Nat := 118140960795 + 1379032 * 2 ^ 59
def prefixEnd_1379032 : Nat := 4983230072969 + 3 ^ 40 * 1379032 * 2
def baseEnd_1379032 : Nat := 472070835954102509771969

theorem tailTrace_1379032 : CollatzResearch.WordTrace tailWord_1379032 prefixEnd_1379032 472070835954102509771969 := by
  unfold tailWord_1379032
  simp only [CollatzResearch.WordTrace]
  refine ⟨25148714570005029380005675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33531619426673372506674233 25148714570005029380005675)
  ·
    refine ⟨37723071855007544070008513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25148714570005029380005675 37723071855007544070008513)
    ·
      refine ⟨28292303891255658052506385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37723071855007544070008513 28292303891255658052506385)
      ·
        refine ⟨21219227918441743539379789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28292303891255658052506385 21219227918441743539379789)
        ·
          refine ⟨7957210469415653827267421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21219227918441743539379789 7957210469415653827267421)
          ·
            refine ⟨2983953926030870185225283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7957210469415653827267421 2983953926030870185225283)
            ·
              refine ⟨4475930889046305277837925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2983953926030870185225283 4475930889046305277837925)
              ·
                refine ⟨839237041696182239594611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4475930889046305277837925 839237041696182239594611)
                ·
                  refine ⟨1258855562544273359391917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 839237041696182239594611 1258855562544273359391917)
                  ·
                    refine ⟨472070835954102509771969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1258855562544273359391917 472070835954102509771969)
                    ·
                      rfl

theorem cell22_1379032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 4, 1, 3].length) (baseStart_1379032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1379032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1379032 prefixEnd_1379032 := by exact prefixLift 1379032
  have htrace : WordTrace (prefixWord ++ tailWord_1379032) baseStart_1379032 baseEnd_1379032 := by
    simpa [prefixWord, tailWord_1379032, baseEnd_1379032] using wordTrace_append hprefix tailTrace_1379032
  have hstable : (prefixWord ++ tailWord_1379032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379032).length < 2 ^ (prefixWord ++ tailWord_1379032).sum := by decide
  have hdescent : baseEnd_1379032 < baseStart_1379032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379043 : List Nat := [1, 1, 1, 7, 1, 1, 1, 1, 1, 7]
def baseStart_1379043 : Nat := 118140960795 + 1379043 * 2 ^ 59
def prefixEnd_1379043 : Nat := 4983230072969 + 3 ^ 40 * 1379043 * 2
def baseEnd_1379043 : Nat := 472074601478902147746935

theorem tailTrace_1379043 : CollatzResearch.WordTrace tailWord_1379043 prefixEnd_1379043 472074601478902147746935 := by
  unfold tailWord_1379043
  simp only [CollatzResearch.WordTrace]
  refine ⟨50297830342970207638661783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33531886895313471759107855 50297830342970207638661783)
  ·
    refine ⟨75446745514455311457992675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50297830342970207638661783 75446745514455311457992675)
    ·
      refine ⟨113170118271682967186989013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75446745514455311457992675 113170118271682967186989013)
      ·
        refine ⟨2652424646992569543445055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 113170118271682967186989013 2652424646992569543445055)
        ·
          refine ⟨3978636970488854315167583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2652424646992569543445055 3978636970488854315167583)
          ·
            refine ⟨5967955455733281472751375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3978636970488854315167583 5967955455733281472751375)
            ·
              refine ⟨8951933183599922209127063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5967955455733281472751375 8951933183599922209127063)
              ·
                refine ⟨13427899775399883313690595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8951933183599922209127063 13427899775399883313690595)
                ·
                  refine ⟨20141849663099824970535893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13427899775399883313690595 20141849663099824970535893)
                  ·
                    refine ⟨472074601478902147746935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20141849663099824970535893 472074601478902147746935)
                    ·
                      rfl

theorem cell22_1379043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 7].length) (baseStart_1379043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1379043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1379043 prefixEnd_1379043 := by exact prefixLift 1379043
  have htrace : WordTrace (prefixWord ++ tailWord_1379043) baseStart_1379043 baseEnd_1379043 := by
    simpa [prefixWord, tailWord_1379043, baseEnd_1379043] using wordTrace_append hprefix tailTrace_1379043
  have hstable : (prefixWord ++ tailWord_1379043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379043).length < 2 ^ (prefixWord ++ tailWord_1379043).sum := by decide
  have hdescent : baseEnd_1379043 < baseStart_1379043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379103 : List Nat := [1, 1, 2, 4, 2, 2, 1, 2, 1, 6]
def baseStart_1379103 : Nat := 118140960795 + 1379103 * 2 ^ 59
def prefixEnd_1379103 : Nat := 4983230072969 + 3 ^ 40 * 1379103 * 2
def baseEnd_1379103 : Nat := 472095140705081991246751

theorem tailTrace_1379103 : CollatzResearch.WordTrace tailWord_1379103 prefixEnd_1379103 472095140705081991246751 := by
  unfold tailWord_1379103
  simp only [CollatzResearch.WordTrace]
  refine ⟨50300018722752837885845963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33533345815168558590563975 50300018722752837885845963)
  ·
    refine ⟨75450028084129256828768945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50300018722752837885845963 75450028084129256828768945)
    ·
      refine ⟨56587521063096942621576709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75450028084129256828768945 56587521063096942621576709)
      ·
        refine ⟨10610160199330676741545633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56587521063096942621576709 10610160199330676741545633)
        ·
          refine ⟨7957620149498007556159225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10610160199330676741545633 7957620149498007556159225)
          ·
            refine ⟨5968215112123505667119419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7957620149498007556159225 5968215112123505667119419)
            ·
              refine ⟨8952322668185258500679129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5968215112123505667119419 8952322668185258500679129)
              ·
                refine ⟨6714242001138943875509347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8952322668185258500679129 6714242001138943875509347)
                ·
                  refine ⟨10071363001708415813264021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6714242001138943875509347 10071363001708415813264021)
                  ·
                    refine ⟨472095140705081991246751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10071363001708415813264021 472095140705081991246751)
                    ·
                      rfl

theorem cell22_1379103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 6].length) (baseStart_1379103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1379103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1379103 prefixEnd_1379103 := by exact prefixLift 1379103
  have htrace : WordTrace (prefixWord ++ tailWord_1379103) baseStart_1379103 baseEnd_1379103 := by
    simpa [prefixWord, tailWord_1379103, baseEnd_1379103] using wordTrace_append hprefix tailTrace_1379103
  have hstable : (prefixWord ++ tailWord_1379103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379103).length < 2 ^ (prefixWord ++ tailWord_1379103).sum := by decide
  have hdescent : baseEnd_1379103 < baseStart_1379103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379156 : List Nat := [2, 4, 1, 1, 4, 2, 2, 1, 2, 3]
def baseStart_1379156 : Nat := 118140960795 + 1379156 * 2 ^ 59
def prefixEnd_1379156 : Nat := 4983230072969 + 3 ^ 40 * 1379156 * 2
def baseEnd_1379156 : Nat := 472113283688207519671589

theorem tailTrace_1379156 : CollatzResearch.WordTrace tailWord_1379156 prefixEnd_1379156 472113283688207519671589 := by
  unfold tailWord_1379156
  simp only [CollatzResearch.WordTrace]
  refine ⟨25150975895780413968762661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33534634527707218625016881 25150975895780413968762661)
  ·
    refine ⟨4715807980458827619142999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25150975895780413968762661 4715807980458827619142999)
    ·
      refine ⟨7073711970688241428714499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4715807980458827619142999 7073711970688241428714499)
      ·
        refine ⟨10610567956032362143071749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7073711970688241428714499 10610567956032362143071749)
        ·
          refine ⟨1989481491756067901825953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10610567956032362143071749 1989481491756067901825953)
          ·
            refine ⟨1492111118817050926369465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1989481491756067901825953 1492111118817050926369465)
            ·
              refine ⟨1119083339112788194777099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1492111118817050926369465 1119083339112788194777099)
              ·
                refine ⟨1678625008669182292165649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1119083339112788194777099 1678625008669182292165649)
                ·
                  refine ⟨1258968756501886719124237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1678625008669182292165649 1258968756501886719124237)
                  ·
                    refine ⟨472113283688207519671589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1258968756501886719124237 472113283688207519671589)
                    ·
                      rfl

theorem cell22_1379156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 2, 1, 2, 3].length) (baseStart_1379156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1379156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1379156 prefixEnd_1379156 := by exact prefixLift 1379156
  have htrace : WordTrace (prefixWord ++ tailWord_1379156) baseStart_1379156 baseEnd_1379156 := by
    simpa [prefixWord, tailWord_1379156, baseEnd_1379156] using wordTrace_append hprefix tailTrace_1379156
  have hstable : (prefixWord ++ tailWord_1379156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379156).length < 2 ^ (prefixWord ++ tailWord_1379156).sum := by decide
  have hdescent : baseEnd_1379156 < baseStart_1379156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379255 : List Nat := [1, 1, 3, 1, 3, 1, 2, 4, 2, 4]
def baseStart_1379255 : Nat := 118140960795 + 1379255 * 2 ^ 59
def prefixEnd_1379255 : Nat := 4983230072969 + 3 ^ 40 * 1379255 * 2
def baseEnd_1379255 : Nat := 472147173411404261446285

theorem tailTrace_1379255 : CollatzResearch.WordTrace tailWord_1379255 prefixEnd_1379255 472147173411404261446285 := by
  unfold tailWord_1379255
  simp only [CollatzResearch.WordTrace]
  refine ⟨50305562618202167845379219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33537041745468111896919479 50305562618202167845379219)
  ·
    refine ⟨75458343927303251768068829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50305562618202167845379219 75458343927303251768068829)
    ·
      refine ⟨28296878972738719413025811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75458343927303251768068829 28296878972738719413025811)
      ·
        refine ⟨42445318459108079119538717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28296878972738719413025811 42445318459108079119538717)
        ·
          refine ⟨15916994422165529669827019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42445318459108079119538717 15916994422165529669827019)
          ·
            refine ⟨23875491633248294504740529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15916994422165529669827019 23875491633248294504740529)
            ·
              refine ⟨17906618724936220878555397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23875491633248294504740529 17906618724936220878555397)
              ·
                refine ⟨3357491010925541414729137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17906618724936220878555397 3357491010925541414729137)
                ·
                  refine ⟨2518118258194156061046853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3357491010925541414729137 2518118258194156061046853)
                  ·
                    refine ⟨472147173411404261446285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2518118258194156061046853 472147173411404261446285)
                    ·
                      rfl

theorem cell22_1379255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 4, 2, 4].length) (baseStart_1379255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1379255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1379255 prefixEnd_1379255 := by exact prefixLift 1379255
  have htrace : WordTrace (prefixWord ++ tailWord_1379255) baseStart_1379255 baseEnd_1379255 := by
    simpa [prefixWord, tailWord_1379255, baseEnd_1379255] using wordTrace_append hprefix tailTrace_1379255
  have hstable : (prefixWord ++ tailWord_1379255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379255).length < 2 ^ (prefixWord ++ tailWord_1379255).sum := by decide
  have hdescent : baseEnd_1379255 < baseStart_1379255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379257 : List Nat := [1, 2, 1, 4, 2, 3, 1, 1, 4, 3]
def baseStart_1379257 : Nat := 118140960795 + 1379257 * 2 ^ 59
def prefixEnd_1379257 : Nat := 4983230072969 + 3 ^ 40 * 1379257 * 2
def baseEnd_1379257 : Nat := 472147858052276922896279

theorem tailTrace_1379257 : CollatzResearch.WordTrace tailWord_1379257 prefixEnd_1379257 472147858052276922896279 := by
  unfold tailWord_1379257
  simp only [CollatzResearch.WordTrace]
  refine ⟨50305635564194922186952025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33537090376129948124634683 50305635564194922186952025)
  ·
    refine ⟨37729226673146191640214019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50305635564194922186952025 37729226673146191640214019)
    ·
      refine ⟨56593840009719287460321029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37729226673146191640214019 56593840009719287460321029)
      ·
        refine ⟨10611345001822366398810193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56593840009719287460321029 10611345001822366398810193)
        ·
          refine ⟨7958508751366774799107645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10611345001822366398810193 7958508751366774799107645)
          ·
            refine ⟨2984440781762540549665367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7958508751366774799107645 2984440781762540549665367)
            ·
              refine ⟨4476661172643810824498051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2984440781762540549665367 4476661172643810824498051)
              ·
                refine ⟨6714991758965716236747077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4476661172643810824498051 6714991758965716236747077)
                ·
                  refine ⟨1259060954806071794390077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6714991758965716236747077 1259060954806071794390077)
                  ·
                    refine ⟨472147858052276922896279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1259060954806071794390077 472147858052276922896279)
                    ·
                      rfl

theorem cell22_1379257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 4, 3].length) (baseStart_1379257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1379257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1379257 prefixEnd_1379257 := by exact prefixLift 1379257
  have htrace : WordTrace (prefixWord ++ tailWord_1379257) baseStart_1379257 baseEnd_1379257 := by
    simpa [prefixWord, tailWord_1379257, baseEnd_1379257] using wordTrace_append hprefix tailTrace_1379257
  have hstable : (prefixWord ++ tailWord_1379257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379257).length < 2 ^ (prefixWord ++ tailWord_1379257).sum := by decide
  have hdescent : baseEnd_1379257 < baseStart_1379257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379370 : List Nat := [3, 1, 4, 1, 3, 2, 2, 2, 1, 3]
def baseStart_1379370 : Nat := 118140960795 + 1379370 * 2 ^ 59
def prefixEnd_1379370 : Nat := 4983230072969 + 3 ^ 40 * 1379370 * 2
def baseEnd_1379370 : Nat := 472186540261582294820933

theorem tailTrace_1379370 : CollatzResearch.WordTrace tailWord_1379370 prefixEnd_1379370 472186540261582294820933 := by
  unfold tailWord_1379370
  simp only [CollatzResearch.WordTrace]
  refine ⟨12577439253196385621453891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33539838008523694990543709 12577439253196385621453891)
  ·
    refine ⟨18866158879794578432180837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12577439253196385621453891 18866158879794578432180837)
    ·
      refine ⟨3537404789961483456033907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18866158879794578432180837 3537404789961483456033907)
      ·
        refine ⟨5306107184942225184050861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3537404789961483456033907 5306107184942225184050861)
        ·
          refine ⟨1989790194353334444019073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5306107184942225184050861 1989790194353334444019073)
          ·
            refine ⟨1492342645765000833014305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1989790194353334444019073 1492342645765000833014305)
            ·
              refine ⟨1119256984323750624760729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1492342645765000833014305 1119256984323750624760729)
              ·
                refine ⟨839442738242812968570547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1119256984323750624760729 839442738242812968570547)
                ·
                  refine ⟨1259164107364219452855821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 839442738242812968570547 1259164107364219452855821)
                  ·
                    refine ⟨472186540261582294820933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1259164107364219452855821 472186540261582294820933)
                    ·
                      rfl

theorem cell22_1379370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_1379370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1379370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1379370 prefixEnd_1379370 := by exact prefixLift 1379370
  have htrace : WordTrace (prefixWord ++ tailWord_1379370) baseStart_1379370 baseEnd_1379370 := by
    simpa [prefixWord, tailWord_1379370, baseEnd_1379370] using wordTrace_append hprefix tailTrace_1379370
  have hstable : (prefixWord ++ tailWord_1379370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379370).length < 2 ^ (prefixWord ++ tailWord_1379370).sum := by decide
  have hdescent : baseEnd_1379370 < baseStart_1379370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379392 : List Nat := [2, 1, 1, 2, 2, 3, 4, 1, 1, 5]
def baseStart_1379392 : Nat := 118140960795 + 1379392 * 2 ^ 59
def prefixEnd_1379392 : Nat := 4983230072969 + 3 ^ 40 * 1379392 * 2
def baseEnd_1379392 : Nat := 472194071311181570770865

theorem tailTrace_1379392 : CollatzResearch.WordTrace tailWord_1379392 prefixEnd_1379392 472194071311181570770865 := by
  unfold tailWord_1379392
  simp only [CollatzResearch.WordTrace]
  refine ⟨25155279709352920121558215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33540372945803893495410953 25155279709352920121558215)
  ·
    refine ⟨37732919564029380182337323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25155279709352920121558215 37732919564029380182337323)
    ·
      refine ⟨56599379346044070273505985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37732919564029380182337323 56599379346044070273505985)
      ·
        refine ⟨42449534509533052705129489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56599379346044070273505985 42449534509533052705129489)
        ·
          refine ⟨31837150882149789528847117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42449534509533052705129489 31837150882149789528847117)
          ·
            refine ⟨11938931580806171073317669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31837150882149789528847117 11938931580806171073317669)
            ·
              refine ⟨2238549671401157076247063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11938931580806171073317669 2238549671401157076247063)
              ·
                refine ⟨3357824507101735614370595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2238549671401157076247063 3357824507101735614370595)
                ·
                  refine ⟨5036736760652603421555893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3357824507101735614370595 5036736760652603421555893)
                  ·
                    refine ⟨472194071311181570770865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5036736760652603421555893 472194071311181570770865)
                    ·
                      rfl

theorem cell22_1379392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 1, 1, 5].length) (baseStart_1379392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1379392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1379392 prefixEnd_1379392 := by exact prefixLift 1379392
  have htrace : WordTrace (prefixWord ++ tailWord_1379392) baseStart_1379392 baseEnd_1379392 := by
    simpa [prefixWord, tailWord_1379392, baseEnd_1379392] using wordTrace_append hprefix tailTrace_1379392
  have hstable : (prefixWord ++ tailWord_1379392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379392).length < 2 ^ (prefixWord ++ tailWord_1379392).sum := by decide
  have hdescent : baseEnd_1379392 < baseStart_1379392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379426 : List Nat := [3, 3, 2, 2, 1, 2, 1, 1, 4, 3]
def baseStart_1379426 : Nat := 118140960795 + 1379426 * 2 ^ 59
def prefixEnd_1379426 : Nat := 4983230072969 + 3 ^ 40 * 1379426 * 2
def baseEnd_1379426 : Nat := 472205710206016815420761

theorem tailTrace_1379426 : CollatzResearch.WordTrace tailWord_1379426 prefixEnd_1379426 472205710206016815420761 := by
  unfold tailWord_1379426
  simp only [CollatzResearch.WordTrace]
  refine ⟨12577949875145666012463533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33541199667055109366569421 12577949875145666012463533)
  ·
    refine ⟨4716731203179624754673825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12577949875145666012463533 4716731203179624754673825)
    ·
      refine ⟨3537548402384718566005369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4716731203179624754673825 3537548402384718566005369)
      ·
        refine ⟨2653161301788538924504027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3537548402384718566005369 2653161301788538924504027)
        ·
          refine ⟨3979741952682808386756041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2653161301788538924504027 3979741952682808386756041)
          ·
            refine ⟨2984806464512106290067031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3979741952682808386756041 2984806464512106290067031)
            ·
              refine ⟨4477209696768159435100547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2984806464512106290067031 4477209696768159435100547)
              ·
                refine ⟨6715814545152239152650821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4477209696768159435100547 6715814545152239152650821)
                ·
                  refine ⟨1259215227216044841122029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6715814545152239152650821 1259215227216044841122029)
                  ·
                    refine ⟨472205710206016815420761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1259215227216044841122029 472205710206016815420761)
                    ·
                      rfl

theorem cell22_1379426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_1379426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1379426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1379426 prefixEnd_1379426 := by exact prefixLift 1379426
  have htrace : WordTrace (prefixWord ++ tailWord_1379426) baseStart_1379426 baseEnd_1379426 := by
    simpa [prefixWord, tailWord_1379426, baseEnd_1379426] using wordTrace_append hprefix tailTrace_1379426
  have hstable : (prefixWord ++ tailWord_1379426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379426).length < 2 ^ (prefixWord ++ tailWord_1379426).sum := by decide
  have hdescent : baseEnd_1379426 < baseStart_1379426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379488 : List Nat := [2, 1, 1, 4, 2, 1, 5, 2, 1, 3]
def baseStart_1379488 : Nat := 118140960795 + 1379488 * 2 ^ 59
def prefixEnd_1379488 : Nat := 4983230072969 + 3 ^ 40 * 1379488 * 2
def baseEnd_1379488 : Nat := 472226934073069320370571

theorem tailTrace_1379488 : CollatzResearch.WordTrace tailWord_1379488 prefixEnd_1379488 472226934073069320370571 := by
  unfold tailWord_1379488
  simp only [CollatzResearch.WordTrace]
  refine ⟨25157030413179024319305559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33542707217572032425740745 25157030413179024319305559)
  ·
    refine ⟨37735545619768536478958339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25157030413179024319305559 37735545619768536478958339)
    ·
      refine ⟨56603318429652804718437509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37735545619768536478958339 56603318429652804718437509)
      ·
        refine ⟨10613122205559900884707033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56603318429652804718437509 10613122205559900884707033)
        ·
          refine ⟨7959841654169925663530275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10613122205559900884707033 7959841654169925663530275)
          ·
            refine ⟨11939762481254888495295413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7959841654169925663530275 11939762481254888495295413)
            ·
              refine ⟨1119352732617645796433945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11939762481254888495295413 1119352732617645796433945)
              ·
                refine ⟨839514549463234347325459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1119352732617645796433945 839514549463234347325459)
                ·
                  refine ⟨1259271824194851520988189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 839514549463234347325459 1259271824194851520988189)
                  ·
                    refine ⟨472226934073069320370571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1259271824194851520988189 472226934073069320370571)
                    ·
                      rfl

theorem cell22_1379488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 5, 2, 1, 3].length) (baseStart_1379488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1379488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1379488 prefixEnd_1379488 := by exact prefixLift 1379488
  have htrace : WordTrace (prefixWord ++ tailWord_1379488) baseStart_1379488 baseEnd_1379488 := by
    simpa [prefixWord, tailWord_1379488, baseEnd_1379488] using wordTrace_append hprefix tailTrace_1379488
  have hstable : (prefixWord ++ tailWord_1379488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379488).length < 2 ^ (prefixWord ++ tailWord_1379488).sum := by decide
  have hdescent : baseEnd_1379488 < baseStart_1379488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379501 : List Nat := [1, 5, 2, 1, 3, 1, 1, 3, 5]
def baseStart_1379501 : Nat := 118140960795 + 1379501 * 2 ^ 59
def prefixEnd_1379501 : Nat := 4983230072969 + 3 ^ 40 * 1379501 * 2
def baseEnd_1379501 : Nat := 157410461412913873265177

theorem tailTrace_1379501 : CollatzResearch.WordTrace tailWord_1379501 prefixEnd_1379501 157410461412913873265177 := by
  unfold tailWord_1379501
  simp only [CollatzResearch.WordTrace]
  refine ⟨50314534975310951858834357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33543023316873967905889571 50314534975310951858834357)
  ·
    refine ⟨4716987653935401736765721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50314534975310951858834357 4716987653935401736765721)
    ·
      refine ⟨3537740740451551302574291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4716987653935401736765721 3537740740451551302574291)
      ·
        refine ⟨5306611110677326953861437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3537740740451551302574291 5306611110677326953861437)
        ·
          refine ⟨1989979166503997607698039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5306611110677326953861437 1989979166503997607698039)
          ·
            refine ⟨2984968749755996411547059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1989979166503997607698039 2984968749755996411547059)
            ·
              refine ⟨4477453124633994617320589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2984968749755996411547059 4477453124633994617320589)
              ·
                refine ⟨1679044921737747981495221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4477453124633994617320589 1679044921737747981495221)
                ·
                  refine ⟨157410461412913873265177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1679044921737747981495221 157410461412913873265177)
                  ·
                    rfl

theorem cell22_1379501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_1379501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1379501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1379501 prefixEnd_1379501 := by exact prefixLift 1379501
  have htrace : WordTrace (prefixWord ++ tailWord_1379501) baseStart_1379501 baseEnd_1379501 := by
    simpa [prefixWord, tailWord_1379501, baseEnd_1379501] using wordTrace_append hprefix tailTrace_1379501
  have hstable : (prefixWord ++ tailWord_1379501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379501).length < 2 ^ (prefixWord ++ tailWord_1379501).sum := by decide
  have hdescent : baseEnd_1379501 < baseStart_1379501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379589 : List Nat := [1, 3, 1, 1, 2, 1, 3, 2, 5, 3]
def baseStart_1379589 : Nat := 118140960795 + 1379589 * 2 ^ 59
def prefixEnd_1379589 : Nat := 4983230072969 + 3 ^ 40 * 1379589 * 2
def baseEnd_1379589 : Nat := 472261508437138723595261

theorem tailTrace_1379589 : CollatzResearch.WordTrace tailWord_1379589 prefixEnd_1379589 472261508437138723595261 := by
  unfold tailWord_1379589
  simp only [CollatzResearch.WordTrace]
  refine ⟨50317744598992142888037821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33545163065994761925358547 50317744598992142888037821)
  ·
    refine ⟨18869154224622053583014183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50317744598992142888037821 18869154224622053583014183)
    ·
      refine ⟨28303731336933080374521275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18869154224622053583014183 28303731336933080374521275)
      ·
        refine ⟨42455597005399620561781913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28303731336933080374521275 42455597005399620561781913)
        ·
          refine ⟨31841697754049715421336435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42455597005399620561781913 31841697754049715421336435)
          ·
            refine ⟨47762546631074573132004653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31841697754049715421336435 47762546631074573132004653)
            ·
              refine ⟨17910954986652964924501745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47762546631074573132004653 17910954986652964924501745)
              ·
                refine ⟨13433216239989723693376309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17910954986652964924501745 13433216239989723693376309)
                ·
                  refine ⟨1259364022499036596254029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13433216239989723693376309 1259364022499036596254029)
                  ·
                    refine ⟨472261508437138723595261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1259364022499036596254029 472261508437138723595261)
                    ·
                      rfl

theorem cell22_1379589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 5, 3].length) (baseStart_1379589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1379589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1379589 prefixEnd_1379589 := by exact prefixLift 1379589
  have htrace : WordTrace (prefixWord ++ tailWord_1379589) baseStart_1379589 baseEnd_1379589 := by
    simpa [prefixWord, tailWord_1379589, baseEnd_1379589] using wordTrace_append hprefix tailTrace_1379589
  have hstable : (prefixWord ++ tailWord_1379589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379589).length < 2 ^ (prefixWord ++ tailWord_1379589).sum := by decide
  have hdescent : baseEnd_1379589 < baseStart_1379589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379679 : List Nat := [1, 1, 2, 3, 1, 2, 1, 5, 1, 5]
def baseStart_1379679 : Nat := 118140960795 + 1379679 * 2 ^ 59
def prefixEnd_1379679 : Nat := 4983230072969 + 3 ^ 40 * 1379679 * 2
def baseEnd_1379679 : Nat := 472292317276408488844985

theorem tailTrace_1379679 : CollatzResearch.WordTrace tailWord_1379679 prefixEnd_1379679 472292317276408488844985 := by
  unfold tailWord_1379679
  simp only [CollatzResearch.WordTrace]
  refine ⟨50321027168666088258814091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33547351445777392172542727 50321027168666088258814091)
  ·
    refine ⟨75481540752999132388221137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50321027168666088258814091 75481540752999132388221137)
    ·
      refine ⟨56611155564749349291165853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75481540752999132388221137 56611155564749349291165853)
      ·
        refine ⟨21229183336781005984187195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56611155564749349291165853 21229183336781005984187195)
        ·
          refine ⟨31843775005171508976280793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21229183336781005984187195 31843775005171508976280793)
          ·
            refine ⟨23882831253878631732210595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31843775005171508976280793 23882831253878631732210595)
            ·
              refine ⟨35824246880817947598315893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23882831253878631732210595 35824246880817947598315893)
              ·
                refine ⟨3358523145076682587342115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35824246880817947598315893 3358523145076682587342115)
                ·
                  refine ⟨5037784717615023881013173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3358523145076682587342115 5037784717615023881013173)
                  ·
                    refine ⟨472292317276408488844985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5037784717615023881013173 472292317276408488844985)
                    ·
                      rfl

theorem cell22_1379679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 5, 1, 5].length) (baseStart_1379679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1379679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1379679 prefixEnd_1379679 := by exact prefixLift 1379679
  have htrace : WordTrace (prefixWord ++ tailWord_1379679) baseStart_1379679 baseEnd_1379679 := by
    simpa [prefixWord, tailWord_1379679, baseEnd_1379679] using wordTrace_append hprefix tailTrace_1379679
  have hstable : (prefixWord ++ tailWord_1379679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379679).length < 2 ^ (prefixWord ++ tailWord_1379679).sum := by decide
  have hdescent : baseEnd_1379679 < baseStart_1379679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379683 : List Nat := [1, 1, 1, 5, 2, 4, 1, 2, 1, 4]
def baseStart_1379683 : Nat := 118140960795 + 1379683 * 2 ^ 59
def prefixEnd_1379683 : Nat := 4983230072969 + 3 ^ 40 * 1379683 * 2
def baseEnd_1379683 : Nat := 472293686558153811744973

theorem tailTrace_1379683 : CollatzResearch.WordTrace tailWord_1379683 prefixEnd_1379683 472293686558153811744973 := by
  unfold tailWord_1379683
  simp only [CollatzResearch.WordTrace]
  refine ⟨50321173060651596941959703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33547448707101064627973135 50321173060651596941959703)
  ·
    refine ⟨75481759590977395412939555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50321173060651596941959703 75481759590977395412939555)
    ·
      refine ⟨113222639386466093119409333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75481759590977395412939555 113222639386466093119409333)
      ·
        refine ⟨10614622442481196229944625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 113222639386466093119409333 10614622442481196229944625)
        ·
          refine ⟨7960966831860897172458469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10614622442481196229944625 7960966831860897172458469)
          ·
            refine ⟨1492681280973918219835963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7960966831860897172458469 1492681280973918219835963)
            ·
              refine ⟨2239021921460877329753945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1492681280973918219835963 2239021921460877329753945)
              ·
                refine ⟨1679266441095657997315459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2239021921460877329753945 1679266441095657997315459)
                ·
                  refine ⟨2518899661643486995973189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1679266441095657997315459 2518899661643486995973189)
                  ·
                    refine ⟨472293686558153811744973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2518899661643486995973189 472293686558153811744973)
                    ·
                      rfl

theorem cell22_1379683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 2, 1, 4].length) (baseStart_1379683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1379683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1379683 prefixEnd_1379683 := by exact prefixLift 1379683
  have htrace : WordTrace (prefixWord ++ tailWord_1379683) baseStart_1379683 baseEnd_1379683 := by
    simpa [prefixWord, tailWord_1379683, baseEnd_1379683] using wordTrace_append hprefix tailTrace_1379683
  have hstable : (prefixWord ++ tailWord_1379683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379683).length < 2 ^ (prefixWord ++ tailWord_1379683).sum := by decide
  have hdescent : baseEnd_1379683 < baseStart_1379683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379715 : List Nat := [1, 1, 1, 3, 5, 3, 2, 2, 4]
def baseStart_1379715 : Nat := 118140960795 + 1379715 * 2 ^ 59
def prefixEnd_1379715 : Nat := 4983230072969 + 3 ^ 40 * 1379715 * 2
def baseEnd_1379715 : Nat := 157434880270705464981625

theorem tailTrace_1379715 : CollatzResearch.WordTrace tailWord_1379715 prefixEnd_1379715 157434880270705464981625 := by
  unfold tailWord_1379715
  simp only [CollatzResearch.WordTrace]
  refine ⟨50322340196535666407124599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33548226797690444271416399 50322340196535666407124599)
  ·
    refine ⟨75483510294803499610686899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50322340196535666407124599 75483510294803499610686899)
    ·
      refine ⟨113225265442205249416030349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75483510294803499610686899 113225265442205249416030349)
      ·
        refine ⟨42459474540826968531011381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113225265442205249416030349 42459474540826968531011381)
        ·
          refine ⟨3980575738202528299782317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42459474540826968531011381 3980575738202528299782317)
          ·
            refine ⟨1492715901825948112418369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3980575738202528299782317 1492715901825948112418369)
            ·
              refine ⟨1119536926369461084313777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1492715901825948112418369 1119536926369461084313777)
              ·
                refine ⟨839652694777095813235333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1119536926369461084313777 839652694777095813235333)
                ·
                  refine ⟨157434880270705464981625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 839652694777095813235333 157434880270705464981625)
                  ·
                    rfl

theorem cell22_1379715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 2, 2, 4].length) (baseStart_1379715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1379715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1379715 prefixEnd_1379715 := by exact prefixLift 1379715
  have htrace : WordTrace (prefixWord ++ tailWord_1379715) baseStart_1379715 baseEnd_1379715 := by
    simpa [prefixWord, tailWord_1379715, baseEnd_1379715] using wordTrace_append hprefix tailTrace_1379715
  have hstable : (prefixWord ++ tailWord_1379715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379715).length < 2 ^ (prefixWord ++ tailWord_1379715).sum := by decide
  have hdescent : baseEnd_1379715 < baseStart_1379715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379730 : List Nat := [3, 2, 3, 3, 1, 1, 2, 1, 1, 5]
def baseStart_1379730 : Nat := 118140960795 + 1379730 * 2 ^ 59
def prefixEnd_1379730 : Nat := 4983230072969 + 3 ^ 40 * 1379730 * 2
def baseEnd_1379730 : Nat := 472309775618661355819829

theorem tailTrace_1379730 : CollatzResearch.WordTrace tailWord_1379730 prefixEnd_1379730 472309775618661355819829 := by
  unfold tailWord_1379730
  simp only [CollatzResearch.WordTrace]
  refine ⟨12580721822870330992230161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33548591527654215979280429 12580721822870330992230161)
  ·
    refine ⟨9435541367152748244172621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12580721822870330992230161 9435541367152748244172621)
    ·
      refine ⟨3538328012682280591564733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9435541367152748244172621 3538328012682280591564733)
      ·
        refine ⟨1326873004755855221836775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3538328012682280591564733 1326873004755855221836775)
        ·
          refine ⟨1990309507133782832755163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1326873004755855221836775 1990309507133782832755163)
          ·
            refine ⟨2985464260700674249132745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1990309507133782832755163 2985464260700674249132745)
            ·
              refine ⟨2239098195525505686849559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2985464260700674249132745 2239098195525505686849559)
              ·
                refine ⟨3358647293288258530274339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2239098195525505686849559 3358647293288258530274339)
                ·
                  refine ⟨5037970939932387795411509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3358647293288258530274339 5037970939932387795411509)
                  ·
                    refine ⟨472309775618661355819829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5037970939932387795411509 472309775618661355819829)
                    ·
                      rfl

theorem cell22_1379730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_1379730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1379730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1379730 prefixEnd_1379730 := by exact prefixLift 1379730
  have htrace : WordTrace (prefixWord ++ tailWord_1379730) baseStart_1379730 baseEnd_1379730 := by
    simpa [prefixWord, tailWord_1379730, baseEnd_1379730] using wordTrace_append hprefix tailTrace_1379730
  have hstable : (prefixWord ++ tailWord_1379730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379730).length < 2 ^ (prefixWord ++ tailWord_1379730).sum := by decide
  have hdescent : baseEnd_1379730 < baseStart_1379730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379786 : List Nat := [3, 1, 2, 1, 2, 3, 2, 1, 2, 5]
def baseStart_1379786 : Nat := 118140960795 + 1379786 * 2 ^ 59
def prefixEnd_1379786 : Nat := 4983230072969 + 3 ^ 40 * 1379786 * 2
def baseEnd_1379786 : Nat := 472328945563095876419657

theorem tailTrace_1379786 : CollatzResearch.WordTrace tailWord_1379786 prefixEnd_1379786 472328945563095876419657 := by
  unfold tailWord_1379786
  simp only [CollatzResearch.WordTrace]
  refine ⟨12581232444819611383239803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33549953186185630355306141 12581232444819611383239803)
  ·
    refine ⟨18871848667229417074859705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12581232444819611383239803 18871848667229417074859705)
    ·
      refine ⟨14153886500422062806144779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18871848667229417074859705 14153886500422062806144779)
      ·
        refine ⟨21230829750633094209217169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14153886500422062806144779 21230829750633094209217169)
        ·
          refine ⟨15923122312974820656912877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21230829750633094209217169 15923122312974820656912877)
          ·
            refine ⟨5971170867365557746342329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15923122312974820656912877 5971170867365557746342329)
            ·
              refine ⟨4478378150524168309756747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5971170867365557746342329 4478378150524168309756747)
              ·
                refine ⟨6717567225786252464635121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4478378150524168309756747 6717567225786252464635121)
                ·
                  refine ⟨5038175419339689348476341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6717567225786252464635121 5038175419339689348476341)
                  ·
                    refine ⟨472328945563095876419657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5038175419339689348476341 472328945563095876419657)
                    ·
                      rfl

theorem cell22_1379786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 2, 5].length) (baseStart_1379786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1379786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1379786 prefixEnd_1379786 := by exact prefixLift 1379786
  have htrace : WordTrace (prefixWord ++ tailWord_1379786) baseStart_1379786 baseEnd_1379786 := by
    simpa [prefixWord, tailWord_1379786, baseEnd_1379786] using wordTrace_append hprefix tailTrace_1379786
  have hstable : (prefixWord ++ tailWord_1379786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379786).length < 2 ^ (prefixWord ++ tailWord_1379786).sum := by decide
  have hdescent : baseEnd_1379786 < baseStart_1379786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379852 : List Nat := [2, 2, 1, 2, 6, 1, 1, 2, 1, 4]
def baseStart_1379852 : Nat := 118140960795 + 1379852 * 2 ^ 59
def prefixEnd_1379852 : Nat := 4983230072969 + 3 ^ 40 * 1379852 * 2
def baseEnd_1379852 : Nat := 472351538711893704269455

theorem tailTrace_1379852 : CollatzResearch.WordTrace tailWord_1379852 prefixEnd_1379852 472351538711893704269455 := by
  unfold tailWord_1379852
  simp only [CollatzResearch.WordTrace]
  refine ⟨25163668498519669402430905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33551557998026225869907873 25163668498519669402430905)
  ·
    refine ⟨18872751373889752051823179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25163668498519669402430905 18872751373889752051823179)
    ·
      refine ⟨28309127060834628077734769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18872751373889752051823179 28309127060834628077734769)
      ·
        refine ⟨21231845295625971058301077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28309127060834628077734769 21231845295625971058301077)
        ·
          refine ⟨995242748232467393357863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 21231845295625971058301077 995242748232467393357863)
          ·
            refine ⟨1492864122348701090036795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 995242748232467393357863 1492864122348701090036795)
            ·
              refine ⟨2239296183523051635055193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1492864122348701090036795 2239296183523051635055193)
              ·
                refine ⟨1679472137642288726291395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2239296183523051635055193 1679472137642288726291395)
                ·
                  refine ⟨2519208206463433089437093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1679472137642288726291395 2519208206463433089437093)
                  ·
                    refine ⟨472351538711893704269455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2519208206463433089437093 472351538711893704269455)
                    ·
                      rfl

theorem cell22_1379852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 2, 1, 4].length) (baseStart_1379852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1379852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1379852 prefixEnd_1379852 := by exact prefixLift 1379852
  have htrace : WordTrace (prefixWord ++ tailWord_1379852) baseStart_1379852 baseEnd_1379852 := by
    simpa [prefixWord, tailWord_1379852, baseEnd_1379852] using wordTrace_append hprefix tailTrace_1379852
  have hstable : (prefixWord ++ tailWord_1379852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379852).length < 2 ^ (prefixWord ++ tailWord_1379852).sum := by decide
  have hdescent : baseEnd_1379852 < baseStart_1379852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379861 : List Nat := [1, 3, 2, 1, 3, 2, 2, 8]
def baseStart_1379861 : Nat := 118140960795 + 1379861 * 2 ^ 59
def prefixEnd_1379861 : Nat := 4983230072969 + 3 ^ 40 * 1379861 * 2
def baseEnd_1379861 : Nat := 52483846621757853421603

theorem tailTrace_1379861 : CollatzResearch.WordTrace tailWord_1379861 prefixEnd_1379861 52483846621757853421603 := by
  unfold tailWord_1379861
  simp only [CollatzResearch.WordTrace]
  refine ⟨50327665254006733341939437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33551776836004488894626291 50327665254006733341939437)
  ·
    refine ⟨18872874470252525003227289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50327665254006733341939437 18872874470252525003227289)
    ·
      refine ⟨14154655852689393752420467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18872874470252525003227289 14154655852689393752420467)
      ·
        refine ⟨21231983779034090628630701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14154655852689393752420467 21231983779034090628630701)
        ·
          refine ⟨7961993917137783985736513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21231983779034090628630701 7961993917137783985736513)
          ·
            refine ⟨5971495437853337989302385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7961993917137783985736513 5971495437853337989302385)
            ·
              refine ⟨4478621578390003491976789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5971495437853337989302385 4478621578390003491976789)
              ·
                refine ⟨52483846621757853421603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4478621578390003491976789 52483846621757853421603)
                ·
                  rfl

theorem cell22_1379861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 8].length) (baseStart_1379861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1379861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1379861 prefixEnd_1379861 := by exact prefixLift 1379861
  have htrace : WordTrace (prefixWord ++ tailWord_1379861) baseStart_1379861 baseEnd_1379861 := by
    simpa [prefixWord, tailWord_1379861, baseEnd_1379861] using wordTrace_append hprefix tailTrace_1379861
  have hstable : (prefixWord ++ tailWord_1379861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379861).length < 2 ^ (prefixWord ++ tailWord_1379861).sum := by decide
  have hdescent : baseEnd_1379861 < baseStart_1379861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379891 : List Nat := [1, 1, 1, 2, 4, 3, 1, 1, 2, 6]
def baseStart_1379891 : Nat := 118140960795 + 1379891 * 2 ^ 59
def prefixEnd_1379891 : Nat := 4983230072969 + 3 ^ 40 * 1379891 * 2
def baseEnd_1379891 : Nat := 472364889208910602544335

theorem tailTrace_1379891 : CollatzResearch.WordTrace tailWord_1379891 prefixEnd_1379891 472364889208910602544335 := by
  unfold tailWord_1379891
  simp only [CollatzResearch.WordTrace]
  refine ⟨50328759443898048465531527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33552506295932032310354351 50328759443898048465531527)
  ·
    refine ⟨75493139165847072698297291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50328759443898048465531527 75493139165847072698297291)
    ·
      refine ⟨113239708748770609047445937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75493139165847072698297291 113239708748770609047445937)
      ·
        refine ⟨84929781561577956785584453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113239708748770609047445937 84929781561577956785584453)
        ·
          refine ⟨15924334042795866897297085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84929781561577956785584453 15924334042795866897297085)
          ·
            refine ⟨5971625266048450086486407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15924334042795866897297085 5971625266048450086486407)
            ·
              refine ⟨8957437899072675129729611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5971625266048450086486407 8957437899072675129729611)
              ·
                refine ⟨13436156848609012694594417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8957437899072675129729611 13436156848609012694594417)
                ·
                  refine ⟨10077117636456759520945813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13436156848609012694594417 10077117636456759520945813)
                  ·
                    refine ⟨472364889208910602544335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10077117636456759520945813 472364889208910602544335)
                    ·
                      rfl

theorem cell22_1379891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 6].length) (baseStart_1379891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1379891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1379891 prefixEnd_1379891 := by exact prefixLift 1379891
  have htrace : WordTrace (prefixWord ++ tailWord_1379891) baseStart_1379891 baseEnd_1379891 := by
    simpa [prefixWord, tailWord_1379891, baseEnd_1379891] using wordTrace_append hprefix tailTrace_1379891
  have hstable : (prefixWord ++ tailWord_1379891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379891).length < 2 ^ (prefixWord ++ tailWord_1379891).sum := by decide
  have hdescent : baseEnd_1379891 < baseStart_1379891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379921 : List Nat := [1, 2, 2, 1, 3, 2, 1, 2, 1, 7]
def baseStart_1379921 : Nat := 118140960795 + 1379921 * 2 ^ 59
def prefixEnd_1379921 : Nat := 4983230072969 + 3 ^ 40 * 1379921 * 2
def baseEnd_1379921 : Nat := 472375158822000524294243

theorem tailTrace_1379921 : CollatzResearch.WordTrace tailWord_1379921 prefixEnd_1379921 472375158822000524294243 := by
  unfold tailWord_1379921
  simp only [CollatzResearch.WordTrace]
  refine ⟨50329853633789363589123617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33553235755859575726082411 50329853633789363589123617)
  ·
    refine ⟨37747390225342022691842713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50329853633789363589123617 37747390225342022691842713)
    ·
      refine ⟨28310542669006517018882035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37747390225342022691842713 28310542669006517018882035)
      ·
        refine ⟨42465814003509775528323053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28310542669006517018882035 42465814003509775528323053)
        ·
          refine ⟨15924680251316165823121145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42465814003509775528323053 15924680251316165823121145)
          ·
            refine ⟨11943510188487124367340859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15924680251316165823121145 11943510188487124367340859)
            ·
              refine ⟨17915265282730686551011289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11943510188487124367340859 17915265282730686551011289)
              ·
                refine ⟨13436448962048014913258467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17915265282730686551011289 13436448962048014913258467)
                ·
                  refine ⟨20154673443072022369887701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13436448962048014913258467 20154673443072022369887701)
                  ·
                    refine ⟨472375158822000524294243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20154673443072022369887701 472375158822000524294243)
                    ·
                      rfl

theorem cell22_1379921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 7].length) (baseStart_1379921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1379921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1379921 prefixEnd_1379921 := by exact prefixLift 1379921
  have htrace : WordTrace (prefixWord ++ tailWord_1379921) baseStart_1379921 baseEnd_1379921 := by
    simpa [prefixWord, tailWord_1379921, baseEnd_1379921] using wordTrace_append hprefix tailTrace_1379921
  have hstable : (prefixWord ++ tailWord_1379921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379921).length < 2 ^ (prefixWord ++ tailWord_1379921).sum := by decide
  have hdescent : baseEnd_1379921 < baseStart_1379921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379927 : List Nat := [1, 1, 3, 2, 2, 4, 2, 3, 1, 3]
def baseStart_1379927 : Nat := 118140960795 + 1379927 * 2 ^ 59
def prefixEnd_1379927 : Nat := 4983230072969 + 3 ^ 40 * 1379927 * 2
def baseEnd_1379927 : Nat := 472377212744618508644225

theorem tailTrace_1379927 : CollatzResearch.WordTrace tailWord_1379927 prefixEnd_1379927 472377212744618508644225 := by
  unfold tailWord_1379927
  simp only [CollatzResearch.WordTrace]
  refine ⟨50330072471767626613842035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33553381647845084409228023 50330072471767626613842035)
  ·
    refine ⟨75495108707651439920763053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50330072471767626613842035 75495108707651439920763053)
    ·
      refine ⟨28310665765369289970286145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75495108707651439920763053 28310665765369289970286145)
      ·
        refine ⟨21232999324026967477714609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28310665765369289970286145 21232999324026967477714609)
        ·
          refine ⟨15924749493020225608285957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21232999324026967477714609 15924749493020225608285957)
          ·
            refine ⟨2985890529941292301553617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15924749493020225608285957 2985890529941292301553617)
            ·
              refine ⟨2239417897455969226165213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2985890529941292301553617 2239417897455969226165213)
              ·
                refine ⟨839781711545988459811955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2239417897455969226165213 839781711545988459811955)
                ·
                  refine ⟨1259672567318982689717933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 839781711545988459811955 1259672567318982689717933)
                  ·
                    refine ⟨472377212744618508644225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1259672567318982689717933 472377212744618508644225)
                    ·
                      rfl

theorem cell22_1379927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 3, 1, 3].length) (baseStart_1379927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1379927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1379927 prefixEnd_1379927 := by exact prefixLift 1379927
  have htrace : WordTrace (prefixWord ++ tailWord_1379927) baseStart_1379927 baseEnd_1379927 := by
    simpa [prefixWord, tailWord_1379927, baseEnd_1379927] using wordTrace_append hprefix tailTrace_1379927
  have hstable : (prefixWord ++ tailWord_1379927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379927).length < 2 ^ (prefixWord ++ tailWord_1379927).sum := by decide
  have hdescent : baseEnd_1379927 < baseStart_1379927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379940 : List Nat := [2, 3, 1, 1, 2, 5, 1, 2, 5]
def baseStart_1379940 : Nat := 118140960795 + 1379940 * 2 ^ 59
def prefixEnd_1379940 : Nat := 4983230072969 + 3 ^ 40 * 1379940 * 2
def baseEnd_1379940 : Nat := 157460554303430269356395

theorem tailTrace_1379940 : CollatzResearch.WordTrace tailWord_1379940 prefixEnd_1379940 157460554303430269356395 := by
  unfold tailWord_1379940
  simp only [CollatzResearch.WordTrace]
  refine ⟨25165273310360264917032637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33553697747147019889376849 25165273310360264917032637)
  ·
    refine ⟨9436977491385099343887239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25165273310360264917032637 9436977491385099343887239)
    ·
      refine ⟨14155466237077649015830859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9436977491385099343887239 14155466237077649015830859)
      ·
        refine ⟨21233199355616473523746289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14155466237077649015830859 21233199355616473523746289)
        ·
          refine ⟨15924899516712355142809717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21233199355616473523746289 15924899516712355142809717)
          ·
            refine ⟨1492959329691783294638411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15924899516712355142809717 1492959329691783294638411)
            ·
              refine ⟨2239438994537674941957617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1492959329691783294638411 2239438994537674941957617)
              ·
                refine ⟨1679579245903256206468213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2239438994537674941957617 1679579245903256206468213)
                ·
                  refine ⟨157460554303430269356395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1679579245903256206468213 157460554303430269356395)
                  ·
                    rfl

theorem cell22_1379940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 2, 5].length) (baseStart_1379940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1379940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1379940 prefixEnd_1379940 := by exact prefixLift 1379940
  have htrace : WordTrace (prefixWord ++ tailWord_1379940) baseStart_1379940 baseEnd_1379940 := by
    simpa [prefixWord, tailWord_1379940, baseEnd_1379940] using wordTrace_append hprefix tailTrace_1379940
  have hstable : (prefixWord ++ tailWord_1379940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379940).length < 2 ^ (prefixWord ++ tailWord_1379940).sum := by decide
  have hdescent : baseEnd_1379940 < baseStart_1379940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379957 : List Nat := [1, 3, 4, 2, 1, 2, 3, 1, 5]
def baseStart_1379957 : Nat := 118140960795 + 1379957 * 2 ^ 59
def prefixEnd_1379957 : Nat := 4983230072969 + 3 ^ 40 * 1379957 * 2
def baseEnd_1379957 : Nat := 157462494119236143464711

theorem tailTrace_1379957 : CollatzResearch.WordTrace tailWord_1379957 prefixEnd_1379957 157462494119236143464711 := by
  unfold tailWord_1379957
  simp only [CollatzResearch.WordTrace]
  refine ⟨50331166661658941737434125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33554111107772627824956083 50331166661658941737434125)
  ·
    refine ⟨18874187498122103151537797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50331166661658941737434125 18874187498122103151537797)
    ·
      refine ⟨3538910155897894340913337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18874187498122103151537797 3538910155897894340913337)
      ·
        refine ⟨2654182616923420755685003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3538910155897894340913337 2654182616923420755685003)
        ·
          refine ⟨3981273925385131133527505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2654182616923420755685003 3981273925385131133527505)
          ·
            refine ⟨2985955444038848350145629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3981273925385131133527505 2985955444038848350145629)
            ·
              refine ⟨1119733291514568131304611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2985955444038848350145629 1119733291514568131304611)
              ·
                refine ⟨1679599937271852196956917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1119733291514568131304611 1679599937271852196956917)
                ·
                  refine ⟨157462494119236143464711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1679599937271852196956917 157462494119236143464711)
                  ·
                    rfl

theorem cell22_1379957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 3, 1, 5].length) (baseStart_1379957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1379957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1379957 prefixEnd_1379957 := by exact prefixLift 1379957
  have htrace : WordTrace (prefixWord ++ tailWord_1379957) baseStart_1379957 baseEnd_1379957 := by
    simpa [prefixWord, tailWord_1379957, baseEnd_1379957] using wordTrace_append hprefix tailTrace_1379957
  have hstable : (prefixWord ++ tailWord_1379957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379957).length < 2 ^ (prefixWord ++ tailWord_1379957).sum := by decide
  have hdescent : baseEnd_1379957 < baseStart_1379957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380000 : List Nat := [2, 1, 1, 4, 3, 1, 2, 1, 4, 3]
def baseStart_1380000 : Nat := 118140960795 + 1380000 * 2 ^ 59
def prefixEnd_1380000 : Nat := 4983230072969 + 3 ^ 40 * 1380000 * 2
def baseEnd_1380000 : Nat := 472402202136470651569001

theorem tailTrace_1380000 : CollatzResearch.WordTrace tailWord_1380000 prefixEnd_1380000 472402202136470651569001 := by
  unfold tailWord_1380000
  simp only [CollatzResearch.WordTrace]
  refine ⟨25166367500251580040624727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33555156667002106720832969 25166367500251580040624727)
  ·
    refine ⟨37749551250377370060937091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25166367500251580040624727 37749551250377370060937091)
    ·
      refine ⟨56624326875566055091405637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37749551250377370060937091 56624326875566055091405637)
      ·
        refine ⟨10617061289168635329638557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56624326875566055091405637 10617061289168635329638557)
        ·
          refine ⟨3981397983438238248614459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10617061289168635329638557 3981397983438238248614459)
          ·
            refine ⟨5972096975157357372921689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3981397983438238248614459 5972096975157357372921689)
            ·
              refine ⟨4479072731368018029691267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5972096975157357372921689 4479072731368018029691267)
              ·
                refine ⟨6718609097052027044536901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4479072731368018029691267 6718609097052027044536901)
                ·
                  refine ⟨1259739205697255070850669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6718609097052027044536901 1259739205697255070850669)
                  ·
                    refine ⟨472402202136470651569001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1259739205697255070850669 472402202136470651569001)
                    ·
                      rfl

theorem cell22_1380000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 4, 3].length) (baseStart_1380000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1380000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1380000 prefixEnd_1380000 := by exact prefixLift 1380000
  have htrace : WordTrace (prefixWord ++ tailWord_1380000) baseStart_1380000 baseEnd_1380000 := by
    simpa [prefixWord, tailWord_1380000, baseEnd_1380000] using wordTrace_append hprefix tailTrace_1380000
  have hstable : (prefixWord ++ tailWord_1380000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380000).length < 2 ^ (prefixWord ++ tailWord_1380000).sum := by decide
  have hdescent : baseEnd_1380000 < baseStart_1380000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380008 : List Nat := [2, 1, 7, 1, 2, 1, 2, 1, 5]
def baseStart_1380008 : Nat := 118140960795 + 1380008 * 2 ^ 59
def prefixEnd_1380008 : Nat := 4983230072969 + 3 ^ 40 * 1380008 * 2
def baseEnd_1380008 : Nat := 157468313566653765789659

theorem tailTrace_1380008 : CollatzResearch.WordTrace tailWord_1380008 prefixEnd_1380008 157468313566653765789659 := by
  unfold tailWord_1380008
  simp only [CollatzResearch.WordTrace]
  refine ⟨25166513392237088723770339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33555351189649451631693785 25166513392237088723770339)
  ·
    refine ⟨37749770088355633085655509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25166513392237088723770339 37749770088355633085655509)
    ·
      refine ⟨884760236445835150445051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 37749770088355633085655509 884760236445835150445051)
      ·
        refine ⟨1327140354668752725667577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 884760236445835150445051 1327140354668752725667577)
        ·
          refine ⟨995355266001564544250683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1327140354668752725667577 995355266001564544250683)
          ·
            refine ⟨1493032899002346816376025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 995355266001564544250683 1493032899002346816376025)
            ·
              refine ⟨1119774674251760112282019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1493032899002346816376025 1119774674251760112282019)
              ·
                refine ⟨1679662011377640168423029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1119774674251760112282019 1679662011377640168423029)
                ·
                  refine ⟨157468313566653765789659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1679662011377640168423029 157468313566653765789659)
                  ·
                    rfl

theorem cell22_1380008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 2, 1, 5].length) (baseStart_1380008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1380008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1380008 prefixEnd_1380008 := by exact prefixLift 1380008
  have htrace : WordTrace (prefixWord ++ tailWord_1380008) baseStart_1380008 baseEnd_1380008 := by
    simpa [prefixWord, tailWord_1380008, baseEnd_1380008] using wordTrace_append hprefix tailTrace_1380008
  have hstable : (prefixWord ++ tailWord_1380008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380008).length < 2 ^ (prefixWord ++ tailWord_1380008).sum := by decide
  have hdescent : baseEnd_1380008 < baseStart_1380008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380102 : List Nat := [6, 2, 2, 1, 1, 2, 1, 2, 2, 3]
def baseStart_1380102 : Nat := 118140960795 + 1380102 * 2 ^ 59
def prefixEnd_1380102 : Nat := 4983230072969 + 3 ^ 40 * 1380102 * 2
def baseEnd_1380102 : Nat := 472437118820976385518689

theorem tailTrace_1380102 : CollatzResearch.WordTrace tailWord_1380102 prefixEnd_1380102 472437118820976385518689 := by
  unfold tailWord_1380102
  simp only [CollatzResearch.WordTrace]
  refine ⟨1573014226441675984420705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 33557636830755754334308373 1573014226441675984420705)
  ·
    refine ⟨1179760669831256988315529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1573014226441675984420705 1179760669831256988315529)
    ·
      refine ⟨884820502373442741236647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1179760669831256988315529 884820502373442741236647)
      ·
        refine ⟨1327230753560164111854971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 884820502373442741236647 1327230753560164111854971)
        ·
          refine ⟨1990846130340246167782457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1327230753560164111854971 1990846130340246167782457)
          ·
            refine ⟨1493134597755184625836843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1990846130340246167782457 1493134597755184625836843)
            ·
              refine ⟨2239701896632776938755265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1493134597755184625836843 2239701896632776938755265)
              ·
                refine ⟨1679776422474582704066449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2239701896632776938755265 1679776422474582704066449)
                ·
                  refine ⟨1259832316855937028049837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1679776422474582704066449 1259832316855937028049837)
                  ·
                    refine ⟨472437118820976385518689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1259832316855937028049837 472437118820976385518689)
                    ·
                      rfl

theorem cell22_1380102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_1380102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1380102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1380102 prefixEnd_1380102 := by exact prefixLift 1380102
  have htrace : WordTrace (prefixWord ++ tailWord_1380102) baseStart_1380102 baseEnd_1380102 := by
    simpa [prefixWord, tailWord_1380102, baseEnd_1380102] using wordTrace_append hprefix tailTrace_1380102
  have hstable : (prefixWord ++ tailWord_1380102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380102).length < 2 ^ (prefixWord ++ tailWord_1380102).sum := by decide
  have hdescent : baseEnd_1380102 < baseStart_1380102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380154 : List Nat := [3, 1, 1, 1, 5, 3, 1, 3, 4]
def baseStart_1380154 : Nat := 118140960795 + 1380154 * 2 ^ 59
def prefixEnd_1380154 : Nat := 4983230072969 + 3 ^ 40 * 1380154 * 2
def baseEnd_1380154 : Nat := 157484973161221861072843

theorem tailTrace_1380154 : CollatzResearch.WordTrace tailWord_1380154 prefixEnd_1380154 157484973161221861072843 := by
  unfold tailWord_1380154
  simp only [CollatzResearch.WordTrace]
  refine ⟨12584587960486311095588879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33558901227963496254903677 12584587960486311095588879)
  ·
    refine ⟨18876881940729466643383319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12584587960486311095588879 18876881940729466643383319)
    ·
      refine ⟨28315322911094199965074979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18876881940729466643383319 28315322911094199965074979)
      ·
        refine ⟨42472984366641299947612469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28315322911094199965074979 42472984366641299947612469)
        ·
          refine ⟨3981842284372621870088669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42472984366641299947612469 3981842284372621870088669)
          ·
            refine ⟨1493190856639733201283251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3981842284372621870088669 1493190856639733201283251)
            ·
              refine ⟨2239786284959599801924877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1493190856639733201283251 2239786284959599801924877)
              ·
                refine ⟨839919856859849925721829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2239786284959599801924877 839919856859849925721829)
                ·
                  refine ⟨157484973161221861072843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 839919856859849925721829 157484973161221861072843)
                  ·
                    rfl

theorem cell22_1380154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 3, 4].length) (baseStart_1380154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1380154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1380154 prefixEnd_1380154 := by exact prefixLift 1380154
  have htrace : WordTrace (prefixWord ++ tailWord_1380154) baseStart_1380154 baseEnd_1380154 := by
    simpa [prefixWord, tailWord_1380154, baseEnd_1380154] using wordTrace_append hprefix tailTrace_1380154
  have hstable : (prefixWord ++ tailWord_1380154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380154).length < 2 ^ (prefixWord ++ tailWord_1380154).sum := by decide
  have hdescent : baseEnd_1380154 < baseStart_1380154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380227 : List Nat := [1, 1, 1, 3, 4, 3, 2, 2, 5]
def baseStart_1380227 : Nat := 118140960795 + 1380227 * 2 ^ 59
def prefixEnd_1380227 : Nat := 4983230072969 + 3 ^ 40 * 1380227 * 2
def baseEnd_1380227 : Nat := 157493302958505908714435

theorem tailTrace_1380227 : CollatzResearch.WordTrace tailWord_1380227 prefixEnd_1380227 157493302958505908714435 := by
  unfold tailWord_1380227
  simp only [CollatzResearch.WordTrace]
  refine ⟨50341014370680777849762935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33560676247120518566508623 50341014370680777849762935)
  ·
    refine ⟨75511521556021166774644403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50341014370680777849762935 75511521556021166774644403)
    ·
      refine ⟨113267282334031750161966605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75511521556021166774644403 113267282334031750161966605)
      ·
        refine ⟨42475230875261906310737477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113267282334031750161966605 42475230875261906310737477)
        ·
          refine ⟨7964105789111607433263277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42475230875261906310737477 7964105789111607433263277)
          ·
            refine ⟨2986539670916852787473729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7964105789111607433263277 2986539670916852787473729)
            ·
              refine ⟨2239904753187639590605297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2986539670916852787473729 2239904753187639590605297)
              ·
                refine ⟨1679928564890729692953973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2239904753187639590605297 1679928564890729692953973)
                ·
                  refine ⟨157493302958505908714435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1679928564890729692953973 157493302958505908714435)
                  ·
                    rfl

theorem cell22_1380227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 2, 5].length) (baseStart_1380227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1380227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1380227 prefixEnd_1380227 := by exact prefixLift 1380227
  have htrace : WordTrace (prefixWord ++ tailWord_1380227) baseStart_1380227 baseEnd_1380227 := by
    simpa [prefixWord, tailWord_1380227, baseEnd_1380227] using wordTrace_append hprefix tailTrace_1380227
  have hstable : (prefixWord ++ tailWord_1380227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380227).length < 2 ^ (prefixWord ++ tailWord_1380227).sum := by decide
  have hdescent : baseEnd_1380227 < baseStart_1380227 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380231 : List Nat := [1, 1, 4, 2, 4, 1, 1, 4, 1, 3]
def baseStart_1380231 : Nat := 118140960795 + 1380231 * 2 ^ 59
def prefixEnd_1380231 : Nat := 4983230072969 + 3 ^ 40 * 1380231 * 2
def baseEnd_1380231 : Nat := 472481278157263049043293

theorem tailTrace_1380231 : CollatzResearch.WordTrace tailWord_1380231 prefixEnd_1380231 472481278157263049043293 := by
  unfold tailWord_1380231
  simp only [CollatzResearch.WordTrace]
  refine ⟨50341160262666286532908547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33560773508444191021939031 50341160262666286532908547)
  ·
    refine ⟨75511740393999429799362821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50341160262666286532908547 75511740393999429799362821)
    ·
      refine ⟨14158451323874893087380529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75511740393999429799362821 14158451323874893087380529)
      ·
        refine ⟨10618838492906169815535397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14158451323874893087380529 10618838492906169815535397)
        ·
          refine ⟨1991032217419906840412887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10618838492906169815535397 1991032217419906840412887)
          ·
            refine ⟨2986548326129860260619331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1991032217419906840412887 2986548326129860260619331)
            ·
              refine ⟨4479822489194790390928997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2986548326129860260619331 4479822489194790390928997)
              ·
                refine ⟨839966716724023198299187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4479822489194790390928997 839966716724023198299187)
                ·
                  refine ⟨1259950075086034797448781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 839966716724023198299187 1259950075086034797448781)
                  ·
                    refine ⟨472481278157263049043293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1259950075086034797448781 472481278157263049043293)
                    ·
                      rfl

theorem cell22_1380231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 4, 1, 3].length) (baseStart_1380231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1380231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1380231 prefixEnd_1380231 := by exact prefixLift 1380231
  have htrace : WordTrace (prefixWord ++ tailWord_1380231) baseStart_1380231 baseEnd_1380231 := by
    simpa [prefixWord, tailWord_1380231, baseEnd_1380231] using wordTrace_append hprefix tailTrace_1380231
  have hstable : (prefixWord ++ tailWord_1380231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380231).length < 2 ^ (prefixWord ++ tailWord_1380231).sum := by decide
  have hdescent : baseEnd_1380231 < baseStart_1380231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380240 : List Nat := [2, 1, 1, 1, 1, 1, 2, 6, 3, 4]
def baseStart_1380240 : Nat := 118140960795 + 1380240 * 2 ^ 59
def prefixEnd_1380240 : Nat := 4983230072969 + 3 ^ 40 * 1380240 * 2
def baseEnd_1380240 : Nat := 472484359041190025568265

theorem tailTrace_1380240 : CollatzResearch.WordTrace tailWord_1380240 prefixEnd_1380240 472484359041190025568265 := by
  unfold tailWord_1380240
  simp only [CollatzResearch.WordTrace]
  refine ⟨25170744259816840534993087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33560992346422454046657449 25170744259816840534993087)
  ·
    refine ⟨37756116389725260802489631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25170744259816840534993087 37756116389725260802489631)
    ·
      refine ⟨56634174584587891203734447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37756116389725260802489631 56634174584587891203734447)
      ·
        refine ⟨84951261876881836805601671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56634174584587891203734447 84951261876881836805601671)
        ·
          refine ⟨127426892815322755208402507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84951261876881836805601671 127426892815322755208402507)
          ·
            refine ⟨191140339222984132812603761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127426892815322755208402507 191140339222984132812603761)
            ·
              refine ⟨143355254417238099609452821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191140339222984132812603761 143355254417238099609452821)
              ·
                refine ⟨6719777550808035919193101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 143355254417238099609452821 6719777550808035919193101)
                ·
                  refine ⟨2519916581553013469697413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6719777550808035919193101 2519916581553013469697413)
                  ·
                    refine ⟨472484359041190025568265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2519916581553013469697413 472484359041190025568265)
                    ·
                      rfl

theorem cell22_1380240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 3, 4].length) (baseStart_1380240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1380240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1380240 prefixEnd_1380240 := by exact prefixLift 1380240
  have htrace : WordTrace (prefixWord ++ tailWord_1380240) baseStart_1380240 baseEnd_1380240 := by
    simpa [prefixWord, tailWord_1380240, baseEnd_1380240] using wordTrace_append hprefix tailTrace_1380240
  have hstable : (prefixWord ++ tailWord_1380240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380240).length < 2 ^ (prefixWord ++ tailWord_1380240).sum := by decide
  have hdescent : baseEnd_1380240 < baseStart_1380240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380242 : List Nat := [3, 2, 3, 2, 1, 1, 1, 1, 1, 7]
def baseStart_1380242 : Nat := 118140960795 + 1380242 * 2 ^ 59
def prefixEnd_1380242 : Nat := 4983230072969 + 3 ^ 40 * 1380242 * 2
def baseEnd_1380242 : Nat := 472485043682062687018259

theorem tailTrace_1380242 : CollatzResearch.WordTrace tailWord_1380242 prefixEnd_1380242 472485043682062687018259 := by
  unfold tailWord_1380242
  simp only [CollatzResearch.WordTrace]
  refine ⟨12585390366406608852889745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33561040977084290274372653 12585390366406608852889745)
  ·
    refine ⟨9439042774804956639667309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12585390366406608852889745 9439042774804956639667309)
    ·
      refine ⟨3539641040551858739875241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9439042774804956639667309 3539641040551858739875241)
      ·
        refine ⟨2654730780413894054906431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3539641040551858739875241 2654730780413894054906431)
        ·
          refine ⟨3982096170620841082359647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2654730780413894054906431 3982096170620841082359647)
          ·
            refine ⟨5973144255931261623539471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3982096170620841082359647 5973144255931261623539471)
            ·
              refine ⟨8959716383896892435309207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5973144255931261623539471 8959716383896892435309207)
              ·
                refine ⟨13439574575845338652963811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8959716383896892435309207 13439574575845338652963811)
                ·
                  refine ⟨20159361863768007979445717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13439574575845338652963811 20159361863768007979445717)
                  ·
                    refine ⟨472485043682062687018259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20159361863768007979445717 472485043682062687018259)
                    ·
                      rfl

theorem cell22_1380242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_1380242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1380242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1380242 prefixEnd_1380242 := by exact prefixLift 1380242
  have htrace : WordTrace (prefixWord ++ tailWord_1380242) baseStart_1380242 baseEnd_1380242 := by
    simpa [prefixWord, tailWord_1380242, baseEnd_1380242] using wordTrace_append hprefix tailTrace_1380242
  have hstable : (prefixWord ++ tailWord_1380242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380242).length < 2 ^ (prefixWord ++ tailWord_1380242).sum := by decide
  have hdescent : baseEnd_1380242 < baseStart_1380242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380287 : List Nat := [1, 1, 2, 2, 2, 1, 5, 1, 4, 3]
def baseStart_1380287 : Nat := 118140960795 + 1380287 * 2 ^ 59
def prefixEnd_1380287 : Nat := 4983230072969 + 3 ^ 40 * 1380287 * 2
def baseEnd_1380287 : Nat := 472500448101697569643121

theorem tailTrace_1380287 : CollatzResearch.WordTrace tailWord_1380287 prefixEnd_1380287 472500448101697569643121 := by
  unfold tailWord_1380287
  simp only [CollatzResearch.WordTrace]
  refine ⟨50343202750463408096947115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33562135166975605397964743 50343202750463408096947115)
  ·
    refine ⟨75514804125695112145420673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50343202750463408096947115 75514804125695112145420673)
    ·
      refine ⟨56636103094271334109065505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75514804125695112145420673 56636103094271334109065505)
      ·
        refine ⟨42477077320703500581799129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56636103094271334109065505 42477077320703500581799129)
        ·
          refine ⟨31857807990527625436349347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42477077320703500581799129 31857807990527625436349347)
          ·
            refine ⟨47786711985791438154524021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31857807990527625436349347 47786711985791438154524021)
            ·
              refine ⟨4480004248667947326986627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47786711985791438154524021 4480004248667947326986627)
              ·
                refine ⟨6720006373001920990479941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4480004248667947326986627 6720006373001920990479941)
                ·
                  refine ⟨1260001194937860185714989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6720006373001920990479941 1260001194937860185714989)
                  ·
                    refine ⟨472500448101697569643121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1260001194937860185714989 472500448101697569643121)
                    ·
                      rfl

theorem cell22_1380287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 4, 3].length) (baseStart_1380287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1380287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1380287 prefixEnd_1380287 := by exact prefixLift 1380287
  have htrace : WordTrace (prefixWord ++ tailWord_1380287) baseStart_1380287 baseEnd_1380287 := by
    simpa [prefixWord, tailWord_1380287, baseEnd_1380287] using wordTrace_append hprefix tailTrace_1380287
  have hstable : (prefixWord ++ tailWord_1380287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380287).length < 2 ^ (prefixWord ++ tailWord_1380287).sum := by decide
  have hdescent : baseEnd_1380287 < baseStart_1380287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380332 : List Nat := [2, 2, 1, 1, 2, 1, 1, 4, 5, 3]
def baseStart_1380332 : Nat := 118140960795 + 1380332 * 2 ^ 59
def prefixEnd_1380332 : Nat := 4983230072969 + 3 ^ 40 * 1380332 * 2
def baseEnd_1380332 : Nat := 472515852521332452267983

theorem tailTrace_1380332 : CollatzResearch.WordTrace tailWord_1380332 prefixEnd_1380332 472515852521332452267983 := by
  unfold tailWord_1380332
  simp only [CollatzResearch.WordTrace]
  refine ⟨25172422017650190391167625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33563229356866920521556833 25172422017650190391167625)
  ·
    refine ⟨18879316513237642793375719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25172422017650190391167625 18879316513237642793375719)
    ·
      refine ⟨28318974769856464190063579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18879316513237642793375719 28318974769856464190063579)
      ·
        refine ⟨42478462154784696285095369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28318974769856464190063579 42478462154784696285095369)
        ·
          refine ⟨31858846616088522213821527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42478462154784696285095369 31858846616088522213821527)
          ·
            refine ⟨47788269924132783320732291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31858846616088522213821527 47788269924132783320732291)
            ·
              refine ⟨71682404886199174981098437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47788269924132783320732291 71682404886199174981098437)
              ·
                refine ⟨13440450916162345308955957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71682404886199174981098437 13440450916162345308955957)
                ·
                  refine ⟨1260042273390219872714621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13440450916162345308955957 1260042273390219872714621)
                  ·
                    refine ⟨472515852521332452267983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1260042273390219872714621 472515852521332452267983)
                    ·
                      rfl

theorem cell22_1380332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 3].length) (baseStart_1380332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1380332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1380332 prefixEnd_1380332 := by exact prefixLift 1380332
  have htrace : WordTrace (prefixWord ++ tailWord_1380332) baseStart_1380332 baseEnd_1380332 := by
    simpa [prefixWord, tailWord_1380332, baseEnd_1380332] using wordTrace_append hprefix tailTrace_1380332
  have hstable : (prefixWord ++ tailWord_1380332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380332).length < 2 ^ (prefixWord ++ tailWord_1380332).sum := by decide
  have hdescent : baseEnd_1380332 < baseStart_1380332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380349 : List Nat := [1, 4, 1, 1, 1, 2, 5, 1, 3, 3]
def baseStart_1380349 : Nat := 118140960795 + 1380349 * 2 ^ 59
def prefixEnd_1380349 : Nat := 4983230072969 + 3 ^ 40 * 1380349 * 2
def baseEnd_1380349 : Nat := 472521671968750074592931

theorem tailTrace_1380349 : CollatzResearch.WordTrace tailWord_1380349 prefixEnd_1380349 472521671968750074592931 := by
  unfold tailWord_1380349
  simp only [CollatzResearch.WordTrace]
  refine ⟨50345464076238792685704101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33563642717492528457136067 50345464076238792685704101)
  ·
    refine ⟨9439774514294773628569519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50345464076238792685704101 9439774514294773628569519)
    ·
      refine ⟨14159661771442160442854279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9439774514294773628569519 14159661771442160442854279)
      ·
        refine ⟨21239492657163240664281419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14159661771442160442854279 21239492657163240664281419)
        ·
          refine ⟨31859238985744860996422129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21239492657163240664281419 31859238985744860996422129)
          ·
            refine ⟨23894429239308645747316597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31859238985744860996422129 23894429239308645747316597)
            ·
              refine ⟨2240102741185185538810931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23894429239308645747316597 2240102741185185538810931)
              ·
                refine ⟨3360154111777778308216397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2240102741185185538810931 3360154111777778308216397)
                ·
                  refine ⟨1260057791916666865581149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3360154111777778308216397 1260057791916666865581149)
                  ·
                    refine ⟨472521671968750074592931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1260057791916666865581149 472521671968750074592931)
                    ·
                      rfl

theorem cell22_1380349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 1, 3, 3].length) (baseStart_1380349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1380349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1380349 prefixEnd_1380349 := by exact prefixLift 1380349
  have htrace : WordTrace (prefixWord ++ tailWord_1380349) baseStart_1380349 baseEnd_1380349 := by
    simpa [prefixWord, tailWord_1380349, baseEnd_1380349] using wordTrace_append hprefix tailTrace_1380349
  have hstable : (prefixWord ++ tailWord_1380349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380349).length < 2 ^ (prefixWord ++ tailWord_1380349).sum := by decide
  have hdescent : baseEnd_1380349 < baseStart_1380349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380473 : List Nat := [1, 2, 1, 3, 4, 2, 3, 1, 2, 3]
def baseStart_1380473 : Nat := 118140960795 + 1380473 * 2 ^ 59
def prefixEnd_1380473 : Nat := 4983230072969 + 3 ^ 40 * 1380473 * 2
def baseEnd_1380473 : Nat := 472564119702855084492551

theorem tailTrace_1380473 : CollatzResearch.WordTrace tailWord_1380473 prefixEnd_1380473 472564119702855084492551 := by
  unfold tailWord_1380473
  simp only [CollatzResearch.WordTrace]
  refine ⟨50349986727789561863218073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33566657818526374575478715 50349986727789561863218073)
  ·
    refine ⟨37762490045842171397413555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50349986727789561863218073 37762490045842171397413555)
    ·
      refine ⟨56643735068763257096120333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37762490045842171397413555 56643735068763257096120333)
      ·
        refine ⟨21241400650786221411045125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56643735068763257096120333 21241400650786221411045125)
        ·
          refine ⟨3982762622022416514570961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21241400650786221411045125 3982762622022416514570961)
          ·
            refine ⟨2987071966516812385928221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3982762622022416514570961 2987071966516812385928221)
            ·
              refine ⟨1120151987443804644723083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2987071966516812385928221 1120151987443804644723083)
              ·
                refine ⟨1680227981165706967084625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1120151987443804644723083 1680227981165706967084625)
                ·
                  refine ⟨1260170985874280225313469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1680227981165706967084625 1260170985874280225313469)
                  ·
                    refine ⟨472564119702855084492551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1260170985874280225313469 472564119702855084492551)
                    ·
                      rfl

theorem cell22_1380473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 3, 1, 2, 3].length) (baseStart_1380473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1380473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1380473 prefixEnd_1380473 := by exact prefixLift 1380473
  have htrace : WordTrace (prefixWord ++ tailWord_1380473) baseStart_1380473 baseEnd_1380473 := by
    simpa [prefixWord, tailWord_1380473, baseEnd_1380473] using wordTrace_append hprefix tailTrace_1380473
  have hstable : (prefixWord ++ tailWord_1380473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380473).length < 2 ^ (prefixWord ++ tailWord_1380473).sum := by decide
  have hdescent : baseEnd_1380473 < baseStart_1380473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380527 : List Nat := [1, 1, 2, 1, 2, 3, 1, 1, 2, 8]
def baseStart_1380527 : Nat := 118140960795 + 1380527 * 2 ^ 59
def prefixEnd_1380527 : Nat := 4983230072969 + 3 ^ 40 * 1380527 * 2
def baseEnd_1380527 : Nat := 472582605006416943642385

theorem tailTrace_1380527 : CollatzResearch.WordTrace tailWord_1380527 prefixEnd_1380527 472582605006416943642385 := by
  unfold tailWord_1380527
  simp only [CollatzResearch.WordTrace]
  refine ⟨50351956269593929085683835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33567970846395952723789223 50351956269593929085683835)
  ·
    refine ⟨75527934404390893628525753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50351956269593929085683835 75527934404390893628525753)
    ·
      refine ⟨56645950803293170221394315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75527934404390893628525753 56645950803293170221394315)
      ·
        refine ⟨84968926204939755332091473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56645950803293170221394315 84968926204939755332091473)
        ·
          refine ⟨63726694653704816499068605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84968926204939755332091473 63726694653704816499068605)
          ·
            refine ⟨23897510495139306187150727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63726694653704816499068605 23897510495139306187150727)
            ·
              refine ⟨35846265742708959280726091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23897510495139306187150727 35846265742708959280726091)
              ·
                refine ⟨53769398614063438921089137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35846265742708959280726091 53769398614063438921089137)
                ·
                  refine ⟨40327048960547579190816853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53769398614063438921089137 40327048960547579190816853)
                  ·
                    refine ⟨472582605006416943642385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 40327048960547579190816853 472582605006416943642385)
                    ·
                      rfl

theorem cell22_1380527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 8].length) (baseStart_1380527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1380527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1380527 prefixEnd_1380527 := by exact prefixLift 1380527
  have htrace : WordTrace (prefixWord ++ tailWord_1380527) baseStart_1380527 baseEnd_1380527 := by
    simpa [prefixWord, tailWord_1380527, baseEnd_1380527] using wordTrace_append hprefix tailTrace_1380527
  have hstable : (prefixWord ++ tailWord_1380527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380527).length < 2 ^ (prefixWord ++ tailWord_1380527).sum := by decide
  have hdescent : baseEnd_1380527 < baseStart_1380527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380576 : List Nat := [2, 1, 1, 3, 1, 3, 3, 4, 4]
def baseStart_1380576 : Nat := 118140960795 + 1380576 * 2 ^ 59
def prefixEnd_1380576 : Nat := 4983230072969 + 3 ^ 40 * 1380576 * 2
def baseEnd_1380576 : Nat := 157533126235932383055745

theorem tailTrace_1380576 : CollatzResearch.WordTrace tailWord_1380576 prefixEnd_1380576 157533126235932383055745 := by
  unfold tailWord_1380576
  simp only [CollatzResearch.WordTrace]
  refine ⟨25176871723208205227108791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33569162297610940302811721 25176871723208205227108791)
  ·
    refine ⟨37765307584812307840663187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25176871723208205227108791 37765307584812307840663187)
    ·
      refine ⟨56647961377218461760994781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37765307584812307840663187 56647961377218461760994781)
      ·
        refine ⟨21242985516456923160373043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56647961377218461760994781 21242985516456923160373043)
        ·
          refine ⟨31864478274685384740559565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21242985516456923160373043 31864478274685384740559565)
          ·
            refine ⟨11949179353007019277709837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31864478274685384740559565 11949179353007019277709837)
            ·
              refine ⟨4480942257377632229141189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11949179353007019277709837 4480942257377632229141189)
              ·
                refine ⟨840176673258306042963973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4480942257377632229141189 840176673258306042963973)
                ·
                  refine ⟨157533126235932383055745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 840176673258306042963973 157533126235932383055745)
                  ·
                    rfl

theorem cell22_1380576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 4, 4].length) (baseStart_1380576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1380576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1380576 prefixEnd_1380576 := by exact prefixLift 1380576
  have htrace : WordTrace (prefixWord ++ tailWord_1380576) baseStart_1380576 baseEnd_1380576 := by
    simpa [prefixWord, tailWord_1380576, baseEnd_1380576] using wordTrace_append hprefix tailTrace_1380576
  have hstable : (prefixWord ++ tailWord_1380576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380576).length < 2 ^ (prefixWord ++ tailWord_1380576).sum := by decide
  have hdescent : baseEnd_1380576 < baseStart_1380576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380591 : List Nat := [1, 1, 2, 1, 6, 2, 2, 1, 1, 5]
def baseStart_1380591 : Nat := 118140960795 + 1380591 * 2 ^ 59
def prefixEnd_1380591 : Nat := 4983230072969 + 3 ^ 40 * 1380591 * 2
def baseEnd_1380591 : Nat := 472604513514342110042189

theorem tailTrace_1380591 : CollatzResearch.WordTrace tailWord_1380591 prefixEnd_1380591 472604513514342110042189 := by
  unfold tailWord_1380591
  simp only [CollatzResearch.WordTrace]
  refine ⟨50354290541362068016013627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33569527027574712010675751 50354290541362068016013627)
  ·
    refine ⟨75531435812043102024020441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50354290541362068016013627 75531435812043102024020441)
    ·
      refine ⟨56648576859032326518015331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75531435812043102024020441 56648576859032326518015331)
      ·
        refine ⟨84972865288548489777022997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56648576859032326518015331 84972865288548489777022997)
        ·
          refine ⟨3983103060400710458297953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 84972865288548489777022997 3983103060400710458297953)
          ·
            refine ⟨2987327295300532843723465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3983103060400710458297953 2987327295300532843723465)
            ·
              refine ⟨2240495471475399632792599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2987327295300532843723465 2240495471475399632792599)
              ·
                refine ⟨3360743207213099449188899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2240495471475399632792599 3360743207213099449188899)
                ·
                  refine ⟨5041114810819649173783349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3360743207213099449188899 5041114810819649173783349)
                  ·
                    refine ⟨472604513514342110042189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5041114810819649173783349 472604513514342110042189)
                    ·
                      rfl

theorem cell22_1380591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 1, 1, 5].length) (baseStart_1380591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1380591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1380591 prefixEnd_1380591 := by exact prefixLift 1380591
  have htrace : WordTrace (prefixWord ++ tailWord_1380591) baseStart_1380591 baseEnd_1380591 := by
    simpa [prefixWord, tailWord_1380591, baseEnd_1380591] using wordTrace_append hprefix tailTrace_1380591
  have hstable : (prefixWord ++ tailWord_1380591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380591).length < 2 ^ (prefixWord ++ tailWord_1380591).sum := by decide
  have hdescent : baseEnd_1380591 < baseStart_1380591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380606 : List Nat := [4, 2, 2, 1, 1, 1, 3, 1, 1, 6]
def baseStart_1380606 : Nat := 118140960795 + 1380606 * 2 ^ 59
def prefixEnd_1380606 : Nat := 4983230072969 + 3 ^ 40 * 1380606 * 2
def baseEnd_1380606 : Nat := 472609648320887070917143

theorem tailTrace_1380606 : CollatzResearch.WordTrace tailWord_1380606 prefixEnd_1380606 472609648320887070917143 := by
  unfold tailWord_1380606
  simp only [CollatzResearch.WordTrace]
  refine ⟨6294354704538465697226209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33569891757538483718539781 6294354704538465697226209)
  ·
    refine ⟨4720766028403849272919657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6294354704538465697226209 4720766028403849272919657)
    ·
      refine ⟨3540574521302886954689743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4720766028403849272919657 3540574521302886954689743)
      ·
        refine ⟨5310861781954330432034615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3540574521302886954689743 5310861781954330432034615)
        ·
          refine ⟨7966292672931495648051923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5310861781954330432034615 7966292672931495648051923)
          ·
            refine ⟨11949439009397243472077885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7966292672931495648051923 11949439009397243472077885)
            ·
              refine ⟨4481039628523966302029207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11949439009397243472077885 4481039628523966302029207)
              ·
                refine ⟨6721559442785949453043811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4481039628523966302029207 6721559442785949453043811)
                ·
                  refine ⟨10082339164178924179565717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6721559442785949453043811 10082339164178924179565717)
                  ·
                    refine ⟨472609648320887070917143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10082339164178924179565717 472609648320887070917143)
                    ·
                      rfl

theorem cell22_1380606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_1380606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1380606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1380606 prefixEnd_1380606 := by exact prefixLift 1380606
  have htrace : WordTrace (prefixWord ++ tailWord_1380606) baseStart_1380606 baseEnd_1380606 := by
    simpa [prefixWord, tailWord_1380606, baseEnd_1380606] using wordTrace_append hprefix tailTrace_1380606
  have hstable : (prefixWord ++ tailWord_1380606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380606).length < 2 ^ (prefixWord ++ tailWord_1380606).sum := by decide
  have hdescent : baseEnd_1380606 < baseStart_1380606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380610 : List Nat := [3, 4, 1, 1, 2, 2, 2, 3, 4]
def baseStart_1380610 : Nat := 118140960795 + 1380610 * 2 ^ 59
def prefixEnd_1380610 : Nat := 4983230072969 + 3 ^ 40 * 1380610 * 2
def baseEnd_1380610 : Nat := 157537005867544131272377

theorem tailTrace_1380610 : CollatzResearch.WordTrace tailWord_1380610 prefixEnd_1380610 157537005867544131272377 := by
  unfold tailWord_1380610
  simp only [CollatzResearch.WordTrace]
  refine ⟨12588745882073308565238821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33569989018862156173970189 12588745882073308565238821)
  ·
    refine ⟨2360389852888745355982279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12588745882073308565238821 2360389852888745355982279)
    ·
      refine ⟨3540584779333118033973419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2360389852888745355982279 3540584779333118033973419)
      ·
        refine ⟨5310877168999677050960129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3540584779333118033973419 5310877168999677050960129)
        ·
          refine ⟨3983157876749757788220097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5310877168999677050960129 3983157876749757788220097)
          ·
            refine ⟨2987368407562318341165073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3983157876749757788220097 2987368407562318341165073)
            ·
              refine ⟨2240526305671738755873805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2987368407562318341165073 2240526305671738755873805)
              ·
                refine ⟨840197364626902033452677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2240526305671738755873805 840197364626902033452677)
                ·
                  refine ⟨157537005867544131272377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 840197364626902033452677 157537005867544131272377)
                  ·
                    rfl

theorem cell22_1380610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_1380610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1380610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1380610 prefixEnd_1380610 := by exact prefixLift 1380610
  have htrace : WordTrace (prefixWord ++ tailWord_1380610) baseStart_1380610 baseEnd_1380610 := by
    simpa [prefixWord, tailWord_1380610, baseEnd_1380610] using wordTrace_append hprefix tailTrace_1380610
  have hstable : (prefixWord ++ tailWord_1380610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380610).length < 2 ^ (prefixWord ++ tailWord_1380610).sum := by decide
  have hdescent : baseEnd_1380610 < baseStart_1380610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380612 : List Nat := [2, 3, 2, 2, 4, 1, 2, 1, 1, 4]
def baseStart_1380612 : Nat := 118140960795 + 1380612 * 2 ^ 59
def prefixEnd_1380612 : Nat := 4983230072969 + 3 ^ 40 * 1380612 * 2
def baseEnd_1380612 : Nat := 472611702243505055267125

theorem tailTrace_1380612 : CollatzResearch.WordTrace tailWord_1380612 prefixEnd_1380612 472611702243505055267125 := by
  unfold tailWord_1380612
  simp only [CollatzResearch.WordTrace]
  refine ⟨25177528237142994301264045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33570037649523992401685393 25177528237142994301264045)
  ·
    refine ⟨9441573088928622862974017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25177528237142994301264045 9441573088928622862974017)
    ·
      refine ⟨7081179816696467147230513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9441573088928622862974017 7081179816696467147230513)
      ·
        refine ⟨5310884862522350360422885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7081179816696467147230513 5310884862522350360422885)
        ·
          refine ⟨995790911722940692579291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5310884862522350360422885 995790911722940692579291)
          ·
            refine ⟨1493686367584411038868937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 995790911722940692579291 1493686367584411038868937)
            ·
              refine ⟨1120264775688308279151703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1493686367584411038868937 1120264775688308279151703)
              ·
                refine ⟨1680397163532462418727555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1120264775688308279151703 1680397163532462418727555)
                ·
                  refine ⟨2520595745298693628091333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1680397163532462418727555 2520595745298693628091333)
                  ·
                    refine ⟨472611702243505055267125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2520595745298693628091333 472611702243505055267125)
                    ·
                      rfl

theorem cell22_1380612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 2, 1, 1, 4].length) (baseStart_1380612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1380612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1380612 prefixEnd_1380612 := by exact prefixLift 1380612
  have htrace : WordTrace (prefixWord ++ tailWord_1380612) baseStart_1380612 baseEnd_1380612 := by
    simpa [prefixWord, tailWord_1380612, baseEnd_1380612] using wordTrace_append hprefix tailTrace_1380612
  have hstable : (prefixWord ++ tailWord_1380612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380612).length < 2 ^ (prefixWord ++ tailWord_1380612).sum := by decide
  have hdescent : baseEnd_1380612 < baseStart_1380612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380664 : List Nat := [2, 1, 2, 1, 3, 1, 2, 2, 1, 7]
def baseStart_1380664 : Nat := 118140960795 + 1380664 * 2 ^ 59
def prefixEnd_1380664 : Nat := 4983230072969 + 3 ^ 40 * 1380664 * 2
def baseEnd_1380664 : Nat := 472629502906194252966965

theorem tailTrace_1380664 : CollatzResearch.WordTrace tailWord_1380664 prefixEnd_1380664 472629502906194252966965 := by
  unfold tailWord_1380664
  simp only [CollatzResearch.WordTrace]
  refine ⟨25178476535048800741710523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33571302046731734322280697 25178476535048800741710523)
  ·
    refine ⟨37767714802573201112565785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25178476535048800741710523 37767714802573201112565785)
    ·
      refine ⟨28325786101929900834424339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37767714802573201112565785 28325786101929900834424339)
      ·
        refine ⟨42488679152894851251636509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28325786101929900834424339 42488679152894851251636509)
        ·
          refine ⟨15933254682335569219363691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42488679152894851251636509 15933254682335569219363691)
          ·
            refine ⟨23899882023503353829045537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15933254682335569219363691 23899882023503353829045537)
            ·
              refine ⟨17924911517627515371784153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23899882023503353829045537 17924911517627515371784153)
              ·
                refine ⟨13443683638220636528838115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17924911517627515371784153 13443683638220636528838115)
                ·
                  refine ⟨20165525457330954793257173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13443683638220636528838115 20165525457330954793257173)
                  ·
                    refine ⟨472629502906194252966965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20165525457330954793257173 472629502906194252966965)
                    ·
                      rfl

theorem cell22_1380664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 1, 7].length) (baseStart_1380664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1380664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1380664 prefixEnd_1380664 := by exact prefixLift 1380664
  have htrace : WordTrace (prefixWord ++ tailWord_1380664) baseStart_1380664 baseEnd_1380664 := by
    simpa [prefixWord, tailWord_1380664, baseEnd_1380664] using wordTrace_append hprefix tailTrace_1380664
  have hstable : (prefixWord ++ tailWord_1380664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380664).length < 2 ^ (prefixWord ++ tailWord_1380664).sum := by decide
  have hdescent : baseEnd_1380664 < baseStart_1380664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380700 : List Nat := [2, 2, 4, 3, 1, 1, 1, 3, 5]
def baseStart_1380700 : Nat := 118140960795 + 1380700 * 2 ^ 59
def prefixEnd_1380700 : Nat := 4983230072969 + 3 ^ 40 * 1380700 * 2
def baseEnd_1380700 : Nat := 157547275480634053022285

theorem tailTrace_1380700 : CollatzResearch.WordTrace tailWord_1380700 prefixEnd_1380700 157547275480634053022285 := by
  unfold tailWord_1380700
  simp only [CollatzResearch.WordTrace]
  refine ⟨25179133048983589815865777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33572177398644786421154369 25179133048983589815865777)
  ·
    refine ⟨18884349786737692361899333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25179133048983589815865777 18884349786737692361899333)
    ·
      refine ⟨3540815585013317317856125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18884349786737692361899333 3540815585013317317856125)
      ·
        refine ⟨1327805844379993994196047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3540815585013317317856125 1327805844379993994196047)
        ·
          refine ⟨1991708766569990991294071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1327805844379993994196047 1991708766569990991294071)
          ·
            refine ⟨2987563149854986486941107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1991708766569990991294071 2987563149854986486941107)
            ·
              refine ⟨4481344724782479730411661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2987563149854986486941107 4481344724782479730411661)
              ·
                refine ⟨1680504271793429898904373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4481344724782479730411661 1680504271793429898904373)
                ·
                  refine ⟨157547275480634053022285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1680504271793429898904373 157547275480634053022285)
                  ·
                    rfl

theorem cell22_1380700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 3, 5].length) (baseStart_1380700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1380700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1380700 prefixEnd_1380700 := by exact prefixLift 1380700
  have htrace : WordTrace (prefixWord ++ tailWord_1380700) baseStart_1380700 baseEnd_1380700 := by
    simpa [prefixWord, tailWord_1380700, baseEnd_1380700] using wordTrace_append hprefix tailTrace_1380700
  have hstable : (prefixWord ++ tailWord_1380700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380700).length < 2 ^ (prefixWord ++ tailWord_1380700).sum := by decide
  have hdescent : baseEnd_1380700 < baseStart_1380700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380738 : List Nat := [3, 4, 2, 1, 3, 1, 2, 2, 1, 3]
def baseStart_1380738 : Nat := 118140960795 + 1380738 * 2 ^ 59
def prefixEnd_1380738 : Nat := 4983230072969 + 3 ^ 40 * 1380738 * 2
def baseEnd_1380738 : Nat := 472654834618482726616739

theorem tailTrace_1380738 : CollatzResearch.WordTrace tailWord_1380738 prefixEnd_1380738 472654834618482726616739 := by
  unfold tailWord_1380738
  simp only [CollatzResearch.WordTrace]
  refine ⟨12589913017957378030403717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33573101381219674747743245 12589913017957378030403717)
  ·
    refine ⟨2360608690867008380700697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12589913017957378030403717 2360608690867008380700697)
    ·
      refine ⟨1770456518150256285525523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2360608690867008380700697 1770456518150256285525523)
      ·
        refine ⟨2655684777225384428288285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1770456518150256285525523 2655684777225384428288285)
        ·
          refine ⟨995881791459519160608107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2655684777225384428288285 995881791459519160608107)
          ·
            refine ⟨1493822687189278740912161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 995881791459519160608107 1493822687189278740912161)
            ·
              refine ⟨1120367015391959055684121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1493822687189278740912161 1120367015391959055684121)
              ·
                refine ⟨840275261543969291763091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1120367015391959055684121 840275261543969291763091)
                ·
                  refine ⟨1260412892315953937644637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 840275261543969291763091 1260412892315953937644637)
                  ·
                    refine ⟨472654834618482726616739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1260412892315953937644637 472654834618482726616739)
                    ·
                      rfl

theorem cell22_1380738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_1380738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1380738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1380738 prefixEnd_1380738 := by exact prefixLift 1380738
  have htrace : WordTrace (prefixWord ++ tailWord_1380738) baseStart_1380738 baseEnd_1380738 := by
    simpa [prefixWord, tailWord_1380738, baseEnd_1380738] using wordTrace_append hprefix tailTrace_1380738
  have hstable : (prefixWord ++ tailWord_1380738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380738).length < 2 ^ (prefixWord ++ tailWord_1380738).sum := by decide
  have hdescent : baseEnd_1380738 < baseStart_1380738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380739 : List Nat := [1, 1, 1, 3, 16]
def baseStart_1380739 : Nat := 118140960795 + 1380739 * 2 ^ 59
def prefixEnd_1380739 : Nat := 4983230072969 + 3 ^ 40 * 1380739 * 2
def baseEnd_1380739 : Nat := 1945083032670448795645

theorem tailTrace_1380739 : CollatzResearch.WordTrace tailWord_1380739 prefixEnd_1380739 1945083032670448795645 := by
  unfold tailWord_1380739
  simp only [CollatzResearch.WordTrace]
  refine ⟨50359688544825889292401271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33573125696550592861600847 50359688544825889292401271)
  ·
    refine ⟨75539532817238833938601907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50359688544825889292401271 75539532817238833938601907)
    ·
      refine ⟨113309299225858250907902861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75539532817238833938601907 113309299225858250907902861)
      ·
        refine ⟨42490987209696844090463573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113309299225858250907902861 42490987209696844090463573)
        ·
          refine ⟨1945083032670448795645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 16 42490987209696844090463573 1945083032670448795645)
          ·
            rfl

theorem cell22_1380739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 16].length) (baseStart_1380739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1380739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1380739 prefixEnd_1380739 := by exact prefixLift 1380739
  have htrace : WordTrace (prefixWord ++ tailWord_1380739) baseStart_1380739 baseEnd_1380739 := by
    simpa [prefixWord, tailWord_1380739, baseEnd_1380739] using wordTrace_append hprefix tailTrace_1380739
  have hstable : (prefixWord ++ tailWord_1380739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380739).length < 2 ^ (prefixWord ++ tailWord_1380739).sum := by decide
  have hdescent : baseEnd_1380739 < baseStart_1380739 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380745 : List Nat := [1, 2, 1, 1, 6, 1, 4, 2, 4]
def baseStart_1380745 : Nat := 118140960795 + 1380745 * 2 ^ 59
def prefixEnd_1380745 : Nat := 4983230072969 + 3 ^ 40 * 1380745 * 2
def baseEnd_1380745 : Nat := 157552410287179013897239

theorem tailTrace_1380745 : CollatzResearch.WordTrace tailWord_1380745 prefixEnd_1380745 157552410287179013897239 := by
  unfold tailWord_1380745
  simp only [CollatzResearch.WordTrace]
  refine ⟨50359907382804152317119689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33573271588536101544746459 50359907382804152317119689)
  ·
    refine ⟨37769930537103114237839767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50359907382804152317119689 37769930537103114237839767)
    ·
      refine ⟨56654895805654671356759651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37769930537103114237839767 56654895805654671356759651)
      ·
        refine ⟨84982343708482007035139477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56654895805654671356759651 84982343708482007035139477)
        ·
          refine ⟨3983547361335094079772163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 84982343708482007035139477 3983547361335094079772163)
          ·
            refine ⟨5975321042002641119658245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3983547361335094079772163 5975321042002641119658245)
            ·
              refine ⟨1120372695375495209935921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5975321042002641119658245 1120372695375495209935921)
              ·
                refine ⟨840279521531621407451941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1120372695375495209935921 840279521531621407451941)
                ·
                  refine ⟨157552410287179013897239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 840279521531621407451941 157552410287179013897239)
                  ·
                    rfl

theorem cell22_1380745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 4, 2, 4].length) (baseStart_1380745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1380745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1380745 prefixEnd_1380745 := by exact prefixLift 1380745
  have htrace : WordTrace (prefixWord ++ tailWord_1380745) baseStart_1380745 baseEnd_1380745 := by
    simpa [prefixWord, tailWord_1380745, baseEnd_1380745] using wordTrace_append hprefix tailTrace_1380745
  have hstable : (prefixWord ++ tailWord_1380745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380745).length < 2 ^ (prefixWord ++ tailWord_1380745).sum := by decide
  have hdescent : baseEnd_1380745 < baseStart_1380745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380760 : List Nat := [2, 1, 2, 5, 1, 1, 2, 3, 2, 3]
def baseStart_1380760 : Nat := 118140960795 + 1380760 * 2 ^ 59
def prefixEnd_1380760 : Nat := 4983230072969 + 3 ^ 40 * 1380760 * 2
def baseEnd_1380760 : Nat := 472662365668082002566671

theorem tailTrace_1380760 : CollatzResearch.WordTrace tailWord_1380760 prefixEnd_1380760 472662365668082002566671 := by
  unfold tailWord_1380760
  simp only [CollatzResearch.WordTrace]
  refine ⟨25180227238874904939457867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33573636318499873252610489 25180227238874904939457867)
  ·
    refine ⟨37770340858312357409186801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25180227238874904939457867 37770340858312357409186801)
    ·
      refine ⟨28327755643734268056890101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37770340858312357409186801 28327755643734268056890101)
      ·
        refine ⟨2655727091600087630333447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28327755643734268056890101 2655727091600087630333447)
        ·
          refine ⟨3983590637400131445500171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2655727091600087630333447 3983590637400131445500171)
          ·
            refine ⟨5975385956100197168250257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3983590637400131445500171 5975385956100197168250257)
            ·
              refine ⟨4481539467075147876187693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5975385956100197168250257 4481539467075147876187693)
              ·
                refine ⟨1680577300153180453570385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4481539467075147876187693 1680577300153180453570385)
                ·
                  refine ⟨1260432975114885340177789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1680577300153180453570385 1260432975114885340177789)
                  ·
                    refine ⟨472662365668082002566671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1260432975114885340177789 472662365668082002566671)
                    ·
                      rfl

theorem cell22_1380760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 3, 2, 3].length) (baseStart_1380760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1380760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1380760 prefixEnd_1380760 := by exact prefixLift 1380760
  have htrace : WordTrace (prefixWord ++ tailWord_1380760) baseStart_1380760 baseEnd_1380760 := by
    simpa [prefixWord, tailWord_1380760, baseEnd_1380760] using wordTrace_append hprefix tailTrace_1380760
  have hstable : (prefixWord ++ tailWord_1380760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380760).length < 2 ^ (prefixWord ++ tailWord_1380760).sum := by decide
  have hdescent : baseEnd_1380760 < baseStart_1380760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380775 : List Nat := [1, 1, 6, 1, 1, 4, 1, 1, 2, 4]
def baseStart_1380775 : Nat := 118140960795 + 1380775 * 2 ^ 59
def prefixEnd_1380775 : Nat := 4983230072969 + 3 ^ 40 * 1380775 * 2
def baseEnd_1380775 : Nat := 472667500474626963441625

theorem tailTrace_1380775 : CollatzResearch.WordTrace tailWord_1380775 prefixEnd_1380775 472667500474626963441625 := by
  unfold tailWord_1380775
  simp only [CollatzResearch.WordTrace]
  refine ⟨50361001572695467440711779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33574001048463644960474519 50361001572695467440711779)
  ·
    refine ⟨75541502359043201161067669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50361001572695467440711779 75541502359043201161067669)
    ·
      refine ⟨3541007923080150054425047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 75541502359043201161067669 3541007923080150054425047)
      ·
        refine ⟨5311511884620225081637571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3541007923080150054425047 5311511884620225081637571)
        ·
          refine ⟨7967267826930337622456357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5311511884620225081637571 7967267826930337622456357)
          ·
            refine ⟨1493862717549438304210567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7967267826930337622456357 1493862717549438304210567)
            ·
              refine ⟨2240794076324157456315851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1493862717549438304210567 2240794076324157456315851)
              ·
                refine ⟨3361191114486236184473777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2240794076324157456315851 3361191114486236184473777)
                ·
                  refine ⟨2520893335864677138355333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3361191114486236184473777 2520893335864677138355333)
                  ·
                    refine ⟨472667500474626963441625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2520893335864677138355333 472667500474626963441625)
                    ·
                      rfl

theorem cell22_1380775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_1380775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1380775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1380775 prefixEnd_1380775 := by exact prefixLift 1380775
  have htrace : WordTrace (prefixWord ++ tailWord_1380775) baseStart_1380775 baseEnd_1380775 := by
    simpa [prefixWord, tailWord_1380775, baseEnd_1380775] using wordTrace_append hprefix tailTrace_1380775
  have hstable : (prefixWord ++ tailWord_1380775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380775).length < 2 ^ (prefixWord ++ tailWord_1380775).sum := by decide
  have hdescent : baseEnd_1380775 < baseStart_1380775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380848 : List Nat := [2, 1, 1, 1, 3, 3, 1, 5, 1, 4]
def baseStart_1380848 : Nat := 118140960795 + 1380848 * 2 ^ 59
def prefixEnd_1380848 : Nat := 4983230072969 + 3 ^ 40 * 1380848 * 2
def baseEnd_1380848 : Nat := 472692489866479106366401

theorem tailTrace_1380848 : CollatzResearch.WordTrace tailWord_1380848 prefixEnd_1380848 472692489866479106366401 := by
  unfold tailWord_1380848
  simp only [CollatzResearch.WordTrace]
  refine ⟨25181832050715500454059599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33575776067620667272079465 25181832050715500454059599)
  ·
    refine ⟨37772748076073250681089399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25181832050715500454059599 37772748076073250681089399)
    ·
      refine ⟨56659122114109876021634099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37772748076073250681089399 56659122114109876021634099)
      ·
        refine ⟨84988683171164814032451149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56659122114109876021634099 84988683171164814032451149)
        ·
          refine ⟨31870756189186805262169181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84988683171164814032451149 31870756189186805262169181)
          ·
            refine ⟨11951533570945051973313443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31870756189186805262169181 11951533570945051973313443)
            ·
              refine ⟨17927300356417577959970165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11951533570945051973313443 17927300356417577959970165)
              ·
                refine ⟨1680684408414147933747203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17927300356417577959970165 1680684408414147933747203)
                ·
                  refine ⟨2521026612621221900620805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1680684408414147933747203 2521026612621221900620805)
                  ·
                    refine ⟨472692489866479106366401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2521026612621221900620805 472692489866479106366401)
                    ·
                      rfl

theorem cell22_1380848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 5, 1, 4].length) (baseStart_1380848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1380848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1380848 prefixEnd_1380848 := by exact prefixLift 1380848
  have htrace : WordTrace (prefixWord ++ tailWord_1380848) baseStart_1380848 baseEnd_1380848 := by
    simpa [prefixWord, tailWord_1380848, baseEnd_1380848] using wordTrace_append hprefix tailTrace_1380848
  have hstable : (prefixWord ++ tailWord_1380848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380848).length < 2 ^ (prefixWord ++ tailWord_1380848).sum := by decide
  have hdescent : baseEnd_1380848 < baseStart_1380848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380925 : List Nat := [1, 4, 1, 3, 2, 3, 1, 7]
def baseStart_1380925 : Nat := 118140960795 + 1380925 * 2 ^ 59
def prefixEnd_1380925 : Nat := 4983230072969 + 3 ^ 40 * 1380925 * 2
def baseEnd_1380925 : Nat := 52524316504452952465685

theorem tailTrace_1380925 : CollatzResearch.WordTrace tailWord_1380925 prefixEnd_1380925 52524316504452952465685 := by
  unfold tailWord_1380925
  simp only [CollatzResearch.WordTrace]
  refine ⟨50366472522152043058672229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33577648348101362039114819 50366472522152043058672229)
  ·
    refine ⟨9443713597903508073501043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50366472522152043058672229 9443713597903508073501043)
    ·
      refine ⟨14165570396855262110251565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9443713597903508073501043 14165570396855262110251565)
      ·
        refine ⟨5312088898820723291344337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14165570396855262110251565 5312088898820723291344337)
        ·
          refine ⟨3984066674115542468508253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5312088898820723291344337 3984066674115542468508253)
          ·
            refine ⟨1494025002793328425690595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3984066674115542468508253 1494025002793328425690595)
            ·
              refine ⟨2241037504189992638535893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1494025002793328425690595 2241037504189992638535893)
              ·
                refine ⟨52524316504452952465685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2241037504189992638535893 52524316504452952465685)
                ·
                  rfl

theorem cell22_1380925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 7].length) (baseStart_1380925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1380925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1380925 prefixEnd_1380925 := by exact prefixLift 1380925
  have htrace : WordTrace (prefixWord ++ tailWord_1380925) baseStart_1380925 baseEnd_1380925 := by
    simpa [prefixWord, tailWord_1380925, baseEnd_1380925] using wordTrace_append hprefix tailTrace_1380925
  have hstable : (prefixWord ++ tailWord_1380925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380925).length < 2 ^ (prefixWord ++ tailWord_1380925).sum := by decide
  have hdescent : baseEnd_1380925 < baseStart_1380925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380940 : List Nat := [2, 2, 1, 3, 1, 2, 3, 2, 3, 3]
def baseStart_1380940 : Nat := 118140960795 + 1380940 * 2 ^ 59
def prefixEnd_1380940 : Nat := 4983230072969 + 3 ^ 40 * 1380940 * 2
def baseEnd_1380940 : Nat := 472723983346621533066119

theorem tailTrace_1380940 : CollatzResearch.WordTrace tailWord_1380940 prefixEnd_1380940 472723983346621533066119 := by
  unfold tailWord_1380940
  simp only [CollatzResearch.WordTrace]
  refine ⟨25183509808548850310234137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33578013078065133746978849 25183509808548850310234137)
  ·
    refine ⟨18887632356411637732675603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25183509808548850310234137 18887632356411637732675603)
    ·
      refine ⟨28331448534617456599013405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18887632356411637732675603 28331448534617456599013405)
      ·
        refine ⟨10624293200481546224630027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28331448534617456599013405 10624293200481546224630027)
        ·
          refine ⟨15936439800722319336945041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10624293200481546224630027 15936439800722319336945041)
          ·
            refine ⟨11952329850541739502708781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15936439800722319336945041 11952329850541739502708781)
            ·
              refine ⟨4482123693953152313515793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11952329850541739502708781 4482123693953152313515793)
              ·
                refine ⟨3361592770464864235136845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4482123693953152313515793 3361592770464864235136845)
                ·
                  refine ⟨1260597288924324088176317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3361592770464864235136845 1260597288924324088176317)
                  ·
                    refine ⟨472723983346621533066119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1260597288924324088176317 472723983346621533066119)
                    ·
                      rfl

theorem cell22_1380940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 2, 3, 3].length) (baseStart_1380940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1380940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1380940 prefixEnd_1380940 := by exact prefixLift 1380940
  have htrace : WordTrace (prefixWord ++ tailWord_1380940) baseStart_1380940 baseEnd_1380940 := by
    simpa [prefixWord, tailWord_1380940, baseEnd_1380940] using wordTrace_append hprefix tailTrace_1380940
  have hstable : (prefixWord ++ tailWord_1380940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380940).length < 2 ^ (prefixWord ++ tailWord_1380940).sum := by decide
  have hdescent : baseEnd_1380940 < baseStart_1380940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380974 : List Nat := [4, 1, 2, 2, 2, 1, 2, 4, 1, 3]
def baseStart_1380974 : Nat := 118140960795 + 1380974 * 2 ^ 59
def prefixEnd_1380974 : Nat := 4983230072969 + 3 ^ 40 * 1380974 * 2
def baseEnd_1380974 : Nat := 472735622241456777716015

theorem tailTrace_1380974 : CollatzResearch.WordTrace tailWord_1380974 prefixEnd_1380974 472735622241456777716015 := by
  unfold tailWord_1380974
  simp only [CollatzResearch.WordTrace]
  refine ⟨6296032462371815553400747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33578839799316349618137317 6296032462371815553400747)
  ·
    refine ⟨9444048693557723330101121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6296032462371815553400747 9444048693557723330101121)
    ·
      refine ⟨7083036520168292497575841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9444048693557723330101121 7083036520168292497575841)
      ·
        refine ⟨5312277390126219373181881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7083036520168292497575841 5312277390126219373181881)
        ·
          refine ⟨3984208042594664529886411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5312277390126219373181881 3984208042594664529886411)
          ·
            refine ⟨5976312063891996794829617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3984208042594664529886411 5976312063891996794829617)
            ·
              refine ⟨4482234047918997596122213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5976312063891996794829617 4482234047918997596122213)
              ·
                refine ⟨840418883984812049272915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4482234047918997596122213 840418883984812049272915)
                ·
                  refine ⟨1260628325977218073909373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 840418883984812049272915 1260628325977218073909373)
                  ·
                    refine ⟨472735622241456777716015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1260628325977218073909373 472735622241456777716015)
                    ·
                      rfl

theorem cell22_1380974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 4, 1, 3].length) (baseStart_1380974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1380974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1380974 prefixEnd_1380974 := by exact prefixLift 1380974
  have htrace : WordTrace (prefixWord ++ tailWord_1380974) baseStart_1380974 baseEnd_1380974 := by
    simpa [prefixWord, tailWord_1380974, baseEnd_1380974] using wordTrace_append hprefix tailTrace_1380974
  have hstable : (prefixWord ++ tailWord_1380974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380974).length < 2 ^ (prefixWord ++ tailWord_1380974).sum := by decide
  have hdescent : baseEnd_1380974 < baseStart_1380974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380983 : List Nat := [1, 1, 3, 1, 1, 3, 2, 1, 5, 4]
def baseStart_1380983 : Nat := 118140960795 + 1380983 * 2 ^ 59
def prefixEnd_1380983 : Nat := 4983230072969 + 3 ^ 40 * 1380983 * 2
def baseEnd_1380983 : Nat := 472738703125383754240987

theorem tailTrace_1380983 : CollatzResearch.WordTrace tailWord_1380983 prefixEnd_1380983 472738703125383754240987 := by
  unfold tailWord_1380983
  simp only [CollatzResearch.WordTrace]
  refine ⟨50368587955941918964283603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33579058637294612642855735 50368587955941918964283603)
  ·
    refine ⟨75552881933912878446425405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50368587955941918964283603 75552881933912878446425405)
    ·
      refine ⟨28332330725217329417409527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75552881933912878446425405 28332330725217329417409527)
      ·
        refine ⟨42498496087825994126114291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28332330725217329417409527 42498496087825994126114291)
        ·
          refine ⟨63747744131738991189171437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42498496087825994126114291 63747744131738991189171437)
          ·
            refine ⟨23905404049402121695939289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63747744131738991189171437 23905404049402121695939289)
            ·
              refine ⟨17929053037051591271954467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23905404049402121695939289 17929053037051591271954467)
              ·
                refine ⟨26893579555577386907931701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17929053037051591271954467 26893579555577386907931701)
                ·
                  refine ⟨2521273083335380022618597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26893579555577386907931701 2521273083335380022618597)
                  ·
                    refine ⟨472738703125383754240987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2521273083335380022618597 472738703125383754240987)
                    ·
                      rfl

theorem cell22_1380983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 5, 4].length) (baseStart_1380983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1380983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1380983 prefixEnd_1380983 := by exact prefixLift 1380983
  have htrace : WordTrace (prefixWord ++ tailWord_1380983) baseStart_1380983 baseEnd_1380983 := by
    simpa [prefixWord, tailWord_1380983, baseEnd_1380983] using wordTrace_append hprefix tailTrace_1380983
  have hstable : (prefixWord ++ tailWord_1380983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380983).length < 2 ^ (prefixWord ++ tailWord_1380983).sum := by decide
  have hdescent : baseEnd_1380983 < baseStart_1380983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381043 : List Nat := [1, 1, 1, 2, 3, 4, 1, 9]
def baseStart_1381043 : Nat := 118140960795 + 1381043 * 2 ^ 59
def prefixEnd_1381043 : Nat := 4983230072969 + 3 ^ 40 * 1381043 * 2
def baseEnd_1381043 : Nat := 52528804705729288637867

theorem tailTrace_1381043 : CollatzResearch.WordTrace tailWord_1381043 prefixEnd_1381043 52528804705729288637867 := by
  unfold tailWord_1381043
  simp only [CollatzResearch.WordTrace]
  refine ⟨50370776335724549211467783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33580517557149699474311855 50370776335724549211467783)
  ·
    refine ⟨75556164503586823817201675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50370776335724549211467783 75556164503586823817201675)
    ·
      refine ⟨113334246755380235725802513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75556164503586823817201675 113334246755380235725802513)
      ·
        refine ⟨85000685066535176794351885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113334246755380235725802513 85000685066535176794351885)
        ·
          refine ⟨31875256899950691297881957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85000685066535176794351885 31875256899950691297881957)
          ·
            refine ⟨5976610668740754618352867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31875256899950691297881957 5976610668740754618352867)
            ·
              refine ⟨8964916003111131927529301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5976610668740754618352867 8964916003111131927529301)
              ·
                refine ⟨52528804705729288637867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8964916003111131927529301 52528804705729288637867)
                ·
                  rfl

theorem cell22_1381043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 9].length) (baseStart_1381043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1381043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1381043 prefixEnd_1381043 := by exact prefixLift 1381043
  have htrace : WordTrace (prefixWord ++ tailWord_1381043) baseStart_1381043 baseEnd_1381043 := by
    simpa [prefixWord, tailWord_1381043, baseEnd_1381043] using wordTrace_append hprefix tailTrace_1381043
  have hstable : (prefixWord ++ tailWord_1381043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381043).length < 2 ^ (prefixWord ++ tailWord_1381043).sum := by decide
  have hdescent : baseEnd_1381043 < baseStart_1381043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381060 : List Nat := [2, 3, 3, 1, 1, 2, 2, 8]
def baseStart_1381060 : Nat := 118140960795 + 1381060 * 2 ^ 59
def prefixEnd_1381060 : Nat := 4983230072969 + 3 ^ 40 * 1381060 * 2
def baseEnd_1381060 : Nat := 52529451310997913340639

theorem tailTrace_1381060 : CollatzResearch.WordTrace tailWord_1381060 prefixEnd_1381060 52529451310997913340639 := by
  unfold tailWord_1381060
  simp only [CollatzResearch.WordTrace]
  refine ⟨25185698188331480557418317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33580930917775307409891089 25185698188331480557418317)
  ·
    refine ⟨9444636820624305209031869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25185698188331480557418317 9444636820624305209031869)
    ·
      refine ⟨3541738807734114453386951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9444636820624305209031869 3541738807734114453386951)
      ·
        refine ⟨5312608211601171680080427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3541738807734114453386951 5312608211601171680080427)
        ·
          refine ⟨7968912317401757520120641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5312608211601171680080427 7968912317401757520120641)
          ·
            refine ⟨5976684238051318140090481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7968912317401757520120641 5976684238051318140090481)
            ·
              refine ⟨4482513178538488605067861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5976684238051318140090481 4482513178538488605067861)
              ·
                refine ⟨52529451310997913340639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4482513178538488605067861 52529451310997913340639)
                ·
                  rfl

theorem cell22_1381060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 8].length) (baseStart_1381060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1381060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1381060 prefixEnd_1381060 := by exact prefixLift 1381060
  have htrace : WordTrace (prefixWord ++ tailWord_1381060) baseStart_1381060 baseEnd_1381060 := by
    simpa [prefixWord, tailWord_1381060, baseEnd_1381060] using wordTrace_append hprefix tailTrace_1381060
  have hstable : (prefixWord ++ tailWord_1381060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381060).length < 2 ^ (prefixWord ++ tailWord_1381060).sum := by decide
  have hdescent : baseEnd_1381060 < baseStart_1381060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381077 : List Nat := [1, 3, 2, 5, 2, 9]
def baseStart_1381077 : Nat := 118140960795 + 1381077 * 2 ^ 59
def prefixEnd_1381077 : Nat := 4983230072969 + 3 ^ 40 * 1381077 * 2
def baseEnd_1381077 : Nat := 5836677546251837560379

theorem tailTrace_1381077 : CollatzResearch.WordTrace tailWord_1381077 prefixEnd_1381077 5836677546251837560379 := by
  unfold tailWord_1381077
  simp only [CollatzResearch.WordTrace]
  refine ⟨50372016417601373018205485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33581344278400915345470323 50372016417601373018205485)
  ·
    refine ⟨18889506156600514881827057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50372016417601373018205485 18889506156600514881827057)
    ·
      refine ⟨14167129617450386161370293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18889506156600514881827057 14167129617450386161370293)
      ·
        refine ⟨1328168401635973702628465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14167129617450386161370293 1328168401635973702628465)
        ·
          refine ⟨996126301226980276971349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1328168401635973702628465 996126301226980276971349)
          ·
            refine ⟨5836677546251837560379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 996126301226980276971349 5836677546251837560379)
            ·
              rfl

theorem cell22_1381077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 9].length) (baseStart_1381077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1381077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1381077 prefixEnd_1381077 := by exact prefixLift 1381077
  have htrace : WordTrace (prefixWord ++ tailWord_1381077) baseStart_1381077 baseEnd_1381077 := by
    simpa [prefixWord, tailWord_1381077, baseEnd_1381077] using wordTrace_append hprefix tailTrace_1381077
  have hstable : (prefixWord ++ tailWord_1381077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381077).length < 2 ^ (prefixWord ++ tailWord_1381077).sum := by decide
  have hdescent : baseEnd_1381077 < baseStart_1381077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381105 : List Nat := [1, 2, 2, 2, 2, 2, 1, 5, 5]
def baseStart_1381105 : Nat := 118140960795 + 1381105 * 2 ^ 59
def prefixEnd_1381105 : Nat := 4983230072969 + 3 ^ 40 * 1381105 * 2
def baseEnd_1381105 : Nat := 157593488739538700896871

theorem tailTrace_1381105 : CollatzResearch.WordTrace tailWord_1381105 prefixEnd_1381105 157593488739538700896871 := by
  unfold tailWord_1381105
  simp only [CollatzResearch.WordTrace]
  refine ⟨50373037661499933800224769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33582025107666622533483179 50373037661499933800224769)
  ·
    refine ⟨37779778246124950350168577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50373037661499933800224769 37779778246124950350168577)
    ·
      refine ⟨28334833684593712762626433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37779778246124950350168577 28334833684593712762626433)
      ·
        refine ⟨21251125263445284571969825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28334833684593712762626433 21251125263445284571969825)
        ·
          refine ⟨15938343947583963428977369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21251125263445284571969825 15938343947583963428977369)
          ·
            refine ⟨11953757960687972571733027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15938343947583963428977369 11953757960687972571733027)
            ·
              refine ⟨17930636941031958857599541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11953757960687972571733027 17930636941031958857599541)
              ·
                refine ⟨1680997213221746142899957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17930636941031958857599541 1680997213221746142899957)
                ·
                  refine ⟨157593488739538700896871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1680997213221746142899957 157593488739538700896871)
                  ·
                    rfl

theorem cell22_1381105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 5, 5].length) (baseStart_1381105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1381105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1381105 prefixEnd_1381105 := by exact prefixLift 1381105
  have htrace : WordTrace (prefixWord ++ tailWord_1381105) baseStart_1381105 baseEnd_1381105 := by
    simpa [prefixWord, tailWord_1381105, baseEnd_1381105] using wordTrace_append hprefix tailTrace_1381105
  have hstable : (prefixWord ++ tailWord_1381105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381105).length < 2 ^ (prefixWord ++ tailWord_1381105).sum := by decide
  have hdescent : baseEnd_1381105 < baseStart_1381105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381201 : List Nat := [1, 2, 2, 1, 6, 1, 3, 2, 4]
def baseStart_1381201 : Nat := 118140960795 + 1381201 * 2 ^ 59
def prefixEnd_1381201 : Nat := 4983230072969 + 3 ^ 40 * 1381201 * 2
def baseEnd_1381201 : Nat := 157604442993501284096773

theorem tailTrace_1381201 : CollatzResearch.WordTrace tailWord_1381201 prefixEnd_1381201 157604442993501284096773 := by
  unfold tailWord_1381201
  simp only [CollatzResearch.WordTrace]
  refine ⟨50376539069152142195719457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33584359379434761463812971 50376539069152142195719457)
  ·
    refine ⟨37782404301864106646789593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50376539069152142195719457 37782404301864106646789593)
    ·
      refine ⟨28336803226398079985092195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37782404301864106646789593 28336803226398079985092195)
      ·
        refine ⟨42505204839597119977638293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28336803226398079985092195 42505204839597119977638293)
        ·
          refine ⟨1992431476856114998951795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 42505204839597119977638293 1992431476856114998951795)
          ·
            refine ⟨2988647215284172498427693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1992431476856114998951795 2988647215284172498427693)
            ·
              refine ⟨1120742705731564686910385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2988647215284172498427693 1120742705731564686910385)
              ·
                refine ⟨840557029298673515182789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1120742705731564686910385 840557029298673515182789)
                ·
                  refine ⟨157604442993501284096773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 840557029298673515182789 157604442993501284096773)
                  ·
                    rfl

theorem cell22_1381201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 3, 2, 4].length) (baseStart_1381201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1381201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1381201 prefixEnd_1381201 := by exact prefixLift 1381201
  have htrace : WordTrace (prefixWord ++ tailWord_1381201) baseStart_1381201 baseEnd_1381201 := by
    simpa [prefixWord, tailWord_1381201, baseEnd_1381201] using wordTrace_append hprefix tailTrace_1381201
  have hstable : (prefixWord ++ tailWord_1381201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381201).length < 2 ^ (prefixWord ++ tailWord_1381201).sum := by decide
  have hdescent : baseEnd_1381201 < baseStart_1381201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381212 : List Nat := [2, 2, 4, 2, 1, 1, 1, 9]
def baseStart_1381212 : Nat := 118140960795 + 1381212 * 2 ^ 59
def prefixEnd_1381212 : Nat := 4983230072969 + 3 ^ 40 * 1381212 * 2
def baseEnd_1381212 : Nat := 52535232722811498918365

theorem tailTrace_1381212 : CollatzResearch.WordTrace tailWord_1381212 prefixEnd_1381212 52535232722811498918365 := by
  unfold tailWord_1381212
  simp only [CollatzResearch.WordTrace]
  refine ⟨25188470136056145537184945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33584626848074860716246593 25188470136056145537184945)
  ·
    refine ⟨18891352602042109152888709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25188470136056145537184945 18891352602042109152888709)
    ·
      refine ⟨3542128612882895466166633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18891352602042109152888709 3542128612882895466166633)
      ·
        refine ⟨2656596459662171599624975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3542128612882895466166633 2656596459662171599624975)
        ·
          refine ⟨3984894689493257399437463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2656596459662171599624975 3984894689493257399437463)
          ·
            refine ⟨5977342034239886099156195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3984894689493257399437463 5977342034239886099156195)
            ·
              refine ⟨8966013051359829148734293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5977342034239886099156195 8966013051359829148734293)
              ·
                refine ⟨52535232722811498918365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8966013051359829148734293 52535232722811498918365)
                ·
                  rfl

theorem cell22_1381212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 9].length) (baseStart_1381212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1381212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1381212 prefixEnd_1381212 := by exact prefixLift 1381212
  have htrace : WordTrace (prefixWord ++ tailWord_1381212) baseStart_1381212 baseEnd_1381212 := by
    simpa [prefixWord, tailWord_1381212, baseEnd_1381212] using wordTrace_append hprefix tailTrace_1381212
  have hstable : (prefixWord ++ tailWord_1381212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381212).length < 2 ^ (prefixWord ++ tailWord_1381212).sum := by decide
  have hdescent : baseEnd_1381212 < baseStart_1381212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381227 : List Nat := [1, 1, 1, 1, 2, 2, 4, 4, 3, 3]
def baseStart_1381227 : Nat := 118140960795 + 1381227 * 2 ^ 59
def prefixEnd_1381227 : Nat := 4983230072969 + 3 ^ 40 * 1381227 * 2
def baseEnd_1381227 : Nat := 472822229311848451140239

theorem tailTrace_1381227 : CollatzResearch.WordTrace tailWord_1381227 prefixEnd_1381227 472822229311848451140239 := by
  unfold tailWord_1381227
  simp only [CollatzResearch.WordTrace]
  refine ⟨50377487367057948636165935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33584991578038632424110623 50377487367057948636165935)
  ·
    refine ⟨75566231050586922954248903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50377487367057948636165935 75566231050586922954248903)
    ·
      refine ⟨113349346575880384431373355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75566231050586922954248903 113349346575880384431373355)
      ·
        refine ⟨170024019863820576647060033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113349346575880384431373355 170024019863820576647060033)
        ·
          refine ⟨127518014897865432485295025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170024019863820576647060033 127518014897865432485295025)
          ·
            refine ⟨95638511173399074363971269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127518014897865432485295025 95638511173399074363971269)
            ·
              refine ⟨17932220845012326443244613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95638511173399074363971269 17932220845012326443244613)
              ·
                refine ⟨3362291408439811208108365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17932220845012326443244613 3362291408439811208108365)
                ·
                  refine ⟨1260859278164929203040637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3362291408439811208108365 1260859278164929203040637)
                  ·
                    refine ⟨472822229311848451140239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1260859278164929203040637 472822229311848451140239)
                    ·
                      rfl

theorem cell22_1381227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4, 3, 3].length) (baseStart_1381227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1381227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1381227 prefixEnd_1381227 := by exact prefixLift 1381227
  have htrace : WordTrace (prefixWord ++ tailWord_1381227) baseStart_1381227 baseEnd_1381227 := by
    simpa [prefixWord, tailWord_1381227, baseEnd_1381227] using wordTrace_append hprefix tailTrace_1381227
  have hstable : (prefixWord ++ tailWord_1381227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381227).length < 2 ^ (prefixWord ++ tailWord_1381227).sum := by decide
  have hdescent : baseEnd_1381227 < baseStart_1381227 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381240 : List Nat := [2, 1, 2, 1, 1, 1, 1, 6, 7]
def baseStart_1381240 : Nat := 118140960795 + 1381240 * 2 ^ 59
def prefixEnd_1381240 : Nat := 4983230072969 + 3 ^ 40 * 1381240 * 2
def baseEnd_1381240 : Nat := 157608893159173583521733

theorem tailTrace_1381240 : CollatzResearch.WordTrace tailWord_1381240 prefixEnd_1381240 157608893159173583521733 := by
  unfold tailWord_1381240
  simp only [CollatzResearch.WordTrace]
  refine ⟨25188980758005425928194587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33585307677340567904259449 25188980758005425928194587)
  ·
    refine ⟨37783471137008138892291881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25188980758005425928194587 37783471137008138892291881)
    ·
      refine ⟨28337603352756104169218911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37783471137008138892291881 28337603352756104169218911)
      ·
        refine ⟨42506405029134156253828367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28337603352756104169218911 42506405029134156253828367)
        ·
          refine ⟨63759607543701234380742551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42506405029134156253828367 63759607543701234380742551)
          ·
            refine ⟨95639411315551851571113827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63759607543701234380742551 95639411315551851571113827)
            ·
              refine ⟨143459116973327777356670741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95639411315551851571113827 143459116973327777356670741)
              ·
                refine ⟨6724646108124739563593941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 143459116973327777356670741 6724646108124739563593941)
                ·
                  refine ⟨157608893159173583521733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6724646108124739563593941 157608893159173583521733)
                  ·
                    rfl

theorem cell22_1381240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 7].length) (baseStart_1381240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1381240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1381240 prefixEnd_1381240 := by exact prefixLift 1381240
  have htrace : WordTrace (prefixWord ++ tailWord_1381240) baseStart_1381240 baseEnd_1381240 := by
    simpa [prefixWord, tailWord_1381240, baseEnd_1381240] using wordTrace_append hprefix tailTrace_1381240
  have hstable : (prefixWord ++ tailWord_1381240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381240).length < 2 ^ (prefixWord ++ tailWord_1381240).sum := by decide
  have hdescent : baseEnd_1381240 < baseStart_1381240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381250 : List Nat := [3, 4, 2, 2, 1, 1, 2, 2, 2, 3]
def baseStart_1381250 : Nat := 118140960795 + 1381250 * 2 ^ 59
def prefixEnd_1381250 : Nat := 4983230072969 + 3 ^ 40 * 1381250 * 2
def baseEnd_1381250 : Nat := 472830102681884057815169

theorem tailTrace_1381250 : CollatzResearch.WordTrace tailWord_1381250 prefixEnd_1381250 472830102681884057815169 := by
  unfold tailWord_1381250
  simp only [CollatzResearch.WordTrace]
  refine ⟨12594581561493655891063301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33585550830649749042835469 12594581561493655891063301)
  ·
    refine ⟨2361484042780060479574369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12594581561493655891063301 2361484042780060479574369)
    ·
      refine ⟨1771113032085045359680777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2361484042780060479574369 1771113032085045359680777)
      ·
        refine ⟨1328334774063784019760583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1771113032085045359680777 1328334774063784019760583)
        ·
          refine ⟨1992502161095676029640875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1328334774063784019760583 1992502161095676029640875)
          ·
            refine ⟨2988753241643514044461313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1992502161095676029640875 2988753241643514044461313)
            ·
              refine ⟨2241564931232635533345985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2988753241643514044461313 2241564931232635533345985)
              ·
                refine ⟨1681173698424476650009489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2241564931232635533345985 1681173698424476650009489)
                ·
                  refine ⟨1260880273818357487507117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1681173698424476650009489 1260880273818357487507117)
                  ·
                    refine ⟨472830102681884057815169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1260880273818357487507117 472830102681884057815169)
                    ·
                      rfl

theorem cell22_1381250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_1381250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1381250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1381250 prefixEnd_1381250 := by exact prefixLift 1381250
  have htrace : WordTrace (prefixWord ++ tailWord_1381250) baseStart_1381250 baseEnd_1381250 := by
    simpa [prefixWord, tailWord_1381250, baseEnd_1381250] using wordTrace_append hprefix tailTrace_1381250
  have hstable : (prefixWord ++ tailWord_1381250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381250).length < 2 ^ (prefixWord ++ tailWord_1381250).sum := by decide
  have hdescent : baseEnd_1381250 < baseStart_1381250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381257 : List Nat := [1, 2, 1, 1, 5, 2, 1, 4, 5]
def baseStart_1381257 : Nat := 118140960795 + 1381257 * 2 ^ 59
def prefixEnd_1381257 : Nat := 4983230072969 + 3 ^ 40 * 1381257 * 2
def baseEnd_1381257 : Nat := 157610832974979457630049

theorem tailTrace_1381257 : CollatzResearch.WordTrace tailWord_1381257 prefixEnd_1381257 157610832974979457630049 := by
  unfold tailWord_1381257
  simp only [CollatzResearch.WordTrace]
  refine ⟨50378581556949263759758025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33585721037966175839838683 50378581556949263759758025)
  ·
    refine ⟨37783936167711947819818519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50378581556949263759758025 37783936167711947819818519)
    ·
      refine ⟨56675904251567921729727779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37783936167711947819818519 56675904251567921729727779)
      ·
        refine ⟨85013856377351882594591669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56675904251567921729727779 85013856377351882594591669)
        ·
          refine ⟨7970049035376738993242969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 85013856377351882594591669 7970049035376738993242969)
          ·
            refine ⟨5977536776532554244932227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7970049035376738993242969 5977536776532554244932227)
            ·
              refine ⟨8966305164798831367398341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5977536776532554244932227 8966305164798831367398341)
              ·
                refine ⟨1681182218399780881387189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8966305164798831367398341 1681182218399780881387189)
                ·
                  refine ⟨157610832974979457630049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1681182218399780881387189 157610832974979457630049)
                  ·
                    rfl

theorem cell22_1381257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 4, 5].length) (baseStart_1381257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1381257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1381257 prefixEnd_1381257 := by exact prefixLift 1381257
  have htrace : WordTrace (prefixWord ++ tailWord_1381257) baseStart_1381257 baseEnd_1381257 := by
    simpa [prefixWord, tailWord_1381257, baseEnd_1381257] using wordTrace_append hprefix tailTrace_1381257
  have hstable : (prefixWord ++ tailWord_1381257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381257).length < 2 ^ (prefixWord ++ tailWord_1381257).sum := by decide
  have hdescent : baseEnd_1381257 < baseStart_1381257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381304 : List Nat := [2, 1, 2, 1, 2, 5, 1, 3, 1, 4]
def baseStart_1381304 : Nat := 118140960795 + 1381304 * 2 ^ 59
def prefixEnd_1381304 : Nat := 4983230072969 + 3 ^ 40 * 1381304 * 2
def baseEnd_1381304 : Nat := 472848587985445916965003

theorem tailTrace_1381304 : CollatzResearch.WordTrace tailWord_1381304 prefixEnd_1381304 472848587985445916965003 := by
  unfold tailWord_1381304
  simp only [CollatzResearch.WordTrace]
  refine ⟨25190147893889495393359483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33586863858519327191145977 25190147893889495393359483)
  ·
    refine ⟨37785221840834243090039225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25190147893889495393359483 37785221840834243090039225)
    ·
      refine ⟨28338916380625682317529419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37785221840834243090039225 28338916380625682317529419)
      ·
        refine ⟨42508374570938523476294129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28338916380625682317529419 42508374570938523476294129)
        ·
          refine ⟨31881280928203892607220597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42508374570938523476294129 31881280928203892607220597)
          ·
            refine ⟨2988870087019114931926931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31881280928203892607220597 2988870087019114931926931)
            ·
              refine ⟨4483305130528672397890397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2988870087019114931926931 4483305130528672397890397)
              ·
                refine ⟨1681239423948252149208899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4483305130528672397890397 1681239423948252149208899)
                ·
                  refine ⟨2521859135922378223813349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1681239423948252149208899 2521859135922378223813349)
                  ·
                    refine ⟨472848587985445916965003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2521859135922378223813349 472848587985445916965003)
                    ·
                      rfl

theorem cell22_1381304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 3, 1, 4].length) (baseStart_1381304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1381304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1381304 prefixEnd_1381304 := by exact prefixLift 1381304
  have htrace : WordTrace (prefixWord ++ tailWord_1381304) baseStart_1381304 baseEnd_1381304 := by
    simpa [prefixWord, tailWord_1381304, baseEnd_1381304] using wordTrace_append hprefix tailTrace_1381304
  have hstable : (prefixWord ++ tailWord_1381304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381304).length < 2 ^ (prefixWord ++ tailWord_1381304).sum := by decide
  have hdescent : baseEnd_1381304 < baseStart_1381304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381319 : List Nat := [1, 1, 4, 1, 1, 2, 4, 4, 4]
def baseStart_1381319 : Nat := 118140960795 + 1381319 * 2 ^ 59
def prefixEnd_1381319 : Nat := 4983230072969 + 3 ^ 40 * 1381319 * 2
def baseEnd_1381319 : Nat := 157617907597330292613319

theorem tailTrace_1381319 : CollatzResearch.WordTrace tailWord_1381319 prefixEnd_1381319 157617907597330292613319 := by
  unfold tailWord_1381319
  simp only [CollatzResearch.WordTrace]
  refine ⟨50380842882724648348515011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33587228588483098899010007 50380842882724648348515011)
  ·
    refine ⟨75571264324086972522772517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50380842882724648348515011 75571264324086972522772517)
    ·
      refine ⟨14169612060766307348019847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75571264324086972522772517 14169612060766307348019847)
      ·
        refine ⟨21254418091149461022029771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14169612060766307348019847 21254418091149461022029771)
        ·
          refine ⟨31881627136724191533044657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21254418091149461022029771 31881627136724191533044657)
          ·
            refine ⟨23911220352543143649783493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31881627136724191533044657 23911220352543143649783493)
            ·
              refine ⟨4483353816101839434334405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23911220352543143649783493 4483353816101839434334405)
              ·
                refine ⟨840628840519094893937701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4483353816101839434334405 840628840519094893937701)
                ·
                  refine ⟨157617907597330292613319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 840628840519094893937701 157617907597330292613319)
                  ·
                    rfl

theorem cell22_1381319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 4, 4].length) (baseStart_1381319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1381319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1381319 prefixEnd_1381319 := by exact prefixLift 1381319
  have htrace : WordTrace (prefixWord ++ tailWord_1381319) baseStart_1381319 baseEnd_1381319 := by
    simpa [prefixWord, tailWord_1381319, baseEnd_1381319] using wordTrace_append hprefix tailTrace_1381319
  have hstable : (prefixWord ++ tailWord_1381319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381319).length < 2 ^ (prefixWord ++ tailWord_1381319).sum := by decide
  have hdescent : baseEnd_1381319 < baseStart_1381319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381347 : List Nat := [1, 1, 1, 6, 1, 1, 3, 8]
def baseStart_1381347 : Nat := 118140960795 + 1381347 * 2 ^ 59
def prefixEnd_1381347 : Nat := 4983230072969 + 3 ^ 40 * 1381347 * 2
def baseEnd_1381347 : Nat := 52540367529356459793319

theorem tailTrace_1381347 : CollatzResearch.WordTrace tailWord_1381347 prefixEnd_1381347 52540367529356459793319 := by
  unfold tailWord_1381347
  simp only [CollatzResearch.WordTrace]
  refine ⟨50381864126623209130534295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33587909417748806087022863 50381864126623209130534295)
  ·
    refine ⟨75572796189934813695801443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50381864126623209130534295 75572796189934813695801443)
    ·
      refine ⟨113359194284902220543702165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75572796189934813695801443 113359194284902220543702165)
      ·
        refine ⟨5313712232104791587986039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 113359194284902220543702165 5313712232104791587986039)
        ·
          refine ⟨7970568348157187381979059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5313712232104791587986039 7970568348157187381979059)
          ·
            refine ⟨11955852522235781072968589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7970568348157187381979059 11955852522235781072968589)
            ·
              refine ⟨4483444695838417902363221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11955852522235781072968589 4483444695838417902363221)
              ·
                refine ⟨52540367529356459793319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4483444695838417902363221 52540367529356459793319)
                ·
                  rfl

theorem cell22_1381347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 8].length) (baseStart_1381347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1381347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1381347 prefixEnd_1381347 := by exact prefixLift 1381347
  have htrace : WordTrace (prefixWord ++ tailWord_1381347) baseStart_1381347 baseEnd_1381347 := by
    simpa [prefixWord, tailWord_1381347, baseEnd_1381347] using wordTrace_append hprefix tailTrace_1381347
  have hstable : (prefixWord ++ tailWord_1381347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381347).length < 2 ^ (prefixWord ++ tailWord_1381347).sum := by decide
  have hdescent : baseEnd_1381347 < baseStart_1381347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381366 : List Nat := [5, 1, 1, 1, 3, 2, 1, 2, 2, 4]
def baseStart_1381366 : Nat := 118140960795 + 1381366 * 2 ^ 59
def prefixEnd_1381366 : Nat := 4983230072969 + 3 ^ 40 * 1381366 * 2
def baseEnd_1381366 : Nat := 472869811852498421914813

theorem tailTrace_1381366 : CollatzResearch.WordTrace tailWord_1381366 prefixEnd_1381366 472869811852498421914813 := by
  unfold tailWord_1381366
  simp only [CollatzResearch.WordTrace]
  refine ⟨3148909819597148460967247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33588371409036250250317301 3148909819597148460967247)
  ·
    refine ⟨4723364729395722691450871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3148909819597148460967247 4723364729395722691450871)
    ·
      refine ⟨7085047094093584037176307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4723364729395722691450871 7085047094093584037176307)
      ·
        refine ⟨10627570641140376055764461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7085047094093584037176307 10627570641140376055764461)
        ·
          refine ⟨3985338990427641020911673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10627570641140376055764461 3985338990427641020911673)
          ·
            refine ⟨2989004242820730765683755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3985338990427641020911673 2989004242820730765683755)
            ·
              refine ⟨4483506364231096148525633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2989004242820730765683755 4483506364231096148525633)
              ·
                refine ⟨3362629773173322111394225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4483506364231096148525633 3362629773173322111394225)
                ·
                  refine ⟨2521972329879991583545669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3362629773173322111394225 2521972329879991583545669)
                  ·
                    refine ⟨472869811852498421914813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2521972329879991583545669 472869811852498421914813)
                    ·
                      rfl

theorem cell22_1381366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_1381366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1381366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1381366 prefixEnd_1381366 := by exact prefixLift 1381366
  have htrace : WordTrace (prefixWord ++ tailWord_1381366) baseStart_1381366 baseEnd_1381366 := by
    simpa [prefixWord, tailWord_1381366, baseEnd_1381366] using wordTrace_append hprefix tailTrace_1381366
  have hstable : (prefixWord ++ tailWord_1381366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381366).length < 2 ^ (prefixWord ++ tailWord_1381366).sum := by decide
  have hdescent : baseEnd_1381366 < baseStart_1381366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381430 : List Nat := [5, 1, 2, 1, 1, 3, 1, 4, 1, 3]
def baseStart_1381430 : Nat := 118140960795 + 1381430 * 2 ^ 59
def prefixEnd_1381430 : Nat := 4983230072969 + 3 ^ 40 * 1381430 * 2
def baseEnd_1381430 : Nat := 472891720360423588314617

theorem tailTrace_1381430 : CollatzResearch.WordTrace tailWord_1381430 prefixEnd_1381430 472891720360423588314617 := by
  unfold tailWord_1381430
  simp only [CollatzResearch.WordTrace]
  refine ⟨3149055711582657144112859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33589927590215009537203829 3149055711582657144112859)
  ·
    refine ⟨4723583567373985716169289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3149055711582657144112859 4723583567373985716169289)
    ·
      refine ⟨3542687675530489287126967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4723583567373985716169289 3542687675530489287126967)
      ·
        refine ⟨5314031513295733930690451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3542687675530489287126967 5314031513295733930690451)
        ·
          refine ⟨7971047269943600896035677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5314031513295733930690451 7971047269943600896035677)
          ·
            refine ⟨2989142726228850336013379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7971047269943600896035677 2989142726228850336013379)
            ·
              refine ⟨4483714089343275504020069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2989142726228850336013379 4483714089343275504020069)
              ·
                refine ⟨840696391751864157003763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4483714089343275504020069 840696391751864157003763)
                ·
                  refine ⟨1261044587627796235505645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 840696391751864157003763 1261044587627796235505645)
                  ·
                    refine ⟨472891720360423588314617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1261044587627796235505645 472891720360423588314617)
                    ·
                      rfl

theorem cell22_1381430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_1381430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1381430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1381430 prefixEnd_1381430 := by exact prefixLift 1381430
  have htrace : WordTrace (prefixWord ++ tailWord_1381430) baseStart_1381430 baseEnd_1381430 := by
    simpa [prefixWord, tailWord_1381430, baseEnd_1381430] using wordTrace_append hprefix tailTrace_1381430
  have hstable : (prefixWord ++ tailWord_1381430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381430).length < 2 ^ (prefixWord ++ tailWord_1381430).sum := by decide
  have hdescent : baseEnd_1381430 < baseStart_1381430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381441 : List Nat := [1, 2, 5, 1, 3, 1, 1, 1, 2, 5]
def baseStart_1381441 : Nat := 118140960795 + 1381441 * 2 ^ 59
def prefixEnd_1381441 : Nat := 4983230072969 + 3 ^ 40 * 1381441 * 2
def baseEnd_1381441 : Nat := 472895485885223226289583

theorem tailTrace_1381441 : CollatzResearch.WordTrace tailWord_1381441 prefixEnd_1381441 472895485885223226289583 := by
  unfold tailWord_1381441
  simp only [CollatzResearch.WordTrace]
  refine ⟨50385292588282663184456177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33590195058855108789637451 50385292588282663184456177)
  ·
    refine ⟨37788969441211997388342133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50385292588282663184456177 37788969441211997388342133)
    ·
      refine ⟨3542715885113624755157075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37788969441211997388342133 3542715885113624755157075)
      ·
        refine ⟨5314073827670437132735613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3542715885113624755157075 5314073827670437132735613)
        ·
          refine ⟨1992777685376413924775855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5314073827670437132735613 1992777685376413924775855)
          ·
            refine ⟨2989166528064620887163783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1992777685376413924775855 2989166528064620887163783)
            ·
              refine ⟨4483749792096931330745675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2989166528064620887163783 4483749792096931330745675)
              ·
                refine ⟨6725624688145396996118513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4483749792096931330745675 6725624688145396996118513)
                ·
                  refine ⟨5044218516109047747088885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6725624688145396996118513 5044218516109047747088885)
                  ·
                    refine ⟨472895485885223226289583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5044218516109047747088885 472895485885223226289583)
                    ·
                      rfl

theorem cell22_1381441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_1381441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1381441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1381441 prefixEnd_1381441 := by exact prefixLift 1381441
  have htrace : WordTrace (prefixWord ++ tailWord_1381441) baseStart_1381441 baseEnd_1381441 := by
    simpa [prefixWord, tailWord_1381441, baseEnd_1381441] using wordTrace_append hprefix tailTrace_1381441
  have hstable : (prefixWord ++ tailWord_1381441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381441).length < 2 ^ (prefixWord ++ tailWord_1381441).sum := by decide
  have hdescent : baseEnd_1381441 < baseStart_1381441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381454 : List Nat := [4, 1, 1, 1, 1, 3, 3, 2, 6]
def baseStart_1381454 : Nat := 118140960795 + 1381454 * 2 ^ 59
def prefixEnd_1381454 : Nat := 4983230072969 + 3 ^ 40 * 1381454 * 2
def baseEnd_1381454 : Nat := 157633312016965175238181

theorem tailTrace_1381454 : CollatzResearch.WordTrace tailWord_1381454 prefixEnd_1381454 157633312016965175238181 := by
  unfold tailWord_1381454
  simp only [CollatzResearch.WordTrace]
  refine ⟨6298220842154445800584927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33590511158157044269786277 6298220842154445800584927)
  ·
    refine ⟨9447331263231668700877391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6298220842154445800584927 9447331263231668700877391)
    ·
      refine ⟨14170996894847503051316087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9447331263231668700877391 14170996894847503051316087)
      ·
        refine ⟨21256495342271254576974131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14170996894847503051316087 21256495342271254576974131)
        ·
          refine ⟨31884743013406881865461197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21256495342271254576974131 31884743013406881865461197)
          ·
            refine ⟨11956778630027580699547949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31884743013406881865461197 11956778630027580699547949)
            ·
              refine ⟨4483791986260342762330481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11956778630027580699547949 4483791986260342762330481)
              ·
                refine ⟨3362843989695257071747861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4483791986260342762330481 3362843989695257071747861)
                ·
                  refine ⟨157633312016965175238181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3362843989695257071747861 157633312016965175238181)
                  ·
                    rfl

theorem cell22_1381454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 2, 6].length) (baseStart_1381454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1381454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1381454 prefixEnd_1381454 := by exact prefixLift 1381454
  have htrace : WordTrace (prefixWord ++ tailWord_1381454) baseStart_1381454 baseEnd_1381454 := by
    simpa [prefixWord, tailWord_1381454, baseEnd_1381454] using wordTrace_append hprefix tailTrace_1381454
  have hstable : (prefixWord ++ tailWord_1381454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381454).length < 2 ^ (prefixWord ++ tailWord_1381454).sum := by decide
  have hdescent : baseEnd_1381454 < baseStart_1381454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381471 : List Nat := [1, 1, 2, 3, 1, 1, 6, 3, 4]
def baseStart_1381471 : Nat := 118140960795 + 1381471 * 2 ^ 59
def prefixEnd_1381471 : Nat := 4983230072969 + 3 ^ 40 * 1381471 * 2
def baseEnd_1381471 : Nat := 157635251832771049346497

theorem tailTrace_1381471 : CollatzResearch.WordTrace tailWord_1381471 prefixEnd_1381471 157635251832771049346497 := by
  unfold tailWord_1381471
  simp only [CollatzResearch.WordTrace]
  refine ⟨50386386778173978308048267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33590924518782652205365511 50386386778173978308048267)
  ·
    refine ⟨75579580167260967462072401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50386386778173978308048267 75579580167260967462072401)
    ·
      refine ⟨56684685125445725596554301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75579580167260967462072401 56684685125445725596554301)
      ·
        refine ⟨21256756922042147098707863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56684685125445725596554301 21256756922042147098707863)
        ·
          refine ⟨31885135383063220648061795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21256756922042147098707863 31885135383063220648061795)
          ·
            refine ⟨47827703074594830972092693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31885135383063220648061795 47827703074594830972092693)
            ·
              refine ⟨2241923581621632701816845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 47827703074594830972092693 2241923581621632701816845)
              ·
                refine ⟨840721343108112263181317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2241923581621632701816845 840721343108112263181317)
                ·
                  refine ⟨157635251832771049346497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 840721343108112263181317 157635251832771049346497)
                  ·
                    rfl

theorem cell22_1381471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 3, 4].length) (baseStart_1381471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1381471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1381471 prefixEnd_1381471 := by exact prefixLift 1381471
  have htrace : WordTrace (prefixWord ++ tailWord_1381471) baseStart_1381471 baseEnd_1381471 := by
    simpa [prefixWord, tailWord_1381471, baseEnd_1381471] using wordTrace_append hprefix tailTrace_1381471
  have hstable : (prefixWord ++ tailWord_1381471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381471).length < 2 ^ (prefixWord ++ tailWord_1381471).sum := by decide
  have hdescent : baseEnd_1381471 < baseStart_1381471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381484 : List Nat := [2, 2, 1, 1, 3, 2, 2, 1, 4, 4]
def baseStart_1381484 : Nat := 118140960795 + 1381484 * 2 ^ 59
def prefixEnd_1381484 : Nat := 4983230072969 + 3 ^ 40 * 1381484 * 2
def baseEnd_1381484 : Nat := 472910205663985447464451

theorem tailTrace_1381484 : CollatzResearch.WordTrace tailWord_1381484 prefixEnd_1381484 472910205663985447464451 := by
  unfold tailWord_1381484
  simp only [CollatzResearch.WordTrace]
  refine ⟨25193430463563440764135753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33591240618084587685514337 25193430463563440764135753)
  ·
    refine ⟨18895072847672580573101815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25193430463563440764135753 18895072847672580573101815)
    ·
      refine ⟨28342609271508870859652723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18895072847672580573101815 28342609271508870859652723)
      ·
        refine ⟨42513913907263306289479085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28342609271508870859652723 42513913907263306289479085)
        ·
          refine ⟨15942717715223739858554657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42513913907263306289479085 15942717715223739858554657)
          ·
            refine ⟨11957038286417804893915993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15942717715223739858554657 11957038286417804893915993)
            ·
              refine ⟨8967778714813353670436995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11957038286417804893915993 8967778714813353670436995)
              ·
                refine ⟨13451668072220030505655493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8967778714813353670436995 13451668072220030505655493)
                ·
                  refine ⟨2522187763541255719810405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13451668072220030505655493 2522187763541255719810405)
                  ·
                    refine ⟨472910205663985447464451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2522187763541255719810405 472910205663985447464451)
                    ·
                      rfl

theorem cell22_1381484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 4].length) (baseStart_1381484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1381484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1381484 prefixEnd_1381484 := by exact prefixLift 1381484
  have htrace : WordTrace (prefixWord ++ tailWord_1381484) baseStart_1381484 baseEnd_1381484 := by
    simpa [prefixWord, tailWord_1381484, baseEnd_1381484] using wordTrace_append hprefix tailTrace_1381484
  have hstable : (prefixWord ++ tailWord_1381484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381484).length < 2 ^ (prefixWord ++ tailWord_1381484).sum := by decide
  have hdescent : baseEnd_1381484 < baseStart_1381484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381514 : List Nat := [3, 1, 2, 3, 1, 1, 1, 1, 2, 7]
def baseStart_1381514 : Nat := 118140960795 + 1381514 * 2 ^ 59
def prefixEnd_1381514 : Nat := 4983230072969 + 3 ^ 40 * 1381514 * 2
def baseEnd_1381514 : Nat := 472920475277075369214359

theorem tailTrace_1381514 : CollatzResearch.WordTrace tailWord_1381514 prefixEnd_1381514 472920475277075369214359 := by
  unfold tailWord_1381514
  simp only [CollatzResearch.WordTrace]
  refine ⟨12596988779254549162965899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33591970078012131101242397 12596988779254549162965899)
  ·
    refine ⟨18895483168881823744448849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12596988779254549162965899 18895483168881823744448849)
    ·
      refine ⟨14171612376661367808336637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18895483168881823744448849 14171612376661367808336637)
      ·
        refine ⟨5314354641248012928126239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14171612376661367808336637 5314354641248012928126239)
        ·
          refine ⟨7971531961872019392189359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5314354641248012928126239 7971531961872019392189359)
          ·
            refine ⟨11957297942808029088284039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7971531961872019392189359 11957297942808029088284039)
            ·
              refine ⟨17935946914212043632426059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11957297942808029088284039 17935946914212043632426059)
              ·
                refine ⟨26903920371318065448639089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17935946914212043632426059 26903920371318065448639089)
                ·
                  refine ⟨20177940278488549086479317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26903920371318065448639089 20177940278488549086479317)
                  ·
                    refine ⟨472920475277075369214359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20177940278488549086479317 472920475277075369214359)
                    ·
                      rfl

theorem cell22_1381514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_1381514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1381514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1381514 prefixEnd_1381514 := by exact prefixLift 1381514
  have htrace : WordTrace (prefixWord ++ tailWord_1381514) baseStart_1381514 baseEnd_1381514 := by
    simpa [prefixWord, tailWord_1381514, baseEnd_1381514] using wordTrace_append hprefix tailTrace_1381514
  have hstable : (prefixWord ++ tailWord_1381514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381514).length < 2 ^ (prefixWord ++ tailWord_1381514).sum := by decide
  have hdescent : baseEnd_1381514 < baseStart_1381514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381559 : List Nat := [1, 1, 3, 1, 4, 1, 2, 1, 1, 7]
def baseStart_1381559 : Nat := 118140960795 + 1381559 * 2 ^ 59
def prefixEnd_1381559 : Nat := 4983230072969 + 3 ^ 40 * 1381559 * 2
def baseEnd_1381559 : Nat := 472935879696710251839221

theorem tailTrace_1381559 : CollatzResearch.WordTrace tailWord_1381559 prefixEnd_1381559 472935879696710251839221 := by
  unfold tailWord_1381559
  simp only [CollatzResearch.WordTrace]
  refine ⟨50389596401855169337251731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33593064267903446224834487 50389596401855169337251731)
  ·
    refine ⟨75584394602782754005877597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50389596401855169337251731 75584394602782754005877597)
    ·
      refine ⟨28344147976043532752204099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75584394602782754005877597 28344147976043532752204099)
      ·
        refine ⟨42516221964065299128306149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28344147976043532752204099 42516221964065299128306149)
        ·
          refine ⟨7971791618262243586557403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42516221964065299128306149 7971791618262243586557403)
          ·
            refine ⟨11957687427393365379836105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7971791618262243586557403 11957687427393365379836105)
            ·
              refine ⟨8968265570545024034877079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11957687427393365379836105 8968265570545024034877079)
              ·
                refine ⟨13452398355817536052315619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8968265570545024034877079 13452398355817536052315619)
                ·
                  refine ⟨20178597533726304078473429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13452398355817536052315619 20178597533726304078473429)
                  ·
                    refine ⟨472935879696710251839221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20178597533726304078473429 472935879696710251839221)
                    ·
                      rfl

theorem cell22_1381559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 7].length) (baseStart_1381559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1381559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1381559 prefixEnd_1381559 := by exact prefixLift 1381559
  have htrace : WordTrace (prefixWord ++ tailWord_1381559) baseStart_1381559 baseEnd_1381559 := by
    simpa [prefixWord, tailWord_1381559, baseEnd_1381559] using wordTrace_append hprefix tailTrace_1381559
  have hstable : (prefixWord ++ tailWord_1381559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381559).length < 2 ^ (prefixWord ++ tailWord_1381559).sum := by decide
  have hdescent : baseEnd_1381559 < baseStart_1381559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381561 : List Nat := [1, 2, 1, 4, 1, 4, 1, 3, 5]
def baseStart_1381561 : Nat := 118140960795 + 1381561 * 2 ^ 59
def prefixEnd_1381561 : Nat := 4983230072969 + 3 ^ 40 * 1381561 * 2
def baseEnd_1381561 : Nat := 157645521445860971096405

theorem tailTrace_1381561 : CollatzResearch.WordTrace tailWord_1381561 prefixEnd_1381561 157645521445860971096405 := by
  unfold tailWord_1381561
  simp only [CollatzResearch.WordTrace]
  refine ⟨50389669347847923678824537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33593112898565282452549691 50389669347847923678824537)
  ·
    refine ⟨37792252010885942759118403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50389669347847923678824537 37792252010885942759118403)
    ·
      refine ⟨56688378016328914138677605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37792252010885942759118403 56688378016328914138677605)
      ·
        refine ⟨10629070878061671401002051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56688378016328914138677605 10629070878061671401002051)
        ·
          refine ⟨15943606317092507101503077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10629070878061671401002051 15943606317092507101503077)
          ·
            refine ⟨2989426184454845081531827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15943606317092507101503077 2989426184454845081531827)
            ·
              refine ⟨4484139276682267622297741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2989426184454845081531827 4484139276682267622297741)
              ·
                refine ⟨1681552228755850358361653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4484139276682267622297741 1681552228755850358361653)
                ·
                  refine ⟨157645521445860971096405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1681552228755850358361653 157645521445860971096405)
                  ·
                    rfl

theorem cell22_1381561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 3, 5].length) (baseStart_1381561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1381561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1381561 prefixEnd_1381561 := by exact prefixLift 1381561
  have htrace : WordTrace (prefixWord ++ tailWord_1381561) baseStart_1381561 baseEnd_1381561 := by
    simpa [prefixWord, tailWord_1381561, baseEnd_1381561] using wordTrace_append hprefix tailTrace_1381561
  have hstable : (prefixWord ++ tailWord_1381561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381561).length < 2 ^ (prefixWord ++ tailWord_1381561).sum := by decide
  have hdescent : baseEnd_1381561 < baseStart_1381561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381591 : List Nat := [1, 1, 3, 2, 1, 2, 2, 5, 1, 4]
def baseStart_1381591 : Nat := 118140960795 + 1381591 * 2 ^ 59
def prefixEnd_1381591 : Nat := 4983230072969 + 3 ^ 40 * 1381591 * 2
def baseEnd_1381591 : Nat := 472946833950672835039123

theorem tailTrace_1381591 : CollatzResearch.WordTrace tailWord_1381591 prefixEnd_1381591 472946833950672835039123 := by
  unfold tailWord_1381591
  simp only [CollatzResearch.WordTrace]
  refine ⟨50390763537739238802416627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33593842358492825868277751 50390763537739238802416627)
  ·
    refine ⟨75586145306608858203624941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50390763537739238802416627 75586145306608858203624941)
    ·
      refine ⟨28344804489978321826359353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75586145306608858203624941 28344804489978321826359353)
      ·
        refine ⟨21258603367483741369769515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28344804489978321826359353 21258603367483741369769515)
        ·
          refine ⟨31887905051225612054654273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21258603367483741369769515 31887905051225612054654273)
          ·
            refine ⟨23915928788419209040990705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31887905051225612054654273 23915928788419209040990705)
            ·
              refine ⟨17936946591314406780743029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23915928788419209040990705 17936946591314406780743029)
              ·
                refine ⟨1681588742935725635694659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17936946591314406780743029 1681588742935725635694659)
                ·
                  refine ⟨2522383114403588453541989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1681588742935725635694659 2522383114403588453541989)
                  ·
                    refine ⟨472946833950672835039123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2522383114403588453541989 472946833950672835039123)
                    ·
                      rfl

theorem cell22_1381591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 5, 1, 4].length) (baseStart_1381591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1381591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1381591 prefixEnd_1381591 := by exact prefixLift 1381591
  have htrace : WordTrace (prefixWord ++ tailWord_1381591) baseStart_1381591 baseEnd_1381591 := by
    simpa [prefixWord, tailWord_1381591, baseEnd_1381591] using wordTrace_append hprefix tailTrace_1381591
  have hstable : (prefixWord ++ tailWord_1381591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381591).length < 2 ^ (prefixWord ++ tailWord_1381591).sum := by decide
  have hdescent : baseEnd_1381591 < baseStart_1381591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381640 : List Nat := [2, 1, 3, 2, 4, 1, 2, 3, 4]
def baseStart_1381640 : Nat := 118140960795 + 1381640 * 2 ^ 59
def prefixEnd_1381640 : Nat := 4983230072969 + 3 ^ 40 * 1381640 * 2
def baseEnd_1381640 : Nat := 157654535884017680187991

theorem tailTrace_1381640 : CollatzResearch.WordTrace tailWord_1381640 prefixEnd_1381640 157654535884017680187991 := by
  unfold tailWord_1381640
  simp only [CollatzResearch.WordTrace]
  refine ⟨25196275357280860085475187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33595033809707813447300249 25196275357280860085475187)
  ·
    refine ⟨37794413035921290128212781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25196275357280860085475187 37794413035921290128212781)
    ·
      refine ⟨14172904888470483798079793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37794413035921290128212781 14172904888470483798079793)
      ·
        refine ⟨10629678666352862848559845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14172904888470483798079793 10629678666352862848559845)
        ·
          refine ⟨1993064749941161784104971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10629678666352862848559845 1993064749941161784104971)
          ·
            refine ⟨2989597124911742676157457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1993064749941161784104971 2989597124911742676157457)
            ·
              refine ⟨2242197843683807007118093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2989597124911742676157457 2242197843683807007118093)
              ·
                refine ⟨840824191381427627669285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2242197843683807007118093 840824191381427627669285)
                ·
                  refine ⟨157654535884017680187991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 840824191381427627669285 157654535884017680187991)
                  ·
                    rfl

theorem cell22_1381640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 3, 4].length) (baseStart_1381640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1381640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1381640 prefixEnd_1381640 := by exact prefixLift 1381640
  have htrace : WordTrace (prefixWord ++ tailWord_1381640) baseStart_1381640 baseEnd_1381640 := by
    simpa [prefixWord, tailWord_1381640, baseEnd_1381640] using wordTrace_append hprefix tailTrace_1381640
  have hstable : (prefixWord ++ tailWord_1381640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381640).length < 2 ^ (prefixWord ++ tailWord_1381640).sum := by decide
  have hdescent : baseEnd_1381640 < baseStart_1381640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381672 : List Nat := [2, 1, 5, 1, 2, 2, 3, 1, 2, 3]
def baseStart_1381672 : Nat := 118140960795 + 1381672 * 2 ^ 59
def prefixEnd_1381672 : Nat := 4983230072969 + 3 ^ 40 * 1381672 * 2
def baseEnd_1381672 : Nat := 472974561906015623763875

theorem tailTrace_1381672 : CollatzResearch.WordTrace tailWord_1381672 prefixEnd_1381672 472974561906015623763875 := by
  unfold tailWord_1381672
  simp only [CollatzResearch.WordTrace]
  refine ⟨25196858925222894818057635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33595811900297193090743513 25196858925222894818057635)
  ·
    refine ⟨37795288387834342227086453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25196858925222894818057635 37795288387834342227086453)
    ·
      refine ⟨3543308286359469583789355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37795288387834342227086453 3543308286359469583789355)
      ·
        refine ⟨5314962429539204375684033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3543308286359469583789355 5314962429539204375684033)
        ·
          refine ⟨3986221822154403281763025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5314962429539204375684033 3986221822154403281763025)
          ·
            refine ⟨2989666366615802461322269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3986221822154403281763025 2989666366615802461322269)
            ·
              refine ⟨1121124887480925922995851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2989666366615802461322269 1121124887480925922995851)
              ·
                refine ⟨1681687331221388884493777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1121124887480925922995851 1681687331221388884493777)
                ·
                  refine ⟨1261265498416041663370333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1681687331221388884493777 1261265498416041663370333)
                  ·
                    refine ⟨472974561906015623763875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1261265498416041663370333 472974561906015623763875)
                    ·
                      rfl

theorem cell22_1381672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_1381672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1381672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1381672 prefixEnd_1381672 := by exact prefixLift 1381672
  have htrace : WordTrace (prefixWord ++ tailWord_1381672) baseStart_1381672 baseEnd_1381672 := by
    simpa [prefixWord, tailWord_1381672, baseEnd_1381672] using wordTrace_append hprefix tailTrace_1381672
  have hstable : (prefixWord ++ tailWord_1381672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381672).length < 2 ^ (prefixWord ++ tailWord_1381672).sum := by decide
  have hdescent : baseEnd_1381672 < baseStart_1381672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381683 : List Nat := [1, 1, 1, 2, 5, 2, 2, 2, 3, 3]
def baseStart_1381683 : Nat := 118140960795 + 1381683 * 2 ^ 59
def prefixEnd_1381683 : Nat := 4983230072969 + 3 ^ 40 * 1381683 * 2
def baseEnd_1381683 : Nat := 472978327430815261738841

theorem tailTrace_1381683 : CollatzResearch.WordTrace tailWord_1381683 prefixEnd_1381683 472978327430815261738841 := by
  unfold tailWord_1381683
  simp only [CollatzResearch.WordTrace]
  refine ⟨50394119053405938514765703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33596079368937292343177135 50394119053405938514765703)
  ·
    refine ⟨75591178580108907772148555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50394119053405938514765703 75591178580108907772148555)
    ·
      refine ⟨113386767870163361658222833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75591178580108907772148555 113386767870163361658222833)
      ·
        refine ⟨85040075902622521243667125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113386767870163361658222833 85040075902622521243667125)
        ·
          refine ⟨7972507115870861366593793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 85040075902622521243667125 7972507115870861366593793)
          ·
            refine ⟨5979380336903146024945345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7972507115870861366593793 5979380336903146024945345)
            ·
              refine ⟨4484535252677359518709009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5979380336903146024945345 4484535252677359518709009)
              ·
                refine ⟨3363401439508019639031757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4484535252677359518709009 3363401439508019639031757)
                ·
                  refine ⟨1261275539815507364636909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3363401439508019639031757 1261275539815507364636909)
                  ·
                    refine ⟨472978327430815261738841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1261275539815507364636909 472978327430815261738841)
                    ·
                      rfl

theorem cell22_1381683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 2, 3, 3].length) (baseStart_1381683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1381683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1381683 prefixEnd_1381683 := by exact prefixLift 1381683
  have htrace : WordTrace (prefixWord ++ tailWord_1381683) baseStart_1381683 baseEnd_1381683 := by
    simpa [prefixWord, tailWord_1381683, baseEnd_1381683] using wordTrace_append hprefix tailTrace_1381683
  have hstable : (prefixWord ++ tailWord_1381683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381683).length < 2 ^ (prefixWord ++ tailWord_1381683).sum := by decide
  have hdescent : baseEnd_1381683 < baseStart_1381683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381702 : List Nat := [6, 1, 1, 3, 1, 2, 8]
def baseStart_1381702 : Nat := 118140960795 + 1381702 * 2 ^ 59
def prefixEnd_1381702 : Nat := 4983230072969 + 3 ^ 40 * 1381702 * 2
def baseEnd_1381702 : Nat := 17517956722929835019029

theorem tailTrace_1381702 : CollatzResearch.WordTrace tailWord_1381702 prefixEnd_1381702 17517956722929835019029 := by
  unfold tailWord_1381702
  simp only [CollatzResearch.WordTrace]
  refine ⟨1574837876260534523740855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 33596541360224736506471573 1574837876260534523740855)
  ·
    refine ⟨2362256814390801785611283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1574837876260534523740855 2362256814390801785611283)
    ·
      refine ⟨3543385221586202678416925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2362256814390801785611283 3543385221586202678416925)
      ·
        refine ⟨1328769458094826004406347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3543385221586202678416925 1328769458094826004406347)
        ·
          refine ⟨1993154187142239006609521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1328769458094826004406347 1993154187142239006609521)
          ·
            refine ⟨1494865640356679254957141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1993154187142239006609521 1494865640356679254957141)
            ·
              refine ⟨17517956722929835019029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1494865640356679254957141 17517956722929835019029)
              ·
                rfl

theorem cell22_1381702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 8].length) (baseStart_1381702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1381702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1381702 prefixEnd_1381702 := by exact prefixLift 1381702
  have htrace : WordTrace (prefixWord ++ tailWord_1381702) baseStart_1381702 baseEnd_1381702 := by
    simpa [prefixWord, tailWord_1381702, baseEnd_1381702] using wordTrace_append hprefix tailTrace_1381702
  have hstable : (prefixWord ++ tailWord_1381702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381702).length < 2 ^ (prefixWord ++ tailWord_1381702).sum := by decide
  have hdescent : baseEnd_1381702 < baseStart_1381702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381805 : List Nat := [1, 5, 2, 2, 1, 2, 1, 1, 1, 6]
def baseStart_1381805 : Nat := 118140960795 + 1381805 * 2 ^ 59
def prefixEnd_1381805 : Nat := 4983230072969 + 3 ^ 40 * 1381805 * 2
def baseEnd_1381805 : Nat := 473020090524047610188467

theorem tailTrace_1381805 : CollatzResearch.WordTrace tailWord_1381805 prefixEnd_1381805 473020090524047610188467 := by
  unfold tailWord_1381805
  simp only [CollatzResearch.WordTrace]
  refine ⟨50398568758963953350706869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33599045839309302233804579 50398568758963953350706869)
  ·
    refine ⟨4724865821152870626628769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50398568758963953350706869 4724865821152870626628769)
    ·
      refine ⟨3543649365864652969971577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4724865821152870626628769 3543649365864652969971577)
      ·
        refine ⟨2657737024398489727478683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3543649365864652969971577 2657737024398489727478683)
        ·
          refine ⟨3986605536597734591218025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2657737024398489727478683 3986605536597734591218025)
          ·
            refine ⟨2989954152448300943413519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3986605536597734591218025 2989954152448300943413519)
            ·
              refine ⟨4484931228672451415120279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2989954152448300943413519 4484931228672451415120279)
              ·
                refine ⟨6727396843008677122680419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4484931228672451415120279 6727396843008677122680419)
                ·
                  refine ⟨10091095264513015684020629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6727396843008677122680419 10091095264513015684020629)
                  ·
                    refine ⟨473020090524047610188467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10091095264513015684020629 473020090524047610188467)
                    ·
                      rfl

theorem cell22_1381805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_1381805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1381805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1381805 prefixEnd_1381805 := by exact prefixLift 1381805
  have htrace : WordTrace (prefixWord ++ tailWord_1381805) baseStart_1381805 baseEnd_1381805 := by
    simpa [prefixWord, tailWord_1381805, baseEnd_1381805] using wordTrace_append hprefix tailTrace_1381805
  have hstable : (prefixWord ++ tailWord_1381805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381805).length < 2 ^ (prefixWord ++ tailWord_1381805).sum := by decide
  have hdescent : baseEnd_1381805 < baseStart_1381805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381826 : List Nat := [3, 5, 2, 1, 1, 1, 2, 1, 6]
def baseStart_1381826 : Nat := 118140960795 + 1381826 * 2 ^ 59
def prefixEnd_1381826 : Nat := 4983230072969 + 3 ^ 40 * 1381826 * 2
def baseEnd_1381826 : Nat := 157675759751070185137801

theorem tailTrace_1381826 : CollatzResearch.WordTrace tailWord_1381826 prefixEnd_1381826 157675759751070185137801 := by
  unfold tailWord_1381826
  simp only [CollatzResearch.WordTrace]
  refine ⟨12599833672971968484305333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33599556461258582624814221 12599833672971968484305333)
  ·
    refine ⟨1181234406841122045403625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12599833672971968484305333 1181234406841122045403625)
    ·
      refine ⟨885925805130841534052719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1181234406841122045403625 885925805130841534052719)
      ·
        refine ⟨1328888707696262301079079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 885925805130841534052719 1328888707696262301079079)
        ·
          refine ⟨1993333061544393451618619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1328888707696262301079079 1993333061544393451618619)
          ·
            refine ⟨2989999592316590177427929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1993333061544393451618619 2989999592316590177427929)
            ·
              refine ⟨2242499694237442633070947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2989999592316590177427929 2242499694237442633070947)
              ·
                refine ⟨3363749541356163949606421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2242499694237442633070947 3363749541356163949606421)
                ·
                  refine ⟨157675759751070185137801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3363749541356163949606421 157675759751070185137801)
                  ·
                    rfl

theorem cell22_1381826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_1381826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1381826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1381826 prefixEnd_1381826 := by exact prefixLift 1381826
  have htrace : WordTrace (prefixWord ++ tailWord_1381826) baseStart_1381826 baseEnd_1381826 := by
    simpa [prefixWord, tailWord_1381826, baseEnd_1381826] using wordTrace_append hprefix tailTrace_1381826
  have hstable : (prefixWord ++ tailWord_1381826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381826).length < 2 ^ (prefixWord ++ tailWord_1381826).sum := by decide
  have hdescent : baseEnd_1381826 < baseStart_1381826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381848 : List Nat := [2, 1, 2, 2, 2, 1, 2, 5, 5]
def baseStart_1381848 : Nat := 118140960795 + 1381848 * 2 ^ 59
def prefixEnd_1381848 : Nat := 4983230072969 + 3 ^ 40 * 1381848 * 2
def baseEnd_1381848 : Nat := 157678270100936610454445

theorem tailTrace_1381848 : CollatzResearch.WordTrace tailWord_1381848 prefixEnd_1381848 157678270100936610454445 := by
  unfold tailWord_1381848
  simp only [CollatzResearch.WordTrace]
  refine ⟨25200068548904085847261099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33600091398538781129681465 25200068548904085847261099)
  ·
    refine ⟨37800102823356128770891649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25200068548904085847261099 37800102823356128770891649)
    ·
      refine ⟨28350077117517096578168737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37800102823356128770891649 28350077117517096578168737)
      ·
        refine ⟨21262557838137822433626553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28350077117517096578168737 21262557838137822433626553)
        ·
          refine ⟨15946918378603366825219915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21262557838137822433626553 15946918378603366825219915)
          ·
            refine ⟨23920377567905050237829873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15946918378603366825219915 23920377567905050237829873)
            ·
              refine ⟨17940283175928787678372405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23920377567905050237829873 17940283175928787678372405)
              ·
                refine ⟨1681901547743323844847413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17940283175928787678372405 1681901547743323844847413)
                ·
                  refine ⟨157678270100936610454445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1681901547743323844847413 157678270100936610454445)
                  ·
                    rfl

theorem cell22_1381848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 5, 5].length) (baseStart_1381848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1381848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1381848 prefixEnd_1381848 := by exact prefixLift 1381848
  have htrace : WordTrace (prefixWord ++ tailWord_1381848) baseStart_1381848 baseEnd_1381848 := by
    simpa [prefixWord, tailWord_1381848, baseEnd_1381848] using wordTrace_append hprefix tailTrace_1381848
  have hstable : (prefixWord ++ tailWord_1381848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381848).length < 2 ^ (prefixWord ++ tailWord_1381848).sum := by decide
  have hdescent : baseEnd_1381848 < baseStart_1381848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381886 : List Nat := [4, 2, 2, 3, 1, 2, 1, 1, 3, 3]
def baseStart_1381886 : Nat := 118140960795 + 1381886 * 2 ^ 59
def prefixEnd_1381886 : Nat := 4983230072969 + 3 ^ 40 * 1381886 * 2
def baseEnd_1381886 : Nat := 473047818479390398913219

theorem tailTrace_1381886 : CollatzResearch.WordTrace tailWord_1381886 prefixEnd_1381886 473047818479390398913219 := by
  unfold tailWord_1381886
  simp only [CollatzResearch.WordTrace]
  refine ⟨6300190383958813023050689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33601015381113669456270341 6300190383958813023050689)
  ·
    refine ⟨4725142787969109767288017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6300190383958813023050689 4725142787969109767288017)
    ·
      refine ⟨3543857090976832325466013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4725142787969109767288017 3543857090976832325466013)
      ·
        refine ⟨1328946409116312122049755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3543857090976832325466013 1328946409116312122049755)
        ·
          refine ⟨1993419613674468183074633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1328946409116312122049755 1993419613674468183074633)
          ·
            refine ⟨1495064710255851137305975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1993419613674468183074633 1495064710255851137305975)
            ·
              refine ⟨2242597065383776705958963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1495064710255851137305975 2242597065383776705958963)
              ·
                refine ⟨3363895598075665058938445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2242597065383776705958963 3363895598075665058938445)
                ·
                  refine ⟨1261460849278374397101917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3363895598075665058938445 1261460849278374397101917)
                  ·
                    refine ⟨473047818479390398913219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1261460849278374397101917 473047818479390398913219)
                    ·
                      rfl

theorem cell22_1381886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_1381886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1381886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1381886 prefixEnd_1381886 := by exact prefixLift 1381886
  have htrace : WordTrace (prefixWord ++ tailWord_1381886) baseStart_1381886 baseEnd_1381886 := by
    simpa [prefixWord, tailWord_1381886, baseEnd_1381886] using wordTrace_append hprefix tailTrace_1381886
  have hstable : (prefixWord ++ tailWord_1381886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381886).length < 2 ^ (prefixWord ++ tailWord_1381886).sum := by decide
  have hdescent : baseEnd_1381886 < baseStart_1381886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381899 : List Nat := [1, 1, 1, 1, 9, 1, 2, 1, 5]
def baseStart_1381899 : Nat := 118140960795 + 1381899 * 2 ^ 59
def prefixEnd_1381899 : Nat := 4983230072969 + 3 ^ 40 * 1381899 * 2
def baseEnd_1381899 : Nat := 157684089548354232779393

theorem tailTrace_1381899 : CollatzResearch.WordTrace tailWord_1381899 prefixEnd_1381899 157684089548354232779393 := by
  unfold tailWord_1381899
  simp only [CollatzResearch.WordTrace]
  refine ⟨50401997220623407404628751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33601331480415604936419167 50401997220623407404628751)
  ·
    refine ⟨75602995830935111106943127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50401997220623407404628751 75602995830935111106943127)
    ·
      refine ⟨113404493746402666660414691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75602995830935111106943127 113404493746402666660414691)
      ·
        refine ⟨170106740619603999990622037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113404493746402666660414691 170106740619603999990622037)
        ·
          refine ⟨996719183317992187445051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 170106740619603999990622037 996719183317992187445051)
          ·
            refine ⟨1495078774976988281167577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 996719183317992187445051 1495078774976988281167577)
            ·
              refine ⟨1121309081232741210875683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1495078774976988281167577 1121309081232741210875683)
              ·
                refine ⟨1681963621849111816313525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1121309081232741210875683 1681963621849111816313525)
                ·
                  refine ⟨157684089548354232779393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1681963621849111816313525 157684089548354232779393)
                  ·
                    rfl

theorem cell22_1381899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 2, 1, 5].length) (baseStart_1381899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1381899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1381899 prefixEnd_1381899 := by exact prefixLift 1381899
  have htrace : WordTrace (prefixWord ++ tailWord_1381899) baseStart_1381899 baseEnd_1381899 := by
    simpa [prefixWord, tailWord_1381899, baseEnd_1381899] using wordTrace_append hprefix tailTrace_1381899
  have hstable : (prefixWord ++ tailWord_1381899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381899).length < 2 ^ (prefixWord ++ tailWord_1381899).sum := by decide
  have hdescent : baseEnd_1381899 < baseStart_1381899 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381944 : List Nat := [2, 1, 2, 1, 4, 4, 2, 2, 4]
def baseStart_1381944 : Nat := 118140960795 + 1381944 * 2 ^ 59
def prefixEnd_1381944 : Nat := 4983230072969 + 3 ^ 40 * 1381944 * 2
def baseEnd_1381944 : Nat := 157689224354899193654347

theorem tailTrace_1381944 : CollatzResearch.WordTrace tailWord_1381944 prefixEnd_1381944 157689224354899193654347 := by
  unfold tailWord_1381944
  simp only [CollatzResearch.WordTrace]
  refine ⟨25201819252730190045008443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33602425670306920060011257 25201819252730190045008443)
  ·
    refine ⟨37802728879095285067512665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25201819252730190045008443 37802728879095285067512665)
    ·
      refine ⟨28352046659321463800634499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37802728879095285067512665 28352046659321463800634499)
      ·
        refine ⟨42528069988982195700951749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28352046659321463800634499 42528069988982195700951749)
        ·
          refine ⟨7974013122934161693928453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42528069988982195700951749 7974013122934161693928453)
          ·
            refine ⟨1495127460550155317611585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7974013122934161693928453 1495127460550155317611585)
            ·
              refine ⟨1121345595412616488208689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1495127460550155317611585 1121345595412616488208689)
              ·
                refine ⟨841009196559462366156517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1121345595412616488208689 841009196559462366156517)
                ·
                  refine ⟨157689224354899193654347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 841009196559462366156517 157689224354899193654347)
                  ·
                    rfl

theorem cell22_1381944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 2, 2, 4].length) (baseStart_1381944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1381944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1381944 prefixEnd_1381944 := by exact prefixLift 1381944
  have htrace : WordTrace (prefixWord ++ tailWord_1381944) baseStart_1381944 baseEnd_1381944 := by
    simpa [prefixWord, tailWord_1381944, baseEnd_1381944] using wordTrace_append hprefix tailTrace_1381944
  have hstable : (prefixWord ++ tailWord_1381944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381944).length < 2 ^ (prefixWord ++ tailWord_1381944).sum := by decide
  have hdescent : baseEnd_1381944 < baseStart_1381944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381968 : List Nat := [2, 1, 1, 1, 1, 3, 3, 2, 2, 6]
def baseStart_1381968 : Nat := 118140960795 + 1381968 * 2 ^ 59
def prefixEnd_1381968 : Nat := 4983230072969 + 3 ^ 40 * 1381968 * 2
def baseEnd_1381968 : Nat := 473075888755169518362967

theorem tailTrace_1381968 : CollatzResearch.WordTrace tailWord_1381968 prefixEnd_1381968 473075888755169518362967 := by
  unfold tailWord_1381968
  simp only [CollatzResearch.WordTrace]
  refine ⟨25202256928686716094445279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33603009238248954792593705 25202256928686716094445279)
  ·
    refine ⟨37803385393030074141667919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25202256928686716094445279 37803385393030074141667919)
    ·
      refine ⟨56705078089545111212501879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37803385393030074141667919 56705078089545111212501879)
      ·
        refine ⟨85057617134317666818752819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56705078089545111212501879 85057617134317666818752819)
        ·
          refine ⟨127586425701476500228129229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85057617134317666818752819 127586425701476500228129229)
          ·
            refine ⟨47844909638053687585548461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127586425701476500228129229 47844909638053687585548461)
            ·
              refine ⟨17941841114270132844580673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47844909638053687585548461 17941841114270132844580673)
              ·
                refine ⟨13456380835702599633435505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17941841114270132844580673 13456380835702599633435505)
                ·
                  refine ⟨10092285626776949725076629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13456380835702599633435505 10092285626776949725076629)
                  ·
                    refine ⟨473075888755169518362967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10092285626776949725076629 473075888755169518362967)
                    ·
                      rfl

theorem cell22_1381968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 2, 6].length) (baseStart_1381968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1381968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1381968 prefixEnd_1381968 := by exact prefixLift 1381968
  have htrace : WordTrace (prefixWord ++ tailWord_1381968) baseStart_1381968 baseEnd_1381968 := by
    simpa [prefixWord, tailWord_1381968, baseEnd_1381968] using wordTrace_append hprefix tailTrace_1381968
  have hstable : (prefixWord ++ tailWord_1381968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381968).length < 2 ^ (prefixWord ++ tailWord_1381968).sum := by decide
  have hdescent : baseEnd_1381968 < baseStart_1381968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382000 : List Nat := [2, 1, 1, 1, 6, 2, 1, 1, 7]
def baseStart_1382000 : Nat := 118140960795 + 1382000 * 2 ^ 59
def prefixEnd_1382000 : Nat := 4983230072969 + 3 ^ 40 * 1382000 * 2
def baseEnd_1382000 : Nat := 157695614336377367187623

theorem tailTrace_1382000 : CollatzResearch.WordTrace tailWord_1382000 prefixEnd_1382000 157695614336377367187623 := by
  unfold tailWord_1382000
  simp only [CollatzResearch.WordTrace]
  refine ⟨25202840496628750827027727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33603787328838334436036969 25202840496628750827027727)
  ·
    refine ⟨37804260744943126240541591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25202840496628750827027727 37804260744943126240541591)
    ·
      refine ⟨56706391117414689360812387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37804260744943126240541591 56706391117414689360812387)
      ·
        refine ⟨85059586676122034041218581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56706391117414689360812387 85059586676122034041218581)
        ·
          refine ⟨3987168125443220345682121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 85059586676122034041218581 3987168125443220345682121)
          ·
            refine ⟨2990376094082415259261591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3987168125443220345682121 2990376094082415259261591)
            ·
              refine ⟨4485564141123622888892387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2990376094082415259261591 4485564141123622888892387)
              ·
                refine ⟨6728346211685434333338581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4485564141123622888892387 6728346211685434333338581)
                ·
                  refine ⟨157695614336377367187623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6728346211685434333338581 157695614336377367187623)
                  ·
                    rfl

theorem cell22_1382000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 7].length) (baseStart_1382000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1382000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1382000 prefixEnd_1382000 := by exact prefixLift 1382000
  have htrace : WordTrace (prefixWord ++ tailWord_1382000) baseStart_1382000 baseEnd_1382000 := by
    simpa [prefixWord, tailWord_1382000, baseEnd_1382000] using wordTrace_append hprefix tailTrace_1382000
  have hstable : (prefixWord ++ tailWord_1382000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382000).length < 2 ^ (prefixWord ++ tailWord_1382000).sum := by decide
  have hdescent : baseEnd_1382000 < baseStart_1382000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382113 : List Nat := [1, 2, 3, 1, 6, 1, 2, 2, 4]
def baseStart_1382113 : Nat := 118140960795 + 1382113 * 2 ^ 59
def prefixEnd_1382113 : Nat := 4983230072969 + 3 ^ 40 * 1382113 * 2
def baseEnd_1382113 : Nat := 157708508406145824495841

theorem tailTrace_1382113 : CollatzResearch.WordTrace tailWord_1382113 prefixEnd_1382113 157708508406145824495841 := by
  unfold tailWord_1382113
  simp only [CollatzResearch.WordTrace]
  refine ⟨50409802441848121952918993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33606534961232081301945995 50409802441848121952918993)
  ·
    refine ⟨37807351831386091464689245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50409802441848121952918993 37807351831386091464689245)
    ·
      refine ⟨14177756936769784299258467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37807351831386091464689245 14177756936769784299258467)
      ·
        refine ⟨21266635405154676448887701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14177756936769784299258467 21266635405154676448887701)
        ·
          refine ⟨996873534616625458541611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 21266635405154676448887701 996873534616625458541611)
          ·
            refine ⟨1495310301924938187812417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 996873534616625458541611 1495310301924938187812417)
            ·
              refine ⟨1121482726443703640859313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1495310301924938187812417 1121482726443703640859313)
              ·
                refine ⟨841112044832777730644485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1121482726443703640859313 841112044832777730644485)
                ·
                  refine ⟨157708508406145824495841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 841112044832777730644485 157708508406145824495841)
                  ·
                    rfl

theorem cell22_1382113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 2, 2, 4].length) (baseStart_1382113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1382113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1382113 prefixEnd_1382113 := by exact prefixLift 1382113
  have htrace : WordTrace (prefixWord ++ tailWord_1382113) baseStart_1382113 baseEnd_1382113 := by
    simpa [prefixWord, tailWord_1382113, baseEnd_1382113] using wordTrace_append hprefix tailTrace_1382113
  have hstable : (prefixWord ++ tailWord_1382113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382113).length < 2 ^ (prefixWord ++ tailWord_1382113).sum := by decide
  have hdescent : baseEnd_1382113 < baseStart_1382113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382167 : List Nat := [1, 1, 3, 4, 2, 1, 1, 2, 2, 5]
def baseStart_1382167 : Nat := 118140960795 + 1382167 * 2 ^ 59
def prefixEnd_1382167 : Nat := 4983230072969 + 3 ^ 40 * 1382167 * 2
def baseEnd_1382167 : Nat := 473144010521999332637357

theorem tailTrace_1382167 : CollatzResearch.WordTrace tailWord_1382167 prefixEnd_1382167 473144010521999332637357 := by
  unfold tailWord_1382167
  simp only [CollatzResearch.WordTrace]
  refine ⟨50411771983652489175384755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33607847989101659450256503 50411771983652489175384755)
  ·
    refine ⟨75617657975478733763077133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50411771983652489175384755 75617657975478733763077133)
    ·
      refine ⟨28356621740804525161153925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75617657975478733763077133 28356621740804525161153925)
      ·
        refine ⟨5316866576400848467716361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28356621740804525161153925 5316866576400848467716361)
        ·
          refine ⟨3987649932300636350787271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5316866576400848467716361 3987649932300636350787271)
          ·
            refine ⟨5981474898450954526180907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3987649932300636350787271 5981474898450954526180907)
            ·
              refine ⟨8972212347676431789271361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5981474898450954526180907 8972212347676431789271361)
              ·
                refine ⟨6729159260757323841953521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8972212347676431789271361 6729159260757323841953521)
                ·
                  refine ⟨5046869445567992881465141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6729159260757323841953521 5046869445567992881465141)
                  ·
                    refine ⟨473144010521999332637357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5046869445567992881465141 473144010521999332637357)
                    ·
                      rfl

theorem cell22_1382167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 2, 5].length) (baseStart_1382167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1382167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1382167 prefixEnd_1382167 := by exact prefixLift 1382167
  have htrace : WordTrace (prefixWord ++ tailWord_1382167) baseStart_1382167 baseEnd_1382167 := by
    simpa [prefixWord, tailWord_1382167, baseEnd_1382167] using wordTrace_append hprefix tailTrace_1382167
  have hstable : (prefixWord ++ tailWord_1382167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382167).length < 2 ^ (prefixWord ++ tailWord_1382167).sum := by decide
  have hdescent : baseEnd_1382167 < baseStart_1382167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382229 : List Nat := [1, 3, 2, 2, 2, 2, 2, 1, 4, 3]
def baseStart_1382229 : Nat := 118140960795 + 1382229 * 2 ^ 59
def prefixEnd_1382229 : Nat := 4983230072969 + 3 ^ 40 * 1382229 * 2
def baseEnd_1382229 : Nat := 473165234389051837587167

theorem tailTrace_1382229 : CollatzResearch.WordTrace tailWord_1382229 prefixEnd_1382229 473165234389051837587167 := by
  unfold tailWord_1382229
  simp only [CollatzResearch.WordTrace]
  refine ⟨50414033309427873764141741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33609355539618582509427827 50414033309427873764141741)
  ·
    refine ⟨18905262491035452661553153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50414033309427873764141741 18905262491035452661553153)
    ·
      refine ⟨14178946868276589496164865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18905262491035452661553153 14178946868276589496164865)
      ·
        refine ⟨10634210151207442122123649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14178946868276589496164865 10634210151207442122123649)
        ·
          refine ⟨7975657613405581591592737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10634210151207442122123649 7975657613405581591592737)
          ·
            refine ⟨5981743210054186193694553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7975657613405581591592737 5981743210054186193694553)
            ·
              refine ⟨4486307407540639645270915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5981743210054186193694553 4486307407540639645270915)
              ·
                refine ⟨6729461111310959467906373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4486307407540639645270915 6729461111310959467906373)
                ·
                  refine ⟨1261773958370804900232445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6729461111310959467906373 1261773958370804900232445)
                  ·
                    refine ⟨473165234389051837587167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1261773958370804900232445 473165234389051837587167)
                    ·
                      rfl

theorem cell22_1382229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 4, 3].length) (baseStart_1382229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1382229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1382229 prefixEnd_1382229 := by exact prefixLift 1382229
  have htrace : WordTrace (prefixWord ++ tailWord_1382229) baseStart_1382229 baseEnd_1382229 := by
    simpa [prefixWord, tailWord_1382229, baseEnd_1382229] using wordTrace_append hprefix tailTrace_1382229
  have hstable : (prefixWord ++ tailWord_1382229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382229).length < 2 ^ (prefixWord ++ tailWord_1382229).sum := by decide
  have hdescent : baseEnd_1382229 < baseStart_1382229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382231 : List Nat := [1, 1, 3, 2, 6, 1, 1, 1, 6]
def baseStart_1382231 : Nat := 118140960795 + 1382231 * 2 ^ 59
def prefixEnd_1382231 : Nat := 4983230072969 + 3 ^ 40 * 1382231 * 2
def baseEnd_1382231 : Nat := 157721973009974833012387

theorem tailTrace_1382231 : CollatzResearch.WordTrace tailWord_1382231 prefixEnd_1382231 157721973009974833012387 := by
  unfold tailWord_1382231
  simp only [CollatzResearch.WordTrace]
  refine ⟨50414106255420628105714547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33609404170280418737143031 50414106255420628105714547)
  ·
    refine ⟨75621159383130942158571821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50414106255420628105714547 75621159383130942158571821)
    ·
      refine ⟨28357934768674103309464433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75621159383130942158571821 28357934768674103309464433)
      ·
        refine ⟨21268451076505577482098325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28357934768674103309464433 21268451076505577482098325)
        ·
          refine ⟨996958644211198944473359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 21268451076505577482098325 996958644211198944473359)
          ·
            refine ⟨1495437966316798416710039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 996958644211198944473359 1495437966316798416710039)
            ·
              refine ⟨2243156949475197625065059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1495437966316798416710039 2243156949475197625065059)
              ·
                refine ⟨3364735424212796437597589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2243156949475197625065059 3364735424212796437597589)
                ·
                  refine ⟨157721973009974833012387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3364735424212796437597589 157721973009974833012387)
                  ·
                    rfl

theorem cell22_1382231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 1, 6].length) (baseStart_1382231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1382231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1382231 prefixEnd_1382231 := by exact prefixLift 1382231
  have htrace : WordTrace (prefixWord ++ tailWord_1382231) baseStart_1382231 baseEnd_1382231 := by
    simpa [prefixWord, tailWord_1382231, baseEnd_1382231] using wordTrace_append hprefix tailTrace_1382231
  have hstable : (prefixWord ++ tailWord_1382231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382231).length < 2 ^ (prefixWord ++ tailWord_1382231).sum := by decide
  have hdescent : baseEnd_1382231 < baseStart_1382231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382250 : List Nat := [3, 1, 3, 4, 2, 1, 1, 2, 1, 4]
def baseStart_1382250 : Nat := 118140960795 + 1382250 * 2 ^ 59
def prefixEnd_1382250 : Nat := 4983230072969 + 3 ^ 40 * 1382250 * 2
def baseEnd_1382250 : Nat := 473172423118214782812103

theorem tailTrace_1382250 : CollatzResearch.WordTrace tailWord_1382250 prefixEnd_1382250 473172423118214782812103 := by
  unfold tailWord_1382250
  simp only [CollatzResearch.WordTrace]
  refine ⟨12603699810587948587664051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33609866161567862900437469 12603699810587948587664051)
  ·
    refine ⟨18905549715881922881496077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12603699810587948587664051 18905549715881922881496077)
    ·
      refine ⟨7089581143455721080561029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18905549715881922881496077 7089581143455721080561029)
      ·
        refine ⟨1329296464397947702605193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7089581143455721080561029 1329296464397947702605193)
        ·
          refine ⟨996972348298460776953895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1329296464397947702605193 996972348298460776953895)
          ·
            refine ⟨1495458522447691165430843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 996972348298460776953895 1495458522447691165430843)
            ·
              refine ⟨2243187783671536748146265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1495458522447691165430843 2243187783671536748146265)
              ·
                refine ⟨1682390837753652561109699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2243187783671536748146265 1682390837753652561109699)
                ·
                  refine ⟨2523586256630478841664549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1682390837753652561109699 2523586256630478841664549)
                  ·
                    refine ⟨473172423118214782812103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2523586256630478841664549 473172423118214782812103)
                    ·
                      rfl

theorem cell22_1382250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 2, 1, 4].length) (baseStart_1382250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1382250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1382250 prefixEnd_1382250 := by exact prefixLift 1382250
  have htrace : WordTrace (prefixWord ++ tailWord_1382250) baseStart_1382250 baseEnd_1382250 := by
    simpa [prefixWord, tailWord_1382250, baseEnd_1382250] using wordTrace_append hprefix tailTrace_1382250
  have hstable : (prefixWord ++ tailWord_1382250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382250).length < 2 ^ (prefixWord ++ tailWord_1382250).sum := by decide
  have hdescent : baseEnd_1382250 < baseStart_1382250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382398 : List Nat := [4, 2, 2, 2, 1, 1, 2, 1, 4, 3]
def baseStart_1382398 : Nat := 118140960795 + 1382398 * 2 ^ 59
def prefixEnd_1382398 : Nat := 4983230072969 + 3 ^ 40 * 1382398 * 2
def baseEnd_1382398 : Nat := 473223086542791730111649

theorem tailTrace_1382398 : CollatzResearch.WordTrace tailWord_1382398 prefixEnd_1382398 473223086542791730111649 := by
  unfold tailWord_1382398
  simp only [CollatzResearch.WordTrace]
  refine ⟨6302524655726951953380481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33613464830543743751362565 6302524655726951953380481)
  ·
    refine ⟨4726893491795213965035361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6302524655726951953380481 4726893491795213965035361)
    ·
      refine ⟨3545170118846410473776521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4726893491795213965035361 3545170118846410473776521)
      ·
        refine ⟨2658877589134807855332391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3545170118846410473776521 2658877589134807855332391)
        ·
          refine ⟨3988316383702211782998587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2658877589134807855332391 3988316383702211782998587)
          ·
            refine ⟨5982474575553317674497881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3988316383702211782998587 5982474575553317674497881)
            ·
              refine ⟨4486855931664988255873411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5982474575553317674497881 4486855931664988255873411)
              ·
                refine ⟨6730283897497482383810117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4486855931664988255873411 6730283897497482383810117)
                ·
                  refine ⟨1261928230780777946964397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6730283897497482383810117 1261928230780777946964397)
                  ·
                    refine ⟨473223086542791730111649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1261928230780777946964397 473223086542791730111649)
                    ·
                      rfl

theorem cell22_1382398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_1382398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1382398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1382398 prefixEnd_1382398 := by exact prefixLift 1382398
  have htrace : WordTrace (prefixWord ++ tailWord_1382398) baseStart_1382398 baseEnd_1382398 := by
    simpa [prefixWord, tailWord_1382398, baseEnd_1382398] using wordTrace_append hprefix tailTrace_1382398
  have hstable : (prefixWord ++ tailWord_1382398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382398).length < 2 ^ (prefixWord ++ tailWord_1382398).sum := by decide
  have hdescent : baseEnd_1382398 < baseStart_1382398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382406 : List Nat := [6, 2, 1, 2, 2, 1, 2, 1, 5]
def baseStart_1382406 : Nat := 118140960795 + 1382406 * 2 ^ 59
def prefixEnd_1382406 : Nat := 4983230072969 + 3 ^ 40 * 1382406 * 2
def baseEnd_1382406 : Nat := 157741941702094125303875

theorem tailTrace_1382406 : CollatzResearch.WordTrace tailWord_1382406 prefixEnd_1382406 157741941702094125303875 := by
  unfold tailWord_1382406
  simp only [CollatzResearch.WordTrace]
  refine ⟨1575640282180832281041721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 33613659353191088662223381 1575640282180832281041721)
  ·
    refine ⟨1181730211635624210781291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1575640282180832281041721 1181730211635624210781291)
    ·
      refine ⟨1772595317453436316171937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1181730211635624210781291 1772595317453436316171937)
      ·
        refine ⟨1329446488090077237128953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1772595317453436316171937 1329446488090077237128953)
        ·
          refine ⟨997084866067557927846715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1329446488090077237128953 997084866067557927846715)
          ·
            refine ⟨1495627299101336891770073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 997084866067557927846715 1495627299101336891770073)
            ·
              refine ⟨1121720474326002668827555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1495627299101336891770073 1121720474326002668827555)
              ·
                refine ⟨1682580711489004003241333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1121720474326002668827555 1682580711489004003241333)
                ·
                  refine ⟨157741941702094125303875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1682580711489004003241333 157741941702094125303875)
                  ·
                    rfl

theorem cell22_1382406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_1382406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1382406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1382406 prefixEnd_1382406 := by exact prefixLift 1382406
  have htrace : WordTrace (prefixWord ++ tailWord_1382406) baseStart_1382406 baseEnd_1382406 := by
    simpa [prefixWord, tailWord_1382406, baseEnd_1382406] using wordTrace_append hprefix tailTrace_1382406
  have hstable : (prefixWord ++ tailWord_1382406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382406).length < 2 ^ (prefixWord ++ tailWord_1382406).sum := by decide
  have hdescent : baseEnd_1382406 < baseStart_1382406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382518 : List Nat := [5, 1, 1, 2, 1, 3, 2, 1, 6]
def baseStart_1382518 : Nat := 118140960795 + 1382518 * 2 ^ 59
def prefixEnd_1382518 : Nat := 4983230072969 + 3 ^ 40 * 1382518 * 2
def baseEnd_1382518 : Nat := 157754721665050472370427

theorem tailTrace_1382518 : CollatzResearch.WordTrace tailWord_1382518 prefixEnd_1382518 157754721665050472370427 := by
  unfold tailWord_1382518
  simp only [CollatzResearch.WordTrace]
  refine ⟨3151535875336304757588263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33616382670253917414274805 3151535875336304757588263)
  ·
    refine ⟨4727303813004457136382395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3151535875336304757588263 4727303813004457136382395)
    ·
      refine ⟨7090955719506685704573593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4727303813004457136382395 7090955719506685704573593)
      ·
        refine ⟨5318216789630014278430195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7090955719506685704573593 5318216789630014278430195)
        ·
          refine ⟨7977325184445021417645293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5318216789630014278430195 7977325184445021417645293)
          ·
            refine ⟨2991496944166883031616985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7977325184445021417645293 2991496944166883031616985)
            ·
              refine ⟨2243622708125162273712739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2991496944166883031616985 2243622708125162273712739)
              ·
                refine ⟨3365434062187743410569109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2243622708125162273712739 3365434062187743410569109)
                ·
                  refine ⟨157754721665050472370427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3365434062187743410569109 157754721665050472370427)
                  ·
                    rfl

theorem cell22_1382518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_1382518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1382518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1382518 prefixEnd_1382518 := by exact prefixLift 1382518
  have htrace : WordTrace (prefixWord ++ tailWord_1382518) baseStart_1382518 baseEnd_1382518 := by
    simpa [prefixWord, tailWord_1382518, baseEnd_1382518] using wordTrace_append hprefix tailTrace_1382518
  have hstable : (prefixWord ++ tailWord_1382518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382518).length < 2 ^ (prefixWord ++ tailWord_1382518).sum := by decide
  have hdescent : baseEnd_1382518 < baseStart_1382518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382533 : List Nat := [1, 3, 1, 1, 5, 3, 1, 1, 1, 5]
def baseStart_1382533 : Nat := 118140960795 + 1382533 * 2 ^ 59
def prefixEnd_1382533 : Nat := 4983230072969 + 3 ^ 40 * 1382533 * 2
def baseEnd_1382533 : Nat := 473269299801696377986235

theorem tailTrace_1382533 : CollatzResearch.WordTrace tailWord_1382533 prefixEnd_1382533 473269299801696377986235 := by
  unfold tailWord_1382533
  simp only [CollatzResearch.WordTrace]
  refine ⟨50425121100326533683208253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33616747400217689122138835 50425121100326533683208253)
  ·
    refine ⟨18909420412622450131203095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50425121100326533683208253 18909420412622450131203095)
    ·
      refine ⟨28364130618933675196804643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18909420412622450131203095 28364130618933675196804643)
      ·
        refine ⟨42546195928400512795206965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28364130618933675196804643 42546195928400512795206965)
        ·
          refine ⟨3988705868287548074550653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42546195928400512795206965 3988705868287548074550653)
          ·
            refine ⟨1495764700607830527956495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3988705868287548074550653 1495764700607830527956495)
            ·
              refine ⟨2243647050911745791934743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1495764700607830527956495 2243647050911745791934743)
              ·
                refine ⟨3365470576367618687902115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2243647050911745791934743 3365470576367618687902115)
                ·
                  refine ⟨5048205864551428031853173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3365470576367618687902115 5048205864551428031853173)
                  ·
                    refine ⟨473269299801696377986235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5048205864551428031853173 473269299801696377986235)
                    ·
                      rfl

theorem cell22_1382533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 1, 1, 5].length) (baseStart_1382533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1382533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1382533 prefixEnd_1382533 := by exact prefixLift 1382533
  have htrace : WordTrace (prefixWord ++ tailWord_1382533) baseStart_1382533 baseEnd_1382533 := by
    simpa [prefixWord, tailWord_1382533, baseEnd_1382533] using wordTrace_append hprefix tailTrace_1382533
  have hstable : (prefixWord ++ tailWord_1382533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382533).length < 2 ^ (prefixWord ++ tailWord_1382533).sum := by decide
  have hdescent : baseEnd_1382533 < baseStart_1382533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382544 : List Nat := [2, 1, 1, 1, 1, 1, 5, 1, 2, 7]
def baseStart_1382544 : Nat := 118140960795 + 1382544 * 2 ^ 59
def prefixEnd_1382544 : Nat := 4983230072969 + 3 ^ 40 * 1382544 * 2
def baseEnd_1382544 : Nat := 473273065326496015961201

theorem tailTrace_1382544 : CollatzResearch.WordTrace tailWord_1382544 prefixEnd_1382544 473273065326496015961201 := by
  unfold tailWord_1382544
  simp only [CollatzResearch.WordTrace]
  refine ⟨25212761151643341280929343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33617014868857788374572457 25212761151643341280929343)
  ·
    refine ⟨37819141727465011921394015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25212761151643341280929343 37819141727465011921394015)
    ·
      refine ⟨56728712591197517882091023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37819141727465011921394015 56728712591197517882091023)
      ·
        refine ⟨85093068886796276823136535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56728712591197517882091023 85093068886796276823136535)
        ·
          refine ⟨127639603330194415234704803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85093068886796276823136535 127639603330194415234704803)
          ·
            refine ⟨191459404995291622852057205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127639603330194415234704803 191459404995291622852057205)
            ·
              refine ⟨17949319218308589642380363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 191459404995291622852057205 17949319218308589642380363)
              ·
                refine ⟨26923978827462884463570545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17949319218308589642380363 26923978827462884463570545)
                ·
                  refine ⟨20192984120597163347677909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26923978827462884463570545 20192984120597163347677909)
                  ·
                    refine ⟨473273065326496015961201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20192984120597163347677909 473273065326496015961201)
                    ·
                      rfl

theorem cell22_1382544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 2, 7].length) (baseStart_1382544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1382544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1382544 prefixEnd_1382544 := by exact prefixLift 1382544
  have htrace : WordTrace (prefixWord ++ tailWord_1382544) baseStart_1382544 baseEnd_1382544 := by
    simpa [prefixWord, tailWord_1382544, baseEnd_1382544] using wordTrace_append hprefix tailTrace_1382544
  have hstable : (prefixWord ++ tailWord_1382544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382544).length < 2 ^ (prefixWord ++ tailWord_1382544).sum := by decide
  have hdescent : baseEnd_1382544 < baseStart_1382544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382546 : List Nat := [3, 2, 3, 1, 1, 1, 3, 8]
def baseStart_1382546 : Nat := 118140960795 + 1382546 * 2 ^ 59
def prefixEnd_1382546 : Nat := 4983230072969 + 3 ^ 40 * 1382546 * 2
def baseEnd_1382546 : Nat := 52585972218596519712355

theorem tailTrace_1382546 : CollatzResearch.WordTrace tailWord_1382546 prefixEnd_1382546 52585972218596519712355 := by
  unfold tailWord_1382546
  simp only [CollatzResearch.WordTrace]
  refine ⟨12606398812319859225857873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33617063499519624602287661 12606398812319859225857873)
  ·
    refine ⟨9454799109239894419393405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12606398812319859225857873 9454799109239894419393405)
    ·
      refine ⟨3545549665964960407272527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9454799109239894419393405 3545549665964960407272527)
      ·
        refine ⟨5318324498947440610908791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3545549665964960407272527 5318324498947440610908791)
        ·
          refine ⟨7977486748421160916363187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5318324498947440610908791 7977486748421160916363187)
          ·
            refine ⟨11966230122631741374544781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7977486748421160916363187 11966230122631741374544781)
            ·
              refine ⟨4487336295986903015454293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11966230122631741374544781 4487336295986903015454293)
              ·
                refine ⟨52585972218596519712355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4487336295986903015454293 52585972218596519712355)
                ·
                  rfl

theorem cell22_1382546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 8].length) (baseStart_1382546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1382546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1382546 prefixEnd_1382546 := by exact prefixLift 1382546
  have htrace : WordTrace (prefixWord ++ tailWord_1382546) baseStart_1382546 baseEnd_1382546 := by
    simpa [prefixWord, tailWord_1382546, baseEnd_1382546] using wordTrace_append hprefix tailTrace_1382546
  have hstable : (prefixWord ++ tailWord_1382546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382546).length < 2 ^ (prefixWord ++ tailWord_1382546).sum := by decide
  have hdescent : baseEnd_1382546 < baseStart_1382546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382552 : List Nat := [2, 1, 2, 4, 4, 1, 1, 3, 4]
def baseStart_1382552 : Nat := 118140960795 + 1382552 * 2 ^ 59
def prefixEnd_1382552 : Nat := 4983230072969 + 3 ^ 40 * 1382552 * 2
def baseEnd_1382552 : Nat := 157758601296662220587059

theorem tailTrace_1382552 : CollatzResearch.WordTrace tailWord_1382552 prefixEnd_1382552 157758601296662220587059 := by
  unfold tailWord_1382552
  simp only [CollatzResearch.WordTrace]
  refine ⟨25212907043628849964074955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33617209391505133285433273 25212907043628849964074955)
  ·
    refine ⟨37819360565443274946112433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25212907043628849964074955 37819360565443274946112433)
    ·
      refine ⟨28364520424082456209584325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37819360565443274946112433 28364520424082456209584325)
      ·
        refine ⟨5318347579515460539297061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28364520424082456209584325 5318347579515460539297061)
        ·
          refine ⟨997190171159148851118199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5318347579515460539297061 997190171159148851118199)
          ·
            refine ⟨1495785256738723276677299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 997190171159148851118199 1495785256738723276677299)
            ·
              refine ⟨2243677885108084915015949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1495785256738723276677299 2243677885108084915015949)
              ·
                refine ⟨841379206915531843130981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2243677885108084915015949 841379206915531843130981)
                ·
                  refine ⟨157758601296662220587059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 841379206915531843130981 157758601296662220587059)
                  ·
                    rfl

theorem cell22_1382552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 3, 4].length) (baseStart_1382552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1382552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1382552 prefixEnd_1382552 := by exact prefixLift 1382552
  have htrace : WordTrace (prefixWord ++ tailWord_1382552) baseStart_1382552 baseEnd_1382552 := by
    simpa [prefixWord, tailWord_1382552, baseEnd_1382552] using wordTrace_append hprefix tailTrace_1382552
  have hstable : (prefixWord ++ tailWord_1382552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382552).length < 2 ^ (prefixWord ++ tailWord_1382552).sum := by decide
  have hdescent : baseEnd_1382552 < baseStart_1382552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382629 : List Nat := [1, 3, 1, 4, 2, 3, 2, 2, 1, 3]
def baseStart_1382629 : Nat := 118140960795 + 1382629 * 2 ^ 59
def prefixEnd_1382629 : Nat := 4983230072969 + 3 ^ 40 * 1382629 * 2
def baseEnd_1382629 : Nat := 473302162563584127585941

theorem tailTrace_1382629 : CollatzResearch.WordTrace tailWord_1382629 prefixEnd_1382629 473302162563584127585941 := by
  unfold tailWord_1382629
  simp only [CollatzResearch.WordTrace]
  refine ⟨50428622507978742078702941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33619081671985828052468627 50428622507978742078702941)
  ·
    refine ⟨18910733440492028279513603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50428622507978742078702941 18910733440492028279513603)
    ·
      refine ⟨28366100160738042419270405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18910733440492028279513603 28366100160738042419270405)
      ·
        refine ⟨5318643780138382953613201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28366100160738042419270405 5318643780138382953613201)
        ·
          refine ⟨3988982835103787215209901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5318643780138382953613201 3988982835103787215209901)
          ·
            refine ⟨1495868563163920205703713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3988982835103787215209901 1495868563163920205703713)
            ·
              refine ⟨1121901422372940154277785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1495868563163920205703713 1121901422372940154277785)
              ·
                refine ⟨841426066779705115708339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1121901422372940154277785 841426066779705115708339)
                ·
                  refine ⟨1262139100169557673562509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 841426066779705115708339 1262139100169557673562509)
                  ·
                    refine ⟨473302162563584127585941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1262139100169557673562509 473302162563584127585941)
                    ·
                      rfl

theorem cell22_1382629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 2, 2, 1, 3].length) (baseStart_1382629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1382629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1382629 prefixEnd_1382629 := by exact prefixLift 1382629
  have htrace : WordTrace (prefixWord ++ tailWord_1382629) baseStart_1382629 baseEnd_1382629 := by
    simpa [prefixWord, tailWord_1382629, baseEnd_1382629] using wordTrace_append hprefix tailTrace_1382629
  have hstable : (prefixWord ++ tailWord_1382629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382629).length < 2 ^ (prefixWord ++ tailWord_1382629).sum := by decide
  have hdescent : baseEnd_1382629 < baseStart_1382629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382636 : List Nat := [2, 2, 1, 1, 2, 3, 2, 3, 6]
def baseStart_1382636 : Nat := 118140960795 + 1382636 * 2 ^ 59
def prefixEnd_1382636 : Nat := 4983230072969 + 3 ^ 40 * 1382636 * 2
def baseEnd_1382636 : Nat := 157768186268879480886973

theorem tailTrace_1382636 : CollatzResearch.WordTrace tailWord_1382636 prefixEnd_1382636 157768186268879480886973 := by
  unfold tailWord_1382636
  simp only [CollatzResearch.WordTrace]
  refine ⟨25214438909476691137103881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33619251879302254849471841 25214438909476691137103881)
  ·
    refine ⟨18910829182107518352827911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25214438909476691137103881 18910829182107518352827911)
    ·
      refine ⟨28366243773161277529241867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18910829182107518352827911 28366243773161277529241867)
      ·
        refine ⟨42549365659741916293862801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28366243773161277529241867 42549365659741916293862801)
        ·
          refine ⟨31912024244806437220397101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42549365659741916293862801 31912024244806437220397101)
          ·
            refine ⟨11967009091802413957648913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31912024244806437220397101 11967009091802413957648913)
            ·
              refine ⟨8975256818851810468236685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11967009091802413957648913 8975256818851810468236685)
              ·
                refine ⟨3365721307069428925588757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8975256818851810468236685 3365721307069428925588757)
                ·
                  refine ⟨157768186268879480886973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3365721307069428925588757 157768186268879480886973)
                  ·
                    rfl

theorem cell22_1382636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 6].length) (baseStart_1382636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1382636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1382636 prefixEnd_1382636 := by exact prefixLift 1382636
  have htrace : WordTrace (prefixWord ++ tailWord_1382636) baseStart_1382636 baseEnd_1382636 := by
    simpa [prefixWord, tailWord_1382636, baseEnd_1382636] using wordTrace_append hprefix tailTrace_1382636
  have hstable : (prefixWord ++ tailWord_1382636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382636).length < 2 ^ (prefixWord ++ tailWord_1382636).sum := by decide
  have hdescent : baseEnd_1382636 < baseStart_1382636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382668 : List Nat := [2, 2, 1, 2, 2, 2, 2, 2, 4, 3]
def baseStart_1382668 : Nat := 118140960795 + 1382668 * 2 ^ 59
def prefixEnd_1382668 : Nat := 4983230072969 + 3 ^ 40 * 1382668 * 2
def baseEnd_1382668 : Nat := 473315513060601025860821

theorem tailTrace_1382668 : CollatzResearch.WordTrace tailWord_1382668 prefixEnd_1382668 473315513060601025860821 := by
  unfold tailWord_1382668
  simp only [CollatzResearch.WordTrace]
  refine ⟨25215022477418725869686329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33620029969891634492915105 25215022477418725869686329)
  ·
    refine ⟨18911266858064044402264747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25215022477418725869686329 18911266858064044402264747)
    ·
      refine ⟨28366900287096066603397121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18911266858064044402264747 28366900287096066603397121)
      ·
        refine ⟨21275175215322049952547841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28366900287096066603397121 21275175215322049952547841)
        ·
          refine ⟨15956381411491537464410881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21275175215322049952547841 15956381411491537464410881)
          ·
            refine ⟨11967286058618653098308161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15956381411491537464410881 11967286058618653098308161)
            ·
              refine ⟨8975464543963989823731121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11967286058618653098308161 8975464543963989823731121)
              ·
                refine ⟨6731598407972992367798341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8975464543963989823731121 6731598407972992367798341)
                ·
                  refine ⟨1262174701494936068962189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6731598407972992367798341 1262174701494936068962189)
                  ·
                    refine ⟨473315513060601025860821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1262174701494936068962189 473315513060601025860821)
                    ·
                      rfl

theorem cell22_1382668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 4, 3].length) (baseStart_1382668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1382668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1382668 prefixEnd_1382668 := by exact prefixLift 1382668
  have htrace : WordTrace (prefixWord ++ tailWord_1382668) baseStart_1382668 baseEnd_1382668 := by
    simpa [prefixWord, tailWord_1382668, baseEnd_1382668] using wordTrace_append hprefix tailTrace_1382668
  have hstable : (prefixWord ++ tailWord_1382668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382668).length < 2 ^ (prefixWord ++ tailWord_1382668).sum := by decide
  have hdescent : baseEnd_1382668 < baseStart_1382668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382670 : List Nat := [4, 1, 1, 2, 1, 2, 4, 3, 4]
def baseStart_1382670 : Nat := 118140960795 + 1382670 * 2 ^ 59
def prefixEnd_1382670 : Nat := 4983230072969 + 3 ^ 40 * 1382670 * 2
def baseEnd_1382670 : Nat := 157772065900491229103605

theorem tailTrace_1382670 : CollatzResearch.WordTrace tailWord_1382670 prefixEnd_1382670 157772065900491229103605 := by
  unfold tailWord_1382670
  simp only [CollatzResearch.WordTrace]
  refine ⟨6303764737603775760118183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33620078600553470720630309 6303764737603775760118183)
  ·
    refine ⟨9455647106405663640177275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6303764737603775760118183 9455647106405663640177275)
    ·
      refine ⟨14183470659608495460265913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9455647106405663640177275 14183470659608495460265913)
      ·
        refine ⟨10637602994706371595199435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14183470659608495460265913 10637602994706371595199435)
        ·
          refine ⟨15956404492059557392799153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10637602994706371595199435 15956404492059557392799153)
          ·
            refine ⟨11967303369044668044599365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15956404492059557392799153 11967303369044668044599365)
            ·
              refine ⟨2243869381695875258362381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11967303369044668044599365 2243869381695875258362381)
              ·
                refine ⟨841451018135953221885893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2243869381695875258362381 841451018135953221885893)
                ·
                  refine ⟨157772065900491229103605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 841451018135953221885893 157772065900491229103605)
                  ·
                    rfl

theorem cell22_1382670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 3, 4].length) (baseStart_1382670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1382670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1382670 prefixEnd_1382670 := by exact prefixLift 1382670
  have htrace : WordTrace (prefixWord ++ tailWord_1382670) baseStart_1382670 baseEnd_1382670 := by
    simpa [prefixWord, tailWord_1382670, baseEnd_1382670] using wordTrace_append hprefix tailTrace_1382670
  have hstable : (prefixWord ++ tailWord_1382670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382670).length < 2 ^ (prefixWord ++ tailWord_1382670).sum := by decide
  have hdescent : baseEnd_1382670 < baseStart_1382670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382711 : List Nat := [1, 1, 3, 1, 2, 1, 1, 4, 2, 6]
def baseStart_1382711 : Nat := 118140960795 + 1382711 * 2 ^ 59
def prefixEnd_1382711 : Nat := 4983230072969 + 3 ^ 40 * 1382711 * 2
def baseEnd_1382711 : Nat := 473330232839363247035689

theorem tailTrace_1382711 : CollatzResearch.WordTrace tailWord_1382711 prefixEnd_1382711 473330232839363247035689 := by
  unfold tailWord_1382711
  simp only [CollatzResearch.WordTrace]
  refine ⟨50431613293681670083187987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33621075529121113388791991 50431613293681670083187987)
  ·
    refine ⟨75647419940522505124781981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50431613293681670083187987 75647419940522505124781981)
    ·
      refine ⟨28367782477695939421793243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75647419940522505124781981 28367782477695939421793243)
      ·
        refine ⟨42551673716543909132689865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28367782477695939421793243 42551673716543909132689865)
        ·
          refine ⟨31913755287407931849517399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42551673716543909132689865 31913755287407931849517399)
          ·
            refine ⟨47870632931111897774276099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31913755287407931849517399 47870632931111897774276099)
            ·
              refine ⟨71805949396667846661414149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47870632931111897774276099 71805949396667846661414149)
              ·
                refine ⟨13463615511875221249015153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71805949396667846661414149 13463615511875221249015153)
                ·
                  refine ⟨10097711633906415936761365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13463615511875221249015153 10097711633906415936761365)
                  ·
                    refine ⟨473330232839363247035689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10097711633906415936761365 473330232839363247035689)
                    ·
                      rfl

theorem cell22_1382711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 6].length) (baseStart_1382711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1382711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1382711 prefixEnd_1382711 := by exact prefixLift 1382711
  have htrace : WordTrace (prefixWord ++ tailWord_1382711) baseStart_1382711 baseEnd_1382711 := by
    simpa [prefixWord, tailWord_1382711, baseEnd_1382711] using wordTrace_append hprefix tailTrace_1382711
  have hstable : (prefixWord ++ tailWord_1382711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382711).length < 2 ^ (prefixWord ++ tailWord_1382711).sum := by decide
  have hdescent : baseEnd_1382711 < baseStart_1382711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382743 : List Nat := [1, 1, 3, 2, 3, 1, 2, 4, 5]
def baseStart_1382743 : Nat := 118140960795 + 1382743 * 2 ^ 59
def prefixEnd_1382743 : Nat := 4983230072969 + 3 ^ 40 * 1382743 * 2
def baseEnd_1382743 : Nat := 157780395697775276745197

theorem tailTrace_1382743 : CollatzResearch.WordTrace tailWord_1382743 prefixEnd_1382743 157780395697775276745197 := by
  unfold tailWord_1382743
  simp only [CollatzResearch.WordTrace]
  refine ⟨50432780429565739548352883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33621853619710493032235255 50432780429565739548352883)
  ·
    refine ⟨75649170644348609322529325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50432780429565739548352883 75649170644348609322529325)
    ·
      refine ⟨28368438991630728495948497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75649170644348609322529325 28368438991630728495948497)
      ·
        refine ⟨21276329243723046371961373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28368438991630728495948497 21276329243723046371961373)
        ·
          refine ⟨7978623466396142389485515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21276329243723046371961373 7978623466396142389485515)
          ·
            refine ⟨11967935199594213584228273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7978623466396142389485515 11967935199594213584228273)
            ·
              refine ⟨8975951399695660188171205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11967935199594213584228273 8975951399695660188171205)
              ·
                refine ⟨1682990887442936285282101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8975951399695660188171205 1682990887442936285282101)
                ·
                  refine ⟨157780395697775276745197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1682990887442936285282101 157780395697775276745197)
                  ·
                    rfl

theorem cell22_1382743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 4, 5].length) (baseStart_1382743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1382743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1382743 prefixEnd_1382743 := by exact prefixLift 1382743
  have htrace : WordTrace (prefixWord ++ tailWord_1382743) baseStart_1382743 baseEnd_1382743 := by
    simpa [prefixWord, tailWord_1382743, baseEnd_1382743] using wordTrace_append hprefix tailTrace_1382743
  have hstable : (prefixWord ++ tailWord_1382743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382743).length < 2 ^ (prefixWord ++ tailWord_1382743).sum := by decide
  have hdescent : baseEnd_1382743 < baseStart_1382743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382760 : List Nat := [2, 1, 4, 2, 2, 2, 1, 3, 5]
def baseStart_1382760 : Nat := 118140960795 + 1382760 * 2 ^ 59
def prefixEnd_1382760 : Nat := 4983230072969 + 3 ^ 40 * 1382760 * 2
def baseEnd_1382760 : Nat := 157782335513581150853513

theorem tailTrace_1382760 : CollatzResearch.WordTrace tailWord_1382760 prefixEnd_1382760 157782335513581150853513 := by
  unfold tailWord_1382760
  simp only [CollatzResearch.WordTrace]
  refine ⟨25216700235252075725860867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33622266980336100967814489 25216700235252075725860867)
  ·
    refine ⟨37825050352878113588791301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25216700235252075725860867 37825050352878113588791301)
    ·
      refine ⟨7092196941164646297898369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37825050352878113588791301 7092196941164646297898369)
      ·
        refine ⟨5319147705873484723423777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7092196941164646297898369 5319147705873484723423777)
        ·
          refine ⟨3989360779405113542567833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5319147705873484723423777 3989360779405113542567833)
          ·
            refine ⟨2992020584553835156925875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3989360779405113542567833 2992020584553835156925875)
            ·
              refine ⟨4488030876830752735388813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2992020584553835156925875 4488030876830752735388813)
              ·
                refine ⟨1683011578811532275770805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4488030876830752735388813 1683011578811532275770805)
                ·
                  refine ⟨157782335513581150853513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1683011578811532275770805 157782335513581150853513)
                  ·
                    rfl

theorem cell22_1382760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 3, 5].length) (baseStart_1382760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1382760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1382760 prefixEnd_1382760 := by exact prefixLift 1382760
  have htrace : WordTrace (prefixWord ++ tailWord_1382760) baseStart_1382760 baseEnd_1382760 := by
    simpa [prefixWord, tailWord_1382760, baseEnd_1382760] using wordTrace_append hprefix tailTrace_1382760
  have hstable : (prefixWord ++ tailWord_1382760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382760).length < 2 ^ (prefixWord ++ tailWord_1382760).sum := by decide
  have hdescent : baseEnd_1382760 < baseStart_1382760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382955 : List Nat := [1, 1, 1, 1, 2, 1, 3, 3, 6, 3]
def baseStart_1382955 : Nat := 118140960795 + 1382955 * 2 ^ 59
def prefixEnd_1382955 : Nat := 4983230072969 + 3 ^ 40 * 1382955 * 2
def baseEnd_1382955 : Nat := 473413759025827943934941

theorem tailTrace_1382955 : CollatzResearch.WordTrace tailWord_1382955 prefixEnd_1382955 473413759025827943934941 := by
  unfold tailWord_1382955
  simp only [CollatzResearch.WordTrace]
  refine ⟨50440512704797699755070319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33627008469865133170046879 50440512704797699755070319)
  ·
    refine ⟨75660769057196549632605479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50440512704797699755070319 75660769057196549632605479)
    ·
      refine ⟨113491153585794824448908219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75660769057196549632605479 113491153585794824448908219)
      ·
        refine ⟨170236730378692236673362329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113491153585794824448908219 170236730378692236673362329)
        ·
          refine ⟨127677547784019177505021747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170236730378692236673362329 127677547784019177505021747)
          ·
            refine ⟨191516321676028766257532621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127677547784019177505021747 191516321676028766257532621)
            ·
              refine ⟨71818620628510787346574733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 191516321676028766257532621 71818620628510787346574733)
              ·
                refine ⟨26931982735691545254965525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71818620628510787346574733 26931982735691545254965525)
                ·
                  refine ⟨1262436690735541183826509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 26931982735691545254965525 1262436690735541183826509)
                  ·
                    refine ⟨473413759025827943934941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1262436690735541183826509 473413759025827943934941)
                    ·
                      rfl

theorem cell22_1382955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 6, 3].length) (baseStart_1382955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1382955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1382955 prefixEnd_1382955 := by exact prefixLift 1382955
  have htrace : WordTrace (prefixWord ++ tailWord_1382955) baseStart_1382955 baseEnd_1382955 := by
    simpa [prefixWord, tailWord_1382955, baseEnd_1382955] using wordTrace_append hprefix tailTrace_1382955
  have hstable : (prefixWord ++ tailWord_1382955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382955).length < 2 ^ (prefixWord ++ tailWord_1382955).sum := by decide
  have hdescent : baseEnd_1382955 < baseStart_1382955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382989 : List Nat := [1, 6, 1, 1, 2, 2, 2, 1, 1, 5]
def baseStart_1382989 : Nat := 118140960795 + 1382989 * 2 ^ 59
def prefixEnd_1382989 : Nat := 4983230072969 + 3 ^ 40 * 1382989 * 2
def baseEnd_1382989 : Nat := 473425397920663188584837

theorem tailTrace_1382989 : CollatzResearch.WordTrace tailWord_1382989 prefixEnd_1382989 473425397920663188584837 := by
  unfold tailWord_1382989
  simp only [CollatzResearch.WordTrace]
  refine ⟨50441752786674523561808021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33627835191116349041205347 50441752786674523561808021)
  ·
    refine ⟨2364457161875368291959751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 50441752786674523561808021 2364457161875368291959751)
    ·
      refine ⟨3546685742813052437939627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2364457161875368291959751 3546685742813052437939627)
      ·
        refine ⟨5320028614219578656909441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3546685742813052437939627 5320028614219578656909441)
        ·
          refine ⟨3990021460664683992682081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5320028614219578656909441 3990021460664683992682081)
          ·
            refine ⟨2992516095498512994511561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3990021460664683992682081 2992516095498512994511561)
            ·
              refine ⟨2244387071623884745883671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2992516095498512994511561 2244387071623884745883671)
              ·
                refine ⟨3366580607435827118825507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2244387071623884745883671 3366580607435827118825507)
                ·
                  refine ⟨5049870911153740678238261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3366580607435827118825507 5049870911153740678238261)
                  ·
                    refine ⟨473425397920663188584837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5049870911153740678238261 473425397920663188584837)
                    ·
                      rfl

theorem cell22_1382989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_1382989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1382989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1382989 prefixEnd_1382989 := by exact prefixLift 1382989
  have htrace : WordTrace (prefixWord ++ tailWord_1382989) baseStart_1382989 baseEnd_1382989 := by
    simpa [prefixWord, tailWord_1382989, baseEnd_1382989] using wordTrace_append hprefix tailTrace_1382989
  have hstable : (prefixWord ++ tailWord_1382989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382989).length < 2 ^ (prefixWord ++ tailWord_1382989).sum := by decide
  have hdescent : baseEnd_1382989 < baseStart_1382989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383010 : List Nat := [3, 3, 2, 3, 2, 1, 2, 1, 1, 4]
def baseStart_1383010 : Nat := 118140960795 + 1383010 * 2 ^ 59
def prefixEnd_1383010 : Nat := 4983230072969 + 3 ^ 40 * 1383010 * 2
def baseEnd_1383010 : Nat := 473432586649826133809773

theorem tailTrace_1383010 : CollatzResearch.WordTrace tailWord_1383010 prefixEnd_1383010 473432586649826133809773 := by
  unfold tailWord_1383010
  simp only [CollatzResearch.WordTrace]
  refine ⟨12610629679899611037080621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33628345813065629432214989 12610629679899611037080621)
  ·
    refine ⟨4728986129962354138905233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12610629679899611037080621 4728986129962354138905233)
    ·
      refine ⟨3546739597471765604178925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4728986129962354138905233 3546739597471765604178925)
      ·
        refine ⟨1330027349051912101567097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3546739597471765604178925 1330027349051912101567097)
        ·
          refine ⟨997520511788934076175323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1330027349051912101567097 997520511788934076175323)
          ·
            refine ⟨1496280767683401114262985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 997520511788934076175323 1496280767683401114262985)
            ·
              refine ⟨1122210575762550835697239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1496280767683401114262985 1122210575762550835697239)
              ·
                refine ⟨1683315863643826253545859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1122210575762550835697239 1683315863643826253545859)
                ·
                  refine ⟨2524973795465739380318789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1683315863643826253545859 2524973795465739380318789)
                  ·
                    refine ⟨473432586649826133809773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2524973795465739380318789 473432586649826133809773)
                    ·
                      rfl

theorem cell22_1383010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_1383010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1383010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1383010 prefixEnd_1383010 := by exact prefixLift 1383010
  have htrace : WordTrace (prefixWord ++ tailWord_1383010) baseStart_1383010 baseEnd_1383010 := by
    simpa [prefixWord, tailWord_1383010, baseEnd_1383010] using wordTrace_append hprefix tailTrace_1383010
  have hstable : (prefixWord ++ tailWord_1383010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383010).length < 2 ^ (prefixWord ++ tailWord_1383010).sum := by decide
  have hdescent : baseEnd_1383010 < baseStart_1383010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383068 : List Nat := [2, 2, 3, 2, 2, 3, 1, 3, 1, 3]
def baseStart_1383068 : Nat := 118140960795 + 1383068 * 2 ^ 59
def prefixEnd_1383068 : Nat := 4983230072969 + 3 ^ 40 * 1383068 * 2
def baseEnd_1383068 : Nat := 473452441235133315859595

theorem tailTrace_1383068 : CollatzResearch.WordTrace tailWord_1383068 prefixEnd_1383068 473452441235133315859595 := by
  unfold tailWord_1383068
  simp only [CollatzResearch.WordTrace]
  refine ⟨25222317076694160026966929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33629756102258880035955905 25222317076694160026966929)
  ·
    refine ⟨18916737807520620020225197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25222317076694160026966929 18916737807520620020225197)
    ·
      refine ⟨7093776677820232507584449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18916737807520620020225197 7093776677820232507584449)
      ·
        refine ⟨5320332508365174380688337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7093776677820232507584449 5320332508365174380688337)
        ·
          refine ⟨3990249381273880785516253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5320332508365174380688337 3990249381273880785516253)
          ·
            refine ⟨1496343517977705294568595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3990249381273880785516253 1496343517977705294568595)
            ·
              refine ⟨2244515276966557941852893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1496343517977705294568595 2244515276966557941852893)
              ·
                refine ⟨841693228862459228194835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2244515276966557941852893 841693228862459228194835)
                ·
                  refine ⟨1262539843293688842292253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 841693228862459228194835 1262539843293688842292253)
                  ·
                    refine ⟨473452441235133315859595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1262539843293688842292253 473452441235133315859595)
                    ·
                      rfl

theorem cell22_1383068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 3, 1, 3].length) (baseStart_1383068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1383068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1383068 prefixEnd_1383068 := by exact prefixLift 1383068
  have htrace : WordTrace (prefixWord ++ tailWord_1383068) baseStart_1383068 baseEnd_1383068 := by
    simpa [prefixWord, tailWord_1383068, baseEnd_1383068] using wordTrace_append hprefix tailTrace_1383068
  have hstable : (prefixWord ++ tailWord_1383068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383068).length < 2 ^ (prefixWord ++ tailWord_1383068).sum := by decide
  have hdescent : baseEnd_1383068 < baseStart_1383068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383139 : List Nat := [1, 1, 1, 7, 1, 1, 2, 2, 2, 4]
def baseStart_1383139 : Nat := 118140960795 + 1383139 * 2 ^ 59
def prefixEnd_1383139 : Nat := 4983230072969 + 3 ^ 40 * 1383139 * 2
def baseEnd_1383139 : Nat := 473476745986112797334377

theorem tailTrace_1383139 : CollatzResearch.WordTrace tailWord_1383139 prefixEnd_1383139 473476745986112797334377 := by
  unfold tailWord_1383139
  simp only [CollatzResearch.WordTrace]
  refine ⟨50447223736131099179768471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33631482490754066119845647 50447223736131099179768471)
  ·
    refine ⟨75670835604196648769652707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50447223736131099179768471 75670835604196648769652707)
    ·
      refine ⟨113506253406294973154479061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75670835604196648769652707 113506253406294973154479061)
      ·
        refine ⟨2660302814210038433308103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 113506253406294973154479061 2660302814210038433308103)
        ·
          refine ⟨3990454221315057649962155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2660302814210038433308103 3990454221315057649962155)
          ·
            refine ⟨5985681331972586474943233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3990454221315057649962155 5985681331972586474943233)
            ·
              refine ⟨4489260998979439856207425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5985681331972586474943233 4489260998979439856207425)
              ·
                refine ⟨3366945749234579892155569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4489260998979439856207425 3366945749234579892155569)
                ·
                  refine ⟨2525209311925934919116677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3366945749234579892155569 2525209311925934919116677)
                  ·
                    refine ⟨473476745986112797334377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2525209311925934919116677 473476745986112797334377)
                    ·
                      rfl

theorem cell22_1383139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 2, 2, 4].length) (baseStart_1383139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1383139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1383139 prefixEnd_1383139 := by exact prefixLift 1383139
  have htrace : WordTrace (prefixWord ++ tailWord_1383139) baseStart_1383139 baseEnd_1383139 := by
    simpa [prefixWord, tailWord_1383139, baseEnd_1383139] using wordTrace_append hprefix tailTrace_1383139
  have hstable : (prefixWord ++ tailWord_1383139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383139).length < 2 ^ (prefixWord ++ tailWord_1383139).sum := by decide
  have hdescent : baseEnd_1383139 < baseStart_1383139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383141 : List Nat := [1, 3, 1, 4, 1, 3, 2, 2, 2, 3]
def baseStart_1383141 : Nat := 118140960795 + 1383141 * 2 ^ 59
def prefixEnd_1383141 : Nat := 4983230072969 + 3 ^ 40 * 1383141 * 2
def baseEnd_1383141 : Nat := 473477430626985458784371

theorem tailTrace_1383141 : CollatzResearch.WordTrace tailWord_1383141 prefixEnd_1383141 473477430626985458784371 := by
  unfold tailWord_1383141
  simp only [CollatzResearch.WordTrace]
  refine ⟨50447296682123853521341277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33631531121415902347560851 50447296682123853521341277)
  ·
    refine ⟨18917736255796445070502979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50447296682123853521341277 18917736255796445070502979)
    ·
      refine ⟨28376604383694667605754469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18917736255796445070502979 28376604383694667605754469)
      ·
        refine ⟨5320613321942750176078963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28376604383694667605754469 5320613321942750176078963)
        ·
          refine ⟨7980919982914125264118445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5320613321942750176078963 7980919982914125264118445)
          ·
            refine ⟨2992844993592796974044417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7980919982914125264118445 2992844993592796974044417)
            ·
              refine ⟨2244633745194597730533313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2992844993592796974044417 2244633745194597730533313)
              ·
                refine ⟨1683475308895948297899985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2244633745194597730533313 1683475308895948297899985)
                ·
                  refine ⟨1262606481671961223424989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1683475308895948297899985 1262606481671961223424989)
                  ·
                    refine ⟨473477430626985458784371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1262606481671961223424989 473477430626985458784371)
                    ·
                      rfl

theorem cell22_1383141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 2, 2, 3].length) (baseStart_1383141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1383141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1383141 prefixEnd_1383141 := by exact prefixLift 1383141
  have htrace : WordTrace (prefixWord ++ tailWord_1383141) baseStart_1383141 baseEnd_1383141 := by
    simpa [prefixWord, tailWord_1383141, baseEnd_1383141] using wordTrace_append hprefix tailTrace_1383141
  have hstable : (prefixWord ++ tailWord_1383141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383141).length < 2 ^ (prefixWord ++ tailWord_1383141).sum := by decide
  have hdescent : baseEnd_1383141 < baseStart_1383141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383154 : List Nat := [3, 2, 1, 3, 1, 4, 1, 7]
def baseStart_1383154 : Nat := 118140960795 + 1383154 * 2 ^ 59
def prefixEnd_1383154 : Nat := 4983230072969 + 3 ^ 40 * 1383154 * 2
def baseEnd_1383154 : Nat := 52609097865850862023259

theorem tailTrace_1383154 : CollatzResearch.WordTrace tailWord_1383154 prefixEnd_1383154 52609097865850862023259 := by
  unfold tailWord_1383154
  simp only [CollatzResearch.WordTrace]
  refine ⟨12611942707769189185391129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33631847220717837827709677 12611942707769189185391129)
  ·
    refine ⟨9458957030826891889043347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12611942707769189185391129 9458957030826891889043347)
    ·
      refine ⟨14188435546240337833565021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9458957030826891889043347 14188435546240337833565021)
      ·
        refine ⟨5320663329840126687586883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14188435546240337833565021 5320663329840126687586883)
        ·
          refine ⟨7980994994760190031380325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5320663329840126687586883 7980994994760190031380325)
          ·
            refine ⟨1496436561517535630883811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7980994994760190031380325 1496436561517535630883811)
            ·
              refine ⟨2244654842276303446325717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1496436561517535630883811 2244654842276303446325717)
              ·
                refine ⟨52609097865850862023259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2244654842276303446325717 52609097865850862023259)
                ·
                  rfl

theorem cell22_1383154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 7].length) (baseStart_1383154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1383154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1383154 prefixEnd_1383154 := by exact prefixLift 1383154
  have htrace : WordTrace (prefixWord ++ tailWord_1383154) baseStart_1383154 baseEnd_1383154 := by
    simpa [prefixWord, tailWord_1383154, baseEnd_1383154] using wordTrace_append hprefix tailTrace_1383154
  have hstable : (prefixWord ++ tailWord_1383154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383154).length < 2 ^ (prefixWord ++ tailWord_1383154).sum := by decide
  have hdescent : baseEnd_1383154 < baseStart_1383154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383182 : List Nat := [4, 1, 1, 2, 1, 1, 1, 4, 7]
def baseStart_1383182 : Nat := 118140960795 + 1383182 * 2 ^ 59
def prefixEnd_1383182 : Nat := 4983230072969 + 3 ^ 40 * 1383182 * 2
def baseEnd_1383182 : Nat := 157830488588291672836415

theorem tailTrace_1383182 : CollatzResearch.WordTrace tailWord_1383182 prefixEnd_1383182 157830488588291672836415 := by
  unfold tailWord_1383182
  simp only [CollatzResearch.WordTrace]
  refine ⟨6306099009371914690447975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33632528049983545015722533 6306099009371914690447975)
  ·
    refine ⟨9459148514057872035671963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6306099009371914690447975 9459148514057872035671963)
    ·
      refine ⟨14188722771086808053507945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9459148514057872035671963 14188722771086808053507945)
      ·
        refine ⟨10641542078315106040130959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14188722771086808053507945 10641542078315106040130959)
        ·
          refine ⟨15962313117472659060196439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10641542078315106040130959 15962313117472659060196439)
          ·
            refine ⟨23943469676208988590294659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15962313117472659060196439 23943469676208988590294659)
            ·
              refine ⟨35915204514313482885441989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23943469676208988590294659 35915204514313482885441989)
              ·
                refine ⟨6734100846433778041020373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35915204514313482885441989 6734100846433778041020373)
                ·
                  refine ⟨157830488588291672836415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6734100846433778041020373 157830488588291672836415)
                  ·
                    rfl

theorem cell22_1383182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 7].length) (baseStart_1383182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1383182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1383182 prefixEnd_1383182 := by exact prefixLift 1383182
  have htrace : WordTrace (prefixWord ++ tailWord_1383182) baseStart_1383182 baseEnd_1383182 := by
    simpa [prefixWord, tailWord_1383182, baseEnd_1383182] using wordTrace_append hprefix tailTrace_1383182
  have hstable : (prefixWord ++ tailWord_1383182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383182).length < 2 ^ (prefixWord ++ tailWord_1383182).sum := by decide
  have hdescent : baseEnd_1383182 < baseStart_1383182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383199 : List Nat := [1, 1, 2, 4, 2, 2, 3, 2, 5]
def baseStart_1383199 : Nat := 118140960795 + 1383199 * 2 ^ 59
def prefixEnd_1383199 : Nat := 4983230072969 + 3 ^ 40 * 1383199 * 2
def baseEnd_1383199 : Nat := 157832428404097546944731

theorem tailTrace_1383199 : CollatzResearch.WordTrace tailWord_1383199 prefixEnd_1383199 157832428404097546944731 := by
  unfold tailWord_1383199
  simp only [CollatzResearch.WordTrace]
  refine ⟨50449412115913729426952651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33632941410609152951301767 50449412115913729426952651)
  ·
    refine ⟨75674118173870594140428977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50449412115913729426952651 75674118173870594140428977)
    ·
      refine ⟨56755588630402945605321733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75674118173870594140428977 56755588630402945605321733)
      ·
        refine ⟨10641672868200552300997825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56755588630402945605321733 10641672868200552300997825)
        ·
          refine ⟨7981254651150414225748369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10641672868200552300997825 7981254651150414225748369)
          ·
            refine ⟨5985940988362810669311277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7981254651150414225748369 5985940988362810669311277)
            ·
              refine ⟨2244727870636054000991729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5985940988362810669311277 2244727870636054000991729)
              ·
                refine ⟨1683545902977040500743797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2244727870636054000991729 1683545902977040500743797)
                ·
                  refine ⟨157832428404097546944731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1683545902977040500743797 157832428404097546944731)
                  ·
                    rfl

theorem cell22_1383199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 2, 5].length) (baseStart_1383199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1383199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1383199 prefixEnd_1383199 := by exact prefixLift 1383199
  have htrace : WordTrace (prefixWord ++ tailWord_1383199) baseStart_1383199 baseEnd_1383199 := by
    simpa [prefixWord, tailWord_1383199, baseEnd_1383199] using wordTrace_append hprefix tailTrace_1383199
  have hstable : (prefixWord ++ tailWord_1383199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383199).length < 2 ^ (prefixWord ++ tailWord_1383199).sum := by decide
  have hdescent : baseEnd_1383199 < baseStart_1383199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383276 : List Nat := [2, 2, 1, 1, 4, 1, 3, 3, 2, 3]
def baseStart_1383276 : Nat := 118140960795 + 1383276 * 2 ^ 59
def prefixEnd_1383276 : Nat := 4983230072969 + 3 ^ 40 * 1383276 * 2
def baseEnd_1383276 : Nat := 473523643885890106658957

theorem tailTrace_1383276 : CollatzResearch.WordTrace tailWord_1383276 prefixEnd_1383276 473523643885890106658957 := by
  unfold tailWord_1383276
  simp only [CollatzResearch.WordTrace]
  refine ⟨25226110268317385788752841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33634813691089847718337121 25226110268317385788752841)
  ·
    refine ⟨18919582701238039341564631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25226110268317385788752841 18919582701238039341564631)
    ·
      refine ⟨28379374051857059012346947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18919582701238039341564631 28379374051857059012346947)
      ·
        refine ⟨42569061077785588518520421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28379374051857059012346947 42569061077785588518520421)
        ·
          refine ⟨7981698952084797847222579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42569061077785588518520421 7981698952084797847222579)
          ·
            refine ⟨11972548428127196770833869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7981698952084797847222579 11972548428127196770833869)
            ·
              refine ⟨4489705660547698789062701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11972548428127196770833869 4489705660547698789062701)
              ·
                refine ⟨1683639622705387045898513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4489705660547698789062701 1683639622705387045898513)
                ·
                  refine ⟨1262729717029040284423885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1683639622705387045898513 1262729717029040284423885)
                  ·
                    refine ⟨473523643885890106658957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1262729717029040284423885 473523643885890106658957)
                    ·
                      rfl

theorem cell22_1383276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 3].length) (baseStart_1383276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1383276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1383276 prefixEnd_1383276 := by exact prefixLift 1383276
  have htrace : WordTrace (prefixWord ++ tailWord_1383276) baseStart_1383276 baseEnd_1383276 := by
    simpa [prefixWord, tailWord_1383276, baseEnd_1383276] using wordTrace_append hprefix tailTrace_1383276
  have hstable : (prefixWord ++ tailWord_1383276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383276).length < 2 ^ (prefixWord ++ tailWord_1383276).sum := by decide
  have hdescent : baseEnd_1383276 < baseStart_1383276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383287 : List Nat := [1, 1, 3, 1, 1, 2, 1, 3, 2, 7]
def baseStart_1383287 : Nat := 118140960795 + 1383287 * 2 ^ 59
def prefixEnd_1383287 : Nat := 4983230072969 + 3 ^ 40 * 1383287 * 2
def baseEnd_1383287 : Nat := 473527409410689744633923

theorem tailTrace_1383287 : CollatzResearch.WordTrace tailWord_1383287 prefixEnd_1383287 473527409410689744633923 := by
  unfold tailWord_1383287
  simp only [CollatzResearch.WordTrace]
  refine ⟨50452621739594920456156115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33635081159729946970770743 50452621739594920456156115)
  ·
    refine ⟨75678932609392380684234173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50452621739594920456156115 75678932609392380684234173)
    ·
      refine ⟨28379599728522142756587815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75678932609392380684234173 28379599728522142756587815)
      ·
        refine ⟨42569399592783214134881723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28379599728522142756587815 42569399592783214134881723)
        ·
          refine ⟨63854099389174821202322585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42569399592783214134881723 63854099389174821202322585)
          ·
            refine ⟨47890574541881115901741939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63854099389174821202322585 47890574541881115901741939)
            ·
              refine ⟨71835861812821673852612909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47890574541881115901741939 71835861812821673852612909)
              ·
                refine ⟨26938448179808127694729841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71835861812821673852612909 26938448179808127694729841)
                ·
                  refine ⟨20203836134856095771047381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26938448179808127694729841 20203836134856095771047381)
                  ·
                    refine ⟨473527409410689744633923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20203836134856095771047381 473527409410689744633923)
                    ·
                      rfl

theorem cell22_1383287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 7].length) (baseStart_1383287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1383287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1383287 prefixEnd_1383287 := by exact prefixLift 1383287
  have htrace : WordTrace (prefixWord ++ tailWord_1383287) baseStart_1383287 baseEnd_1383287 := by
    simpa [prefixWord, tailWord_1383287, baseEnd_1383287] using wordTrace_append hprefix tailTrace_1383287
  have hstable : (prefixWord ++ tailWord_1383287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383287).length < 2 ^ (prefixWord ++ tailWord_1383287).sum := by decide
  have hdescent : baseEnd_1383287 < baseStart_1383287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383349 : List Nat := [1, 3, 3, 2, 1, 1, 1, 2, 1, 7]
def baseStart_1383349 : Nat := 118140960795 + 1383349 * 2 ^ 59
def prefixEnd_1383349 : Nat := 4983230072969 + 3 ^ 40 * 1383349 * 2
def baseEnd_1383349 : Nat := 473548633277742249583733

theorem tailTrace_1383349 : CollatzResearch.WordTrace tailWord_1383349 prefixEnd_1383349 473548633277742249583733 := by
  unfold tailWord_1383349
  simp only [CollatzResearch.WordTrace]
  refine ⟨50454883065370305044913101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33636588710246870029942067 50454883065370305044913101)
  ·
    refine ⟨18920581149513864391842413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50454883065370305044913101 18920581149513864391842413)
    ·
      refine ⟨7095217931067699146940905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18920581149513864391842413 7095217931067699146940905)
      ·
        refine ⟨5321413448300774360205679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7095217931067699146940905 5321413448300774360205679)
        ·
          refine ⟨7982120172451161540308519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5321413448300774360205679 7982120172451161540308519)
          ·
            refine ⟨11973180258676742310462779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7982120172451161540308519 11973180258676742310462779)
            ·
              refine ⟨17959770388015113465694169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11973180258676742310462779 17959770388015113465694169)
              ·
                refine ⟨13469827791011335099270627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17959770388015113465694169 13469827791011335099270627)
                ·
                  refine ⟨20204741686517002648905941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13469827791011335099270627 20204741686517002648905941)
                  ·
                    refine ⟨473548633277742249583733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20204741686517002648905941 473548633277742249583733)
                    ·
                      rfl

theorem cell22_1383349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_1383349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1383349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1383349 prefixEnd_1383349 := by exact prefixLift 1383349
  have htrace : WordTrace (prefixWord ++ tailWord_1383349) baseStart_1383349 baseEnd_1383349 := by
    simpa [prefixWord, tailWord_1383349, baseEnd_1383349] using wordTrace_append hprefix tailTrace_1383349
  have hstable : (prefixWord ++ tailWord_1383349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383349).length < 2 ^ (prefixWord ++ tailWord_1383349).sum := by decide
  have hdescent : baseEnd_1383349 < baseStart_1383349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383368 : List Nat := [2, 1, 3, 1, 5, 2, 1, 2, 5]
def baseStart_1383368 : Nat := 118140960795 + 1383368 * 2 ^ 59
def prefixEnd_1383368 : Nat := 4983230072969 + 3 ^ 40 * 1383368 * 2
def baseEnd_1383368 : Nat := 157851712455344177786225

theorem tailTrace_1383368 : CollatzResearch.WordTrace tailWord_1383368 prefixEnd_1383368 157851712455344177786225 := by
  unfold tailWord_1383368
  simp only [CollatzResearch.WordTrace]
  refine ⟨25227788026150735644927379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33637050701534314193236505 25227788026150735644927379)
  ·
    refine ⟨37841682039226103467391069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25227788026150735644927379 37841682039226103467391069)
    ·
      refine ⟨14190630764709788800271651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37841682039226103467391069 14190630764709788800271651)
      ·
        refine ⟨21285946147064683200407477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14190630764709788800271651 21285946147064683200407477)
        ·
          refine ⟨1995557451287314050038201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21285946147064683200407477 1995557451287314050038201)
          ·
            refine ⟨1496668088465485537528651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1995557451287314050038201 1496668088465485537528651)
            ·
              refine ⟨2245002132698228306292977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1496668088465485537528651 2245002132698228306292977)
              ·
                refine ⟨1683751599523671229719733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2245002132698228306292977 1683751599523671229719733)
                ·
                  refine ⟨157851712455344177786225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1683751599523671229719733 157851712455344177786225)
                  ·
                    rfl

theorem cell22_1383368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 2, 5].length) (baseStart_1383368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1383368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1383368 prefixEnd_1383368 := by exact prefixLift 1383368
  have htrace : WordTrace (prefixWord ++ tailWord_1383368) baseStart_1383368 baseEnd_1383368 := by
    simpa [prefixWord, tailWord_1383368, baseEnd_1383368] using wordTrace_append hprefix tailTrace_1383368
  have hstable : (prefixWord ++ tailWord_1383368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383368).length < 2 ^ (prefixWord ++ tailWord_1383368).sum := by decide
  have hdescent : baseEnd_1383368 < baseStart_1383368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383445 : List Nat := [1, 3, 2, 1, 4, 1, 4, 1, 2, 3]
def baseStart_1383445 : Nat := 118140960795 + 1383445 * 2 ^ 59
def prefixEnd_1383445 : Nat := 4983230072969 + 3 ^ 40 * 1383445 * 2
def baseEnd_1383445 : Nat := 473581496039629999183439

theorem tailTrace_1383445 : CollatzResearch.WordTrace tailWord_1383445 prefixEnd_1383445 473581496039629999183439 := by
  unfold tailWord_1383445
  simp only [CollatzResearch.WordTrace]
  refine ⟨50458384473022513440407789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33638922982015008960271859 50458384473022513440407789)
  ·
    refine ⟨18921894177383442540152921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50458384473022513440407789 18921894177383442540152921)
    ·
      refine ⟨14191420633037581905114691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18921894177383442540152921 14191420633037581905114691)
      ·
        refine ⟨21287130949556372857672037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14191420633037581905114691 21287130949556372857672037)
        ·
          refine ⟨3991337053041819910813507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21287130949556372857672037 3991337053041819910813507)
          ·
            refine ⟨5987005579562729866220261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3991337053041819910813507 5987005579562729866220261)
            ·
              refine ⟨1122563546168011849916299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5987005579562729866220261 1122563546168011849916299)
              ·
                refine ⟨1683845319252017774874449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1122563546168011849916299 1683845319252017774874449)
                ·
                  refine ⟨1262883989439013331155837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1683845319252017774874449 1262883989439013331155837)
                  ·
                    refine ⟨473581496039629999183439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1262883989439013331155837 473581496039629999183439)
                    ·
                      rfl

theorem cell22_1383445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 4, 1, 2, 3].length) (baseStart_1383445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1383445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1383445 prefixEnd_1383445 := by exact prefixLift 1383445
  have htrace : WordTrace (prefixWord ++ tailWord_1383445) baseStart_1383445 baseEnd_1383445 := by
    simpa [prefixWord, tailWord_1383445, baseEnd_1383445] using wordTrace_append hprefix tailTrace_1383445
  have hstable : (prefixWord ++ tailWord_1383445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383445).length < 2 ^ (prefixWord ++ tailWord_1383445).sum := by decide
  have hdescent : baseEnd_1383445 < baseStart_1383445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383499 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 1, 10]
def baseStart_1383499 : Nat := 118140960795 + 1383499 * 2 ^ 59
def prefixEnd_1383499 : Nat := 4983230072969 + 3 ^ 40 * 1383499 * 2
def baseEnd_1383499 : Nat := 473599981343191858333273

theorem tailTrace_1383499 : CollatzResearch.WordTrace tailWord_1383499 prefixEnd_1383499 473599981343191858333273 := by
  unfold tailWord_1383499
  simp only [CollatzResearch.WordTrace]
  refine ⟨50460354014826880662873551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33640236009884587108582367 50460354014826880662873551)
  ·
    refine ⟨75690531022240320994310327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50460354014826880662873551 75690531022240320994310327)
    ·
      refine ⟨113535796533360481491465491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75690531022240320994310327 113535796533360481491465491)
      ·
        refine ⟨170303694800040722237198237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113535796533360481491465491 170303694800040722237198237)
        ·
          refine ⟨63863885550015270838949339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 170303694800040722237198237 63863885550015270838949339)
          ·
            refine ⟨95795828325022906258424009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63863885550015270838949339 95795828325022906258424009)
            ·
              refine ⟨71846871243767179693818007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95795828325022906258424009 71846871243767179693818007)
              ·
                refine ⟨107770306865650769540727011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71846871243767179693818007 107770306865650769540727011)
                ·
                  refine ⟨161655460298476154311090517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107770306865650769540727011 161655460298476154311090517)
                  ·
                    refine ⟨473599981343191858333273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 161655460298476154311090517 473599981343191858333273)
                    ·
                      rfl

theorem cell22_1383499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 10].length) (baseStart_1383499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1383499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1383499 prefixEnd_1383499 := by exact prefixLift 1383499
  have htrace : WordTrace (prefixWord ++ tailWord_1383499) baseStart_1383499 baseEnd_1383499 := by
    simpa [prefixWord, tailWord_1383499, baseEnd_1383499] using wordTrace_append hprefix tailTrace_1383499
  have hstable : (prefixWord ++ tailWord_1383499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383499).length < 2 ^ (prefixWord ++ tailWord_1383499).sum := by decide
  have hdescent : baseEnd_1383499 < baseStart_1383499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383548 : List Nat := [2, 2, 2, 1, 1, 3, 1, 6, 4]
def baseStart_1383548 : Nat := 118140960795 + 1383548 * 2 ^ 59
def prefixEnd_1383548 : Nat := 4983230072969 + 3 ^ 40 * 1383548 * 2
def baseEnd_1383548 : Nat := 157872251681524021286041

theorem tailTrace_1383548 : CollatzResearch.WordTrace tailWord_1383548 prefixEnd_1383548 157872251681524021286041 := by
  unfold tailWord_1383548
  simp only [CollatzResearch.WordTrace]
  refine ⟨25231070595824681015703649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33641427461099574687604865 25231070595824681015703649)
  ·
    refine ⟨18923302946868510761777737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25231070595824681015703649 18923302946868510761777737)
    ·
      refine ⟨14192477210151383071333303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18923302946868510761777737 14192477210151383071333303)
      ·
        refine ⟨21288715815227074606999955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14192477210151383071333303 21288715815227074606999955)
        ·
          refine ⟨31933073722840611910499933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21288715815227074606999955 31933073722840611910499933)
          ·
            refine ⟨11974902646065229466437475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31933073722840611910499933 11974902646065229466437475)
            ·
              refine ⟨17962353969097844199656213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11974902646065229466437475 17962353969097844199656213)
              ·
                refine ⟨841985342301461446858885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17962353969097844199656213 841985342301461446858885)
                ·
                  refine ⟨157872251681524021286041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 841985342301461446858885 157872251681524021286041)
                  ·
                    rfl

theorem cell22_1383548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 6, 4].length) (baseStart_1383548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1383548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1383548 prefixEnd_1383548 := by exact prefixLift 1383548
  have htrace : WordTrace (prefixWord ++ tailWord_1383548) baseStart_1383548 baseEnd_1383548 := by
    simpa [prefixWord, tailWord_1383548, baseEnd_1383548] using wordTrace_append hprefix tailTrace_1383548
  have hstable : (prefixWord ++ tailWord_1383548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383548).length < 2 ^ (prefixWord ++ tailWord_1383548).sum := by decide
  have hdescent : baseEnd_1383548 < baseStart_1383548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383561 : List Nat := [1, 2, 1, 1, 4, 3, 1, 2, 1, 6]
def baseStart_1383561 : Nat := 118140960795 + 1383561 * 2 ^ 59
def prefixEnd_1383561 : Nat := 4983230072969 + 3 ^ 40 * 1383561 * 2
def baseEnd_1383561 : Nat := 473621205210244363283083

theorem tailTrace_1383561 : CollatzResearch.WordTrace tailWord_1383561 prefixEnd_1383561 473621205210244363283083 := by
  unfold tailWord_1383561
  simp only [CollatzResearch.WordTrace]
  refine ⟨50462615340602265251630537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33641743560401510167753691 50462615340602265251630537)
  ·
    refine ⟨37846961505451698938722903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50462615340602265251630537 37846961505451698938722903)
    ·
      refine ⟨56770442258177548408084355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37846961505451698938722903 56770442258177548408084355)
      ·
        refine ⟨85155663387266322612126533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56770442258177548408084355 85155663387266322612126533)
        ·
          refine ⟨15966686885112435489773725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85155663387266322612126533 15966686885112435489773725)
          ·
            refine ⟨5987507581917163308665147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15966686885112435489773725 5987507581917163308665147)
            ·
              refine ⟨8981261372875744962997721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5987507581917163308665147 8981261372875744962997721)
              ·
                refine ⟨6735946029656808722248291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8981261372875744962997721 6735946029656808722248291)
                ·
                  refine ⟨10103919044485213083372437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6735946029656808722248291 10103919044485213083372437)
                  ·
                    refine ⟨473621205210244363283083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10103919044485213083372437 473621205210244363283083)
                    ·
                      rfl

theorem cell22_1383561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 6].length) (baseStart_1383561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1383561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1383561 prefixEnd_1383561 := by exact prefixLift 1383561
  have htrace : WordTrace (prefixWord ++ tailWord_1383561) baseStart_1383561 baseEnd_1383561 := by
    simpa [prefixWord, tailWord_1383561, baseEnd_1383561] using wordTrace_append hprefix tailTrace_1383561
  have hstable : (prefixWord ++ tailWord_1383561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383561).length < 2 ^ (prefixWord ++ tailWord_1383561).sum := by decide
  have hdescent : baseEnd_1383561 < baseStart_1383561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383563 : List Nat := [1, 1, 1, 1, 4, 1, 1, 7, 2, 3]
def baseStart_1383563 : Nat := 118140960795 + 1383563 * 2 ^ 59
def prefixEnd_1383563 : Nat := 4983230072969 + 3 ^ 40 * 1383563 * 2
def baseEnd_1383563 : Nat := 473621889851117024733077

theorem tailTrace_1383563 : CollatzResearch.WordTrace tailWord_1383563 prefixEnd_1383563 473621889851117024733077 := by
  unfold tailWord_1383563
  simp only [CollatzResearch.WordTrace]
  refine ⟨50462688286595019593203343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33641792191063346395468895 50462688286595019593203343)
  ·
    refine ⟨75694032429892529389805015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50462688286595019593203343 75694032429892529389805015)
    ·
      refine ⟨113541048644838794084707523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75694032429892529389805015 113541048644838794084707523)
      ·
        refine ⟨170311572967258191127061285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113541048644838794084707523 170311572967258191127061285)
        ·
          refine ⟨31933419931360910836323991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 170311572967258191127061285 31933419931360910836323991)
          ·
            refine ⟨47900129897041366254485987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31933419931360910836323991 47900129897041366254485987)
            ·
              refine ⟨71850194845562049381728981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47900129897041366254485987 71850194845562049381728981)
              ·
                refine ⟨1683988941692860532384273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 71850194845562049381728981 1683988941692860532384273)
                ·
                  refine ⟨1262991706269645399288205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1683988941692860532384273 1262991706269645399288205)
                  ·
                    refine ⟨473621889851117024733077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1262991706269645399288205 473621889851117024733077)
                    ·
                      rfl

theorem cell22_1383563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 7, 2, 3].length) (baseStart_1383563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1383563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1383563 prefixEnd_1383563 := by exact prefixLift 1383563
  have htrace : WordTrace (prefixWord ++ tailWord_1383563) baseStart_1383563 baseEnd_1383563 := by
    simpa [prefixWord, tailWord_1383563, baseEnd_1383563] using wordTrace_append hprefix tailTrace_1383563
  have hstable : (prefixWord ++ tailWord_1383563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383563).length < 2 ^ (prefixWord ++ tailWord_1383563).sum := by decide
  have hdescent : baseEnd_1383563 < baseStart_1383563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383578 : List Nat := [3, 1, 1, 5, 1, 1, 2, 1, 1, 6]
def baseStart_1383578 : Nat := 118140960795 + 1383578 * 2 ^ 59
def prefixEnd_1383578 : Nat := 4983230072969 + 3 ^ 40 * 1383578 * 2
def baseEnd_1383578 : Nat := 473627024657661985608031

theorem tailTrace_1383578 : CollatzResearch.WordTrace tailWord_1383578 prefixEnd_1383578 473627024657661985608031 := by
  unfold tailWord_1383578
  simp only [CollatzResearch.WordTrace]
  refine ⟨12615808845385169288749847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33642156921027118103332925 12615808845385169288749847)
  ·
    refine ⟨18923713268077753933124771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12615808845385169288749847 18923713268077753933124771)
    ·
      refine ⟨28385569902116630899687157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18923713268077753933124771 28385569902116630899687157)
      ·
        refine ⟨2661147178323434146845671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28385569902116630899687157 2661147178323434146845671)
        ·
          refine ⟨3991720767485151220268507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2661147178323434146845671 3991720767485151220268507)
          ·
            refine ⟨5987581151227726830402761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3991720767485151220268507 5987581151227726830402761)
            ·
              refine ⟨4490685863420795122802071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5987581151227726830402761 4490685863420795122802071)
              ·
                refine ⟨6736028795131192684203107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4490685863420795122802071 6736028795131192684203107)
                ·
                  refine ⟨10104043192696789026304661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6736028795131192684203107 10104043192696789026304661)
                  ·
                    refine ⟨473627024657661985608031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10104043192696789026304661 473627024657661985608031)
                    ·
                      rfl

theorem cell22_1383578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 1, 6].length) (baseStart_1383578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1383578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1383578 prefixEnd_1383578 := by exact prefixLift 1383578
  have htrace : WordTrace (prefixWord ++ tailWord_1383578) baseStart_1383578 baseEnd_1383578 := by
    simpa [prefixWord, tailWord_1383578, baseEnd_1383578] using wordTrace_append hprefix tailTrace_1383578
  have hstable : (prefixWord ++ tailWord_1383578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383578).length < 2 ^ (prefixWord ++ tailWord_1383578).sum := by decide
  have hdescent : baseEnd_1383578 < baseStart_1383578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383582 : List Nat := [4, 3, 1, 1, 2, 1, 3, 3, 4]
def baseStart_1383582 : Nat := 118140960795 + 1383582 * 2 ^ 59
def prefixEnd_1383582 : Nat := 4983230072969 + 3 ^ 40 * 1383582 * 2
def baseEnd_1383582 : Nat := 157876131313135769502673

theorem tailTrace_1383582 : CollatzResearch.WordTrace tailWord_1383582 prefixEnd_1383582 157876131313135769502673 := by
  unfold tailWord_1383582
  simp only [CollatzResearch.WordTrace]
  refine ⟨6307922659190773229768125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33642254182350790558763333 6307922659190773229768125)
  ·
    refine ⟨2365470997196539961163047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6307922659190773229768125 2365470997196539961163047)
    ·
      refine ⟨3548206495794809941744571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2365470997196539961163047 3548206495794809941744571)
      ·
        refine ⟨5322309743692214912616857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3548206495794809941744571 5322309743692214912616857)
        ·
          refine ⟨3991732307769161184462643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5322309743692214912616857 3991732307769161184462643)
          ·
            refine ⟨5987598461653741776693965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3991732307769161184462643 5987598461653741776693965)
            ·
              refine ⟨2245349423120153166260237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5987598461653741776693965 2245349423120153166260237)
              ·
                refine ⟨842006033670057437347589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2245349423120153166260237 842006033670057437347589)
                ·
                  refine ⟨157876131313135769502673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 842006033670057437347589 157876131313135769502673)
                  ·
                    rfl

theorem cell22_1383582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_1383582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1383582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1383582 prefixEnd_1383582 := by exact prefixLift 1383582
  have htrace : WordTrace (prefixWord ++ tailWord_1383582) baseStart_1383582 baseEnd_1383582 := by
    simpa [prefixWord, tailWord_1383582, baseEnd_1383582] using wordTrace_append hprefix tailTrace_1383582
  have hstable : (prefixWord ++ tailWord_1383582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383582).length < 2 ^ (prefixWord ++ tailWord_1383582).sum := by decide
  have hdescent : baseEnd_1383582 < baseStart_1383582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383608 : List Nat := [2, 1, 2, 1, 2, 1, 2, 5, 3, 3]
def baseStart_1383608 : Nat := 118140960795 + 1383608 * 2 ^ 59
def prefixEnd_1383608 : Nat := 4983230072969 + 3 ^ 40 * 1383608 * 2
def baseEnd_1383608 : Nat := 473637294270751907357939

theorem tailTrace_1383608 : CollatzResearch.WordTrace tailWord_1383608 prefixEnd_1383608 473637294270751907357939 := by
  unfold tailWord_1383608
  simp only [CollatzResearch.WordTrace]
  refine ⟨25232164785715996139295739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33642886380954661519060985 25232164785715996139295739)
  ·
    refine ⟨37848247178573994208943609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25232164785715996139295739 37848247178573994208943609)
    ·
      refine ⟨28386185383930495656707707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37848247178573994208943609 28386185383930495656707707)
      ·
        refine ⟨42579278075895743485061561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28386185383930495656707707 42579278075895743485061561)
        ·
          refine ⟨31934458556921807613796171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42579278075895743485061561 31934458556921807613796171)
          ·
            refine ⟨47901687835382711420694257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31934458556921807613796171 47901687835382711420694257)
            ·
              refine ⟨35926265876537033565520693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47901687835382711420694257 35926265876537033565520693)
              ·
                refine ⟨3368087425925346896767565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35926265876537033565520693 3368087425925346896767565)
                ·
                  refine ⟨1263032784722005086287837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3368087425925346896767565 1263032784722005086287837)
                  ·
                    refine ⟨473637294270751907357939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1263032784722005086287837 473637294270751907357939)
                    ·
                      rfl

theorem cell22_1383608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 5, 3, 3].length) (baseStart_1383608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1383608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1383608 prefixEnd_1383608 := by exact prefixLift 1383608
  have htrace : WordTrace (prefixWord ++ tailWord_1383608) baseStart_1383608 baseEnd_1383608 := by
    simpa [prefixWord, tailWord_1383608, baseEnd_1383608] using wordTrace_append hprefix tailTrace_1383608
  have hstable : (prefixWord ++ tailWord_1383608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383608).length < 2 ^ (prefixWord ++ tailWord_1383608).sum := by decide
  have hdescent : baseEnd_1383608 < baseStart_1383608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383614 : List Nat := [4, 2, 1, 1, 3, 3, 2, 1, 2, 3]
def baseStart_1383614 : Nat := 118140960795 + 1383614 * 2 ^ 59
def prefixEnd_1383614 : Nat := 4983230072969 + 3 ^ 40 * 1383614 * 2
def baseEnd_1383614 : Nat := 473639348193369891707921

theorem tailTrace_1383614 : CollatzResearch.WordTrace tailWord_1383614 prefixEnd_1383614 473639348193369891707921 := by
  unfold tailWord_1383614
  simp only [CollatzResearch.WordTrace]
  refine ⟨6308068551176281912913737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33643032272940170202206597 6308068551176281912913737)
  ·
    refine ⟨4731051413382211434685303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6308068551176281912913737 4731051413382211434685303)
    ·
      refine ⟨7096577120073317152027955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4731051413382211434685303 7096577120073317152027955)
      ·
        refine ⟨10644865680109975728041933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7096577120073317152027955 10644865680109975728041933)
        ·
          refine ⟨3991824630041240898015725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10644865680109975728041933 3991824630041240898015725)
          ·
            refine ⟨1496934236265465336755897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3991824630041240898015725 1496934236265465336755897)
            ·
              refine ⟨1122700677199099002566923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1496934236265465336755897 1122700677199099002566923)
              ·
                refine ⟨1684051015798648503850385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1122700677199099002566923 1684051015798648503850385)
                ·
                  refine ⟨1263038261848986377887789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1684051015798648503850385 1263038261848986377887789)
                  ·
                    refine ⟨473639348193369891707921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1263038261848986377887789 473639348193369891707921)
                    ·
                      rfl

theorem cell22_1383614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 2, 1, 2, 3].length) (baseStart_1383614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1383614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1383614 prefixEnd_1383614 := by exact prefixLift 1383614
  have htrace : WordTrace (prefixWord ++ tailWord_1383614) baseStart_1383614 baseEnd_1383614 := by
    simpa [prefixWord, tailWord_1383614, baseEnd_1383614] using wordTrace_append hprefix tailTrace_1383614
  have hstable : (prefixWord ++ tailWord_1383614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383614).length < 2 ^ (prefixWord ++ tailWord_1383614).sum := by decide
  have hdescent : baseEnd_1383614 < baseStart_1383614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383629 : List Nat := [1, 6, 2, 2, 1, 1, 2, 1, 2, 4]
def baseStart_1383629 : Nat := 118140960795 + 1383629 * 2 ^ 59
def prefixEnd_1383629 : Nat := 4983230072969 + 3 ^ 40 * 1383629 * 2
def baseEnd_1383629 : Nat := 473644482999914852582875

theorem tailTrace_1383629 : CollatzResearch.WordTrace tailWord_1383629 prefixEnd_1383629 473644482999914852582875 := by
  unfold tailWord_1383629
  simp only [CollatzResearch.WordTrace]
  refine ⟨50465095504355912865105941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33643397002903941910070627 50465095504355912865105941)
  ·
    refine ⟨2365551351766683415551841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 50465095504355912865105941 2365551351766683415551841)
    ·
      refine ⟨1774163513825012561663881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2365551351766683415551841 1774163513825012561663881)
      ·
        refine ⟨1330622635368759421247911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1774163513825012561663881 1330622635368759421247911)
        ·
          refine ⟨1995933953053139131871867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1330622635368759421247911 1995933953053139131871867)
          ·
            refine ⟨2993900929579708697807801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1995933953053139131871867 2993900929579708697807801)
            ·
              refine ⟨2245425697184781523355851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2993900929579708697807801 2245425697184781523355851)
              ·
                refine ⟨3368138545777172285033777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2245425697184781523355851 3368138545777172285033777)
                ·
                  refine ⟨2526103909332879213775333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3368138545777172285033777 2526103909332879213775333)
                  ·
                    refine ⟨473644482999914852582875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2526103909332879213775333 473644482999914852582875)
                    ·
                      rfl

theorem cell22_1383629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_1383629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1383629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1383629 prefixEnd_1383629 := by exact prefixLift 1383629
  have htrace : WordTrace (prefixWord ++ tailWord_1383629) baseStart_1383629 baseEnd_1383629 := by
    simpa [prefixWord, tailWord_1383629, baseEnd_1383629] using wordTrace_append hprefix tailTrace_1383629
  have hstable : (prefixWord ++ tailWord_1383629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383629).length < 2 ^ (prefixWord ++ tailWord_1383629).sum := by decide
  have hdescent : baseEnd_1383629 < baseStart_1383629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383659 : List Nat := [1, 1, 1, 1, 2, 8, 2, 2, 1, 3]
def baseStart_1383659 : Nat := 118140960795 + 1383659 * 2 ^ 59
def prefixEnd_1383659 : Nat := 4983230072969 + 3 ^ 40 * 1383659 * 2
def baseEnd_1383659 : Nat := 473654752613004774332783

theorem tailTrace_1383659 : CollatzResearch.WordTrace tailWord_1383659 prefixEnd_1383659 473654752613004774332783 := by
  unfold tailWord_1383659
  simp only [CollatzResearch.WordTrace]
  refine ⟨50466189694247227988698031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33644126462831485325798687 50466189694247227988698031)
  ·
    refine ⟨75699284541370841983047047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50466189694247227988698031 75699284541370841983047047)
    ·
      refine ⟨113548926812056262974570571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75699284541370841983047047 113548926812056262974570571)
      ·
        refine ⟨170323390218084394461855857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113548926812056262974570571 170323390218084394461855857)
        ·
          refine ⟨127742542663563295846391893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170323390218084394461855857 127742542663563295846391893)
          ·
            refine ⟨1496982921838632373199905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 127742542663563295846391893 1496982921838632373199905)
            ·
              refine ⟨1122737191378974279899929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1496982921838632373199905 1122737191378974279899929)
              ·
                refine ⟨842052893534230709924947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1122737191378974279899929 842052893534230709924947)
                ·
                  refine ⟨1263079340301346064887421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 842052893534230709924947 1263079340301346064887421)
                  ·
                    refine ⟨473654752613004774332783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1263079340301346064887421 473654752613004774332783)
                    ·
                      rfl

theorem cell22_1383659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 2, 2, 1, 3].length) (baseStart_1383659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1383659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1383659 prefixEnd_1383659 := by exact prefixLift 1383659
  have htrace : WordTrace (prefixWord ++ tailWord_1383659) baseStart_1383659 baseEnd_1383659 := by
    simpa [prefixWord, tailWord_1383659, baseEnd_1383659] using wordTrace_append hprefix tailTrace_1383659
  have hstable : (prefixWord ++ tailWord_1383659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383659).length < 2 ^ (prefixWord ++ tailWord_1383659).sum := by decide
  have hdescent : baseEnd_1383659 < baseStart_1383659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383683 : List Nat := [1, 1, 1, 3, 2, 5, 1, 2, 6]
def baseStart_1383683 : Nat := 118140960795 + 1383683 * 2 ^ 59
def prefixEnd_1383683 : Nat := 4983230072969 + 3 ^ 40 * 1383683 * 2
def baseEnd_1383683 : Nat := 157887656101158903910903

theorem tailTrace_1383683 : CollatzResearch.WordTrace tailWord_1383683 prefixEnd_1383683 157887656101158903910903 := by
  unfold tailWord_1383683
  simp only [CollatzResearch.WordTrace]
  refine ⟨50467065046160280087571703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33644710030773520058381135 50467065046160280087571703)
  ·
    refine ⟨75700597569240420131357555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50467065046160280087571703 75700597569240420131357555)
    ·
      refine ⟨113550896353860630197036333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75700597569240420131357555 113550896353860630197036333)
      ·
        refine ⟨42581586132697736323888625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113550896353860630197036333 42581586132697736323888625)
        ·
          refine ⟨31936189599523302242916469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42581586132697736323888625 31936189599523302242916469)
          ·
            refine ⟨2994017774955309585273419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31936189599523302242916469 2994017774955309585273419)
            ·
              refine ⟨4491026662432964377910129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2994017774955309585273419 4491026662432964377910129)
              ·
                refine ⟨3368269996824723283432597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4491026662432964377910129 3368269996824723283432597)
                ·
                  refine ⟨157887656101158903910903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3368269996824723283432597 157887656101158903910903)
                  ·
                    rfl

theorem cell22_1383683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 2, 6].length) (baseStart_1383683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1383683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1383683 prefixEnd_1383683 := by exact prefixLift 1383683
  have htrace : WordTrace (prefixWord ++ tailWord_1383683) baseStart_1383683 baseEnd_1383683 := by
    simpa [prefixWord, tailWord_1383683, baseEnd_1383683] using wordTrace_append hprefix tailTrace_1383683
  have hstable : (prefixWord ++ tailWord_1383683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383683).length < 2 ^ (prefixWord ++ tailWord_1383683).sum := by decide
  have hdescent : baseEnd_1383683 < baseStart_1383683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383713 : List Nat := [1, 2, 3, 2, 1, 1, 1, 3, 4, 4]
def baseStart_1383713 : Nat := 118140960795 + 1383713 * 2 ^ 59
def prefixEnd_1383713 : Nat := 4983230072969 + 3 ^ 40 * 1383713 * 2
def baseEnd_1383713 : Nat := 473673237916566633482617

theorem tailTrace_1383713 : CollatzResearch.WordTrace tailWord_1383713 prefixEnd_1383713 473673237916566633482617 := by
  unfold tailWord_1383713
  simp only [CollatzResearch.WordTrace]
  refine ⟨50468159236051595211163793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33645439490701063474109195 50468159236051595211163793)
  ·
    refine ⟨37851119427038696408372845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50468159236051595211163793 37851119427038696408372845)
    ·
      refine ⟨14194169785139511153139817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37851119427038696408372845 14194169785139511153139817)
      ·
        refine ⟨10645627338854633364854863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14194169785139511153139817 10645627338854633364854863)
        ·
          refine ⟨15968441008281950047282295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10645627338854633364854863 15968441008281950047282295)
          ·
            refine ⟨23952661512422925070923443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15968441008281950047282295 23952661512422925070923443)
            ·
              refine ⟨35928992268634387606385165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23952661512422925070923443 35928992268634387606385165)
              ·
                refine ⟨13473372100737895352394437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35928992268634387606385165 13473372100737895352394437)
                ·
                  refine ⟨2526257268888355378573957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13473372100737895352394437 2526257268888355378573957)
                  ·
                    refine ⟨473673237916566633482617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2526257268888355378573957 473673237916566633482617)
                    ·
                      rfl

theorem cell22_1383713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 4, 4].length) (baseStart_1383713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1383713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1383713 prefixEnd_1383713 := by exact prefixLift 1383713
  have htrace : WordTrace (prefixWord ++ tailWord_1383713) baseStart_1383713 baseEnd_1383713 := by
    simpa [prefixWord, tailWord_1383713, baseEnd_1383713] using wordTrace_append hprefix tailTrace_1383713
  have hstable : (prefixWord ++ tailWord_1383713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383713).length < 2 ^ (prefixWord ++ tailWord_1383713).sum := by decide
  have hdescent : baseEnd_1383713 < baseStart_1383713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383715 : List Nat := [1, 1, 1, 4, 2, 4, 1, 1, 4, 3]
def baseStart_1383715 : Nat := 118140960795 + 1383715 * 2 ^ 59
def prefixEnd_1383715 : Nat := 4983230072969 + 3 ^ 40 * 1383715 * 2
def baseEnd_1383715 : Nat := 473673922557439294932611

theorem tailTrace_1383715 : CollatzResearch.WordTrace tailWord_1383715 prefixEnd_1383715 473673922557439294932611 := by
  unfold tailWord_1383715
  simp only [CollatzResearch.WordTrace]
  refine ⟨50468232182044349552736599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33645488121362899701824399 50468232182044349552736599)
  ·
    refine ⟨75702348273066524329104899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50468232182044349552736599 75702348273066524329104899)
    ·
      refine ⟨113553522409599786493657349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75702348273066524329104899 113553522409599786493657349)
      ·
        refine ⟨21291285451799959967560753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113553522409599786493657349 21291285451799959967560753)
        ·
          refine ⟨15968464088849969975670565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21291285451799959967560753 15968464088849969975670565)
          ·
            refine ⟨2994087016659369370438231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15968464088849969975670565 2994087016659369370438231)
            ·
              refine ⟨4491130524989054055657347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2994087016659369370438231 4491130524989054055657347)
              ·
                refine ⟨6736695787483581083486021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4491130524989054055657347 6736695787483581083486021)
                ·
                  refine ⟨1263130460153171453153629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6736695787483581083486021 1263130460153171453153629)
                  ·
                    refine ⟨473673922557439294932611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1263130460153171453153629 473673922557439294932611)
                    ·
                      rfl

theorem cell22_1383715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 4, 3].length) (baseStart_1383715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1383715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1383715 prefixEnd_1383715 := by exact prefixLift 1383715
  have htrace : WordTrace (prefixWord ++ tailWord_1383715) baseStart_1383715 baseEnd_1383715 := by
    simpa [prefixWord, tailWord_1383715, baseEnd_1383715] using wordTrace_append hprefix tailTrace_1383715
  have hstable : (prefixWord ++ tailWord_1383715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383715).length < 2 ^ (prefixWord ++ tailWord_1383715).sum := by decide
  have hdescent : baseEnd_1383715 < baseStart_1383715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383745 : List Nat := [1, 2, 5, 2, 1, 2, 1, 8]
def baseStart_1383745 : Nat := 118140960795 + 1383745 * 2 ^ 59
def prefixEnd_1383745 : Nat := 4983230072969 + 3 ^ 40 * 1383745 * 2
def baseEnd_1383745 : Nat := 52631576907836579631391

theorem tailTrace_1383745 : CollatzResearch.WordTrace tailWord_1383745 prefixEnd_1383745 52631576907836579631391 := by
  unfold tailWord_1383745
  simp only [CollatzResearch.WordTrace]
  refine ⟨50469326371935664676328689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33646217581290443117552459 50469326371935664676328689)
  ·
    refine ⟨37851994778951748507246517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50469326371935664676328689 37851994778951748507246517)
    ·
      refine ⟨3548624510526726422554361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37851994778951748507246517 3548624510526726422554361)
      ·
        refine ⟨2661468382895044816915771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3548624510526726422554361 2661468382895044816915771)
        ·
          refine ⟨3992202574342567225373657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2661468382895044816915771 3992202574342567225373657)
          ·
            refine ⟨2994151930756925419030243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3992202574342567225373657 2994151930756925419030243)
            ·
              refine ⟨4491227896135388128545365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2994151930756925419030243 4491227896135388128545365)
              ·
                refine ⟨52631576907836579631391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4491227896135388128545365 52631576907836579631391)
                ·
                  rfl

theorem cell22_1383745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 8].length) (baseStart_1383745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1383745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1383745 prefixEnd_1383745 := by exact prefixLift 1383745
  have htrace : WordTrace (prefixWord ++ tailWord_1383745) baseStart_1383745 baseEnd_1383745 := by
    simpa [prefixWord, tailWord_1383745, baseEnd_1383745] using wordTrace_append hprefix tailTrace_1383745
  have hstable : (prefixWord ++ tailWord_1383745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383745).length < 2 ^ (prefixWord ++ tailWord_1383745).sum := by decide
  have hdescent : baseEnd_1383745 < baseStart_1383745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383777 : List Nat := [1, 2, 3, 1, 1, 1, 1, 8, 1, 3]
def baseStart_1383777 : Nat := 118140960795 + 1383777 * 2 ^ 59
def prefixEnd_1383777 : Nat := 4983230072969 + 3 ^ 40 * 1383777 * 2
def baseEnd_1383777 : Nat := 473695146424491799882421

theorem tailTrace_1383777 : CollatzResearch.WordTrace tailWord_1383777 prefixEnd_1383777 473695146424491799882421 := by
  unfold tailWord_1383777
  simp only [CollatzResearch.WordTrace]
  refine ⟨50470493507819734141493585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33646995671879822760995723 50470493507819734141493585)
  ·
    refine ⟨37852870130864800606120189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50470493507819734141493585 37852870130864800606120189)
    ·
      refine ⟨14194826299074300227295071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37852870130864800606120189 14194826299074300227295071)
      ·
        refine ⟨21292239448611450340942607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14194826299074300227295071 21292239448611450340942607)
        ·
          refine ⟨31938359172917175511413911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21292239448611450340942607 31938359172917175511413911)
          ·
            refine ⟨47907538759375763267120867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31938359172917175511413911 47907538759375763267120867)
            ·
              refine ⟨71861308139063644900681301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47907538759375763267120867 71861308139063644900681301)
              ·
                refine ⟨842124704754652088679859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 71861308139063644900681301 842124704754652088679859)
                ·
                  refine ⟨1263187057131978133019789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 842124704754652088679859 1263187057131978133019789)
                  ·
                    refine ⟨473695146424491799882421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1263187057131978133019789 473695146424491799882421)
                    ·
                      rfl

theorem cell22_1383777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 8, 1, 3].length) (baseStart_1383777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1383777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1383777 prefixEnd_1383777 := by exact prefixLift 1383777
  have htrace : WordTrace (prefixWord ++ tailWord_1383777) baseStart_1383777 baseEnd_1383777 := by
    simpa [prefixWord, tailWord_1383777, baseEnd_1383777] using wordTrace_append hprefix tailTrace_1383777
  have hstable : (prefixWord ++ tailWord_1383777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383777).length < 2 ^ (prefixWord ++ tailWord_1383777).sum := by decide
  have hdescent : baseEnd_1383777 < baseStart_1383777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383828 : List Nat := [2, 4, 2, 1, 2, 3, 2, 2, 1, 3]
def baseStart_1383828 : Nat := 118140960795 + 1383828 * 2 ^ 59
def prefixEnd_1383828 : Nat := 4983230072969 + 3 ^ 40 * 1383828 * 2
def baseEnd_1383828 : Nat := 473712604766744666857265

theorem tailTrace_1383828 : CollatzResearch.WordTrace tailWord_1383828 prefixEnd_1383828 473712604766744666857265 := by
  unfold tailWord_1383828
  simp only [CollatzResearch.WordTrace]
  refine ⟨25236176815317484925800069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33648235753756646567733425 25236176815317484925800069)
  ·
    refine ⟨4731783152872028423587513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25236176815317484925800069 4731783152872028423587513)
    ·
      refine ⟨3548837364654021317690635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4731783152872028423587513 3548837364654021317690635)
      ·
        refine ⟨5323256046981031976535953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3548837364654021317690635 5323256046981031976535953)
        ·
          refine ⟨3992442035235773982401965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5323256046981031976535953 3992442035235773982401965)
          ·
            refine ⟨1497165763213415243400737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3992442035235773982401965 1497165763213415243400737)
            ·
              refine ⟨1122874322410061432550553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1497165763213415243400737 1122874322410061432550553)
              ·
                refine ⟨842155741807546074412915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1122874322410061432550553 842155741807546074412915)
                ·
                  refine ⟨1263233612711319111619373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 842155741807546074412915 1263233612711319111619373)
                  ·
                    refine ⟨473712604766744666857265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1263233612711319111619373 473712604766744666857265)
                    ·
                      rfl

theorem cell22_1383828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_1383828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1383828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1383828 prefixEnd_1383828 := by exact prefixLift 1383828
  have htrace : WordTrace (prefixWord ++ tailWord_1383828) baseStart_1383828 baseEnd_1383828 := by
    simpa [prefixWord, tailWord_1383828, baseEnd_1383828] using wordTrace_append hprefix tailTrace_1383828
  have hstable : (prefixWord ++ tailWord_1383828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383828).length < 2 ^ (prefixWord ++ tailWord_1383828).sum := by decide
  have hdescent : baseEnd_1383828 < baseStart_1383828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383884 : List Nat := [2, 2, 1, 4, 2, 1, 3, 2, 2, 3]
def baseStart_1383884 : Nat := 118140960795 + 1383884 * 2 ^ 59
def prefixEnd_1383884 : Nat := 4983230072969 + 3 ^ 40 * 1383884 * 2
def baseEnd_1383884 : Nat := 473731774711179187457093

theorem tailTrace_1383884 : CollatzResearch.WordTrace tailWord_1383884 prefixEnd_1383884 473731774711179187457093 := by
  unfold tailWord_1383884
  simp only [CollatzResearch.WordTrace]
  refine ⟨25237198059216045707819353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33649597412288060943759137 25237198059216045707819353)
  ·
    refine ⟨18927898544412034280864515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25237198059216045707819353 18927898544412034280864515)
    ·
      refine ⟨28391847816618051421296773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18927898544412034280864515 28391847816618051421296773)
      ·
        refine ⟨5323471465615884641493145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28391847816618051421296773 5323471465615884641493145)
        ·
          refine ⟨3992603599211913481119859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5323471465615884641493145 3992603599211913481119859)
          ·
            refine ⟨5988905398817870221679789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3992603599211913481119859 5988905398817870221679789)
            ·
              refine ⟨2245839524556701333129921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5988905398817870221679789 2245839524556701333129921)
              ·
                refine ⟨1684379643417525999847441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2245839524556701333129921 1684379643417525999847441)
                ·
                  refine ⟨1263284732563144499885581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1684379643417525999847441 1263284732563144499885581)
                  ·
                    refine ⟨473731774711179187457093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1263284732563144499885581 473731774711179187457093)
                    ·
                      rfl

theorem cell22_1383884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 2, 2, 3].length) (baseStart_1383884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1383884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1383884 prefixEnd_1383884 := by exact prefixLift 1383884
  have htrace : WordTrace (prefixWord ++ tailWord_1383884) baseStart_1383884 baseEnd_1383884 := by
    simpa [prefixWord, tailWord_1383884, baseEnd_1383884] using wordTrace_append hprefix tailTrace_1383884
  have hstable : (prefixWord ++ tailWord_1383884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383884).length < 2 ^ (prefixWord ++ tailWord_1383884).sum := by decide
  have hdescent : baseEnd_1383884 < baseStart_1383884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383901 : List Nat := [1, 4, 3, 1, 1, 3, 3, 1, 2, 3]
def baseStart_1383901 : Nat := 118140960795 + 1383901 * 2 ^ 59
def prefixEnd_1383901 : Nat := 4983230072969 + 3 ^ 40 * 1383901 * 2
def baseEnd_1383901 : Nat := 473737594158596809782041

theorem tailTrace_1383901 : CollatzResearch.WordTrace tailWord_1383901 prefixEnd_1383901 473737594158596809782041 := by
  unfold tailWord_1383901
  simp only [CollatzResearch.WordTrace]
  refine ⟨50475016159370503319007557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33650010772913668879338371 50475016159370503319007557)
  ·
    refine ⟨9464065529881969372313917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50475016159370503319007557 9464065529881969372313917)
    ·
      refine ⟨3549024573705738514617719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9464065529881969372313917 3549024573705738514617719)
      ·
        refine ⟨5323536860558607771926579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3549024573705738514617719 5323536860558607771926579)
        ·
          refine ⟨7985305290837911657889869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5323536860558607771926579 7985305290837911657889869)
          ·
            refine ⟨2994489484064216871708701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7985305290837911657889869 2994489484064216871708701)
            ·
              refine ⟨1122933556524081326890763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2994489484064216871708701 1122933556524081326890763)
              ·
                refine ⟨1684400334786121990336145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1122933556524081326890763 1684400334786121990336145)
                ·
                  refine ⟨1263300251089591492752109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1684400334786121990336145 1263300251089591492752109)
                  ·
                    refine ⟨473737594158596809782041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1263300251089591492752109 473737594158596809782041)
                    ·
                      rfl

theorem cell22_1383901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_1383901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1383901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1383901 prefixEnd_1383901 := by exact prefixLift 1383901
  have htrace : WordTrace (prefixWord ++ tailWord_1383901) baseStart_1383901 baseEnd_1383901 := by
    simpa [prefixWord, tailWord_1383901, baseEnd_1383901] using wordTrace_append hprefix tailTrace_1383901
  have hstable : (prefixWord ++ tailWord_1383901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383901).length < 2 ^ (prefixWord ++ tailWord_1383901).sum := by decide
  have hdescent : baseEnd_1383901 < baseStart_1383901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383912 : List Nat := [2, 1, 4, 1, 1, 2, 1, 4, 3, 3]
def baseStart_1383912 : Nat := 118140960795 + 1383912 * 2 ^ 59
def prefixEnd_1383912 : Nat := 4983230072969 + 3 ^ 40 * 1383912 * 2
def baseEnd_1383912 : Nat := 473741359683396447757007

theorem tailTrace_1383912 : CollatzResearch.WordTrace tailWord_1383912 prefixEnd_1383912 473741359683396447757007 := by
  unfold tailWord_1383912
  simp only [CollatzResearch.WordTrace]
  refine ⟨25237708681165326098828995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33650278241553768131771993 25237708681165326098828995)
  ·
    refine ⟨37856563021747989148243493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25237708681165326098828995 37856563021747989148243493)
    ·
      refine ⟨7098105566577747965295655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37856563021747989148243493 7098105566577747965295655)
      ·
        refine ⟨10647158349866621947943483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7098105566577747965295655 10647158349866621947943483)
        ·
          refine ⟨15970737524799932921915225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10647158349866621947943483 15970737524799932921915225)
          ·
            refine ⟨11978053143599949691436419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15970737524799932921915225 11978053143599949691436419)
            ·
              refine ⟨17967079715399924537154629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11978053143599949691436419 17967079715399924537154629)
              ·
                refine ⟨3368827446637485850716493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17967079715399924537154629 3368827446637485850716493)
                ·
                  refine ⟨1263310292489057194018685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3368827446637485850716493 1263310292489057194018685)
                  ·
                    refine ⟨473741359683396447757007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1263310292489057194018685 473741359683396447757007)
                    ·
                      rfl

theorem cell22_1383912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 4, 3, 3].length) (baseStart_1383912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1383912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1383912 prefixEnd_1383912 := by exact prefixLift 1383912
  have htrace : WordTrace (prefixWord ++ tailWord_1383912) baseStart_1383912 baseEnd_1383912 := by
    simpa [prefixWord, tailWord_1383912, baseEnd_1383912] using wordTrace_append hprefix tailTrace_1383912
  have hstable : (prefixWord ++ tailWord_1383912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383912).length < 2 ^ (prefixWord ++ tailWord_1383912).sum := by decide
  have hdescent : baseEnd_1383912 < baseStart_1383912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383914 : List Nat := [3, 1, 3, 1, 4, 2, 2, 6]
def baseStart_1383914 : Nat := 118140960795 + 1383914 * 2 ^ 59
def prefixEnd_1383914 : Nat := 4983230072969 + 3 ^ 40 * 1383914 * 2
def baseEnd_1383914 : Nat := 52638004924918789911889

theorem tailTrace_1383914 : CollatzResearch.WordTrace tailWord_1383914 prefixEnd_1383914 52638004924918789911889 := by
  unfold tailWord_1383914
  simp only [CollatzResearch.WordTrace]
  refine ⟨12618872577080851634807699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33650326872215604359487197 12618872577080851634807699)
  ·
    refine ⟨18928308865621277452211549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12618872577080851634807699 18928308865621277452211549)
    ·
      refine ⟨7098115824607979044579331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18928308865621277452211549 7098115824607979044579331)
      ·
        refine ⟨10647173736911968566868997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7098115824607979044579331 10647173736911968566868997)
        ·
          refine ⟨1996345075670994106287937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10647173736911968566868997 1996345075670994106287937)
          ·
            refine ⟨1497258806753245579715953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1996345075670994106287937 1497258806753245579715953)
            ·
              refine ⟨1122944105064934184786965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1497258806753245579715953 1122944105064934184786965)
              ·
                refine ⟨52638004924918789911889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1122944105064934184786965 52638004924918789911889)
                ·
                  rfl

theorem cell22_1383914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 2, 6].length) (baseStart_1383914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1383914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1383914 prefixEnd_1383914 := by exact prefixLift 1383914
  have htrace : WordTrace (prefixWord ++ tailWord_1383914) baseStart_1383914 baseEnd_1383914 := by
    simpa [prefixWord, tailWord_1383914, baseEnd_1383914] using wordTrace_append hprefix tailTrace_1383914
  have hstable : (prefixWord ++ tailWord_1383914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383914).length < 2 ^ (prefixWord ++ tailWord_1383914).sum := by decide
  have hdescent : baseEnd_1383914 < baseStart_1383914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384000 : List Nat := [2, 1, 1, 2, 2, 2, 1, 2, 3, 6]
def baseStart_1384000 : Nat := 118140960795 + 1384000 * 2 ^ 59
def prefixEnd_1384000 : Nat := 4983230072969 + 3 ^ 40 * 1384000 * 2
def baseEnd_1384000 : Nat := 473771483881793551556737

theorem tailTrace_1384000 : CollatzResearch.WordTrace tailWord_1384000 prefixEnd_1384000 473771483881793551556737 := by
  unfold tailWord_1384000
  simp only [CollatzResearch.WordTrace]
  refine ⟨25239313493005921613430727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33652417990674562151240969 25239313493005921613430727)
  ·
    refine ⟨37858970239508882420146091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25239313493005921613430727 37858970239508882420146091)
    ·
      refine ⟨56788455359263323630219137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37858970239508882420146091 56788455359263323630219137)
      ·
        refine ⟨42591341519447492722664353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56788455359263323630219137 42591341519447492722664353)
        ·
          refine ⟨31943506139585619541998265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42591341519447492722664353 31943506139585619541998265)
          ·
            refine ⟨23957629604689214656498699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31943506139585619541998265 23957629604689214656498699)
            ·
              refine ⟨35936444407033821984748049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23957629604689214656498699 35936444407033821984748049)
              ·
                refine ⟨26952333305275366488561037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35936444407033821984748049 26952333305275366488561037)
                ·
                  refine ⟨10107124989478262433210389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26952333305275366488561037 10107124989478262433210389)
                  ·
                    refine ⟨473771483881793551556737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10107124989478262433210389 473771483881793551556737)
                    ·
                      rfl

theorem cell22_1384000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 3, 6].length) (baseStart_1384000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1384000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1384000 prefixEnd_1384000 := by exact prefixLift 1384000
  have htrace : WordTrace (prefixWord ++ tailWord_1384000) baseStart_1384000 baseEnd_1384000 := by
    simpa [prefixWord, tailWord_1384000, baseEnd_1384000] using wordTrace_append hprefix tailTrace_1384000
  have hstable : (prefixWord ++ tailWord_1384000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384000).length < 2 ^ (prefixWord ++ tailWord_1384000).sum := by decide
  have hdescent : baseEnd_1384000 < baseStart_1384000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384047 : List Nat := [1, 1, 2, 1, 3, 2, 1, 1, 7, 3]
def baseStart_1384047 : Nat := 118140960795 + 1384047 * 2 ^ 59
def prefixEnd_1384047 : Nat := 4983230072969 + 3 ^ 40 * 1384047 * 2
def baseEnd_1384047 : Nat := 473787572942301095631593

theorem tailTrace_1384047 : CollatzResearch.WordTrace tailWord_1384047 prefixEnd_1384047 473787572942301095631593 := by
  unfold tailWord_1384047
  simp only [CollatzResearch.WordTrace]
  refine ⟨50480341216841570253822395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33653560811227713502548263 50480341216841570253822395)
  ·
    refine ⟨75720511825262355380733593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50480341216841570253822395 75720511825262355380733593)
    ·
      refine ⟨56790383868946766535550195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75720511825262355380733593 56790383868946766535550195)
      ·
        refine ⟨85185575803420149803325293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56790383868946766535550195 85185575803420149803325293)
        ·
          refine ⟨31944590926282556176246985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85185575803420149803325293 31944590926282556176246985)
          ·
            refine ⟨23958443194711917132185239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31944590926282556176246985 23958443194711917132185239)
            ·
              refine ⟨35937664792067875698277859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23958443194711917132185239 35937664792067875698277859)
              ·
                refine ⟨53906497188101813547416789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35937664792067875698277859 53906497188101813547416789)
                ·
                  refine ⟨1263433527846136255017581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 53906497188101813547416789 1263433527846136255017581)
                  ·
                    refine ⟨473787572942301095631593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1263433527846136255017581 473787572942301095631593)
                    ·
                      rfl

theorem cell22_1384047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 7, 3].length) (baseStart_1384047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1384047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1384047 prefixEnd_1384047 := by exact prefixLift 1384047
  have htrace : WordTrace (prefixWord ++ tailWord_1384047) baseStart_1384047 baseEnd_1384047 := by
    simpa [prefixWord, tailWord_1384047, baseEnd_1384047] using wordTrace_append hprefix tailTrace_1384047
  have hstable : (prefixWord ++ tailWord_1384047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384047).length < 2 ^ (prefixWord ++ tailWord_1384047).sum := by decide
  have hdescent : baseEnd_1384047 < baseStart_1384047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384053 : List Nat := [1, 3, 4, 2, 1, 3, 1, 2, 2, 3]
def baseStart_1384053 : Nat := 118140960795 + 1384053 * 2 ^ 59
def prefixEnd_1384053 : Nat := 4983230072969 + 3 ^ 40 * 1384053 * 2
def baseEnd_1384053 : Nat := 473789626864919079981575

theorem tailTrace_1384053 : CollatzResearch.WordTrace tailWord_1384053 prefixEnd_1384053 473789626864919079981575 := by
  unfold tailWord_1384053
  simp only [CollatzResearch.WordTrace]
  refine ⟨50480560054819833278540813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33653706703213222185693875 50480560054819833278540813)
  ·
    refine ⟨18930210020557437479452805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50480560054819833278540813 18930210020557437479452805)
    ·
      refine ⟨3549414378854519527397401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18930210020557437479452805 3549414378854519527397401)
      ·
        refine ⟨2662060784140889645548051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3549414378854519527397401 2662060784140889645548051)
        ·
          refine ⟨3993091176211334468322077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2662060784140889645548051 3993091176211334468322077)
          ·
            refine ⟨1497409191079250425620779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3993091176211334468322077 1497409191079250425620779)
            ·
              refine ⟨2246113786618875638431169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1497409191079250425620779 2246113786618875638431169)
              ·
                refine ⟨1684585339964156728823377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2246113786618875638431169 1684585339964156728823377)
                ·
                  refine ⟨1263439004973117546617533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1684585339964156728823377 1263439004973117546617533)
                  ·
                    refine ⟨473789626864919079981575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1263439004973117546617533 473789626864919079981575)
                    ·
                      rfl

theorem cell22_1384053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_1384053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1384053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1384053 prefixEnd_1384053 := by exact prefixLift 1384053
  have htrace : WordTrace (prefixWord ++ tailWord_1384053) baseStart_1384053 baseEnd_1384053 := by
    simpa [prefixWord, tailWord_1384053, baseEnd_1384053] using wordTrace_append hprefix tailTrace_1384053
  have hstable : (prefixWord ++ tailWord_1384053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384053).length < 2 ^ (prefixWord ++ tailWord_1384053).sum := by decide
  have hdescent : baseEnd_1384053 < baseStart_1384053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384064 : List Nat := [2, 1, 1, 2, 1, 4, 4, 1, 3, 3]
def baseStart_1384064 : Nat := 118140960795 + 1384064 * 2 ^ 59
def prefixEnd_1384064 : Nat := 4983230072969 + 3 ^ 40 * 1384064 * 2
def baseEnd_1384064 : Nat := 473793392389718717956541

theorem tailTrace_1384064 : CollatzResearch.WordTrace tailWord_1384064 prefixEnd_1384064 473793392389718717956541 := by
  unfold tailWord_1384064
  simp only [CollatzResearch.WordTrace]
  refine ⟨25240480628889991078595623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33653974171853321438127497 25240480628889991078595623)
  ·
    refine ⟨37860720943334986617893435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25240480628889991078595623 37860720943334986617893435)
    ·
      refine ⟨56791081415002479926840153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37860720943334986617893435 56791081415002479926840153)
      ·
        refine ⟨42593311061251859945130115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56791081415002479926840153 42593311061251859945130115)
        ·
          refine ⟨63889966591877789917695173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42593311061251859945130115 63889966591877789917695173)
          ·
            refine ⟨11979368735977085609567845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63889966591877789917695173 11979368735977085609567845)
            ·
              refine ⟨2246131637995703551793971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11979368735977085609567845 2246131637995703551793971)
              ·
                refine ⟨3369197456993555327690957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2246131637995703551793971 3369197456993555327690957)
                ·
                  refine ⟨1263449046372583247884109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3369197456993555327690957 1263449046372583247884109)
                  ·
                    refine ⟨473793392389718717956541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1263449046372583247884109 473793392389718717956541)
                    ·
                      rfl

theorem cell22_1384064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 1, 3, 3].length) (baseStart_1384064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1384064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1384064 prefixEnd_1384064 := by exact prefixLift 1384064
  have htrace : WordTrace (prefixWord ++ tailWord_1384064) baseStart_1384064 baseEnd_1384064 := by
    simpa [prefixWord, tailWord_1384064, baseEnd_1384064] using wordTrace_append hprefix tailTrace_1384064
  have hstable : (prefixWord ++ tailWord_1384064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384064).length < 2 ^ (prefixWord ++ tailWord_1384064).sum := by decide
  have hdescent : baseEnd_1384064 < baseStart_1384064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384094 : List Nat := [4, 3, 1, 1, 1, 2, 1, 2, 7]
def baseStart_1384094 : Nat := 118140960795 + 1384094 * 2 ^ 59
def prefixEnd_1384094 : Nat := 4983230072969 + 3 ^ 40 * 1384094 * 2
def baseEnd_1384094 : Nat := 157934554000936213235483

theorem tailTrace_1384094 : CollatzResearch.WordTrace tailWord_1384094 prefixEnd_1384094 157934554000936213235483 := by
  unfold tailWord_1384094
  simp only [CollatzResearch.WordTrace]
  refine ⟨6310256930958912160097917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33654703631780864853855557 6310256930958912160097917)
  ·
    refine ⟨2366346349109592060036719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6310256930958912160097917 2366346349109592060036719)
    ·
      refine ⟨3549519523664388090055079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2366346349109592060036719 3549519523664388090055079)
      ·
        refine ⟨5324279285496582135082619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3549519523664388090055079 5324279285496582135082619)
        ·
          refine ⟨7986418928244873202623929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5324279285496582135082619 7986418928244873202623929)
          ·
            refine ⟨5989814196183654901967947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7986418928244873202623929 5989814196183654901967947)
            ·
              refine ⟨8984721294275482352951921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5989814196183654901967947 8984721294275482352951921)
              ·
                refine ⟨6738540970706611764713941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8984721294275482352951921 6738540970706611764713941)
                ·
                  refine ⟨157934554000936213235483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6738540970706611764713941 157934554000936213235483)
                  ·
                    rfl

theorem cell22_1384094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_1384094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1384094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1384094 prefixEnd_1384094 := by exact prefixLift 1384094
  have htrace : WordTrace (prefixWord ++ tailWord_1384094) baseStart_1384094 baseEnd_1384094 := by
    simpa [prefixWord, tailWord_1384094, baseEnd_1384094] using wordTrace_append hprefix tailTrace_1384094
  have hstable : (prefixWord ++ tailWord_1384094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384094).length < 2 ^ (prefixWord ++ tailWord_1384094).sum := by decide
  have hdescent : baseEnd_1384094 < baseStart_1384094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384154 : List Nat := [3, 1, 1, 2, 2, 4, 1, 2, 1, 5]
def baseStart_1384154 : Nat := 118140960795 + 1384154 * 2 ^ 59
def prefixEnd_1384154 : Nat := 4983230072969 + 3 ^ 40 * 1384154 * 2
def baseEnd_1384154 : Nat := 473824201228988483206265

theorem tailTrace_1384154 : CollatzResearch.WordTrace tailWord_1384154 prefixEnd_1384154 473824201228988483206265 := by
  unfold tailWord_1384154
  simp only [CollatzResearch.WordTrace]
  refine ⟨12621060956863481881991879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33656162551635951685311677 12621060956863481881991879)
  ·
    refine ⟨18931591435295222822987819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12621060956863481881991879 18931591435295222822987819)
    ·
      refine ⟨28397387152942834234481729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18931591435295222822987819 28397387152942834234481729)
      ·
        refine ⟨21298040364707125675861297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28397387152942834234481729 21298040364707125675861297)
        ·
          refine ⟨15973530273530344256895973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21298040364707125675861297 15973530273530344256895973)
          ·
            refine ⟨2995036926286939548167995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15973530273530344256895973 2995036926286939548167995)
            ·
              refine ⟨4492555389430409322251993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2995036926286939548167995 4492555389430409322251993)
              ·
                refine ⟨3369416542072806991688995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4492555389430409322251993 3369416542072806991688995)
                ·
                  refine ⟨5054124813109210487533493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3369416542072806991688995 5054124813109210487533493)
                  ·
                    refine ⟨473824201228988483206265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5054124813109210487533493 473824201228988483206265)
                    ·
                      rfl

theorem cell22_1384154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 2, 1, 5].length) (baseStart_1384154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1384154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1384154 prefixEnd_1384154 := by exact prefixLift 1384154
  have htrace : WordTrace (prefixWord ++ tailWord_1384154) baseStart_1384154 baseEnd_1384154 := by
    simpa [prefixWord, tailWord_1384154, baseEnd_1384154] using wordTrace_append hprefix tailTrace_1384154
  have hstable : (prefixWord ++ tailWord_1384154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384154).length < 2 ^ (prefixWord ++ tailWord_1384154).sum := by decide
  have hdescent : baseEnd_1384154 < baseStart_1384154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384173 : List Nat := [1, 5, 1, 2, 1, 2, 4, 2, 4]
def baseStart_1384173 : Nat := 118140960795 + 1384173 * 2 ^ 59
def prefixEnd_1384173 : Nat := 4983230072969 + 3 ^ 40 * 1384173 * 2
def baseEnd_1384173 : Nat := 157943568439092922327069

theorem tailTrace_1384173 : CollatzResearch.WordTrace tailWord_1384173 prefixEnd_1384173 157943568439092922327069 := by
  unfold tailWord_1384173
  simp only [CollatzResearch.WordTrace]
  refine ⟨50484936814385093772909173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33656624542923395848606115 50484936814385093772909173)
  ·
    refine ⟨4732962826348602541210235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50484936814385093772909173 4732962826348602541210235)
    ·
      refine ⟨7099444239522903811815353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4732962826348602541210235 7099444239522903811815353)
      ·
        refine ⟨5324583179642177858861515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7099444239522903811815353 5324583179642177858861515)
        ·
          refine ⟨7986874769463266788292273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5324583179642177858861515 7986874769463266788292273)
          ·
            refine ⟨5990156077097450091219205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7986874769463266788292273 5990156077097450091219205)
            ·
              refine ⟨1123154264455771892103601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5990156077097450091219205 1123154264455771892103601)
              ·
                refine ⟨842365698341828919077701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1123154264455771892103601 842365698341828919077701)
                ·
                  refine ⟨157943568439092922327069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 842365698341828919077701 157943568439092922327069)
                  ·
                    rfl

theorem cell22_1384173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 4, 2, 4].length) (baseStart_1384173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1384173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1384173 prefixEnd_1384173 := by exact prefixLift 1384173
  have htrace : WordTrace (prefixWord ++ tailWord_1384173) baseStart_1384173 baseEnd_1384173 := by
    simpa [prefixWord, tailWord_1384173, baseEnd_1384173] using wordTrace_append hprefix tailTrace_1384173
  have hstable : (prefixWord ++ tailWord_1384173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384173).length < 2 ^ (prefixWord ++ tailWord_1384173).sum := by decide
  have hdescent : baseEnd_1384173 < baseStart_1384173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384229 : List Nat := [1, 3, 1, 2, 3, 3, 1, 1, 7]
def baseStart_1384229 : Nat := 118140960795 + 1384229 * 2 ^ 59
def prefixEnd_1384229 : Nat := 4983230072969 + 3 ^ 40 * 1384229 * 2
def baseEnd_1384229 : Nat := 157949958420571095860345

theorem tailTrace_1384229 : CollatzResearch.WordTrace tailWord_1384229 prefixEnd_1384229 157949958420571095860345 := by
  unfold tailWord_1384229
  simp only [CollatzResearch.WordTrace]
  refine ⟨50486979302182215336947741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33657986201454810224631827 50486979302182215336947741)
  ·
    refine ⟨18932617238318330751355403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50486979302182215336947741 18932617238318330751355403)
    ·
      refine ⟨28398925857477496127033105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18932617238318330751355403 28398925857477496127033105)
      ·
        refine ⟨21299194393108122095274829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28398925857477496127033105 21299194393108122095274829)
        ·
          refine ⟨7987197897415545785728061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21299194393108122095274829 7987197897415545785728061)
          ·
            refine ⟨2995199211530829669648023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7987197897415545785728061 2995199211530829669648023)
            ·
              refine ⟨4492798817296244504472035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2995199211530829669648023 4492798817296244504472035)
              ·
                refine ⟨6739198225944366756708053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4492798817296244504472035 6739198225944366756708053)
                ·
                  refine ⟨157949958420571095860345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6739198225944366756708053 157949958420571095860345)
                  ·
                    rfl

theorem cell22_1384229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 7].length) (baseStart_1384229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1384229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1384229 prefixEnd_1384229 := by exact prefixLift 1384229
  have htrace : WordTrace (prefixWord ++ tailWord_1384229) baseStart_1384229 baseEnd_1384229 := by
    simpa [prefixWord, tailWord_1384229, baseEnd_1384229] using wordTrace_append hprefix tailTrace_1384229
  have hstable : (prefixWord ++ tailWord_1384229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384229).length < 2 ^ (prefixWord ++ tailWord_1384229).sum := by decide
  have hdescent : baseEnd_1384229 < baseStart_1384229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384304 : List Nat := [2, 1, 1, 1, 4, 1, 1, 1, 6, 4]
def baseStart_1384304 : Nat := 118140960795 + 1384304 * 2 ^ 59
def prefixEnd_1384304 : Nat := 4983230072969 + 3 ^ 40 * 1384304 * 2
def baseEnd_1384304 : Nat := 473875549294438091955805

theorem tailTrace_1384304 : CollatzResearch.WordTrace tailWord_1384304 prefixEnd_1384304 473875549294438091955805 := by
  unfold tailWord_1384304
  simp only [CollatzResearch.WordTrace]
  refine ⟨25244857388455251572963983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33659809851273668763951977 25244857388455251572963983)
  ·
    refine ⟨37867286082682877359445975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25244857388455251572963983 37867286082682877359445975)
    ·
      refine ⟨56800929124024316039168963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37867286082682877359445975 56800929124024316039168963)
      ·
        refine ⟨85201393686036474058753445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56800929124024316039168963 85201393686036474058753445)
        ·
          refine ⟨15975261316131838886016271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85201393686036474058753445 15975261316131838886016271)
          ·
            refine ⟨23962891974197758329024407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15975261316131838886016271 23962891974197758329024407)
            ·
              refine ⟨35944337961296637493536611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23962891974197758329024407 35944337961296637493536611)
              ·
                refine ⟨53916506941944956240304917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35944337961296637493536611 53916506941944956240304917)
                ·
                  refine ⟨2527336262903669823764293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 53916506941944956240304917 2527336262903669823764293)
                  ·
                    refine ⟨473875549294438091955805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2527336262903669823764293 473875549294438091955805)
                    ·
                      rfl

theorem cell22_1384304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 6, 4].length) (baseStart_1384304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1384304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1384304 prefixEnd_1384304 := by exact prefixLift 1384304
  have htrace : WordTrace (prefixWord ++ tailWord_1384304) baseStart_1384304 baseEnd_1384304 := by
    simpa [prefixWord, tailWord_1384304, baseEnd_1384304] using wordTrace_append hprefix tailTrace_1384304
  have hstable : (prefixWord ++ tailWord_1384304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384304).length < 2 ^ (prefixWord ++ tailWord_1384304).sum := by decide
  have hdescent : baseEnd_1384304 < baseStart_1384304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384338 : List Nat := [3, 2, 3, 2, 1, 1, 2, 2, 2, 4]
def baseStart_1384338 : Nat := 118140960795 + 1384338 * 2 ^ 59
def prefixEnd_1384338 : Nat := 4983230072969 + 3 ^ 40 * 1384338 * 2
def baseEnd_1384338 : Nat := 473887188189273336605701

theorem tailTrace_1384338 : CollatzResearch.WordTrace tailWord_1384338 prefixEnd_1384338 473887188189273336605701 := by
  unfold tailWord_1384338
  simp only [CollatzResearch.WordTrace]
  refine ⟨12622738714696831738166417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33660636572524884635110445 12622738714696831738166417)
  ·
    refine ⟨9467054036022623803624813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12622738714696831738166417 9467054036022623803624813)
    ·
      refine ⟨3550145263508483926359305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9467054036022623803624813 3550145263508483926359305)
      ·
        refine ⟨2662608947631362944769479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3550145263508483926359305 2662608947631362944769479)
        ·
          refine ⟨3993913421447044417154219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2662608947631362944769479 3993913421447044417154219)
          ·
            refine ⟨5990870132170566625731329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3993913421447044417154219 5990870132170566625731329)
            ·
              refine ⟨4493152599127924969298497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5990870132170566625731329 4493152599127924969298497)
              ·
                refine ⟨3369864449345943726973873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4493152599127924969298497 3369864449345943726973873)
                ·
                  refine ⟨2527398337009457795230405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3369864449345943726973873 2527398337009457795230405)
                  ·
                    refine ⟨473887188189273336605701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2527398337009457795230405 473887188189273336605701)
                    ·
                      rfl

theorem cell22_1384338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_1384338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1384338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1384338 prefixEnd_1384338 := by exact prefixLift 1384338
  have htrace : WordTrace (prefixWord ++ tailWord_1384338) baseStart_1384338 baseEnd_1384338 := by
    simpa [prefixWord, tailWord_1384338, baseEnd_1384338] using wordTrace_append hprefix tailTrace_1384338
  have hstable : (prefixWord ++ tailWord_1384338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384338).length < 2 ^ (prefixWord ++ tailWord_1384338).sum := by decide
  have hdescent : baseEnd_1384338 < baseStart_1384338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384340 : List Nat := [2, 4, 2, 1, 1, 3, 2, 2, 2, 3]
def baseStart_1384340 : Nat := 118140960795 + 1384340 * 2 ^ 59
def prefixEnd_1384340 : Nat := 4983230072969 + 3 ^ 40 * 1384340 * 2
def baseEnd_1384340 : Nat := 473887872830145998055695

theorem tailTrace_1384340 : CollatzResearch.WordTrace tailWord_1384340 prefixEnd_1384340 473887872830145998055695 := by
  unfold tailWord_1384340
  simp only [CollatzResearch.WordTrace]
  refine ⟨25245513902390040647119237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33660685203186720862825649 25245513902390040647119237)
  ·
    refine ⟨4733533856698132621334857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25245513902390040647119237 4733533856698132621334857)
    ·
      refine ⟨3550150392523599466001143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4733533856698132621334857 3550150392523599466001143)
      ·
        refine ⟨5325225588785399199001715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3550150392523599466001143 5325225588785399199001715)
        ·
          refine ⟨7987838383178098798502573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5325225588785399199001715 7987838383178098798502573)
          ·
            refine ⟨2995439393691787049438465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7987838383178098798502573 2995439393691787049438465)
            ·
              refine ⟨2246579545268840287078849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2995439393691787049438465 2246579545268840287078849)
              ·
                refine ⟨1684934658951630215309137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2246579545268840287078849 1684934658951630215309137)
                ·
                  refine ⟨1263700994213722661481853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1684934658951630215309137 1263700994213722661481853)
                  ·
                    refine ⟨473887872830145998055695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1263700994213722661481853 473887872830145998055695)
                    ·
                      rfl

theorem cell22_1384340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_1384340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1384340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1384340 prefixEnd_1384340 := by exact prefixLift 1384340
  have htrace : WordTrace (prefixWord ++ tailWord_1384340) baseStart_1384340 baseEnd_1384340 := by
    simpa [prefixWord, tailWord_1384340, baseEnd_1384340] using wordTrace_append hprefix tailTrace_1384340
  have hstable : (prefixWord ++ tailWord_1384340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384340).length < 2 ^ (prefixWord ++ tailWord_1384340).sum := by decide
  have hdescent : baseEnd_1384340 < baseStart_1384340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384353 : List Nat := [1, 2, 3, 4, 2, 2, 1, 7]
def baseStart_1384353 : Nat := 118140960795 + 1384353 * 2 ^ 59
def prefixEnd_1384353 : Nat := 4983230072969 + 3 ^ 40 * 1384353 * 2
def baseEnd_1384353 : Nat := 52654702555090921942295

theorem tailTrace_1384353 : CollatzResearch.WordTrace tailWord_1384353 prefixEnd_1384353 52654702555090921942295 := by
  unfold tailWord_1384353
  simp only [CollatzResearch.WordTrace]
  refine ⟨50491501953732984514461713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33661001302488656342974475 50491501953732984514461713)
  ·
    refine ⟨37868626465299738385846285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50491501953732984514461713 37868626465299738385846285)
    ·
      refine ⟨14200734924487401894692357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37868626465299738385846285 14200734924487401894692357)
      ·
        refine ⟨2662637798341387855254817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14200734924487401894692357 2662637798341387855254817)
        ·
          refine ⟨1996978348756040891441113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2662637798341387855254817 1996978348756040891441113)
          ·
            refine ⟨1497733761567030668580835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1996978348756040891441113 1497733761567030668580835)
            ·
              refine ⟨2246600642350546002871253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1497733761567030668580835 2246600642350546002871253)
              ·
                refine ⟨52654702555090921942295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2246600642350546002871253 52654702555090921942295)
                ·
                  rfl

theorem cell22_1384353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 7].length) (baseStart_1384353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1384353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1384353 prefixEnd_1384353 := by exact prefixLift 1384353
  have htrace : WordTrace (prefixWord ++ tailWord_1384353) baseStart_1384353 baseEnd_1384353 := by
    simpa [prefixWord, tailWord_1384353, baseEnd_1384353] using wordTrace_append hprefix tailTrace_1384353
  have hstable : (prefixWord ++ tailWord_1384353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384353).length < 2 ^ (prefixWord ++ tailWord_1384353).sum := by decide
  have hdescent : baseEnd_1384353 < baseStart_1384353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384372 : List Nat := [2, 5, 2, 1, 2, 2, 1, 1, 2, 4]
def baseStart_1384372 : Nat := 118140960795 + 1384372 * 2 ^ 59
def prefixEnd_1384372 : Nat := 4983230072969 + 3 ^ 40 * 1384372 * 2
def baseEnd_1384372 : Nat := 473898827084108581255597

theorem tailTrace_1384372 : CollatzResearch.WordTrace tailWord_1384372 prefixEnd_1384372 473898827084108581255597 := by
  unfold tailWord_1384372
  simp only [CollatzResearch.WordTrace]
  refine ⟨25246097470332075379701685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33661463293776100506268913 25246097470332075379701685)
  ·
    refine ⟨2366821637843632066847033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25246097470332075379701685 2366821637843632066847033)
    ·
      refine ⟨1775116228382724050135275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2366821637843632066847033 1775116228382724050135275)
      ·
        refine ⟨2662674342574086075202913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1775116228382724050135275 2662674342574086075202913)
        ·
          refine ⟨1997005756930564556402185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2662674342574086075202913 1997005756930564556402185)
          ·
            refine ⟨1497754317697923417301639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1997005756930564556402185 1497754317697923417301639)
            ·
              refine ⟨2246631476546885125952459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1497754317697923417301639 2246631476546885125952459)
              ·
                refine ⟨3369947214820327688928689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2246631476546885125952459 3369947214820327688928689)
                ·
                  refine ⟨2527460411115245766696517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3369947214820327688928689 2527460411115245766696517)
                  ·
                    refine ⟨473898827084108581255597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2527460411115245766696517 473898827084108581255597)
                    ·
                      rfl

theorem cell22_1384372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_1384372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1384372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1384372 prefixEnd_1384372 := by exact prefixLift 1384372
  have htrace : WordTrace (prefixWord ++ tailWord_1384372) baseStart_1384372 baseEnd_1384372 := by
    simpa [prefixWord, tailWord_1384372, baseEnd_1384372] using wordTrace_append hprefix tailTrace_1384372
  have hstable : (prefixWord ++ tailWord_1384372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384372).length < 2 ^ (prefixWord ++ tailWord_1384372).sum := by decide
  have hdescent : baseEnd_1384372 < baseStart_1384372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384379 : List Nat := [1, 1, 1, 1, 1, 2, 2, 4, 4, 5]
def baseStart_1384379 : Nat := 118140960795 + 1384379 * 2 ^ 59
def prefixEnd_1384379 : Nat := 4983230072969 + 3 ^ 40 * 1384379 * 2
def baseEnd_1384379 : Nat := 473901223327162896330575

theorem tailTrace_1384379 : CollatzResearch.WordTrace tailWord_1384379 prefixEnd_1384379 473901223327162896330575 := by
  unfold tailWord_1384379
  simp only [CollatzResearch.WordTrace]
  refine ⟨50492450251638790954908191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33661633501092527303272127 50492450251638790954908191)
  ·
    refine ⟨75738675377458186432362287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50492450251638790954908191 75738675377458186432362287)
    ·
      refine ⟨113608013066187279648543431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75738675377458186432362287 113608013066187279648543431)
      ·
        refine ⟨170412019599280919472815147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113608013066187279648543431 170412019599280919472815147)
        ·
          refine ⟨255618029398921379209222721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170412019599280919472815147 255618029398921379209222721)
          ·
            refine ⟨191713522049191034406917041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 255618029398921379209222721 191713522049191034406917041)
            ·
              refine ⟨143785141536893275805187781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191713522049191034406917041 143785141536893275805187781)
              ·
                refine ⟨26959714038167489213472709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 143785141536893275805187781 26959714038167489213472709)
                ·
                  refine ⟨5054946382156404227526133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26959714038167489213472709 5054946382156404227526133)
                  ·
                    refine ⟨473901223327162896330575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5054946382156404227526133 473901223327162896330575)
                    ·
                      rfl

theorem cell22_1384379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4, 5].length) (baseStart_1384379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1384379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1384379 prefixEnd_1384379 := by exact prefixLift 1384379
  have htrace : WordTrace (prefixWord ++ tailWord_1384379) baseStart_1384379 baseEnd_1384379 := by
    simpa [prefixWord, tailWord_1384379, baseEnd_1384379] using wordTrace_append hprefix tailTrace_1384379
  have hstable : (prefixWord ++ tailWord_1384379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384379).length < 2 ^ (prefixWord ++ tailWord_1384379).sum := by decide
  have hdescent : baseEnd_1384379 < baseStart_1384379 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384396 : List Nat := [2, 2, 1, 4, 1, 2, 1, 2, 2, 5]
def baseStart_1384396 : Nat := 118140960795 + 1384396 * 2 ^ 59
def prefixEnd_1384396 : Nat := 4983230072969 + 3 ^ 40 * 1384396 * 2
def baseEnd_1384396 : Nat := 473907042774580518655523

theorem tailTrace_1384396 : CollatzResearch.WordTrace tailWord_1384396 prefixEnd_1384396 473907042774580518655523 := by
  unfold tailWord_1384396
  simp only [CollatzResearch.WordTrace]
  refine ⟨25246535146288601429138521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33662046861718135238851361 25246535146288601429138521)
  ·
    refine ⟨18934901359716451071853891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25246535146288601429138521 18934901359716451071853891)
    ·
      refine ⟨28402352039574676607780837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18934901359716451071853891 28402352039574676607780837)
      ·
        refine ⟨5325441007420251863958907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28402352039574676607780837 5325441007420251863958907)
        ·
          refine ⟨7988161511130377795938361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5325441007420251863958907 7988161511130377795938361)
          ·
            refine ⟨5991121133347783346953771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7988161511130377795938361 5991121133347783346953771)
            ·
              refine ⟨8986681700021675020430657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5991121133347783346953771 8986681700021675020430657)
              ·
                refine ⟨6740011275016256265322993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8986681700021675020430657 6740011275016256265322993)
                ·
                  refine ⟨5055008456262192198992245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6740011275016256265322993 5055008456262192198992245)
                  ·
                    refine ⟨473907042774580518655523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5055008456262192198992245 473907042774580518655523)
                    ·
                      rfl

theorem cell22_1384396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 2, 5].length) (baseStart_1384396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1384396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1384396 prefixEnd_1384396 := by exact prefixLift 1384396
  have htrace : WordTrace (prefixWord ++ tailWord_1384396) baseStart_1384396 baseEnd_1384396 := by
    simpa [prefixWord, tailWord_1384396, baseEnd_1384396] using wordTrace_append hprefix tailTrace_1384396
  have hstable : (prefixWord ++ tailWord_1384396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384396).length < 2 ^ (prefixWord ++ tailWord_1384396).sum := by decide
  have hdescent : baseEnd_1384396 < baseStart_1384396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384426 : List Nat := [3, 1, 3, 1, 2, 1, 1, 4, 6]
def baseStart_1384426 : Nat := 118140960795 + 1384426 * 2 ^ 59
def prefixEnd_1384426 : Nat := 4983230072969 + 3 ^ 40 * 1384426 * 2
def baseEnd_1384426 : Nat := 157972437462556813468477

theorem tailTrace_1384426 : CollatzResearch.WordTrace tailWord_1384426 prefixEnd_1384426 157972437462556813468477 := by
  unfold tailWord_1384426
  simp only [CollatzResearch.WordTrace]
  refine ⟨12623541120617129495467283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33662776321645678654579421 12623541120617129495467283)
  ·
    refine ⟨18935311680925694243200925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12623541120617129495467283 18935311680925694243200925)
    ·
      refine ⟨7100741880347135341200347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18935311680925694243200925 7100741880347135341200347)
      ·
        refine ⟨10651112820520703011800521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7100741880347135341200347 10651112820520703011800521)
        ·
          refine ⟨7988334615390527258850391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10651112820520703011800521 7988334615390527258850391)
          ·
            refine ⟨11982501923085790888275587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7988334615390527258850391 11982501923085790888275587)
            ·
              refine ⟨17973752884628686332413381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11982501923085790888275587 17973752884628686332413381)
              ·
                refine ⟨3370078665867878687327509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17973752884628686332413381 3370078665867878687327509)
                ·
                  refine ⟨157972437462556813468477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3370078665867878687327509 157972437462556813468477)
                  ·
                    rfl

theorem cell22_1384426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 4, 6].length) (baseStart_1384426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1384426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1384426 prefixEnd_1384426 := by exact prefixLift 1384426
  have htrace : WordTrace (prefixWord ++ tailWord_1384426) baseStart_1384426 baseEnd_1384426 := by
    simpa [prefixWord, tailWord_1384426, baseEnd_1384426] using wordTrace_append hprefix tailTrace_1384426
  have hstable : (prefixWord ++ tailWord_1384426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384426).length < 2 ^ (prefixWord ++ tailWord_1384426).sum := by decide
  have hdescent : baseEnd_1384426 < baseStart_1384426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384443 : List Nat := [1, 1, 1, 1, 1, 3, 7, 3, 4]
def baseStart_1384443 : Nat := 118140960795 + 1384443 * 2 ^ 59
def prefixEnd_1384443 : Nat := 4983230072969 + 3 ^ 40 * 1384443 * 2
def baseEnd_1384443 : Nat := 157974377278362687576793

theorem tailTrace_1384443 : CollatzResearch.WordTrace tailWord_1384443 prefixEnd_1384443 157974377278362687576793 := by
  unfold tailWord_1384443
  simp only [CollatzResearch.WordTrace]
  refine ⟨50494784523406929885237983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33663189682271286590158655 50494784523406929885237983)
  ·
    refine ⟨75742176785110394827856975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50494784523406929885237983 75742176785110394827856975)
    ·
      refine ⟨113613265177665592241785463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75742176785110394827856975 113613265177665592241785463)
      ·
        refine ⟨170419897766498388362678195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113613265177665592241785463 170419897766498388362678195)
        ·
          refine ⟨255629846649747582544017293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170419897766498388362678195 255629846649747582544017293)
          ·
            refine ⟨95861192493655343454006485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 255629846649747582544017293 95861192493655343454006485)
            ·
              refine ⟨2246746699070047112203277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 95861192493655343454006485 2246746699070047112203277)
              ·
                refine ⟨842530012151267667076229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2246746699070047112203277 842530012151267667076229)
                ·
                  refine ⟨157974377278362687576793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 842530012151267667076229 157974377278362687576793)
                  ·
                    rfl

theorem cell22_1384443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 3, 4].length) (baseStart_1384443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1384443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1384443 prefixEnd_1384443 := by exact prefixLift 1384443
  have htrace : WordTrace (prefixWord ++ tailWord_1384443) baseStart_1384443 baseEnd_1384443 := by
    simpa [prefixWord, tailWord_1384443, baseEnd_1384443] using wordTrace_append hprefix tailTrace_1384443
  have hstable : (prefixWord ++ tailWord_1384443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384443).length < 2 ^ (prefixWord ++ tailWord_1384443).sum := by decide
  have hdescent : baseEnd_1384443 < baseStart_1384443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384460 : List Nat := [2, 2, 1, 2, 3, 1, 5, 2, 4]
def baseStart_1384460 : Nat := 118140960795 + 1384460 * 2 ^ 59
def prefixEnd_1384460 : Nat := 4983230072969 + 3 ^ 40 * 1384460 * 2
def baseEnd_1384460 : Nat := 157976317094168561685109

theorem tailTrace_1384460 : CollatzResearch.WordTrace tailWord_1384460 prefixEnd_1384460 157976317094168561685109 := by
  unfold tailWord_1384460
  simp only [CollatzResearch.WordTrace]
  refine ⟨25247702282172670894303417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33663603042896894525737889 25247702282172670894303417)
  ·
    refine ⟨18935776711629503170727563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25247702282172670894303417 18935776711629503170727563)
    ·
      refine ⟨28403665067444254756091345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18935776711629503170727563 28403665067444254756091345)
      ·
        refine ⟨21302748800583191067068509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28403665067444254756091345 21302748800583191067068509)
        ·
          refine ⟨7988530800218696650150691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21302748800583191067068509 7988530800218696650150691)
          ·
            refine ⟨11982796200328044975226037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7988530800218696650150691 11982796200328044975226037)
            ·
              refine ⟨1123387143780754216427441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11982796200328044975226037 1123387143780754216427441)
              ·
                refine ⟨842540357835565662320581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1123387143780754216427441 842540357835565662320581)
                ·
                  refine ⟨157976317094168561685109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 842540357835565662320581 157976317094168561685109)
                  ·
                    rfl

theorem cell22_1384460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 5, 2, 4].length) (baseStart_1384460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1384460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1384460 prefixEnd_1384460 := by exact prefixLift 1384460
  have htrace : WordTrace (prefixWord ++ tailWord_1384460) baseStart_1384460 baseEnd_1384460 := by
    simpa [prefixWord, tailWord_1384460, baseEnd_1384460] using wordTrace_append hprefix tailTrace_1384460
  have hstable : (prefixWord ++ tailWord_1384460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384460).length < 2 ^ (prefixWord ++ tailWord_1384460).sum := by decide
  have hdescent : baseEnd_1384460 < baseStart_1384460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384490 : List Nat := [3, 1, 4, 1, 2, 2, 2, 1, 2, 4]
def baseStart_1384490 : Nat := 118140960795 + 1384490 * 2 ^ 59
def prefixEnd_1384490 : Nat := 4983230072969 + 3 ^ 40 * 1384490 * 2
def baseEnd_1384490 : Nat := 473939220895595606805235

theorem tailTrace_1384490 : CollatzResearch.WordTrace tailWord_1384490 prefixEnd_1384490 473939220895595606805235 := by
  unfold tailWord_1384490
  simp only [CollatzResearch.WordTrace]
  refine ⟨12624124688559164228049731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33664332502824437941465949 12624124688559164228049731)
  ·
    refine ⟨18936187032838746342074597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12624124688559164228049731 18936187032838746342074597)
    ·
      refine ⟨3550535068657264939138987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18936187032838746342074597 3550535068657264939138987)
      ·
        refine ⟨5325802602985897408708481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3550535068657264939138987 5325802602985897408708481)
        ·
          refine ⟨3994351952239423056531361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5325802602985897408708481 3994351952239423056531361)
          ·
            refine ⟨2995763964179567292398521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3994351952239423056531361 2995763964179567292398521)
            ·
              refine ⟨2246822973134675469298891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2995763964179567292398521 2246822973134675469298891)
              ·
                refine ⟨3370234459702013203948337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2246822973134675469298891 3370234459702013203948337)
                ·
                  refine ⟨2527675844776509902961253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3370234459702013203948337 2527675844776509902961253)
                  ·
                    refine ⟨473939220895595606805235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2527675844776509902961253 473939220895595606805235)
                    ·
                      rfl

theorem cell22_1384490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_1384490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1384490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1384490 prefixEnd_1384490 := by exact prefixLift 1384490
  have htrace : WordTrace (prefixWord ++ tailWord_1384490) baseStart_1384490 baseEnd_1384490 := by
    simpa [prefixWord, tailWord_1384490, baseEnd_1384490] using wordTrace_append hprefix tailTrace_1384490
  have hstable : (prefixWord ++ tailWord_1384490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384490).length < 2 ^ (prefixWord ++ tailWord_1384490).sum := by decide
  have hdescent : baseEnd_1384490 < baseStart_1384490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384533 : List Nat := [1, 3, 2, 2, 1, 3, 2, 3, 5]
def baseStart_1384533 : Nat := 118140960795 + 1384533 * 2 ^ 59
def prefixEnd_1384533 : Nat := 4983230072969 + 3 ^ 40 * 1384533 * 2
def baseEnd_1384533 : Nat := 157984646891452609326701

theorem tailTrace_1384533 : CollatzResearch.WordTrace tailWord_1384533 prefixEnd_1384533 157984646891452609326701 := by
  unfold tailWord_1384533
  simp only [CollatzResearch.WordTrace]
  refine ⟨50498067093080875256014253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33665378062053916837342835 50498067093080875256014253)
  ·
    refine ⟨18936775159905328221005345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50498067093080875256014253 18936775159905328221005345)
    ·
      refine ⟨14202581369928996165754009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18936775159905328221005345 14202581369928996165754009)
      ·
        refine ⟨10651936027446747124315507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14202581369928996165754009 10651936027446747124315507)
        ·
          refine ⟨15977904041170120686473261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10651936027446747124315507 15977904041170120686473261)
          ·
            refine ⟨5991714015438795257427473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15977904041170120686473261 5991714015438795257427473)
            ·
              refine ⟨4493785511579096443070605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5991714015438795257427473 4493785511579096443070605)
              ·
                refine ⟨1685169566842161166151477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4493785511579096443070605 1685169566842161166151477)
                ·
                  refine ⟨157984646891452609326701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1685169566842161166151477 157984646891452609326701)
                  ·
                    rfl

theorem cell22_1384533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 3, 5].length) (baseStart_1384533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1384533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1384533 prefixEnd_1384533 := by exact prefixLift 1384533
  have htrace : WordTrace (prefixWord ++ tailWord_1384533) baseStart_1384533 baseEnd_1384533 := by
    simpa [prefixWord, tailWord_1384533, baseEnd_1384533] using wordTrace_append hprefix tailTrace_1384533
  have hstable : (prefixWord ++ tailWord_1384533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384533).length < 2 ^ (prefixWord ++ tailWord_1384533).sum := by decide
  have hdescent : baseEnd_1384533 < baseStart_1384533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384554 : List Nat := [3, 1, 3, 2, 3, 1, 2, 3, 1, 3]
def baseStart_1384554 : Nat := 118140960795 + 1384554 * 2 ^ 59
def prefixEnd_1384554 : Nat := 4983230072969 + 3 ^ 40 * 1384554 * 2
def baseEnd_1384554 : Nat := 473961129403520773205039

theorem tailTrace_1384554 : CollatzResearch.WordTrace tailWord_1384554 prefixEnd_1384554 473961129403520773205039 := by
  unfold tailWord_1384554
  simp only [CollatzResearch.WordTrace]
  refine ⟨12624708256501198960632179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33665888684003197228352477 12624708256501198960632179)
  ·
    refine ⟨18937062384751798440948269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12624708256501198960632179 18937062384751798440948269)
    ·
      refine ⟨7101398394281924415355601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18937062384751798440948269 7101398394281924415355601)
      ·
        refine ⟨5326048795711443311516701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7101398394281924415355601 5326048795711443311516701)
        ·
          refine ⟨1997268298391791241818763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5326048795711443311516701 1997268298391791241818763)
          ·
            refine ⟨2995902447587686862728145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1997268298391791241818763 2995902447587686862728145)
            ·
              refine ⟨2246926835690765147046109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2995902447587686862728145 2246926835690765147046109)
              ·
                refine ⟨842597563384036930142291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2246926835690765147046109 842597563384036930142291)
                ·
                  refine ⟨1263896345076055395213437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 842597563384036930142291 1263896345076055395213437)
                  ·
                    refine ⟨473961129403520773205039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1263896345076055395213437 473961129403520773205039)
                    ·
                      rfl

theorem cell22_1384554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 3, 1, 3].length) (baseStart_1384554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1384554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1384554 prefixEnd_1384554 := by exact prefixLift 1384554
  have htrace : WordTrace (prefixWord ++ tailWord_1384554) baseStart_1384554 baseEnd_1384554 := by
    simpa [prefixWord, tailWord_1384554, baseEnd_1384554] using wordTrace_append hprefix tailTrace_1384554
  have hstable : (prefixWord ++ tailWord_1384554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384554).length < 2 ^ (prefixWord ++ tailWord_1384554).sum := by decide
  have hdescent : baseEnd_1384554 < baseStart_1384554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384561 : List Nat := [1, 2, 2, 2, 1, 1, 3, 2, 8]
def baseStart_1384561 : Nat := 118140960795 + 1384561 * 2 ^ 59
def prefixEnd_1384561 : Nat := 4983230072969 + 3 ^ 40 * 1384561 * 2
def baseEnd_1384561 : Nat := 157987841882191696093339

theorem tailTrace_1384561 : CollatzResearch.WordTrace tailWord_1384561 prefixEnd_1384561 157987841882191696093339 := by
  unfold tailWord_1384561
  simp only [CollatzResearch.WordTrace]
  refine ⟨50499088336979436038033537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33666058891319624025355691 50499088336979436038033537)
  ·
    refine ⟨37874316252734577028525153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50499088336979436038033537 37874316252734577028525153)
    ·
      refine ⟨28405737189550932771393865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37874316252734577028525153 28405737189550932771393865)
      ·
        refine ⟨21304302892163199578545399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28405737189550932771393865 21304302892163199578545399)
        ·
          refine ⟨31956454338244799367818099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21304302892163199578545399 31956454338244799367818099)
          ·
            refine ⟨47934681507367199051727149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31956454338244799367818099 47934681507367199051727149)
            ·
              refine ⟨17975505565262699644397681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47934681507367199051727149 17975505565262699644397681)
              ·
                refine ⟨13481629173947024733298261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17975505565262699644397681 13481629173947024733298261)
                ·
                  refine ⟨157987841882191696093339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13481629173947024733298261 157987841882191696093339)
                  ·
                    rfl

theorem cell22_1384561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 8].length) (baseStart_1384561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1384561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1384561 prefixEnd_1384561 := by exact prefixLift 1384561
  have htrace : WordTrace (prefixWord ++ tailWord_1384561) baseStart_1384561 baseEnd_1384561 := by
    simpa [prefixWord, tailWord_1384561, baseEnd_1384561] using wordTrace_append hprefix tailTrace_1384561
  have hstable : (prefixWord ++ tailWord_1384561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384561).length < 2 ^ (prefixWord ++ tailWord_1384561).sum := by decide
  have hdescent : baseEnd_1384561 < baseStart_1384561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384608 : List Nat := [2, 1, 1, 4, 2, 2, 2, 1, 1, 6]
def baseStart_1384608 : Nat := 118140960795 + 1384608 * 2 ^ 59
def prefixEnd_1384608 : Nat := 4983230072969 + 3 ^ 40 * 1384608 * 2
def baseEnd_1384608 : Nat := 473979614707082632354873

theorem tailTrace_1384608 : CollatzResearch.WordTrace tailWord_1384608 prefixEnd_1384608 473979614707082632354873 := by
  unfold tailWord_1384608
  simp only [CollatzResearch.WordTrace]
  refine ⟨25250401283904581532497239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33667201711872775376662985 25250401283904581532497239)
  ·
    refine ⟨37875601925856872298745859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25250401283904581532497239 37875601925856872298745859)
    ·
      refine ⟨56813402888785308448118789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37875601925856872298745859 56813402888785308448118789)
      ·
        refine ⟨10652513041647245334022273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56813402888785308448118789 10652513041647245334022273)
        ·
          refine ⟨7989384781235434000516705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10652513041647245334022273 7989384781235434000516705)
          ·
            refine ⟨5992038585926575500387529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7989384781235434000516705 5992038585926575500387529)
            ·
              refine ⟨4494028939444931625290647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5992038585926575500387529 4494028939444931625290647)
              ·
                refine ⟨6741043409167397437935971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4494028939444931625290647 6741043409167397437935971)
                ·
                  refine ⟨10111565113751096156903957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6741043409167397437935971 10111565113751096156903957)
                  ·
                    refine ⟨473979614707082632354873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10111565113751096156903957 473979614707082632354873)
                    ·
                      rfl

theorem cell22_1384608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 1, 6].length) (baseStart_1384608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1384608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1384608 prefixEnd_1384608 := by exact prefixLift 1384608
  have htrace : WordTrace (prefixWord ++ tailWord_1384608) baseStart_1384608 baseEnd_1384608 := by
    simpa [prefixWord, tailWord_1384608, baseEnd_1384608] using wordTrace_append hprefix tailTrace_1384608
  have hstable : (prefixWord ++ tailWord_1384608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384608).length < 2 ^ (prefixWord ++ tailWord_1384608).sum := by decide
  have hdescent : baseEnd_1384608 < baseStart_1384608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384629 : List Nat := [1, 3, 3, 4, 2, 1, 1, 1, 6]
def baseStart_1384629 : Nat := 118140960795 + 1384629 * 2 ^ 59
def prefixEnd_1384629 : Nat := 4983230072969 + 3 ^ 40 * 1384629 * 2
def baseEnd_1384629 : Nat := 157995601145415192526603

theorem tailTrace_1384629 : CollatzResearch.WordTrace tailWord_1384629 prefixEnd_1384629 157995601145415192526603 := by
  unfold tailWord_1384629
  simp only [CollatzResearch.WordTrace]
  refine ⟨50501568500733083651508941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33667712333822055767672627 50501568500733083651508941)
  ·
    refine ⟨18938088187774906369315853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50501568500733083651508941 18938088187774906369315853)
    ·
      refine ⟨7101783070415589888493445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18938088187774906369315853 7101783070415589888493445)
      ·
        refine ⟨1331584325702923104092521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7101783070415589888493445 1331584325702923104092521)
        ·
          refine ⟨998688244277192328069391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1331584325702923104092521 998688244277192328069391)
          ·
            refine ⟨1498032366415788492104087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 998688244277192328069391 1498032366415788492104087)
            ·
              refine ⟨2247048549623682738156131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1498032366415788492104087 2247048549623682738156131)
              ·
                refine ⟨3370572824435524107234197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2247048549623682738156131 3370572824435524107234197)
                ·
                  refine ⟨157995601145415192526603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3370572824435524107234197 157995601145415192526603)
                  ·
                    rfl

theorem cell22_1384629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 1, 6].length) (baseStart_1384629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1384629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1384629 prefixEnd_1384629 := by exact prefixLift 1384629
  have htrace : WordTrace (prefixWord ++ tailWord_1384629) baseStart_1384629 baseEnd_1384629 := by
    simpa [prefixWord, tailWord_1384629, baseEnd_1384629] using wordTrace_append hprefix tailTrace_1384629
  have hstable : (prefixWord ++ tailWord_1384629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384629).length < 2 ^ (prefixWord ++ tailWord_1384629).sum := by decide
  have hdescent : baseEnd_1384629 < baseStart_1384629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384644 : List Nat := [2, 3, 3, 1, 2, 1, 4, 1, 2, 3]
def baseStart_1384644 : Nat := 118140960795 + 1384644 * 2 ^ 59
def prefixEnd_1384644 : Nat := 4983230072969 + 3 ^ 40 * 1384644 * 2
def baseEnd_1384644 : Nat := 473991938242790538454763

theorem tailTrace_1384644 : CollatzResearch.WordTrace tailWord_1384644 prefixEnd_1384644 473991938242790538454763 := by
  unfold tailWord_1384644
  simp only [CollatzResearch.WordTrace]
  refine ⟨25251057797839370606652493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33668077063785827475536657 25251057797839370606652493)
  ·
    refine ⟨9469146674189763977494685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25251057797839370606652493 9469146674189763977494685)
    ·
      refine ⟨3550930002821161491560507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9469146674189763977494685 3550930002821161491560507)
      ·
        refine ⟨5326395004231742237340761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3550930002821161491560507 5326395004231742237340761)
        ·
          refine ⟨3994796253173806678005571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5326395004231742237340761 3994796253173806678005571)
          ·
            refine ⟨5992194379760710017008357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3994796253173806678005571 5992194379760710017008357)
            ·
              refine ⟨1123536446205133128189067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5992194379760710017008357 1123536446205133128189067)
              ·
                refine ⟨1685304669307699692283601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1123536446205133128189067 1685304669307699692283601)
                ·
                  refine ⟨1263978501980774769212701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1685304669307699692283601 1263978501980774769212701)
                  ·
                    refine ⟨473991938242790538454763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1263978501980774769212701 473991938242790538454763)
                    ·
                      rfl

theorem cell22_1384644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_1384644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1384644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1384644 prefixEnd_1384644 := by exact prefixLift 1384644
  have htrace : WordTrace (prefixWord ++ tailWord_1384644) baseStart_1384644 baseEnd_1384644 := by
    simpa [prefixWord, tailWord_1384644, baseEnd_1384644] using wordTrace_append hprefix tailTrace_1384644
  have hstable : (prefixWord ++ tailWord_1384644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384644).length < 2 ^ (prefixWord ++ tailWord_1384644).sum := by decide
  have hdescent : baseEnd_1384644 < baseStart_1384644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384672 : List Nat := [2, 1, 1, 3, 1, 3, 2, 5, 1, 3]
def baseStart_1384672 : Nat := 118140960795 + 1384672 * 2 ^ 59
def prefixEnd_1384672 : Nat := 4983230072969 + 3 ^ 40 * 1384672 * 2
def baseEnd_1384672 : Nat := 474001523215007798754677

theorem tailTrace_1384672 : CollatzResearch.WordTrace tailWord_1384672 prefixEnd_1384672 474001523215007798754677 := by
  unfold tailWord_1384672
  simp only [CollatzResearch.WordTrace]
  refine ⟨25251568419788650997662135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33668757893051534663549513 25251568419788650997662135)
  ·
    refine ⟨37877352629682976496493203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25251568419788650997662135 37877352629682976496493203)
    ·
      refine ⟨56816028944524464744739805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37877352629682976496493203 56816028944524464744739805)
      ·
        refine ⟨21306010854196674279277427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56816028944524464744739805 21306010854196674279277427)
        ·
          refine ⟨31959016281295011418916141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21306010854196674279277427 31959016281295011418916141)
          ·
            refine ⟨11984631105485629282093553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31959016281295011418916141 11984631105485629282093553)
            ·
              refine ⟨8988473329114221961570165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11984631105485629282093553 8988473329114221961570165)
              ·
                refine ⟨842669374604458308897203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8988473329114221961570165 842669374604458308897203)
                ·
                  refine ⟨1264004061906687463345805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 842669374604458308897203 1264004061906687463345805)
                  ·
                    refine ⟨474001523215007798754677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1264004061906687463345805 474001523215007798754677)
                    ·
                      rfl

theorem cell22_1384672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 5, 1, 3].length) (baseStart_1384672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1384672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1384672 prefixEnd_1384672 := by exact prefixLift 1384672
  have htrace : WordTrace (prefixWord ++ tailWord_1384672) baseStart_1384672 baseEnd_1384672 := by
    simpa [prefixWord, tailWord_1384672, baseEnd_1384672] using wordTrace_append hprefix tailTrace_1384672
  have hstable : (prefixWord ++ tailWord_1384672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384672).length < 2 ^ (prefixWord ++ tailWord_1384672).sum := by decide
  have hdescent : baseEnd_1384672 < baseStart_1384672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384674 : List Nat := [3, 3, 4, 1, 2, 9]
def baseStart_1384674 : Nat := 118140960795 + 1384674 * 2 ^ 59
def prefixEnd_1384674 : Nat := 4983230072969 + 3 ^ 40 * 1384674 * 2
def baseEnd_1384674 : Nat := 5851879109331857533391

theorem tailTrace_1384674 : CollatzResearch.WordTrace tailWord_1384674 prefixEnd_1384674 5851879109331857533391 := by
  unfold tailWord_1384674
  simp only [CollatzResearch.WordTrace]
  refine ⟨12625802446392514084224269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33668806523713370891264717 12625802446392514084224269)
  ·
    refine ⟨4734675917397192781584101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12625802446392514084224269 4734675917397192781584101)
    ·
      refine ⟨887751734511973646547019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4734675917397192781584101 887751734511973646547019)
      ·
        refine ⟨1331627601767960469820529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 887751734511973646547019 1331627601767960469820529)
        ·
          refine ⟨998720701325970352365397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1331627601767960469820529 998720701325970352365397)
          ·
            refine ⟨5851879109331857533391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 998720701325970352365397 5851879109331857533391)
            ·
              rfl

theorem cell22_1384674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 9].length) (baseStart_1384674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1384674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1384674 prefixEnd_1384674 := by exact prefixLift 1384674
  have htrace : WordTrace (prefixWord ++ tailWord_1384674) baseStart_1384674 baseEnd_1384674 := by
    simpa [prefixWord, tailWord_1384674, baseEnd_1384674] using wordTrace_append hprefix tailTrace_1384674
  have hstable : (prefixWord ++ tailWord_1384674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384674).length < 2 ^ (prefixWord ++ tailWord_1384674).sum := by decide
  have hdescent : baseEnd_1384674 < baseStart_1384674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384683 : List Nat := [1, 1, 1, 1, 2, 5, 2, 2, 2, 5]
def baseStart_1384683 : Nat := 118140960795 + 1384683 * 2 ^ 59
def prefixEnd_1384683 : Nat := 4983230072969 + 3 ^ 40 * 1384683 * 2
def baseEnd_1384683 : Nat := 474005288739807436729643

theorem tailTrace_1384683 : CollatzResearch.WordTrace tailWord_1384683 prefixEnd_1384683 474005288739807436729643 := by
  unfold tailWord_1384683
  simp only [CollatzResearch.WordTrace]
  refine ⟨50503538042537450873974703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33669025361691633915983135 50503538042537450873974703)
  ·
    refine ⟨75755307063806176310962055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50503538042537450873974703 75755307063806176310962055)
    ·
      refine ⟨113632960595709264466443083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75755307063806176310962055 113632960595709264466443083)
      ·
        refine ⟨170449440893563896699664625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113632960595709264466443083 170449440893563896699664625)
        ·
          refine ⟨127837080670172922524748469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170449440893563896699664625 127837080670172922524748469)
          ·
            refine ⟨11984726312828711486695169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 127837080670172922524748469 11984726312828711486695169)
            ·
              refine ⟨8988544734621533615021377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11984726312828711486695169 8988544734621533615021377)
              ·
                refine ⟨6741408550966150211266033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8988544734621533615021377 6741408550966150211266033)
                ·
                  refine ⟨5056056413224612658449525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6741408550966150211266033 5056056413224612658449525)
                  ·
                    refine ⟨474005288739807436729643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5056056413224612658449525 474005288739807436729643)
                    ·
                      rfl

theorem cell22_1384683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 2, 5].length) (baseStart_1384683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1384683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1384683 prefixEnd_1384683 := by exact prefixLift 1384683
  have htrace : WordTrace (prefixWord ++ tailWord_1384683) baseStart_1384683 baseEnd_1384683 := by
    simpa [prefixWord, tailWord_1384683, baseEnd_1384683] using wordTrace_append hprefix tailTrace_1384683
  have hstable : (prefixWord ++ tailWord_1384683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384683).length < 2 ^ (prefixWord ++ tailWord_1384683).sum := by decide
  have hdescent : baseEnd_1384683 < baseStart_1384683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384689 : List Nat := [1, 2, 2, 2, 2, 1, 6, 2, 1, 3]
def baseStart_1384689 : Nat := 118140960795 + 1384689 * 2 ^ 59
def prefixEnd_1384689 : Nat := 4983230072969 + 3 ^ 40 * 1384689 * 2
def baseEnd_1384689 : Nat := 474007342662425421079625

theorem tailTrace_1384689 : CollatzResearch.WordTrace tailWord_1384689 prefixEnd_1384689 474007342662425421079625 := by
  unfold tailWord_1384689
  simp only [CollatzResearch.WordTrace]
  refine ⟨50503756880515713898693121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33669171253677142599128747 50503756880515713898693121)
  ·
    refine ⟨37877817660386785424019841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50503756880515713898693121 37877817660386785424019841)
    ·
      refine ⟨28408363245290089068014881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37877817660386785424019841 28408363245290089068014881)
      ·
        refine ⟨21306272433967566801011161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28408363245290089068014881 21306272433967566801011161)
        ·
          refine ⟨15979704325475675100758371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21306272433967566801011161 15979704325475675100758371)
          ·
            refine ⟨23969556488213512651137557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15979704325475675100758371 23969556488213512651137557)
            ·
              refine ⟨1123572960385008405522073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 23969556488213512651137557 1123572960385008405522073)
              ·
                refine ⟨842679720288756304141555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1123572960385008405522073 842679720288756304141555)
                ·
                  refine ⟨1264019580433134456212333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 842679720288756304141555 1264019580433134456212333)
                  ·
                    refine ⟨474007342662425421079625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1264019580433134456212333 474007342662425421079625)
                    ·
                      rfl

theorem cell22_1384689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 6, 2, 1, 3].length) (baseStart_1384689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1384689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1384689 prefixEnd_1384689 := by exact prefixLift 1384689
  have htrace : WordTrace (prefixWord ++ tailWord_1384689) baseStart_1384689 baseEnd_1384689 := by
    simpa [prefixWord, tailWord_1384689, baseEnd_1384689] using wordTrace_append hprefix tailTrace_1384689
  have hstable : (prefixWord ++ tailWord_1384689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384689).length < 2 ^ (prefixWord ++ tailWord_1384689).sum := by decide
  have hdescent : baseEnd_1384689 < baseStart_1384689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384700 : List Nat := [2, 2, 2, 1, 4, 2, 1, 1, 2, 5]
def baseStart_1384700 : Nat := 118140960795 + 1384700 * 2 ^ 59
def prefixEnd_1384700 : Nat := 4983230072969 + 3 ^ 40 * 1384700 * 2
def baseEnd_1384700 : Nat := 474011108187225059054591

theorem tailTrace_1384700 : CollatzResearch.WordTrace tailWord_1384700 prefixEnd_1384700 474011108187225059054591 := by
  unfold tailWord_1384700
  simp only [CollatzResearch.WordTrace]
  refine ⟨25252079041737931388671777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33669438722317241851562369 25252079041737931388671777)
  ·
    refine ⟨18939059281303448541503833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25252079041737931388671777 18939059281303448541503833)
    ·
      refine ⟨14204294460977586406127875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18939059281303448541503833 14204294460977586406127875)
      ·
        refine ⟨21306441691466379609191813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14204294460977586406127875 21306441691466379609191813)
        ·
          refine ⟨3994957817149946176723465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21306441691466379609191813 3994957817149946176723465)
          ·
            refine ⟨2996218362862459632542599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3994957817149946176723465 2996218362862459632542599)
            ·
              refine ⟨4494327544293689448813899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2996218362862459632542599 4494327544293689448813899)
              ·
                refine ⟨6741491316440534173220849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4494327544293689448813899 6741491316440534173220849)
                ·
                  refine ⟨5056118487330400629915637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6741491316440534173220849 5056118487330400629915637)
                  ·
                    refine ⟨474011108187225059054591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5056118487330400629915637 474011108187225059054591)
                    ·
                      rfl

theorem cell22_1384700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 2, 5].length) (baseStart_1384700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1384700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1384700 prefixEnd_1384700 := by exact prefixLift 1384700
  have htrace : WordTrace (prefixWord ++ tailWord_1384700) baseStart_1384700 baseEnd_1384700 := by
    simpa [prefixWord, tailWord_1384700, baseEnd_1384700] using wordTrace_append hprefix tailTrace_1384700
  have hstable : (prefixWord ++ tailWord_1384700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384700).length < 2 ^ (prefixWord ++ tailWord_1384700).sum := by decide
  have hdescent : baseEnd_1384700 < baseStart_1384700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384713 : List Nat := [1, 2, 1, 1, 3, 4, 1, 1, 8]
def baseStart_1384713 : Nat := 118140960795 + 1384713 * 2 ^ 59
def prefixEnd_1384713 : Nat := 4983230072969 + 3 ^ 40 * 1384713 * 2
def baseEnd_1384713 : Nat := 158005186117632452826517

theorem tailTrace_1384713 : CollatzResearch.WordTrace tailWord_1384713 prefixEnd_1384713 158005186117632452826517 := by
  unfold tailWord_1384713
  simp only [CollatzResearch.WordTrace]
  refine ⟨50504632232428765997566793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33669754821619177331711195 50504632232428765997566793)
  ·
    refine ⟨37878474174321574498175095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50504632232428765997566793 37878474174321574498175095)
    ·
      refine ⟨56817711261482361747262643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37878474174321574498175095 56817711261482361747262643)
      ·
        refine ⟨85226566892223542620893965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56817711261482361747262643 85226566892223542620893965)
        ·
          refine ⟨31959962584583828482835237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85226566892223542620893965 31959962584583828482835237)
          ·
            refine ⟨5992492984609467840531607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31959962584583828482835237 5992492984609467840531607)
            ·
              refine ⟨8988739476914201760797411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5992492984609467840531607 8988739476914201760797411)
              ·
                refine ⟨13483109215371302641196117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8988739476914201760797411 13483109215371302641196117)
                ·
                  refine ⟨158005186117632452826517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13483109215371302641196117 158005186117632452826517)
                  ·
                    rfl

theorem cell22_1384713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 8].length) (baseStart_1384713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1384713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1384713 prefixEnd_1384713 := by exact prefixLift 1384713
  have htrace : WordTrace (prefixWord ++ tailWord_1384713) baseStart_1384713 baseEnd_1384713 := by
    simpa [prefixWord, tailWord_1384713, baseEnd_1384713] using wordTrace_append hprefix tailTrace_1384713
  have hstable : (prefixWord ++ tailWord_1384713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384713).length < 2 ^ (prefixWord ++ tailWord_1384713).sum := by decide
  have hdescent : baseEnd_1384713 < baseStart_1384713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384715 : List Nat := [1, 1, 1, 1, 5, 2, 2, 4, 1, 4]
def baseStart_1384715 : Nat := 118140960795 + 1384715 * 2 ^ 59
def prefixEnd_1384715 : Nat := 4983230072969 + 3 ^ 40 * 1384715 * 2
def baseEnd_1384715 : Nat := 474016242993770019929545

theorem tailTrace_1384715 : CollatzResearch.WordTrace tailWord_1384715 prefixEnd_1384715 474016242993770019929545 := by
  unfold tailWord_1384715
  simp only [CollatzResearch.WordTrace]
  refine ⟨50504705178421520339139599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33669803452281013559426399 50504705178421520339139599)
  ·
    refine ⟨75757057767632280508709399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50504705178421520339139599 75757057767632280508709399)
    ·
      refine ⟨113635586651448420763064099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75757057767632280508709399 113635586651448420763064099)
      ·
        refine ⟨170453379977172631144596149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113635586651448420763064099 170453379977172631144596149)
        ·
          refine ⟨15980004372859934169805889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 170453379977172631144596149 15980004372859934169805889)
          ·
            refine ⟨11985003279644950627354417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15980004372859934169805889 11985003279644950627354417)
            ·
              refine ⟨8988752459733712970515813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11985003279644950627354417 8988752459733712970515813)
              ·
                refine ⟨1685391086200071181971715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8988752459733712970515813 1685391086200071181971715)
                ·
                  refine ⟨2528086629300106772957573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1685391086200071181971715 2528086629300106772957573)
                  ·
                    refine ⟨474016242993770019929545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2528086629300106772957573 474016242993770019929545)
                    ·
                      rfl

theorem cell22_1384715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 4, 1, 4].length) (baseStart_1384715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1384715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1384715 prefixEnd_1384715 := by exact prefixLift 1384715
  have htrace : WordTrace (prefixWord ++ tailWord_1384715) baseStart_1384715 baseEnd_1384715 := by
    simpa [prefixWord, tailWord_1384715, baseEnd_1384715] using wordTrace_append hprefix tailTrace_1384715
  have hstable : (prefixWord ++ tailWord_1384715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384715).length < 2 ^ (prefixWord ++ tailWord_1384715).sum := by decide
  have hdescent : baseEnd_1384715 < baseStart_1384715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384762 : List Nat := [3, 1, 1, 1, 4, 4, 1, 1, 1, 5]
def baseStart_1384762 : Nat := 118140960795 + 1384762 * 2 ^ 59
def prefixEnd_1384762 : Nat := 4983230072969 + 3 ^ 40 * 1384762 * 2
def baseEnd_1384762 : Nat := 474032332054277564004401

theorem tailTrace_1384762 : CollatzResearch.WordTrace tailWord_1384762 prefixEnd_1384762 474032332054277564004401 := by
  unfold tailWord_1384762
  simp only [CollatzResearch.WordTrace]
  refine ⟨12626604852312811841525135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33670946272834164910733693 12626604852312811841525135)
  ·
    refine ⟨18939907278469217762287703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12626604852312811841525135 18939907278469217762287703)
    ·
      refine ⟨28409860917703826643431555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18939907278469217762287703 28409860917703826643431555)
      ·
        refine ⟨42614791376555739965147333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28409860917703826643431555 42614791376555739965147333)
        ·
          refine ⟨7990273383104201243465125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42614791376555739965147333 7990273383104201243465125)
          ·
            refine ⟨1498176259332037733149711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7990273383104201243465125 1498176259332037733149711)
            ·
              refine ⟨2247264388998056599724567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1498176259332037733149711 2247264388998056599724567)
              ·
                refine ⟨3370896583497084899586851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2247264388998056599724567 3370896583497084899586851)
                ·
                  refine ⟨5056344875245627349380277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3370896583497084899586851 5056344875245627349380277)
                  ·
                    refine ⟨474032332054277564004401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5056344875245627349380277 474032332054277564004401)
                    ·
                      rfl

theorem cell22_1384762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 1, 1, 5].length) (baseStart_1384762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1384762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1384762 prefixEnd_1384762 := by exact prefixLift 1384762
  have htrace : WordTrace (prefixWord ++ tailWord_1384762) baseStart_1384762 baseEnd_1384762 := by
    simpa [prefixWord, tailWord_1384762, baseEnd_1384762] using wordTrace_append hprefix tailTrace_1384762
  have hstable : (prefixWord ++ tailWord_1384762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384762).length < 2 ^ (prefixWord ++ tailWord_1384762).sum := by decide
  have hdescent : baseEnd_1384762 < baseStart_1384762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384858 : List Nat := [3, 1, 1, 4, 1, 4, 2, 2, 1, 3]
def baseStart_1384858 : Nat := 118140960795 + 1384858 * 2 ^ 59
def prefixEnd_1384858 : Nat := 4983230072969 + 3 ^ 40 * 1384858 * 2
def baseEnd_1384858 : Nat := 474065194816165313604107

theorem tailTrace_1384858 : CollatzResearch.WordTrace tailWord_1384858 prefixEnd_1384858 474065194816165313604107 := by
  unfold tailWord_1384858
  simp only [CollatzResearch.WordTrace]
  refine ⟨12627480204225863940398807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33673280544602303841063485 12627480204225863940398807)
  ·
    refine ⟨18941220306338795910598211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12627480204225863940398807 18941220306338795910598211)
    ·
      refine ⟨28411830459508193865897317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18941220306338795910598211 28411830459508193865897317)
      ·
        refine ⟨5327218211157786349855747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28411830459508193865897317 5327218211157786349855747)
        ·
          refine ⟨7990827316736679524783621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5327218211157786349855747 7990827316736679524783621)
          ·
            refine ⟨1498280121888127410896929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7990827316736679524783621 1498280121888127410896929)
            ·
              refine ⟨1123710091416095558172697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1498280121888127410896929 1123710091416095558172697)
              ·
                refine ⟨842782568562071668629523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1123710091416095558172697 842782568562071668629523)
                ·
                  refine ⟨1264173852843107502944285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 842782568562071668629523 1264173852843107502944285)
                  ·
                    refine ⟨474065194816165313604107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1264173852843107502944285 474065194816165313604107)
                    ·
                      rfl

theorem cell22_1384858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 2, 2, 1, 3].length) (baseStart_1384858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1384858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1384858 prefixEnd_1384858 := by exact prefixLift 1384858
  have htrace : WordTrace (prefixWord ++ tailWord_1384858) baseStart_1384858 baseEnd_1384858 := by
    simpa [prefixWord, tailWord_1384858, baseEnd_1384858] using wordTrace_append hprefix tailTrace_1384858
  have hstable : (prefixWord ++ tailWord_1384858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384858).length < 2 ^ (prefixWord ++ tailWord_1384858).sum := by decide
  have hdescent : baseEnd_1384858 < baseStart_1384858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384931 : List Nat := [1, 1, 1, 6, 4, 1, 1, 1, 1, 5]
def baseStart_1384931 : Nat := 118140960795 + 1384931 * 2 ^ 59
def prefixEnd_1384931 : Nat := 4983230072969 + 3 ^ 40 * 1384931 * 2
def baseEnd_1384931 : Nat := 474090184208017456528883

theorem tailTrace_1384931 : CollatzResearch.WordTrace tailWord_1384931 prefixEnd_1384931 474090184208017456528883 := by
  unfold tailWord_1384931
  simp only [CollatzResearch.WordTrace]
  refine ⟨50512583345638989229002647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33675055563759326152668431 50512583345638989229002647)
  ·
    refine ⟨75768875018458483843503971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50512583345638989229002647 75768875018458483843503971)
    ·
      refine ⟨113653312527687725765255957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75768875018458483843503971 113653312527687725765255957)
      ·
        refine ⟨5327499024735362145246373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 113653312527687725765255957 5327499024735362145246373)
        ·
          refine ⟨998906067137880402233695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5327499024735362145246373 998906067137880402233695)
          ·
            refine ⟨1498359100706820603350543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 998906067137880402233695 1498359100706820603350543)
            ·
              refine ⟨2247538651060230905025815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1498359100706820603350543 2247538651060230905025815)
              ·
                refine ⟨3371307976590346357538723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2247538651060230905025815 3371307976590346357538723)
                ·
                  refine ⟨5056961964885519536308085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3371307976590346357538723 5056961964885519536308085)
                  ·
                    refine ⟨474090184208017456528883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5056961964885519536308085 474090184208017456528883)
                    ·
                      rfl

theorem cell22_1384931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 1, 1, 5].length) (baseStart_1384931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1384931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1384931 prefixEnd_1384931 := by exact prefixLift 1384931
  have htrace : WordTrace (prefixWord ++ tailWord_1384931) baseStart_1384931 baseEnd_1384931 := by
    simpa [prefixWord, tailWord_1384931, baseEnd_1384931] using wordTrace_append hprefix tailTrace_1384931
  have hstable : (prefixWord ++ tailWord_1384931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384931).length < 2 ^ (prefixWord ++ tailWord_1384931).sum := by decide
  have hdescent : baseEnd_1384931 < baseStart_1384931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384972 : List Nat := [2, 2, 1, 2, 4, 1, 2, 1, 7]
def baseStart_1384972 : Nat := 118140960795 + 1384972 * 2 ^ 59
def prefixEnd_1384972 : Nat := 4983230072969 + 3 ^ 40 * 1384972 * 2
def baseEnd_1384972 : Nat := 158034739781969005417919

theorem tailTrace_1384972 : CollatzResearch.WordTrace tailWord_1384972 prefixEnd_1384972 158034739781969005417919 := by
  unfold tailWord_1384972
  simp only [CollatzResearch.WordTrace]
  refine ⟨25257039369245226615622585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33676052492326968820830113 25257039369245226615622585)
  ·
    refine ⟨18942779526933919961716939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25257039369245226615622585 18942779526933919961716939)
    ·
      refine ⟨28414169290400879942575409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18942779526933919961716939 28414169290400879942575409)
      ·
        refine ⟨21310626967800659956931557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28414169290400879942575409 21310626967800659956931557)
        ·
          refine ⟨3995742556462623741924667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21310626967800659956931557 3995742556462623741924667)
          ·
            refine ⟨5993613834693935612887001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3995742556462623741924667 5993613834693935612887001)
            ·
              refine ⟨4495210376020451709665251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5993613834693935612887001 4495210376020451709665251)
              ·
                refine ⟨6742815564030677564497877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4495210376020451709665251 6742815564030677564497877)
                ·
                  refine ⟨158034739781969005417919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6742815564030677564497877 158034739781969005417919)
                  ·
                    rfl

theorem cell22_1384972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 7].length) (baseStart_1384972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1384972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1384972 prefixEnd_1384972 := by exact prefixLift 1384972
  have htrace : WordTrace (prefixWord ++ tailWord_1384972) baseStart_1384972 baseEnd_1384972 := by
    simpa [prefixWord, tailWord_1384972, baseEnd_1384972] using wordTrace_append hprefix tailTrace_1384972
  have hstable : (prefixWord ++ tailWord_1384972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384972).length < 2 ^ (prefixWord ++ tailWord_1384972).sum := by decide
  have hdescent : baseEnd_1384972 < baseStart_1384972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384989 : List Nat := [1, 4, 2, 2, 1, 3, 1, 3, 5]
def baseStart_1384989 : Nat := 118140960795 + 1384989 * 2 ^ 59
def prefixEnd_1384989 : Nat := 4983230072969 + 3 ^ 40 * 1384989 * 2
def baseEnd_1384989 : Nat := 158036679597774879526235

theorem tailTrace_1384989 : CollatzResearch.WordTrace tailWord_1384989 prefixEnd_1384989 158036679597774879526235 := by
  unfold tailWord_1384989
  simp only [CollatzResearch.WordTrace]
  refine ⟨50514698779428865134614021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33676465852952576756409347 50514698779428865134614021)
  ·
    refine ⟨9471506021142912212740129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50514698779428865134614021 9471506021142912212740129)
    ·
      refine ⟨7103629515857184159555097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9471506021142912212740129 7103629515857184159555097)
      ·
        refine ⟨5327722136892888119666323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7103629515857184159555097 5327722136892888119666323)
        ·
          refine ⟨7991583205339332179499485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5327722136892888119666323 7991583205339332179499485)
          ·
            refine ⟨2996843702002249567312307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7991583205339332179499485 2996843702002249567312307)
            ·
              refine ⟨4495265553003374350968461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2996843702002249567312307 4495265553003374350968461)
              ·
                refine ⟨1685724582376265381613173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4495265553003374350968461 1685724582376265381613173)
                ·
                  refine ⟨158036679597774879526235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1685724582376265381613173 158036679597774879526235)
                  ·
                    rfl

theorem cell22_1384989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 3, 5].length) (baseStart_1384989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1384989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1384989 prefixEnd_1384989 := by exact prefixLift 1384989
  have htrace : WordTrace (prefixWord ++ tailWord_1384989) baseStart_1384989 baseEnd_1384989 := by
    simpa [prefixWord, tailWord_1384989, baseEnd_1384989] using wordTrace_append hprefix tailTrace_1384989
  have hstable : (prefixWord ++ tailWord_1384989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384989).length < 2 ^ (prefixWord ++ tailWord_1384989).sum := by decide
  have hdescent : baseEnd_1384989 < baseStart_1384989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385047 : List Nat := [1, 1, 3, 2, 2, 2, 2, 2, 1, 6]
def baseStart_1385047 : Nat := 118140960795 + 1385047 * 2 ^ 59
def prefixEnd_1385047 : Nat := 4983230072969 + 3 ^ 40 * 1385047 * 2
def baseEnd_1385047 : Nat := 474129893378631820628527

theorem tailTrace_1385047 : CollatzResearch.WordTrace tailWord_1385047 prefixEnd_1385047 474129893378631820628527 := by
  unfold tailWord_1385047
  simp only [CollatzResearch.WordTrace]
  refine ⟨50516814213218741040225395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33677876142145827360150263 50516814213218741040225395)
  ·
    refine ⟨75775221319828111560338093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50516814213218741040225395 75775221319828111560338093)
    ·
      refine ⟨28415707994935541835126785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75775221319828111560338093 28415707994935541835126785)
      ·
        refine ⟨21311780996201656376345089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28415707994935541835126785 21311780996201656376345089)
        ·
          refine ⟨15983835747151242282258817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21311780996201656376345089 15983835747151242282258817)
          ·
            refine ⟨11987876810363431711694113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15983835747151242282258817 11987876810363431711694113)
            ·
              refine ⟨8990907607772573783770585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11987876810363431711694113 8990907607772573783770585)
              ·
                refine ⟨6743180705829430337827939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8990907607772573783770585 6743180705829430337827939)
                ·
                  refine ⟨10114771058744145506741909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6743180705829430337827939 10114771058744145506741909)
                  ·
                    refine ⟨474129893378631820628527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10114771058744145506741909 474129893378631820628527)
                    ·
                      rfl

theorem cell22_1385047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 6].length) (baseStart_1385047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1385047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1385047 prefixEnd_1385047 := by exact prefixLift 1385047
  have htrace : WordTrace (prefixWord ++ tailWord_1385047) baseStart_1385047 baseEnd_1385047 := by
    simpa [prefixWord, tailWord_1385047, baseEnd_1385047] using wordTrace_append hprefix tailTrace_1385047
  have hstable : (prefixWord ++ tailWord_1385047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385047).length < 2 ^ (prefixWord ++ tailWord_1385047).sum := by decide
  have hdescent : baseEnd_1385047 < baseStart_1385047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385188 : List Nat := [2, 3, 1, 1, 1, 5, 3, 1, 1, 4]
def baseStart_1385188 : Nat := 118140960795 + 1385188 * 2 ^ 59
def prefixEnd_1385188 : Nat := 4983230072969 + 3 ^ 40 * 1385188 * 2
def baseEnd_1385188 : Nat := 474178160560154452853095

theorem tailTrace_1385188 : CollatzResearch.WordTrace tailWord_1385188 prefixEnd_1385188 474178160560154452853095 := by
  unfold tailWord_1385188
  simp only [CollatzResearch.WordTrace]
  refine ⟨25260978452853961060554109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33681304603805281414072145 25260978452853961060554109)
  ·
    refine ⟨9472866919820235397707791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25260978452853961060554109 9472866919820235397707791)
    ·
      refine ⟨14209300379730353096561687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9472866919820235397707791 14209300379730353096561687)
      ·
        refine ⟨21313950569595529644842531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14209300379730353096561687 21313950569595529644842531)
        ·
          refine ⟨31970925854393294467263797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21313950569595529644842531 31970925854393294467263797)
          ·
            refine ⟨2997274298849371356305981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31970925854393294467263797 2997274298849371356305981)
            ·
              refine ⟨1123977862068514258614743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2997274298849371356305981 1123977862068514258614743)
              ·
                refine ⟨1685966793102771387922115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1123977862068514258614743 1685966793102771387922115)
                ·
                  refine ⟨2528950189654157081883173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1685966793102771387922115 2528950189654157081883173)
                  ·
                    refine ⟨474178160560154452853095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2528950189654157081883173 474178160560154452853095)
                    ·
                      rfl

theorem cell22_1385188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 3, 1, 1, 4].length) (baseStart_1385188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1385188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1385188 prefixEnd_1385188 := by exact prefixLift 1385188
  have htrace : WordTrace (prefixWord ++ tailWord_1385188) baseStart_1385188 baseEnd_1385188 := by
    simpa [prefixWord, tailWord_1385188, baseEnd_1385188] using wordTrace_append hprefix tailTrace_1385188
  have hstable : (prefixWord ++ tailWord_1385188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385188).length < 2 ^ (prefixWord ++ tailWord_1385188).sum := by decide
  have hdescent : baseEnd_1385188 < baseStart_1385188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
