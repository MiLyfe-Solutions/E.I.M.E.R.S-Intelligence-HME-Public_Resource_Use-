import V185TrunkScan23Chunk1013

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6004009 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 8, 2, 3]
def baseStart_6004009 : Nat := 118140960795 + 6004009 * 2 ^ 59
def prefixEnd_6004009 : Nat := 4983230072969 + 3 ^ 40 * 6004009 * 2
def baseEnd_6004009 : Nat := 3082942470920505020875571

theorem tailTrace_6004009 : CollatzResearch.WordTrace tailWord_6004009 prefixEnd_6004009 3082942470920505020875571 := by
  unfold tailWord_6004009
  simp only [CollatzResearch.WordTrace]
  refine ⟨218984198505508270945799081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145989465670338847297199387 218984198505508270945799081)
  ·
    refine ⟨164238148879131203209349311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218984198505508270945799081 164238148879131203209349311)
    ·
      refine ⟨246357223318696804814023967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164238148879131203209349311 246357223318696804814023967)
      ·
        refine ⟨369535834978045207221035951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246357223318696804814023967 369535834978045207221035951)
        ·
          refine ⟨554303752467067810831553927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 369535834978045207221035951 554303752467067810831553927)
          ·
            refine ⟨831455628700601716247330891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 554303752467067810831553927 831455628700601716247330891)
            ·
              refine ⟨1247183443050902574370996337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 831455628700601716247330891 1247183443050902574370996337)
              ·
                refine ⟨935387582288176930778247253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1247183443050902574370996337 935387582288176930778247253)
                ·
                  refine ⟨10961573229939573407557585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 935387582288176930778247253 10961573229939573407557585)
                  ·
                    refine ⟨8221179922454680055668189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10961573229939573407557585 8221179922454680055668189)
                    ·
                      refine ⟨3082942470920505020875571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8221179922454680055668189 3082942470920505020875571)
                      ·
                        rfl

theorem cell23_6004009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 8, 2, 3].length) (baseStart_6004009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6004009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6004009 prefixEnd_6004009 := by exact prefixLift 6004009
  have htrace : WordTrace (prefixWord ++ tailWord_6004009) baseStart_6004009 baseEnd_6004009 := by
    simpa [prefixWord, tailWord_6004009, baseEnd_6004009] using wordTrace_append hprefix tailTrace_6004009
  have hstable : (prefixWord ++ tailWord_6004009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6004009).length < 2 ^ (prefixWord ++ tailWord_6004009).sum := by decide
  have hdescent : baseEnd_6004009 < baseStart_6004009 := by decide
  rcases family_descends (prefixWord ++ tailWord_6004009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6004033 : List Nat := [1, 2, 5, 2, 1, 2, 1, 2, 3, 4]
def baseStart_6004033 : Nat := 118140960795 + 6004033 * 2 ^ 59
def prefixEnd_6004033 : Nat := 4983230072969 + 3 ^ 40 * 6004033 * 2
def baseEnd_6004033 : Nat := 1027651598152070975658487

theorem tailTrace_6004033 : CollatzResearch.WordTrace tailWord_6004033 prefixEnd_6004033 1027651598152070975658487 := by
  unfold tailWord_6004033
  simp only [CollatzResearch.WordTrace]
  refine ⟨218985073857421323044672753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145990049238280882029781835 218985073857421323044672753)
  ·
    refine ⟨164238805393065992283504565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218985073857421323044672753 164238805393065992283504565)
    ·
      refine ⟨15397388005599936776578553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 164238805393065992283504565 15397388005599936776578553)
      ·
        refine ⟨11548041004199952582433915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15397388005599936776578553 11548041004199952582433915)
        ·
          refine ⟨17322061506299928873650873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11548041004199952582433915 17322061506299928873650873)
          ·
            refine ⟨12991546129724946655238155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17322061506299928873650873 12991546129724946655238155)
            ·
              refine ⟨19487319194587419982857233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12991546129724946655238155 19487319194587419982857233)
              ·
                refine ⟨14615489395940564987142925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19487319194587419982857233 14615489395940564987142925)
                ·
                  refine ⟨5480808523477711870178597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14615489395940564987142925 5480808523477711870178597)
                  ·
                    refine ⟨1027651598152070975658487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5480808523477711870178597 1027651598152070975658487)
                    ·
                      rfl

theorem cell23_6004033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_6004033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6004033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6004033 prefixEnd_6004033 := by exact prefixLift 6004033
  have htrace : WordTrace (prefixWord ++ tailWord_6004033) baseStart_6004033 baseEnd_6004033 := by
    simpa [prefixWord, tailWord_6004033, baseEnd_6004033] using wordTrace_append hprefix tailTrace_6004033
  have hstable : (prefixWord ++ tailWord_6004033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6004033).length < 2 ^ (prefixWord ++ tailWord_6004033).sum := by decide
  have hdescent : baseEnd_6004033 < baseStart_6004033 := by decide
  rcases family_descends (prefixWord ++ tailWord_6004033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6004056 : List Nat := [2, 1, 2, 2, 1, 1, 3, 2, 5, 1, 3]
def baseStart_6004056 : Nat := 118140960795 + 6004056 * 2 ^ 59
def prefixEnd_6004056 : Nat := 4983230072969 + 3 ^ 40 * 6004056 * 2
def baseEnd_6004056 : Nat := 3082966604511266336987855

theorem tailTrace_6004056 : CollatzResearch.WordTrace tailWord_6004056 prefixEnd_6004056 3082966604511266336987855 := by
  unfold tailWord_6004056
  simp only [CollatzResearch.WordTrace]
  refine ⟨109492956368168998986380011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145990608490891998648506681 109492956368168998986380011)
  ·
    refine ⟨164239434552253498479570017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109492956368168998986380011 164239434552253498479570017)
    ·
      refine ⟨123179575914190123859677513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164239434552253498479570017 123179575914190123859677513)
      ·
        refine ⟨92384681935642592894758135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123179575914190123859677513 92384681935642592894758135)
        ·
          refine ⟨138577022903463889342137203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92384681935642592894758135 138577022903463889342137203)
          ·
            refine ⟨207865534355195834013205805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138577022903463889342137203 207865534355195834013205805)
            ·
              refine ⟨77949575383198437754952177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 207865534355195834013205805 77949575383198437754952177)
              ·
                refine ⟨58462181537398828316214133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77949575383198437754952177 58462181537398828316214133)
                ·
                  refine ⟨5480829519131140154645075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58462181537398828316214133 5480829519131140154645075)
                  ·
                    refine ⟨8221244278696710231967613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5480829519131140154645075 8221244278696710231967613)
                    ·
                      refine ⟨3082966604511266336987855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8221244278696710231967613 3082966604511266336987855)
                      ·
                        rfl

theorem cell23_6004056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 5, 1, 3].length) (baseStart_6004056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6004056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6004056 prefixEnd_6004056 := by exact prefixLift 6004056
  have htrace : WordTrace (prefixWord ++ tailWord_6004056) baseStart_6004056 baseEnd_6004056 := by
    simpa [prefixWord, tailWord_6004056, baseEnd_6004056] using wordTrace_append hprefix tailTrace_6004056
  have hstable : (prefixWord ++ tailWord_6004056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6004056).length < 2 ^ (prefixWord ++ tailWord_6004056).sum := by decide
  have hdescent : baseEnd_6004056 < baseStart_6004056 := by decide
  rcases family_descends (prefixWord ++ tailWord_6004056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6004124 : List Nat := [2, 2, 3, 4, 2, 1, 1, 1, 3, 1, 3]
def baseStart_6004124 : Nat := 118140960795 + 6004124 * 2 ^ 59
def prefixEnd_6004124 : Nat := 4983230072969 + 3 ^ 40 * 6004124 * 2
def baseEnd_6004124 : Nat := 3083001521195772070937543

theorem tailTrace_6004124 : CollatzResearch.WordTrace tailWord_6004124 prefixEnd_6004124 3083001521195772070937543 := by
  unfold tailWord_6004124
  simp only [CollatzResearch.WordTrace]
  refine ⟨109494196450045822793117713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145992261933394430390823617 109494196450045822793117713)
  ·
    refine ⟨82120647337534367094838285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109494196450045822793117713 82120647337534367094838285)
    ·
      refine ⟨30795242751575387660564357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82120647337534367094838285 30795242751575387660564357)
      ·
        refine ⟨5774108015920385186355817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30795242751575387660564357 5774108015920385186355817)
        ·
          refine ⟨4330581011940288889766863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5774108015920385186355817 4330581011940288889766863)
          ·
            refine ⟨6495871517910433334650295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4330581011940288889766863 6495871517910433334650295)
            ·
              refine ⟨9743807276865650001975443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6495871517910433334650295 9743807276865650001975443)
              ·
                refine ⟨14615710915298475002963165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9743807276865650001975443 14615710915298475002963165)
                ·
                  refine ⟨5480891593236928126111187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14615710915298475002963165 5480891593236928126111187)
                  ·
                    refine ⟨8221337389855392189166781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5480891593236928126111187 8221337389855392189166781)
                    ·
                      refine ⟨3083001521195772070937543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8221337389855392189166781 3083001521195772070937543)
                      ·
                        rfl

theorem cell23_6004124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_6004124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6004124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6004124 prefixEnd_6004124 := by exact prefixLift 6004124
  have htrace : WordTrace (prefixWord ++ tailWord_6004124) baseStart_6004124 baseEnd_6004124 := by
    simpa [prefixWord, tailWord_6004124, baseEnd_6004124] using wordTrace_append hprefix tailTrace_6004124
  have hstable : (prefixWord ++ tailWord_6004124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6004124).length < 2 ^ (prefixWord ++ tailWord_6004124).sum := by decide
  have hdescent : baseEnd_6004124 < baseStart_6004124 := by decide
  rcases family_descends (prefixWord ++ tailWord_6004124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6004159 : List Nat := [1, 1, 2, 2, 2, 1, 1, 3, 1, 4, 5]
def baseStart_6004159 : Nat := 118140960795 + 6004159 * 2 ^ 59
def prefixEnd_6004159 : Nat := 4983230072969 + 3 ^ 40 * 6004159 * 2
def baseEnd_6004159 : Nat := 3083019493018679433999881

theorem tailTrace_6004159 : CollatzResearch.WordTrace tailWord_6004159 prefixEnd_6004159 3083019493018679433999881 := by
  unfold tailWord_6004159
  simp only [CollatzResearch.WordTrace]
  refine ⟨218989669454964846563759531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145993112969976564375839687 218989669454964846563759531)
  ·
    refine ⟨328484504182447269845639297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218989669454964846563759531 328484504182447269845639297)
    ·
      refine ⟨246363378136835452384229473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 328484504182447269845639297 246363378136835452384229473)
      ·
        refine ⟨184772533602626589288172105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246363378136835452384229473 184772533602626589288172105)
        ·
          refine ⟨138579400201969941966129079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184772533602626589288172105 138579400201969941966129079)
          ·
            refine ⟨207869100302954912949193619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138579400201969941966129079 207869100302954912949193619)
            ·
              refine ⟨311803650454432369423790429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207869100302954912949193619 311803650454432369423790429)
              ·
                refine ⟨116926368920412138533921411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 311803650454432369423790429 116926368920412138533921411)
                ·
                  refine ⟨175389553380618207800882117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116926368920412138533921411 175389553380618207800882117)
                  ·
                    refine ⟨32885541258865913962665397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 175389553380618207800882117 32885541258865913962665397)
                    ·
                      refine ⟨3083019493018679433999881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32885541258865913962665397 3083019493018679433999881)
                      ·
                        rfl

theorem cell23_6004159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 4, 5].length) (baseStart_6004159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6004159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6004159 prefixEnd_6004159 := by exact prefixLift 6004159
  have htrace : WordTrace (prefixWord ++ tailWord_6004159) baseStart_6004159 baseEnd_6004159 := by
    simpa [prefixWord, tailWord_6004159, baseEnd_6004159] using wordTrace_append hprefix tailTrace_6004159
  have hstable : (prefixWord ++ tailWord_6004159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6004159).length < 2 ^ (prefixWord ++ tailWord_6004159).sum := by decide
  have hdescent : baseEnd_6004159 < baseStart_6004159 := by decide
  rcases family_descends (prefixWord ++ tailWord_6004159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6004186 : List Nat := [3, 1, 1, 2, 3, 2, 1, 1, 2, 3, 4]
def baseStart_6004186 : Nat := 118140960795 + 6004186 * 2 ^ 59
def prefixEnd_6004186 : Nat := 4983230072969 + 3 ^ 40 * 6004186 * 2
def baseEnd_6004186 : Nat := 3083033356996350828362257

theorem tailTrace_6004186 : CollatzResearch.WordTrace tailWord_6004186 prefixEnd_6004186 3083033356996350828362257 := by
  unfold tailWord_6004186
  simp only [CollatzResearch.WordTrace]
  refine ⟨54747663556466757543748103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145993769483911353449994941 54747663556466757543748103)
  ·
    refine ⟨82121495334700136315622155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54747663556466757543748103 82121495334700136315622155)
    ·
      refine ⟨123182243002050204473433233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82121495334700136315622155 123182243002050204473433233)
      ·
        refine ⟨92386682251537653355074925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123182243002050204473433233 92386682251537653355074925)
        ·
          refine ⟨34645005844326620008153097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92386682251537653355074925 34645005844326620008153097)
          ·
            refine ⟨25983754383244965006114823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34645005844326620008153097 25983754383244965006114823)
            ·
              refine ⟨38975631574867447509172235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25983754383244965006114823 38975631574867447509172235)
              ·
                refine ⟨58463447362301171263758353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38975631574867447509172235 58463447362301171263758353)
                ·
                  refine ⟨43847585521725878447818765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58463447362301171263758353 43847585521725878447818765)
                  ·
                    refine ⟨16442844570647204417932037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43847585521725878447818765 16442844570647204417932037)
                    ·
                      refine ⟨3083033356996350828362257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16442844570647204417932037 3083033356996350828362257)
                      ·
                        rfl

theorem cell23_6004186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 2, 3, 4].length) (baseStart_6004186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6004186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6004186 prefixEnd_6004186 := by exact prefixLift 6004186
  have htrace : WordTrace (prefixWord ++ tailWord_6004186) baseStart_6004186 baseEnd_6004186 := by
    simpa [prefixWord, tailWord_6004186, baseEnd_6004186] using wordTrace_append hprefix tailTrace_6004186
  have hstable : (prefixWord ++ tailWord_6004186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6004186).length < 2 ^ (prefixWord ++ tailWord_6004186).sum := by decide
  have hdescent : baseEnd_6004186 < baseStart_6004186 := by decide
  rcases family_descends (prefixWord ++ tailWord_6004186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6004243 : List Nat := [1, 1, 1, 2, 1, 6, 2, 4, 5]
def baseStart_6004243 : Nat := 118140960795 + 6004243 * 2 ^ 59
def prefixEnd_6004243 : Nat := 4983230072969 + 3 ^ 40 * 6004243 * 2
def baseEnd_6004243 : Nat := 342562513932628567261055

theorem tailTrace_6004243 : CollatzResearch.WordTrace tailWord_6004243 prefixEnd_6004243 342562513932628567261055 := by
  unfold tailWord_6004243
  simp only [CollatzResearch.WordTrace]
  refine ⟨218992733186660528909817383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145995155457773685939878255 218992733186660528909817383)
  ·
    refine ⟨328489099779990793364726075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218992733186660528909817383 328489099779990793364726075)
    ·
      refine ⟨492733649669986190047089113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328489099779990793364726075 492733649669986190047089113)
      ·
        refine ⟨369550237252489642535316835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 492733649669986190047089113 369550237252489642535316835)
        ·
          refine ⟨554325355878734463802975253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 369550237252489642535316835 554325355878734463802975253)
          ·
            refine ⟨25984001056815677990764465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 554325355878734463802975253 25984001056815677990764465)
            ·
              refine ⟨19488000792611758493073349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25984001056815677990764465 19488000792611758493073349)
              ·
                refine ⟨3654000148614704717451253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19488000792611758493073349 3654000148614704717451253)
                ·
                  refine ⟨342562513932628567261055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3654000148614704717451253 342562513932628567261055)
                  ·
                    rfl

theorem cell23_6004243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 4, 5].length) (baseStart_6004243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6004243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6004243 prefixEnd_6004243 := by exact prefixLift 6004243
  have htrace : WordTrace (prefixWord ++ tailWord_6004243) baseStart_6004243 baseEnd_6004243 := by
    simpa [prefixWord, tailWord_6004243, baseEnd_6004243] using wordTrace_append hprefix tailTrace_6004243
  have hstable : (prefixWord ++ tailWord_6004243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6004243).length < 2 ^ (prefixWord ++ tailWord_6004243).sum := by decide
  have hdescent : baseEnd_6004243 < baseStart_6004243 := by decide
  rcases family_descends (prefixWord ++ tailWord_6004243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6004253 : List Nat := [1, 4, 2, 2, 1, 1, 1, 3, 2, 3, 3]
def baseStart_6004253 : Nat := 118140960795 + 6004253 * 2 ^ 59
def prefixEnd_6004253 : Nat := 4983230072969 + 3 ^ 40 * 6004253 * 2
def baseEnd_6004253 : Nat := 3083067760200202066224449

theorem tailTrace_6004253 : CollatzResearch.WordTrace tailWord_6004253 prefixEnd_6004253 3083067760200202066224449 := by
  unfold tailWord_6004253
  simp only [CollatzResearch.WordTrace]
  refine ⟨218993097916624300617681413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145995398611082867078454275 218993097916624300617681413)
  ·
    refine ⟨41061205859367056365815265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 218993097916624300617681413 41061205859367056365815265)
    ·
      refine ⟨30795904394525292274361449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41061205859367056365815265 30795904394525292274361449)
      ·
        refine ⟨23096928295893969205771087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30795904394525292274361449 23096928295893969205771087)
        ·
          refine ⟨34645392443840953808656631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23096928295893969205771087 34645392443840953808656631)
          ·
            refine ⟨51968088665761430712984947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34645392443840953808656631 51968088665761430712984947)
            ·
              refine ⟨77952132998642146069477421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51968088665761430712984947 77952132998642146069477421)
              ·
                refine ⟨29232049874490804776054033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77952132998642146069477421 29232049874490804776054033)
                ·
                  refine ⟨21924037405868103582040525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29232049874490804776054033 21924037405868103582040525)
                  ·
                    refine ⟨8221514027200538843265197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21924037405868103582040525 8221514027200538843265197)
                    ·
                      refine ⟨3083067760200202066224449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8221514027200538843265197 3083067760200202066224449)
                      ·
                        rfl

theorem cell23_6004253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_6004253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6004253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6004253 prefixEnd_6004253 := by exact prefixLift 6004253
  have htrace : WordTrace (prefixWord ++ tailWord_6004253) baseStart_6004253 baseEnd_6004253 := by
    simpa [prefixWord, tailWord_6004253, baseEnd_6004253] using wordTrace_append hprefix tailTrace_6004253
  have hstable : (prefixWord ++ tailWord_6004253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6004253).length < 2 ^ (prefixWord ++ tailWord_6004253).sum := by decide
  have hdescent : baseEnd_6004253 < baseStart_6004253 := by decide
  rcases family_descends (prefixWord ++ tailWord_6004253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6004293 : List Nat := [1, 3, 1, 1, 1, 4, 3, 2, 2, 1, 4]
def baseStart_6004293 : Nat := 118140960795 + 6004293 * 2 ^ 59
def prefixEnd_6004293 : Nat := 4983230072969 + 3 ^ 40 * 6004293 * 2
def baseEnd_6004293 : Nat := 3083088299426381909724265

theorem tailTrace_6004293 : CollatzResearch.WordTrace tailWord_6004293 prefixEnd_6004293 3083088299426381909724265 := by
  unfold tailWord_6004293
  simp only [CollatzResearch.WordTrace]
  refine ⟨218994556836479387449137533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145996371224319591632758355 218994556836479387449137533)
  ·
    refine ⟨82122958813679770293426575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218994556836479387449137533 82122958813679770293426575)
    ·
      refine ⟨123184438220519655440139863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82122958813679770293426575 123184438220519655440139863)
      ·
        refine ⟨184776657330779483160209795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123184438220519655440139863 184776657330779483160209795)
        ·
          refine ⟨277164985996169224740314693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184776657330779483160209795 277164985996169224740314693)
          ·
            refine ⟨51968434874281729638809005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 277164985996169224740314693 51968434874281729638809005)
            ·
              refine ⟨19488163077855648614553377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51968434874281729638809005 19488163077855648614553377)
              ·
                refine ⟨14616122308391736460915033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19488163077855648614553377 14616122308391736460915033)
                ·
                  refine ⟨10962091731293802345686275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14616122308391736460915033 10962091731293802345686275)
                  ·
                    refine ⟨16443137596940703518529413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10962091731293802345686275 16443137596940703518529413)
                    ·
                      refine ⟨3083088299426381909724265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16443137596940703518529413 3083088299426381909724265)
                      ·
                        rfl

theorem cell23_6004293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 2, 2, 1, 4].length) (baseStart_6004293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6004293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6004293 prefixEnd_6004293 := by exact prefixLift 6004293
  have htrace : WordTrace (prefixWord ++ tailWord_6004293) baseStart_6004293 baseEnd_6004293 := by
    simpa [prefixWord, tailWord_6004293, baseEnd_6004293] using wordTrace_append hprefix tailTrace_6004293
  have hstable : (prefixWord ++ tailWord_6004293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6004293).length < 2 ^ (prefixWord ++ tailWord_6004293).sum := by decide
  have hdescent : baseEnd_6004293 < baseStart_6004293 := by decide
  rcases family_descends (prefixWord ++ tailWord_6004293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6004294 : List Nat := [6, 1, 1, 1, 4, 1, 1, 1, 7]
def baseStart_6004294 : Nat := 118140960795 + 6004294 * 2 ^ 59
def prefixEnd_6004294 : Nat := 4983230072969 + 3 ^ 40 * 6004294 * 2
def baseEnd_6004294 : Nat := 342565423656337378423529

theorem tailTrace_6004294 : CollatzResearch.WordTrace tailWord_6004294 prefixEnd_6004294 342565423656337378423529 := by
  unfold tailWord_6004294
  simp only [CollatzResearch.WordTrace]
  refine ⟨6843581040921117644372623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 145996395539650509746615957 6843581040921117644372623)
  ·
    refine ⟨10265371561381676466558935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6843581040921117644372623 10265371561381676466558935)
    ·
      refine ⟨15398057342072514699838403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10265371561381676466558935 15398057342072514699838403)
      ·
        refine ⟨23097086013108772049757605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15398057342072514699838403 23097086013108772049757605)
        ·
          refine ⟨4330703627457894759329551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23097086013108772049757605 4330703627457894759329551)
          ·
            refine ⟨6496055441186842138994327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4330703627457894759329551 6496055441186842138994327)
            ·
              refine ⟨9744083161780263208491491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6496055441186842138994327 9744083161780263208491491)
              ·
                refine ⟨14616124742670394812737237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9744083161780263208491491 14616124742670394812737237)
                ·
                  refine ⟨342565423656337378423529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14616124742670394812737237 342565423656337378423529)
                  ·
                    rfl

theorem cell23_6004294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_6004294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6004294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6004294 prefixEnd_6004294 := by exact prefixLift 6004294
  have htrace : WordTrace (prefixWord ++ tailWord_6004294) baseStart_6004294 baseEnd_6004294 := by
    simpa [prefixWord, tailWord_6004294, baseEnd_6004294] using wordTrace_append hprefix tailTrace_6004294
  have hstable : (prefixWord ++ tailWord_6004294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6004294).length < 2 ^ (prefixWord ++ tailWord_6004294).sum := by decide
  have hdescent : baseEnd_6004294 < baseStart_6004294 := by decide
  rcases family_descends (prefixWord ++ tailWord_6004294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6004330 : List Nat := [3, 1, 3, 2, 1, 2, 1, 3, 2, 2, 3]
def baseStart_6004330 : Nat := 118140960795 + 6004330 * 2 ^ 59
def prefixEnd_6004330 : Nat := 4983230072969 + 3 ^ 40 * 6004330 * 2
def baseEnd_6004330 : Nat := 3083107298210598264961595

theorem tailTrace_6004330 : CollatzResearch.WordTrace tailWord_6004330 prefixEnd_6004330 3083107298210598264961595 := by
  unfold tailWord_6004330
  simp only [CollatzResearch.WordTrace]
  refine ⟨54748976584336335692058611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145997270891563561845489629 54748976584336335692058611)
  ·
    refine ⟨82123464876504503538087917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54748976584336335692058611 82123464876504503538087917)
    ·
      refine ⟨30796299328689188826782969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82123464876504503538087917 30796299328689188826782969)
      ·
        refine ⟨23097224496516891620087227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30796299328689188826782969 23097224496516891620087227)
        ·
          refine ⟨34645836744775337430130841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23097224496516891620087227 34645836744775337430130841)
          ·
            refine ⟨25984377558581503072598131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34645836744775337430130841 25984377558581503072598131)
            ·
              refine ⟨38976566337872254608897197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25984377558581503072598131 38976566337872254608897197)
              ·
                refine ⟨14616212376702095478336449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38976566337872254608897197 14616212376702095478336449)
                ·
                  refine ⟨10962159282526571608752337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14616212376702095478336449 10962159282526571608752337)
                  ·
                    refine ⟨8221619461894928706564253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10962159282526571608752337 8221619461894928706564253)
                    ·
                      refine ⟨3083107298210598264961595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8221619461894928706564253 3083107298210598264961595)
                      ·
                        rfl

theorem cell23_6004330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_6004330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6004330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6004330 prefixEnd_6004330 := by exact prefixLift 6004330
  have htrace : WordTrace (prefixWord ++ tailWord_6004330) baseStart_6004330 baseEnd_6004330 := by
    simpa [prefixWord, tailWord_6004330, baseEnd_6004330] using wordTrace_append hprefix tailTrace_6004330
  have hstable : (prefixWord ++ tailWord_6004330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6004330).length < 2 ^ (prefixWord ++ tailWord_6004330).sum := by decide
  have hdescent : baseEnd_6004330 < baseStart_6004330 := by decide
  rcases family_descends (prefixWord ++ tailWord_6004330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6004403 : List Nat := [1, 1, 1, 2, 3, 3, 2, 3, 1, 1, 5]
def baseStart_6004403 : Nat := 118140960795 + 6004403 * 2 ^ 59
def prefixEnd_6004403 : Nat := 4983230072969 + 3 ^ 40 * 6004403 * 2
def baseEnd_6004403 : Nat := 3083144782298376479348759

theorem tailTrace_6004403 : CollatzResearch.WordTrace tailWord_6004403 prefixEnd_6004403 3083144782298376479348759 := by
  unfold tailWord_6004403
  simp only [CollatzResearch.WordTrace]
  refine ⟨218998568866080876235641863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145999045910720584157094575 218998568866080876235641863)
  ·
    refine ⟨328497853299121314353462795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218998568866080876235641863 328497853299121314353462795)
    ·
      refine ⟨492746779948681971530194193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328497853299121314353462795 492746779948681971530194193)
      ·
        refine ⟨369560084961511478647645645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 492746779948681971530194193 369560084961511478647645645)
        ·
          refine ⟨138585031860566804492867117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 369560084961511478647645645 138585031860566804492867117)
          ·
            refine ⟨51969386947712551684825169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138585031860566804492867117 51969386947712551684825169)
            ·
              refine ⟨38977040210784413763618877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51969386947712551684825169 38977040210784413763618877)
              ·
                refine ⟨14616390079044155161357079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38977040210784413763618877 14616390079044155161357079)
                ·
                  refine ⟨21924585118566232742035619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14616390079044155161357079 21924585118566232742035619)
                  ·
                    refine ⟨32886877677849349113053429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21924585118566232742035619 32886877677849349113053429)
                    ·
                      refine ⟨3083144782298376479348759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32886877677849349113053429 3083144782298376479348759)
                      ·
                        rfl

theorem cell23_6004403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 3, 1, 1, 5].length) (baseStart_6004403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6004403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6004403 prefixEnd_6004403 := by exact prefixLift 6004403
  have htrace : WordTrace (prefixWord ++ tailWord_6004403) baseStart_6004403 baseEnd_6004403 := by
    simpa [prefixWord, tailWord_6004403, baseEnd_6004403] using wordTrace_append hprefix tailTrace_6004403
  have hstable : (prefixWord ++ tailWord_6004403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6004403).length < 2 ^ (prefixWord ++ tailWord_6004403).sum := by decide
  have hdescent : baseEnd_6004403 < baseStart_6004403 := by decide
  rcases family_descends (prefixWord ++ tailWord_6004403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6004410 : List Nat := [3, 1, 1, 1, 2, 5, 1, 1, 4, 4]
def baseStart_6004410 : Nat := 118140960795 + 6004410 * 2 ^ 59
def prefixEnd_6004410 : Nat := 4983230072969 + 3 ^ 40 * 6004410 * 2
def baseEnd_6004410 : Nat := 1027716125554319317320409

theorem tailTrace_6004410 : CollatzResearch.WordTrace tailWord_6004410 prefixEnd_6004410 1027716125554319317320409 := by
  unfold tailWord_6004410
  simp only [CollatzResearch.WordTrace]
  refine ⟨54749706044263879107786671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145999216118037010954097789 54749706044263879107786671)
  ·
    refine ⟨82124559066395818661680007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54749706044263879107786671 82124559066395818661680007)
    ·
      refine ⟨123186838599593727992520011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82124559066395818661680007 123186838599593727992520011)
      ·
        refine ⟨184780257899390591988780017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123186838599593727992520011 184780257899390591988780017)
        ·
          refine ⟨138585193424542943991585013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184780257899390591988780017 138585193424542943991585013)
          ·
            refine ⟨12992361883550900999211095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 138585193424542943991585013 12992361883550900999211095)
            ·
              refine ⟨19488542825326351498816643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12992361883550900999211095 19488542825326351498816643)
              ·
                refine ⟨29232814237989527248224965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19488542825326351498816643 29232814237989527248224965)
                ·
                  refine ⟨5481152669623036359042181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29232814237989527248224965 5481152669623036359042181)
                  ·
                    refine ⟨1027716125554319317320409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5481152669623036359042181 1027716125554319317320409)
                    ·
                      rfl

theorem cell23_6004410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 4, 4].length) (baseStart_6004410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6004410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6004410 prefixEnd_6004410 := by exact prefixLift 6004410
  have htrace : WordTrace (prefixWord ++ tailWord_6004410) baseStart_6004410 baseEnd_6004410 := by
    simpa [prefixWord, tailWord_6004410, baseEnd_6004410] using wordTrace_append hprefix tailTrace_6004410
  have hstable : (prefixWord ++ tailWord_6004410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6004410).length < 2 ^ (prefixWord ++ tailWord_6004410).sum := by decide
  have hdescent : baseEnd_6004410 < baseStart_6004410 := by decide
  rcases family_descends (prefixWord ++ tailWord_6004410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6004413 : List Nat := [1, 4, 1, 2, 1, 2, 2, 2, 1, 1, 6]
def baseStart_6004413 : Nat := 118140960795 + 6004413 * 2 ^ 59
def prefixEnd_6004413 : Nat := 4983230072969 + 3 ^ 40 * 6004413 * 2
def baseEnd_6004413 : Nat := 3083149917104921440223713

theorem tailTrace_6004413 : CollatzResearch.WordTrace tailWord_6004413 prefixEnd_6004413 3083149917104921440223713 := by
  unfold tailWord_6004413
  simp only [CollatzResearch.WordTrace]
  refine ⟨218998933596044647943505893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145999289064029765295670595 218998933596044647943505893)
  ·
    refine ⟨41062300049258371489407355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 218998933596044647943505893 41062300049258371489407355)
    ·
      refine ⟨61593450073887557234111033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41062300049258371489407355 61593450073887557234111033)
      ·
        refine ⟨46195087555415667925583275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61593450073887557234111033 46195087555415667925583275)
        ·
          refine ⟨69292631333123501888374913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46195087555415667925583275 69292631333123501888374913)
          ·
            refine ⟨51969473499842626416281185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69292631333123501888374913 51969473499842626416281185)
            ·
              refine ⟨38977105124881969812210889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51969473499842626416281185 38977105124881969812210889)
              ·
                refine ⟨29232828843661477359158167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38977105124881969812210889 29232828843661477359158167)
                ·
                  refine ⟨43849243265492216038737251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29232828843661477359158167 43849243265492216038737251)
                  ·
                    refine ⟨65773864898238324058105877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43849243265492216038737251 65773864898238324058105877)
                    ·
                      refine ⟨3083149917104921440223713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65773864898238324058105877 3083149917104921440223713)
                      ·
                        rfl

theorem cell23_6004413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_6004413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6004413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6004413 prefixEnd_6004413 := by exact prefixLift 6004413
  have htrace : WordTrace (prefixWord ++ tailWord_6004413) baseStart_6004413 baseEnd_6004413 := by
    simpa [prefixWord, tailWord_6004413, baseEnd_6004413] using wordTrace_append hprefix tailTrace_6004413
  have hstable : (prefixWord ++ tailWord_6004413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6004413).length < 2 ^ (prefixWord ++ tailWord_6004413).sum := by decide
  have hdescent : baseEnd_6004413 < baseStart_6004413 := by decide
  rcases family_descends (prefixWord ++ tailWord_6004413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6004420 : List Nat := [2, 3, 3, 1, 1, 1, 3, 2, 1, 1, 5]
def baseStart_6004420 : Nat := 118140960795 + 6004420 * 2 ^ 59
def prefixEnd_6004420 : Nat := 4983230072969 + 3 ^ 40 * 6004420 * 2
def baseEnd_6004420 : Nat := 3083153511469502912836181

theorem tailTrace_6004420 : CollatzResearch.WordTrace tailWord_6004420 prefixEnd_6004420 3083153511469502912836181 := by
  unfold tailWord_6004420
  simp only [CollatzResearch.WordTrace]
  refine ⟨109499594453509644069505357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145999459271346192092673809 109499594453509644069505357)
  ·
    refine ⟨41062347920066116526064509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109499594453509644069505357 41062347920066116526064509)
    ·
      refine ⟨15398380470024793697274191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41062347920066116526064509 15398380470024793697274191)
      ·
        refine ⟨23097570705037190545911287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15398380470024793697274191 23097570705037190545911287)
        ·
          refine ⟨34646356057555785818866931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23097570705037190545911287 34646356057555785818866931)
          ·
            refine ⟨51969534086333678728300397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34646356057555785818866931 51969534086333678728300397)
            ·
              refine ⟨19488575282375129523112649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51969534086333678728300397 19488575282375129523112649)
              ·
                refine ⟨14616431461781347142334487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19488575282375129523112649 14616431461781347142334487)
                ·
                  refine ⟨21924647192672020713501731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14616431461781347142334487 21924647192672020713501731)
                  ·
                    refine ⟨32886970789008031070252597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21924647192672020713501731 32886970789008031070252597)
                    ·
                      refine ⟨3083153511469502912836181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32886970789008031070252597 3083153511469502912836181)
                      ·
                        rfl

theorem cell23_6004420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_6004420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6004420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6004420 prefixEnd_6004420 := by exact prefixLift 6004420
  have htrace : WordTrace (prefixWord ++ tailWord_6004420) baseStart_6004420 baseEnd_6004420 := by
    simpa [prefixWord, tailWord_6004420, baseEnd_6004420] using wordTrace_append hprefix tailTrace_6004420
  have hstable : (prefixWord ++ tailWord_6004420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6004420).length < 2 ^ (prefixWord ++ tailWord_6004420).sum := by decide
  have hdescent : baseEnd_6004420 < baseStart_6004420 := by decide
  rcases family_descends (prefixWord ++ tailWord_6004420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6004434 : List Nat := [3, 2, 2, 2, 2, 1, 2, 2, 3, 2, 2]
def baseStart_6004434 : Nat := 118140960795 + 6004434 * 2 ^ 59
def prefixEnd_6004434 : Nat := 4983230072969 + 3 ^ 40 * 6004434 * 2
def baseEnd_6004434 : Nat := 3083160700198665858061117

theorem tailTrace_6004434 : CollatzResearch.WordTrace tailWord_6004434 prefixEnd_6004434 3083160700198665858061117 := by
  unfold tailWord_6004434
  simp only [CollatzResearch.WordTrace]
  refine ⟨54749924882242142132505089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145999799685979045686680237 54749924882242142132505089)
  ·
    refine ⟨41062443661681606599378817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54749924882242142132505089 41062443661681606599378817)
    ·
      refine ⟨30796832746261204949534113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41062443661681606599378817 30796832746261204949534113)
      ·
        refine ⟨23097624559695903712150585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30796832746261204949534113 23097624559695903712150585)
        ·
          refine ⟨17323218419771927784112939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23097624559695903712150585 17323218419771927784112939)
          ·
            refine ⟨25984827629657891676169409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17323218419771927784112939 25984827629657891676169409)
            ·
              refine ⟨19488620722243418757127057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25984827629657891676169409 19488620722243418757127057)
              ·
                refine ⟨14616465541682564067845293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19488620722243418757127057 14616465541682564067845293)
                ·
                  refine ⟨5481174578130961525441985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14616465541682564067845293 5481174578130961525441985)
                  ·
                    refine ⟨4110880933598221144081489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5481174578130961525441985 4110880933598221144081489)
                    ·
                      refine ⟨3083160700198665858061117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4110880933598221144081489 3083160700198665858061117)
                      ·
                        rfl

theorem cell23_6004434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 2, 3, 2, 2].length) (baseStart_6004434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6004434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6004434 prefixEnd_6004434 := by exact prefixLift 6004434
  have htrace : WordTrace (prefixWord ++ tailWord_6004434) baseStart_6004434 baseEnd_6004434 := by
    simpa [prefixWord, tailWord_6004434, baseEnd_6004434] using wordTrace_append hprefix tailTrace_6004434
  have hstable : (prefixWord ++ tailWord_6004434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6004434).length < 2 ^ (prefixWord ++ tailWord_6004434).sum := by decide
  have hdescent : baseEnd_6004434 < baseStart_6004434 := by decide
  rcases family_descends (prefixWord ++ tailWord_6004434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6004445 : List Nat := [1, 4, 3, 3, 2, 1, 1, 3, 1, 1, 3]
def baseStart_6004445 : Nat := 118140960795 + 6004445 * 2 ^ 59
def prefixEnd_6004445 : Nat := 4983230072969 + 3 ^ 40 * 6004445 * 2
def baseEnd_6004445 : Nat := 3083166348485865315023567

theorem tailTrace_6004445 : CollatzResearch.WordTrace tailWord_6004445 prefixEnd_6004445 3083166348485865315023567 := by
  unfold tailWord_6004445
  simp only [CollatzResearch.WordTrace]
  refine ⟨219000100731928717408670789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146000067154619144939113859 219000100731928717408670789)
  ·
    refine ⟨41062518887236634514125773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 219000100731928717408670789 41062518887236634514125773)
    ·
      refine ⟨15398444582713737942797165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41062518887236634514125773 15398444582713737942797165)
      ·
        refine ⟨5774416718517651728548937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15398444582713737942797165 5774416718517651728548937)
        ·
          refine ⟨4330812538888238796411703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5774416718517651728548937 4330812538888238796411703)
          ·
            refine ⟨6496218808332358194617555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4330812538888238796411703 6496218808332358194617555)
            ·
              refine ⟨9744328212498537291926333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6496218808332358194617555 9744328212498537291926333)
              ·
                refine ⟨3654123079686951484472375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9744328212498537291926333 3654123079686951484472375)
                ·
                  refine ⟨5481184619530427226708563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3654123079686951484472375 5481184619530427226708563)
                  ·
                    refine ⟨8221776929295640840062845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5481184619530427226708563 8221776929295640840062845)
                    ·
                      refine ⟨3083166348485865315023567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8221776929295640840062845 3083166348485865315023567)
                      ·
                        rfl

theorem cell23_6004445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_6004445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6004445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6004445 prefixEnd_6004445 := by exact prefixLift 6004445
  have htrace : WordTrace (prefixWord ++ tailWord_6004445) baseStart_6004445 baseEnd_6004445 := by
    simpa [prefixWord, tailWord_6004445, baseEnd_6004445] using wordTrace_append hprefix tailTrace_6004445
  have hstable : (prefixWord ++ tailWord_6004445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6004445).length < 2 ^ (prefixWord ++ tailWord_6004445).sum := by decide
  have hdescent : baseEnd_6004445 < baseStart_6004445 := by decide
  rcases family_descends (prefixWord ++ tailWord_6004445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6004463 : List Nat := [1, 1, 2, 1, 5, 1, 1, 2, 2, 2, 5]
def baseStart_6004463 : Nat := 118140960795 + 6004463 * 2 ^ 59
def prefixEnd_6004463 : Nat := 4983230072969 + 3 ^ 40 * 6004463 * 2
def baseEnd_6004463 : Nat := 3083175591137646244598483

theorem tailTrace_6004463 : CollatzResearch.WordTrace tailWord_6004463 prefixEnd_6004463 3083175591137646244598483 := by
  unfold tailWord_6004463
  simp only [CollatzResearch.WordTrace]
  refine ⟨219000757245863506482826043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146000504830575670988550695 219000757245863506482826043)
  ·
    refine ⟨328501135868795259724239065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219000757245863506482826043 328501135868795259724239065)
    ·
      refine ⟨246375851901596444793179299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 328501135868795259724239065 246375851901596444793179299)
      ·
        refine ⟨369563777852394667189768949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246375851901596444793179299 369563777852394667189768949)
        ·
          refine ⟨34646604173662000049040839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 369563777852394667189768949 34646604173662000049040839)
          ·
            refine ⟨51969906260493000073561259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34646604173662000049040839 51969906260493000073561259)
            ·
              refine ⟨77954859390739500110341889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51969906260493000073561259 77954859390739500110341889)
              ·
                refine ⟨58466144543054625082756417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77954859390739500110341889 58466144543054625082756417)
                ·
                  refine ⟨43849608407290968812067313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58466144543054625082756417 43849608407290968812067313)
                  ·
                    refine ⟨32887206305468226609050485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43849608407290968812067313 32887206305468226609050485)
                    ·
                      refine ⟨3083175591137646244598483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32887206305468226609050485 3083175591137646244598483)
                      ·
                        rfl

theorem cell23_6004463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 2, 5].length) (baseStart_6004463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6004463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6004463 prefixEnd_6004463 := by exact prefixLift 6004463
  have htrace : WordTrace (prefixWord ++ tailWord_6004463) baseStart_6004463 baseEnd_6004463 := by
    simpa [prefixWord, tailWord_6004463, baseEnd_6004463] using wordTrace_append hprefix tailTrace_6004463
  have hstable : (prefixWord ++ tailWord_6004463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6004463).length < 2 ^ (prefixWord ++ tailWord_6004463).sum := by decide
  have hdescent : baseEnd_6004463 < baseStart_6004463 := by decide
  rcases family_descends (prefixWord ++ tailWord_6004463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6004468 : List Nat := [2, 6, 1, 1, 1, 1, 3, 1, 3, 2, 2]
def baseStart_6004468 : Nat := 118140960795 + 6004468 * 2 ^ 59
def prefixEnd_6004468 : Nat := 4983230072969 + 3 ^ 40 * 6004468 * 2
def baseEnd_6004468 : Nat := 3083178158540918725035961

theorem tailTrace_6004468 : CollatzResearch.WordTrace tailWord_6004468 prefixEnd_6004468 3083178158540918725035961 := by
  unfold tailWord_6004468
  simp only [CollatzResearch.WordTrace]
  refine ⟨109500469805422696168379029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146000626407230261557838705 109500469805422696168379029)
  ·
    refine ⟨5132834522129188882892767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 109500469805422696168379029 5132834522129188882892767)
    ·
      refine ⟨7699251783193783324339151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5132834522129188882892767 7699251783193783324339151)
      ·
        refine ⟨11548877674790674986508727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7699251783193783324339151 11548877674790674986508727)
        ·
          refine ⟨17323316512186012479763091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11548877674790674986508727 17323316512186012479763091)
          ·
            refine ⟨25984974768279018719644637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17323316512186012479763091 25984974768279018719644637)
            ·
              refine ⟨9744365538104632019866739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25984974768279018719644637 9744365538104632019866739)
              ·
                refine ⟨14616548307156948029800109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9744365538104632019866739 14616548307156948029800109)
                ·
                  refine ⟨5481205615183855511175041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14616548307156948029800109 5481205615183855511175041)
                  ·
                    refine ⟨4110904211387891633381281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5481205615183855511175041 4110904211387891633381281)
                    ·
                      refine ⟨3083178158540918725035961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4110904211387891633381281 3083178158540918725035961)
                      ·
                        rfl

theorem cell23_6004468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_6004468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6004468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6004468 prefixEnd_6004468 := by exact prefixLift 6004468
  have htrace : WordTrace (prefixWord ++ tailWord_6004468) baseStart_6004468 baseEnd_6004468 := by
    simpa [prefixWord, tailWord_6004468, baseEnd_6004468] using wordTrace_append hprefix tailTrace_6004468
  have hstable : (prefixWord ++ tailWord_6004468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6004468).length < 2 ^ (prefixWord ++ tailWord_6004468).sum := by decide
  have hdescent : baseEnd_6004468 < baseStart_6004468 := by decide
  rcases family_descends (prefixWord ++ tailWord_6004468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6004478 : List Nat := [4, 2, 2, 1, 4, 1, 2, 1, 2, 4]
def baseStart_6004478 : Nat := 118140960795 + 6004478 * 2 ^ 59
def prefixEnd_6004478 : Nat := 4983230072969 + 3 ^ 40 * 6004478 * 2
def baseEnd_6004478 : Nat := 1027727764449154561970305

theorem tailTrace_6004478 : CollatzResearch.WordTrace tailWord_6004478 prefixEnd_6004478 1027727764449154561970305 := by
  unfold tailWord_6004478
  simp only [CollatzResearch.WordTrace]
  refine ⟨27375163042601145505577761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146000869560539442696414725 27375163042601145505577761)
  ·
    refine ⟨20531372281950859129183321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27375163042601145505577761 20531372281950859129183321)
    ·
      refine ⟨15398529211463144346887491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20531372281950859129183321 15398529211463144346887491)
      ·
        refine ⟨23097793817194716520331237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15398529211463144346887491 23097793817194716520331237)
        ·
          refine ⟨4330836340724009347562107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23097793817194716520331237 4330836340724009347562107)
          ·
            refine ⟨6496254511086014021343161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4330836340724009347562107 6496254511086014021343161)
            ·
              refine ⟨4872190883314510516007371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6496254511086014021343161 4872190883314510516007371)
              ·
                refine ⟨7308286324971765774011057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4872190883314510516007371 7308286324971765774011057)
                ·
                  refine ⟨5481214743728824330508293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7308286324971765774011057 5481214743728824330508293)
                  ·
                    refine ⟨1027727764449154561970305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5481214743728824330508293 1027727764449154561970305)
                    ·
                      rfl

theorem cell23_6004478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_6004478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6004478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6004478 prefixEnd_6004478 := by exact prefixLift 6004478
  have htrace : WordTrace (prefixWord ++ tailWord_6004478) baseStart_6004478 baseEnd_6004478 := by
    simpa [prefixWord, tailWord_6004478, baseEnd_6004478] using wordTrace_append hprefix tailTrace_6004478
  have hstable : (prefixWord ++ tailWord_6004478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6004478).length < 2 ^ (prefixWord ++ tailWord_6004478).sum := by decide
  have hdescent : baseEnd_6004478 < baseStart_6004478 := by decide
  rcases family_descends (prefixWord ++ tailWord_6004478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6004483 : List Nat := [1, 1, 1, 3, 2, 2, 2, 3, 2, 6]
def baseStart_6004483 : Nat := 118140960795 + 6004483 * 2 ^ 59
def prefixEnd_6004483 : Nat := 4983230072969 + 3 ^ 40 * 6004483 * 2
def baseEnd_6004483 : Nat := 1027728620250245388782797

theorem tailTrace_6004483 : CollatzResearch.WordTrace tailWord_6004483 prefixEnd_6004483 1027728620250245388782797 := by
  unfold tailWord_6004483
  simp only [CollatzResearch.WordTrace]
  refine ⟨219001486705791049898554103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146000991137194033265702735 219001486705791049898554103)
  ·
    refine ⟨328502230058686574847831155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219001486705791049898554103 328502230058686574847831155)
    ·
      refine ⟨492753345088029862271746733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328502230058686574847831155 492753345088029862271746733)
      ·
        refine ⟨184782504408011198351905025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 492753345088029862271746733 184782504408011198351905025)
        ·
          refine ⟨138586878306008398763928769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184782504408011198351905025 138586878306008398763928769)
          ·
            refine ⟨103940158729506299072946577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138586878306008398763928769 103940158729506299072946577)
            ·
              refine ⟨77955119047129724304709933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103940158729506299072946577 77955119047129724304709933)
              ·
                refine ⟨29233169642673646614266225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77955119047129724304709933 29233169642673646614266225)
                ·
                  refine ⟨21924877232005234960699669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29233169642673646614266225 21924877232005234960699669)
                  ·
                    refine ⟨1027728620250245388782797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21924877232005234960699669 1027728620250245388782797)
                    ·
                      rfl

theorem cell23_6004483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 2, 6].length) (baseStart_6004483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6004483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6004483 prefixEnd_6004483 := by exact prefixLift 6004483
  have htrace : WordTrace (prefixWord ++ tailWord_6004483) baseStart_6004483 baseEnd_6004483 := by
    simpa [prefixWord, tailWord_6004483, baseEnd_6004483] using wordTrace_append hprefix tailTrace_6004483
  have hstable : (prefixWord ++ tailWord_6004483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6004483).length < 2 ^ (prefixWord ++ tailWord_6004483).sum := by decide
  have hdescent : baseEnd_6004483 < baseStart_6004483 := by decide
  rcases family_descends (prefixWord ++ tailWord_6004483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6004484 : List Nat := [2, 3, 2, 2, 1, 3, 1, 3, 2, 1, 3]
def baseStart_6004484 : Nat := 118140960795 + 6004484 * 2 ^ 59
def prefixEnd_6004484 : Nat := 4983230072969 + 3 ^ 40 * 6004484 * 2
def baseEnd_6004484 : Nat := 3083186374231390662435887

theorem tailTrace_6004484 : CollatzResearch.WordTrace tailWord_6004484 prefixEnd_6004484 3083186374231390662435887 := by
  unfold tailWord_6004484
  simp only [CollatzResearch.WordTrace]
  refine ⟨109500761589393713534670253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146001015452524951379560337 109500761589393713534670253)
  ·
    refine ⟨41062785596022642575501345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109500761589393713534670253 41062785596022642575501345)
    ·
      refine ⟨30797089197016981931626009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41062785596022642575501345 30797089197016981931626009)
      ·
        refine ⟨23097816897762736448719507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30797089197016981931626009 23097816897762736448719507)
        ·
          refine ⟨34646725346644104673079261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23097816897762736448719507 34646725346644104673079261)
          ·
            refine ⟨12992522004991539252404723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34646725346644104673079261 12992522004991539252404723)
            ·
              refine ⟨19488783007487308878607085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12992522004991539252404723 19488783007487308878607085)
              ·
                refine ⟨7308293627807740829477657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19488783007487308878607085 7308293627807740829477657)
                ·
                  refine ⟨5481220220855805622108243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7308293627807740829477657 5481220220855805622108243)
                  ·
                    refine ⟨8221830331283708433162365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5481220220855805622108243 8221830331283708433162365)
                    ·
                      refine ⟨3083186374231390662435887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8221830331283708433162365 3083186374231390662435887)
                      ·
                        rfl

theorem cell23_6004484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_6004484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6004484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6004484 prefixEnd_6004484 := by exact prefixLift 6004484
  have htrace : WordTrace (prefixWord ++ tailWord_6004484) baseStart_6004484 baseEnd_6004484 := by
    simpa [prefixWord, tailWord_6004484, baseEnd_6004484] using wordTrace_append hprefix tailTrace_6004484
  have hstable : (prefixWord ++ tailWord_6004484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6004484).length < 2 ^ (prefixWord ++ tailWord_6004484).sum := by decide
  have hdescent : baseEnd_6004484 < baseStart_6004484 := by decide
  rcases family_descends (prefixWord ++ tailWord_6004484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6004494 : List Nat := [4, 1, 1, 2, 1, 1, 5, 2, 1, 3, 2]
def baseStart_6004494 : Nat := 118140960795 + 6004494 * 2 ^ 59
def prefixEnd_6004494 : Nat := 4983230072969 + 3 ^ 40 * 6004494 * 2
def baseEnd_6004494 : Nat := 3083191509037935623310841

theorem tailTrace_6004494 : CollatzResearch.WordTrace tailWord_6004494 prefixEnd_6004494 3083191509037935623310841 := by
  unfold tailWord_6004494
  simp only [CollatzResearch.WordTrace]
  refine ⟨27375235988593899847150567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146001258605834132518136357 27375235988593899847150567)
  ·
    refine ⟨41062853982890849770725851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27375235988593899847150567 41062853982890849770725851)
    ·
      refine ⟨61594280974336274656088777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41062853982890849770725851 61594280974336274656088777)
      ·
        refine ⟨46195710730752205992066583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61594280974336274656088777 46195710730752205992066583)
        ·
          refine ⟨69293566096128308988099875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46195710730752205992066583 69293566096128308988099875)
          ·
            refine ⟨103940349144192463482149813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69293566096128308988099875 103940349144192463482149813)
            ·
              refine ⟨9744407732268043451451545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 103940349144192463482149813 9744407732268043451451545)
              ·
                refine ⟨7308305799201032588588659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9744407732268043451451545 7308305799201032588588659)
                ·
                  refine ⟨10962458698801548882882989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7308305799201032588588659 10962458698801548882882989)
                  ·
                    refine ⟨4110922012050580831081121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10962458698801548882882989 4110922012050580831081121)
                    ·
                      refine ⟨3083191509037935623310841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4110922012050580831081121 3083191509037935623310841)
                      ·
                        rfl

theorem cell23_6004494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 2, 1, 3, 2].length) (baseStart_6004494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6004494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6004494 prefixEnd_6004494 := by exact prefixLift 6004494
  have htrace : WordTrace (prefixWord ++ tailWord_6004494) baseStart_6004494 baseEnd_6004494 := by
    simpa [prefixWord, tailWord_6004494, baseEnd_6004494] using wordTrace_append hprefix tailTrace_6004494
  have hstable : (prefixWord ++ tailWord_6004494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6004494).length < 2 ^ (prefixWord ++ tailWord_6004494).sum := by decide
  have hdescent : baseEnd_6004494 < baseStart_6004494 := by decide
  rcases family_descends (prefixWord ++ tailWord_6004494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6004524 : List Nat := [2, 2, 1, 1, 1, 5, 1, 4, 2, 2, 2]
def baseStart_6004524 : Nat := 118140960795 + 6004524 * 2 ^ 59
def prefixEnd_6004524 : Nat := 4983230072969 + 3 ^ 40 * 6004524 * 2
def baseEnd_6004524 : Nat := 3083206913457570505935703

theorem tailTrace_6004524 : CollatzResearch.WordTrace tailWord_6004524 prefixEnd_6004524 3083206913457570505935703 := by
  unfold tailWord_6004524
  simp only [CollatzResearch.WordTrace]
  refine ⟨109501491049321256950398313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146001988065761675933864417 109501491049321256950398313)
  ·
    refine ⟨82126118286990942712798735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109501491049321256950398313 82126118286990942712798735)
    ·
      refine ⟨123189177430486414069198103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82126118286990942712798735 123189177430486414069198103)
      ·
        refine ⟨184783766145729621103797155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123189177430486414069198103 184783766145729621103797155)
        ·
          refine ⟨277175649218594431655695733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184783766145729621103797155 277175649218594431655695733)
          ·
            refine ⟨25985217114243227967721475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 277175649218594431655695733 25985217114243227967721475)
            ·
              refine ⟨38977825671364841951582213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25985217114243227967721475 38977825671364841951582213)
              ·
                refine ⟨7308342313380907865921665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38977825671364841951582213 7308342313380907865921665)
                ·
                  refine ⟨5481256735035680899441249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7308342313380907865921665 5481256735035680899441249)
                  ·
                    refine ⟨4110942551276760674580937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5481256735035680899441249 4110942551276760674580937)
                    ·
                      refine ⟨3083206913457570505935703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4110942551276760674580937 3083206913457570505935703)
                      ·
                        rfl

theorem cell23_6004524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 2, 2].length) (baseStart_6004524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6004524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6004524 prefixEnd_6004524 := by exact prefixLift 6004524
  have htrace : WordTrace (prefixWord ++ tailWord_6004524) baseStart_6004524 baseEnd_6004524 := by
    simpa [prefixWord, tailWord_6004524, baseEnd_6004524] using wordTrace_append hprefix tailTrace_6004524
  have hstable : (prefixWord ++ tailWord_6004524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6004524).length < 2 ^ (prefixWord ++ tailWord_6004524).sum := by decide
  have hdescent : baseEnd_6004524 < baseStart_6004524 := by decide
  rcases family_descends (prefixWord ++ tailWord_6004524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6004540 : List Nat := [2, 2, 2, 2, 1, 1, 3, 1, 1, 5, 3]
def baseStart_6004540 : Nat := 118140960795 + 6004540 * 2 ^ 59
def prefixEnd_6004540 : Nat := 4983230072969 + 3 ^ 40 * 6004540 * 2
def baseEnd_6004540 : Nat := 3083215129148042443335629

theorem tailTrace_6004540 : CollatzResearch.WordTrace tailWord_6004540 prefixEnd_6004540 3083215129148042443335629 := by
  unfold tailWord_6004540
  simp only [CollatzResearch.WordTrace]
  refine ⟨109501782833292274316689537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146002377111056365755586049 109501782833292274316689537)
  ·
    refine ⟨82126337124969205737517153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109501782833292274316689537 82126337124969205737517153)
    ·
      refine ⟨61594752843726904303137865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82126337124969205737517153 61594752843726904303137865)
      ·
        refine ⟨46196064632795178227353399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61594752843726904303137865 46196064632795178227353399)
        ·
          refine ⟨69294096949192767341030099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46196064632795178227353399 69294096949192767341030099)
          ·
            refine ⟨103941145423789151011545149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69294096949192767341030099 103941145423789151011545149)
            ·
              refine ⟨38977929533920931629329431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103941145423789151011545149 38977929533920931629329431)
              ·
                refine ⟨58466894300881397443994147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38977929533920931629329431 58466894300881397443994147)
                ·
                  refine ⟨87700341451322096165991221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58466894300881397443994147 87700341451322096165991221)
                  ·
                    refine ⟨8221907011061446515561677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 87700341451322096165991221 8221907011061446515561677)
                    ·
                      refine ⟨3083215129148042443335629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8221907011061446515561677 3083215129148042443335629)
                      ·
                        rfl

theorem cell23_6004540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 1, 5, 3].length) (baseStart_6004540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6004540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6004540 prefixEnd_6004540 := by exact prefixLift 6004540
  have htrace : WordTrace (prefixWord ++ tailWord_6004540) baseStart_6004540 baseEnd_6004540 := by
    simpa [prefixWord, tailWord_6004540, baseEnd_6004540] using wordTrace_append hprefix tailTrace_6004540
  have hstable : (prefixWord ++ tailWord_6004540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6004540).length < 2 ^ (prefixWord ++ tailWord_6004540).sum := by decide
  have hdescent : baseEnd_6004540 < baseStart_6004540 := by decide
  rcases family_descends (prefixWord ++ tailWord_6004540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6004541 : List Nat := [1, 4, 1, 4, 1, 1, 2, 3, 2, 2, 2]
def baseStart_6004541 : Nat := 118140960795 + 6004541 * 2 ^ 59
def prefixEnd_6004541 : Nat := 4983230072969 + 3 ^ 40 * 6004541 * 2
def baseEnd_6004541 : Nat := 3083215642628696939423125

theorem tailTrace_6004541 : CollatzResearch.WordTrace tailWord_6004541 prefixEnd_6004541 3083215642628696939423125 := by
  unfold tailWord_6004541
  simp only [CollatzResearch.WordTrace]
  refine ⟨219003602139580925804165477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146002401426387283869443651 219003602139580925804165477)
  ·
    refine ⟨41063175401171423588281027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 219003602139580925804165477 41063175401171423588281027)
    ·
      refine ⟨61594763101757135382421541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41063175401171423588281027 61594763101757135382421541)
      ·
        refine ⟨11549018081579462884204039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61594763101757135382421541 11549018081579462884204039)
        ·
          refine ⟨17323527122369194326306059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11549018081579462884204039 17323527122369194326306059)
          ·
            refine ⟨25985290683553791489459089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17323527122369194326306059 25985290683553791489459089)
            ·
              refine ⟨19488968012665343617094317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25985290683553791489459089 19488968012665343617094317)
              ·
                refine ⟨7308363004749503856410369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19488968012665343617094317 7308363004749503856410369)
                ·
                  refine ⟨5481272253562127892307777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7308363004749503856410369 5481272253562127892307777)
                  ·
                    refine ⟨4110954190171595919230833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5481272253562127892307777 4110954190171595919230833)
                    ·
                      refine ⟨3083215642628696939423125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4110954190171595919230833 3083215642628696939423125)
                      ·
                        rfl

theorem cell23_6004541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_6004541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6004541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6004541 prefixEnd_6004541 := by exact prefixLift 6004541
  have htrace : WordTrace (prefixWord ++ tailWord_6004541) baseStart_6004541 baseEnd_6004541 := by
    simpa [prefixWord, tailWord_6004541, baseEnd_6004541] using wordTrace_append hprefix tailTrace_6004541
  have hstable : (prefixWord ++ tailWord_6004541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6004541).length < 2 ^ (prefixWord ++ tailWord_6004541).sum := by decide
  have hdescent : baseEnd_6004541 < baseStart_6004541 := by decide
  rcases family_descends (prefixWord ++ tailWord_6004541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6004564 : List Nat := [2, 4, 1, 1, 3, 2, 2, 3, 5]
def baseStart_6004564 : Nat := 118140960795 + 6004564 * 2 ^ 59
def prefixEnd_6004564 : Nat := 4983230072969 + 3 ^ 40 * 6004564 * 2
def baseEnd_6004564 : Nat := 342580828075972261048391

theorem tailTrace_6004564 : CollatzResearch.WordTrace tailWord_6004564 prefixEnd_6004564 342580828075972261048391 := by
  unfold tailWord_6004564
  simp only [CollatzResearch.WordTrace]
  refine ⟨109502220509248800366126373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146002960678998400488168497 109502220509248800366126373)
  ·
    refine ⟨20531666345484150068648695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109502220509248800366126373 20531666345484150068648695)
    ·
      refine ⟨30797499518226225102973043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20531666345484150068648695 30797499518226225102973043)
      ·
        refine ⟨46196249277339337654459565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30797499518226225102973043 46196249277339337654459565)
        ·
          refine ⟨17323593479002251620422337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46196249277339337654459565 17323593479002251620422337)
          ·
            refine ⟨12992695109251688715316753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17323593479002251620422337 12992695109251688715316753)
            ·
              refine ⟨9744521331938766536487565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12992695109251688715316753 9744521331938766536487565)
              ·
                refine ⟨3654195499477037451182837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9744521331938766536487565 3654195499477037451182837)
                ·
                  refine ⟨342580828075972261048391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3654195499477037451182837 342580828075972261048391)
                  ·
                    rfl

theorem cell23_6004564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 3, 5].length) (baseStart_6004564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6004564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6004564 prefixEnd_6004564 := by exact prefixLift 6004564
  have htrace : WordTrace (prefixWord ++ tailWord_6004564) baseStart_6004564 baseEnd_6004564 := by
    simpa [prefixWord, tailWord_6004564, baseEnd_6004564] using wordTrace_append hprefix tailTrace_6004564
  have hstable : (prefixWord ++ tailWord_6004564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6004564).length < 2 ^ (prefixWord ++ tailWord_6004564).sum := by decide
  have hdescent : baseEnd_6004564 < baseStart_6004564 := by decide
  rcases family_descends (prefixWord ++ tailWord_6004564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6004617 : List Nat := [1, 2, 1, 1, 5, 1, 2, 3, 2, 2, 3]
def baseStart_6004617 : Nat := 118140960795 + 6004617 * 2 ^ 59
def prefixEnd_6004617 : Nat := 4983230072969 + 3 ^ 40 * 6004617 * 2
def baseEnd_6004617 : Nat := 3083254667158438642072775

theorem tailTrace_6004617 : CollatzResearch.WordTrace tailWord_6004617 prefixEnd_6004617 3083254667158438642072775 := by
  unfold tailWord_6004617
  simp only [CollatzResearch.WordTrace]
  refine ⟨219006374087305590783932105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146004249391537060522621403 219006374087305590783932105)
  ·
    refine ⟨164254780565479193087949079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219006374087305590783932105 164254780565479193087949079)
    ·
      refine ⟨246382170848218789631923619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164254780565479193087949079 246382170848218789631923619)
      ·
        refine ⟨369573256272328184447885429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246382170848218789631923619 369573256272328184447885429)
        ·
          refine ⟨34647492775530767291989259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 369573256272328184447885429 34647492775530767291989259)
          ·
            refine ⟨51971239163296150937983889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34647492775530767291989259 51971239163296150937983889)
            ·
              refine ⟨38978429372472113203487917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51971239163296150937983889 38978429372472113203487917)
              ·
                refine ⟨14616911014677042451307969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38978429372472113203487917 14616911014677042451307969)
                ·
                  refine ⟨10962683261007781838480977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14616911014677042451307969 10962683261007781838480977)
                  ·
                    refine ⟨8222012445755836378860733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10962683261007781838480977 8222012445755836378860733)
                    ·
                      refine ⟨3083254667158438642072775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8222012445755836378860733 3083254667158438642072775)
                      ·
                        rfl

theorem cell23_6004617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 3, 2, 2, 3].length) (baseStart_6004617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6004617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6004617 prefixEnd_6004617 := by exact prefixLift 6004617
  have htrace : WordTrace (prefixWord ++ tailWord_6004617) baseStart_6004617 baseEnd_6004617 := by
    simpa [prefixWord, tailWord_6004617, baseEnd_6004617] using wordTrace_append hprefix tailTrace_6004617
  have hstable : (prefixWord ++ tailWord_6004617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6004617).length < 2 ^ (prefixWord ++ tailWord_6004617).sum := by decide
  have hdescent : baseEnd_6004617 < baseStart_6004617 := by decide
  rcases family_descends (prefixWord ++ tailWord_6004617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6004634 : List Nat := [3, 1, 1, 4, 2, 2, 1, 2, 2, 2, 3]
def baseStart_6004634 : Nat := 118140960795 + 6004634 * 2 ^ 59
def prefixEnd_6004634 : Nat := 4983230072969 + 3 ^ 40 * 6004634 * 2
def baseEnd_6004634 : Nat := 3083263396329565075560197

theorem tailTrace_6004634 : CollatzResearch.WordTrace tailWord_6004634 prefixEnd_6004634 3083263396329565075560197 := by
  unfold tailWord_6004634
  simp only [CollatzResearch.WordTrace]
  refine ⟨54751748532061000671825239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146004662752162668458200637 54751748532061000671825239)
  ·
    refine ⟨82127622798091501007737859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54751748532061000671825239 82127622798091501007737859)
    ·
      refine ⟨123191434197137251511606789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82127622798091501007737859 123191434197137251511606789)
      ·
        refine ⟨23098393911963234658426273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123191434197137251511606789 23098393911963234658426273)
        ·
          refine ⟨17323795433972425993819705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23098393911963234658426273 17323795433972425993819705)
          ·
            refine ⟨12992846575479319495364779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17323795433972425993819705 12992846575479319495364779)
            ·
              refine ⟨19489269863218979243047169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12992846575479319495364779 19489269863218979243047169)
              ·
                refine ⟨14616952397414234432285377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19489269863218979243047169 14616952397414234432285377)
                ·
                  refine ⟨10962714298060675824214033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14616952397414234432285377 10962714298060675824214033)
                  ·
                    refine ⟨8222035723545506868160525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10962714298060675824214033 8222035723545506868160525)
                    ·
                      refine ⟨3083263396329565075560197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8222035723545506868160525 3083263396329565075560197)
                      ·
                        rfl

theorem cell23_6004634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_6004634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6004634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6004634 prefixEnd_6004634 := by exact prefixLift 6004634
  have htrace : WordTrace (prefixWord ++ tailWord_6004634) baseStart_6004634 baseEnd_6004634 := by
    simpa [prefixWord, tailWord_6004634, baseEnd_6004634] using wordTrace_append hprefix tailTrace_6004634
  have hstable : (prefixWord ++ tailWord_6004634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6004634).length < 2 ^ (prefixWord ++ tailWord_6004634).sum := by decide
  have hdescent : baseEnd_6004634 < baseStart_6004634 := by decide
  rcases family_descends (prefixWord ++ tailWord_6004634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6004641 : List Nat := [1, 2, 3, 4, 2, 2, 1, 1, 3, 4]
def baseStart_6004641 : Nat := 118140960795 + 6004641 * 2 ^ 59
def prefixEnd_6004641 : Nat := 4983230072969 + 3 ^ 40 * 6004641 * 2
def baseEnd_6004641 : Nat := 1027755663564715516057555

theorem tailTrace_6004641 : CollatzResearch.WordTrace tailWord_6004641 prefixEnd_6004641 1027755663564715516057555 := by
  unfold tailWord_6004641
  simp only [CollatzResearch.WordTrace]
  refine ⟨219007249439218642882805777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146004832959479095255203851 219007249439218642882805777)
  ·
    refine ⟨164255437079413982162104333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219007249439218642882805777 164255437079413982162104333)
    ·
      refine ⟨61595788904780243310789125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164255437079413982162104333 61595788904780243310789125)
      ·
        refine ⟨11549210419646295620772961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61595788904780243310789125 11549210419646295620772961)
        ·
          refine ⟨8661907814734721715579721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11549210419646295620772961 8661907814734721715579721)
          ·
            refine ⟨6496430861051041286684791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8661907814734721715579721 6496430861051041286684791)
            ·
              refine ⟨9744646291576561930027187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6496430861051041286684791 9744646291576561930027187)
              ·
                refine ⟨14616969437364842895040781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9744646291576561930027187 14616969437364842895040781)
                ·
                  refine ⟨5481363539011816085640293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14616969437364842895040781 5481363539011816085640293)
                  ·
                    refine ⟨1027755663564715516057555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5481363539011816085640293 1027755663564715516057555)
                    ·
                      rfl

theorem cell23_6004641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 1, 3, 4].length) (baseStart_6004641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6004641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6004641 prefixEnd_6004641 := by exact prefixLift 6004641
  have htrace : WordTrace (prefixWord ++ tailWord_6004641) baseStart_6004641 baseEnd_6004641 := by
    simpa [prefixWord, tailWord_6004641, baseEnd_6004641] using wordTrace_append hprefix tailTrace_6004641
  have hstable : (prefixWord ++ tailWord_6004641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6004641).length < 2 ^ (prefixWord ++ tailWord_6004641).sum := by decide
  have hdescent : baseEnd_6004641 < baseStart_6004641 := by decide
  rcases family_descends (prefixWord ++ tailWord_6004641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6004698 : List Nat := [3, 1, 1, 2, 5, 1, 1, 4, 1, 1, 3]
def baseStart_6004698 : Nat := 118140960795 + 6004698 * 2 ^ 59
def prefixEnd_6004698 : Nat := 4983230072969 + 3 ^ 40 * 6004698 * 2
def baseEnd_6004698 : Nat := 3083296259091452825159903

theorem tailTrace_6004698 : CollatzResearch.WordTrace tailWord_6004698 prefixEnd_6004698 3083296259091452825159903 := by
  unfold tailWord_6004698
  simp only [CollatzResearch.WordTrace]
  refine ⟨54752332100003035404407687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146006218933341427745087165 54752332100003035404407687)
  ·
    refine ⟨82128498150004553106611531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54752332100003035404407687 82128498150004553106611531)
    ·
      refine ⟨123192747225006829659917297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82128498150004553106611531 123192747225006829659917297)
      ·
        refine ⟨92394560418755122244937973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123192747225006829659917297 92394560418755122244937973)
        ·
          refine ⟨8661990039258292710462935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 92394560418755122244937973 8661990039258292710462935)
          ·
            refine ⟨12992985058887439065694403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8661990039258292710462935 12992985058887439065694403)
            ·
              refine ⟨19489477588331158598541605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12992985058887439065694403 19489477588331158598541605)
              ·
                refine ⟨3654277047812092237226551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19489477588331158598541605 3654277047812092237226551)
                ·
                  refine ⟨5481415571718138355839827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3654277047812092237226551 5481415571718138355839827)
                  ·
                    refine ⟨8222123357577207533759741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5481415571718138355839827 8222123357577207533759741)
                    ·
                      refine ⟨3083296259091452825159903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8222123357577207533759741 3083296259091452825159903)
                      ·
                        rfl

theorem cell23_6004698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 4, 1, 1, 3].length) (baseStart_6004698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6004698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6004698 prefixEnd_6004698 := by exact prefixLift 6004698
  have htrace : WordTrace (prefixWord ++ tailWord_6004698) baseStart_6004698 baseEnd_6004698 := by
    simpa [prefixWord, tailWord_6004698, baseEnd_6004698] using wordTrace_append hprefix tailTrace_6004698
  have hstable : (prefixWord ++ tailWord_6004698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6004698).length < 2 ^ (prefixWord ++ tailWord_6004698).sum := by decide
  have hdescent : baseEnd_6004698 < baseStart_6004698 := by decide
  rcases family_descends (prefixWord ++ tailWord_6004698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6004704 : List Nat := [2, 1, 1, 3, 1, 1, 1, 2, 7, 2, 2]
def baseStart_6004704 : Nat := 118140960795 + 6004704 * 2 ^ 59
def prefixEnd_6004704 : Nat := 4983230072969 + 3 ^ 40 * 6004704 * 2
def baseEnd_6004704 : Nat := 3083299339975379801684875

theorem tailTrace_6004704 : CollatzResearch.WordTrace tailWord_6004704 prefixEnd_6004704 3083299339975379801684875 := by
  unfold tailWord_6004704
  simp only [CollatzResearch.WordTrace]
  refine ⟨109504773618995202321174583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146006364825326936428232777 109504773618995202321174583)
  ·
    refine ⟨164257160428492803481761875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109504773618995202321174583 164257160428492803481761875)
    ·
      refine ⟨246385740642739205222642813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164257160428492803481761875 246385740642739205222642813)
      ·
        refine ⟨92394652741027201958491055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 246385740642739205222642813 92394652741027201958491055)
        ·
          refine ⟨138591979111540802937736583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92394652741027201958491055 138591979111540802937736583)
          ·
            refine ⟨207887968667311204406604875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138591979111540802937736583 207887968667311204406604875)
            ·
              refine ⟨311831953000966806609907313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207887968667311204406604875 311831953000966806609907313)
              ·
                refine ⟨233873964750725104957430485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 311831953000966806609907313 233873964750725104957430485)
                ·
                  refine ⟨5481421048845119647439777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 233873964750725104957430485 5481421048845119647439777)
                  ·
                    refine ⟨4111065786633839735579833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5481421048845119647439777 4111065786633839735579833)
                    ·
                      refine ⟨3083299339975379801684875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4111065786633839735579833 3083299339975379801684875)
                      ·
                        rfl

theorem cell23_6004704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 7, 2, 2].length) (baseStart_6004704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6004704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6004704 prefixEnd_6004704 := by exact prefixLift 6004704
  have htrace : WordTrace (prefixWord ++ tailWord_6004704) baseStart_6004704 baseEnd_6004704 := by
    simpa [prefixWord, tailWord_6004704, baseEnd_6004704] using wordTrace_append hprefix tailTrace_6004704
  have hstable : (prefixWord ++ tailWord_6004704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6004704).length < 2 ^ (prefixWord ++ tailWord_6004704).sum := by decide
  have hdescent : baseEnd_6004704 < baseStart_6004704 := by decide
  rcases family_descends (prefixWord ++ tailWord_6004704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6004714 : List Nat := [3, 1, 3, 1, 2, 1, 1, 5, 2, 4]
def baseStart_6004714 : Nat := 118140960795 + 6004714 * 2 ^ 59
def prefixEnd_6004714 : Nat := 4983230072969 + 3 ^ 40 * 6004714 * 2
def baseEnd_6004714 : Nat := 1027768158260641587519943

theorem tailTrace_6004714 : CollatzResearch.WordTrace tailWord_6004714 prefixEnd_6004714 1027768158260641587519943 := by
  unfold tailWord_6004714
  simp only [CollatzResearch.WordTrace]
  refine ⟨54752477991988544087553299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146006607978636117566808797 54752477991988544087553299)
  ·
    refine ⟨82128716987982816131329949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54752477991988544087553299 82128716987982816131329949)
    ·
      refine ⟨30798268870493556049248731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82128716987982816131329949 30798268870493556049248731)
      ·
        refine ⟨46197403305740334073873097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30798268870493556049248731 46197403305740334073873097)
        ·
          refine ⟨34648052479305250555404823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46197403305740334073873097 34648052479305250555404823)
          ·
            refine ⟨51972078718957875833107235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34648052479305250555404823 51972078718957875833107235)
            ·
              refine ⟨77958118078436813749660853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51972078718957875833107235 77958118078436813749660853)
              ·
                refine ⟨7308573569853451289030705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77958118078436813749660853 7308573569853451289030705)
                ·
                  refine ⟨5481430177390088466773029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7308573569853451289030705 5481430177390088466773029)
                  ·
                    refine ⟨1027768158260641587519943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5481430177390088466773029 1027768158260641587519943)
                    ·
                      rfl

theorem cell23_6004714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 5, 2, 4].length) (baseStart_6004714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6004714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6004714 prefixEnd_6004714 := by exact prefixLift 6004714
  have htrace : WordTrace (prefixWord ++ tailWord_6004714) baseStart_6004714 baseEnd_6004714 := by
    simpa [prefixWord, tailWord_6004714, baseEnd_6004714] using wordTrace_append hprefix tailTrace_6004714
  have hstable : (prefixWord ++ tailWord_6004714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6004714).length < 2 ^ (prefixWord ++ tailWord_6004714).sum := by decide
  have hdescent : baseEnd_6004714 < baseStart_6004714 := by decide
  rcases family_descends (prefixWord ++ tailWord_6004714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6004741 : List Nat := [1, 3, 1, 1, 2, 4, 4, 1, 1, 2, 3]
def baseStart_6004741 : Nat := 118140960795 + 6004741 * 2 ^ 59
def prefixEnd_6004741 : Nat := 4983230072969 + 3 ^ 40 * 6004741 * 2
def baseEnd_6004741 : Nat := 3083318338759596156922205

theorem tailTrace_6004741 : CollatzResearch.WordTrace tailWord_6004741 prefixEnd_6004741 3083318338759596156922205 := by
  unfold tailWord_6004741
  simp only [CollatzResearch.WordTrace]
  refine ⟨219010896738856359961446077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146007264492570906640964051 219010896738856359961446077)
  ·
    refine ⟨82129086277071134985542279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219010896738856359961446077 82129086277071134985542279)
    ·
      refine ⟨123193629415606702478313419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82129086277071134985542279 123193629415606702478313419)
      ·
        refine ⟨184790444123410053717470129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123193629415606702478313419 184790444123410053717470129)
        ·
          refine ⟨138592833092557540288102597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184790444123410053717470129 138592833092557540288102597)
          ·
            refine ⟨25986156204854538804019237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 138592833092557540288102597 25986156204854538804019237)
            ·
              refine ⟨4872404288410226025753607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25986156204854538804019237 4872404288410226025753607)
              ·
                refine ⟨7308606432615339038630411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4872404288410226025753607 7308606432615339038630411)
                ·
                  refine ⟨10962909648923008557945617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7308606432615339038630411 10962909648923008557945617)
                  ·
                    refine ⟨8222182236692256418459213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10962909648923008557945617 8222182236692256418459213)
                    ·
                      refine ⟨3083318338759596156922205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8222182236692256418459213 3083318338759596156922205)
                      ·
                        rfl

theorem cell23_6004741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 4, 1, 1, 2, 3].length) (baseStart_6004741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6004741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6004741 prefixEnd_6004741 := by exact prefixLift 6004741
  have htrace : WordTrace (prefixWord ++ tailWord_6004741) baseStart_6004741 baseEnd_6004741 := by
    simpa [prefixWord, tailWord_6004741, baseEnd_6004741] using wordTrace_append hprefix tailTrace_6004741
  have hstable : (prefixWord ++ tailWord_6004741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6004741).length < 2 ^ (prefixWord ++ tailWord_6004741).sum := by decide
  have hdescent : baseEnd_6004741 < baseStart_6004741 := by decide
  rcases family_descends (prefixWord ++ tailWord_6004741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6004794 : List Nat := [3, 1, 1, 1, 3, 1, 1, 3, 3, 4, 2]
def baseStart_6004794 : Nat := 118140960795 + 6004794 * 2 ^ 59
def prefixEnd_6004794 : Nat := 4983230072969 + 3 ^ 40 * 6004794 * 2
def baseEnd_6004794 : Nat := 3083345553234284449559461

theorem tailTrace_6004794 : CollatzResearch.WordTrace tailWord_6004794 prefixEnd_6004794 3083345553234284449559461 := by
  unfold tailWord_6004794
  simp only [CollatzResearch.WordTrace]
  refine ⟨54753207451916087503281359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146008553205109566675416957 54753207451916087503281359)
  ·
    refine ⟨82129811177874131254922039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54753207451916087503281359 82129811177874131254922039)
    ·
      refine ⟨123194716766811196882383059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82129811177874131254922039 123194716766811196882383059)
      ·
        refine ⟨184792075150216795323574589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123194716766811196882383059 184792075150216795323574589)
        ·
          refine ⟨69297028181331298246340471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184792075150216795323574589 69297028181331298246340471)
          ·
            refine ⟨103945542271996947369510707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69297028181331298246340471 103945542271996947369510707)
            ·
              refine ⟨155918313407995421054266061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103945542271996947369510707 155918313407995421054266061)
              ·
                refine ⟨58469367527998282895349773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 155918313407995421054266061 58469367527998282895349773)
                ·
                  refine ⟨21926012822999356085756165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58469367527998282895349773 21926012822999356085756165)
                  ·
                    refine ⟨4111127404312379266079281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21926012822999356085756165 4111127404312379266079281)
                    ·
                      refine ⟨3083345553234284449559461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4111127404312379266079281 3083345553234284449559461)
                      ·
                        rfl

theorem cell23_6004794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 3, 4, 2].length) (baseStart_6004794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6004794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6004794 prefixEnd_6004794 := by exact prefixLift 6004794
  have htrace : WordTrace (prefixWord ++ tailWord_6004794) baseStart_6004794 baseEnd_6004794 := by
    simpa [prefixWord, tailWord_6004794, baseEnd_6004794] using wordTrace_append hprefix tailTrace_6004794
  have hstable : (prefixWord ++ tailWord_6004794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6004794).length < 2 ^ (prefixWord ++ tailWord_6004794).sum := by decide
  have hdescent : baseEnd_6004794 < baseStart_6004794 := by decide
  rcases family_descends (prefixWord ++ tailWord_6004794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6004822 : List Nat := [5, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3]
def baseStart_6004822 : Nat := 118140960795 + 6004822 * 2 ^ 59
def prefixEnd_6004822 : Nat := 4983230072969 + 3 ^ 40 * 6004822 * 2
def baseEnd_6004822 : Nat := 3083359930692610340009333

theorem tailTrace_6004822 : CollatzResearch.WordTrace tailWord_6004822 prefixEnd_6004822 3083359930692610340009333 := by
  unfold tailWord_6004822
  simp only [CollatzResearch.WordTrace]
  refine ⟨13688365690722681924696545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 146009234034375273863429813 13688365690722681924696545)
  ·
    refine ⟨10266274268042011443522409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13688365690722681924696545 10266274268042011443522409)
    ·
      refine ⟨7699705701031508582641807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10266274268042011443522409 7699705701031508582641807)
      ·
        refine ⟨11549558551547262873962711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7699705701031508582641807 11549558551547262873962711)
        ·
          refine ⟨17324337827320894310944067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11549558551547262873962711 17324337827320894310944067)
          ·
            refine ⟨25986506740981341466416101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17324337827320894310944067 25986506740981341466416101)
            ·
              refine ⟨4872470013934001524953019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25986506740981341466416101 4872470013934001524953019)
              ·
                refine ⟨7308705020901002287429529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4872470013934001524953019 7308705020901002287429529)
                ·
                  refine ⟨5481528765675751715572147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7308705020901002287429529 5481528765675751715572147)
                  ·
                    refine ⟨8222293148513627573358221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5481528765675751715572147 8222293148513627573358221)
                    ·
                      refine ⟨3083359930692610340009333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8222293148513627573358221 3083359930692610340009333)
                      ·
                        rfl

theorem cell23_6004822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_6004822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6004822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6004822 prefixEnd_6004822 := by exact prefixLift 6004822
  have htrace : WordTrace (prefixWord ++ tailWord_6004822) baseStart_6004822 baseEnd_6004822 := by
    simpa [prefixWord, tailWord_6004822, baseEnd_6004822] using wordTrace_append hprefix tailTrace_6004822
  have hstable : (prefixWord ++ tailWord_6004822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6004822).length < 2 ^ (prefixWord ++ tailWord_6004822).sum := by decide
  have hdescent : baseEnd_6004822 < baseStart_6004822 := by decide
  rcases family_descends (prefixWord ++ tailWord_6004822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6004874 : List Nat := [3, 1, 2, 3, 1, 2, 2, 1, 1, 2, 5]
def baseStart_6004874 : Nat := 118140960795 + 6004874 * 2 ^ 59
def prefixEnd_6004874 : Nat := 4983230072969 + 3 ^ 40 * 6004874 * 2
def baseEnd_6004874 : Nat := 3083386631686644136559093

theorem tailTrace_6004874 : CollatzResearch.WordTrace tailWord_6004874 prefixEnd_6004874 3083386631686644136559093 := by
  unfold tailWord_6004874
  simp only [CollatzResearch.WordTrace]
  refine ⟨54753936911843630919009419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146010498431583015784025117 54753936911843630919009419)
  ·
    refine ⟨82130905367765446378514129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54753936911843630919009419 82130905367765446378514129)
    ·
      refine ⟨61598179025824084783885597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82130905367765446378514129 61598179025824084783885597)
      ·
        refine ⟨23099317134684031793957099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61598179025824084783885597 23099317134684031793957099)
        ·
          refine ⟨34648975702026047690935649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23099317134684031793957099 34648975702026047690935649)
          ·
            refine ⟨25986731776519535768201737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34648975702026047690935649 25986731776519535768201737)
            ·
              refine ⟨19490048832389651826151303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25986731776519535768201737 19490048832389651826151303)
              ·
                refine ⟨29235073248584477739226955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19490048832389651826151303 29235073248584477739226955)
                ·
                  refine ⟨43852609872876716608840433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29235073248584477739226955 43852609872876716608840433)
                  ·
                    refine ⟨32889457404657537456630325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43852609872876716608840433 32889457404657537456630325)
                    ·
                      refine ⟨3083386631686644136559093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32889457404657537456630325 3083386631686644136559093)
                      ·
                        rfl

theorem cell23_6004874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_6004874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6004874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6004874 prefixEnd_6004874 := by exact prefixLift 6004874
  have htrace : WordTrace (prefixWord ++ tailWord_6004874) baseStart_6004874 baseEnd_6004874 := by
    simpa [prefixWord, tailWord_6004874, baseEnd_6004874] using wordTrace_append hprefix tailTrace_6004874
  have hstable : (prefixWord ++ tailWord_6004874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6004874).length < 2 ^ (prefixWord ++ tailWord_6004874).sum := by decide
  have hdescent : baseEnd_6004874 < baseStart_6004874 := by decide
  rcases family_descends (prefixWord ++ tailWord_6004874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6004898 : List Nat := [3, 3, 1, 3, 1, 3, 1, 1, 2, 5]
def baseStart_6004898 : Nat := 118140960795 + 6004898 * 2 ^ 59
def prefixEnd_6004898 : Nat := 4983230072969 + 3 ^ 40 * 6004898 * 2
def baseEnd_6004898 : Nat := 1027799651740784014219661

theorem tailTrace_6004898 : CollatzResearch.WordTrace tailWord_6004898 prefixEnd_6004898 1027799651740784014219661 := by
  unfold tailWord_6004898
  simp only [CollatzResearch.WordTrace]
  refine ⟨54754155749821893943727837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146011081999525050516607565 54754155749821893943727837)
  ·
    refine ⟨20532808406183210228897939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54754155749821893943727837 20532808406183210228897939)
    ·
      refine ⟨30799212609274815343346909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20532808406183210228897939 30799212609274815343346909)
      ·
        refine ⟨11549704728478055753755091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30799212609274815343346909 11549704728478055753755091)
        ·
          refine ⟨17324557092717083630632637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11549704728478055753755091 17324557092717083630632637)
          ·
            refine ⟨6496708909768906361487239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17324557092717083630632637 6496708909768906361487239)
            ·
              refine ⟨9745063364653359542230859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6496708909768906361487239 9745063364653359542230859)
              ·
                refine ⟨14617595046980039313346289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9745063364653359542230859 14617595046980039313346289)
                ·
                  refine ⟨10963196285235029485009717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14617595046980039313346289 10963196285235029485009717)
                  ·
                    refine ⟨1027799651740784014219661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10963196285235029485009717 1027799651740784014219661)
                    ·
                      rfl

theorem cell23_6004898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 1, 2, 5].length) (baseStart_6004898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6004898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6004898 prefixEnd_6004898 := by exact prefixLift 6004898
  have htrace : WordTrace (prefixWord ++ tailWord_6004898) baseStart_6004898 baseEnd_6004898 := by
    simpa [prefixWord, tailWord_6004898, baseEnd_6004898] using wordTrace_append hprefix tailTrace_6004898
  have hstable : (prefixWord ++ tailWord_6004898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6004898).length < 2 ^ (prefixWord ++ tailWord_6004898).sum := by decide
  have hdescent : baseEnd_6004898 < baseStart_6004898 := by decide
  rcases family_descends (prefixWord ++ tailWord_6004898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6004928 : List Nat := [2, 1, 1, 2, 5, 1, 2, 4, 1, 4]
def baseStart_6004928 : Nat := 118140960795 + 6004928 * 2 ^ 59
def prefixEnd_6004928 : Nat := 4983230072969 + 3 ^ 40 * 6004928 * 2
def baseEnd_6004928 : Nat := 1027804786547328975094615

theorem tailTrace_6004928 : CollatzResearch.WordTrace tailWord_6004928 prefixEnd_6004928 1027804786547328975094615 := by
  unfold tailWord_6004928
  simp only [CollatzResearch.WordTrace]
  refine ⟨109508858594589445449251719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146011811459452593932335625 109508858594589445449251719)
  ·
    refine ⟨164263287891884168173877579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109508858594589445449251719 164263287891884168173877579)
    ·
      refine ⟨246394931837826252260816369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164263287891884168173877579 246394931837826252260816369)
      ·
        refine ⟨184796198878369689195612277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246394931837826252260816369 184796198878369689195612277)
        ·
          refine ⟨17324643644847158362088651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 184796198878369689195612277 17324643644847158362088651)
          ·
            refine ⟨25986965467270737543132977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17324643644847158362088651 25986965467270737543132977)
            ·
              refine ⟨19490224100453053157349733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25986965467270737543132977 19490224100453053157349733)
              ·
                refine ⟨3654417018834947467003075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19490224100453053157349733 3654417018834947467003075)
                ·
                  refine ⟨5481625528252421200504613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3654417018834947467003075 5481625528252421200504613)
                  ·
                    refine ⟨1027804786547328975094615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5481625528252421200504613 1027804786547328975094615)
                    ·
                      rfl

theorem cell23_6004928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 4, 1, 4].length) (baseStart_6004928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6004928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6004928 prefixEnd_6004928 := by exact prefixLift 6004928
  have htrace : WordTrace (prefixWord ++ tailWord_6004928) baseStart_6004928 baseEnd_6004928 := by
    simpa [prefixWord, tailWord_6004928, baseEnd_6004928] using wordTrace_append hprefix tailTrace_6004928
  have hstable : (prefixWord ++ tailWord_6004928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6004928).length < 2 ^ (prefixWord ++ tailWord_6004928).sum := by decide
  have hdescent : baseEnd_6004928 < baseStart_6004928 := by decide
  rcases family_descends (prefixWord ++ tailWord_6004928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6004937 : List Nat := [1, 2, 1, 1, 2, 1, 1, 3, 2, 9]
def baseStart_6004937 : Nat := 118140960795 + 6004937 * 2 ^ 59
def prefixEnd_6004937 : Nat := 4983230072969 + 3 ^ 40 * 6004937 * 2
def baseEnd_6004937 : Nat := 1027806326989292463357101

theorem tailTrace_6004937 : CollatzResearch.WordTrace tailWord_6004937 prefixEnd_6004937 1027806326989292463357101 := by
  unfold tailWord_6004937
  simp only [CollatzResearch.WordTrace]
  refine ⟨219018045446146285435581065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146012030297430856957054043 219018045446146285435581065)
  ·
    refine ⟨164263534084609714076685799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219018045446146285435581065 164263534084609714076685799)
    ·
      refine ⟨246395301126914571115028699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164263534084609714076685799 246395301126914571115028699)
      ·
        refine ⟨369592951690371856672543049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246395301126914571115028699 369592951690371856672543049)
        ·
          refine ⟨277194713767778892504407287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 369592951690371856672543049 277194713767778892504407287)
          ·
            refine ⟨415792070651668338756610931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277194713767778892504407287 415792070651668338756610931)
            ·
              refine ⟨623688105977502508134916397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 415792070651668338756610931 623688105977502508134916397)
              ·
                refine ⟨233883039741563440550593649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 623688105977502508134916397 233883039741563440550593649)
                ·
                  refine ⟨175412279806172580412945237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 233883039741563440550593649 175412279806172580412945237)
                  ·
                    refine ⟨1027806326989292463357101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 175412279806172580412945237 1027806326989292463357101)
                    ·
                      rfl

theorem cell23_6004937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 9].length) (baseStart_6004937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6004937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6004937 prefixEnd_6004937 := by exact prefixLift 6004937
  have htrace : WordTrace (prefixWord ++ tailWord_6004937) baseStart_6004937 baseEnd_6004937 := by
    simpa [prefixWord, tailWord_6004937, baseEnd_6004937] using wordTrace_append hprefix tailTrace_6004937
  have hstable : (prefixWord ++ tailWord_6004937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6004937).length < 2 ^ (prefixWord ++ tailWord_6004937).sum := by decide
  have hdescent : baseEnd_6004937 < baseStart_6004937 := by decide
  rcases family_descends (prefixWord ++ tailWord_6004937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6004954 : List Nat := [3, 1, 1, 2, 2, 1, 2, 3, 3, 5]
def baseStart_6004954 : Nat := 118140960795 + 6004954 * 2 ^ 59
def prefixEnd_6004954 : Nat := 4983230072969 + 3 ^ 40 * 6004954 * 2
def baseEnd_6004954 : Nat := 1027809236713001274519575

theorem tailTrace_6004954 : CollatzResearch.WordTrace tailWord_6004954 prefixEnd_6004954 1027809236713001274519575 := by
  unfold tailWord_6004954
  simp only [CollatzResearch.WordTrace]
  refine ⟨54754666371771174334737479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146012443658056464892633277 54754666371771174334737479)
  ·
    refine ⟨82131999557656761502106219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54754666371771174334737479 82131999557656761502106219)
    ·
      refine ⟨123197999336485142253159329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82131999557656761502106219 123197999336485142253159329)
      ·
        refine ⟨92398499502363856689869497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123197999336485142253159329 92398499502363856689869497)
        ·
          refine ⟨69298874626772892517402123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92398499502363856689869497 69298874626772892517402123)
          ·
            refine ⟨103948311940159338776103185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69298874626772892517402123 103948311940159338776103185)
            ·
              refine ⟨77961233955119504082077389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103948311940159338776103185 77961233955119504082077389)
              ·
                refine ⟨29235462733169814030779021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77961233955119504082077389 29235462733169814030779021)
                ·
                  refine ⟨10963298524938680261542133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29235462733169814030779021 10963298524938680261542133)
                  ·
                    refine ⟨1027809236713001274519575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10963298524938680261542133 1027809236713001274519575)
                    ·
                      rfl

theorem cell23_6004954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 3, 5].length) (baseStart_6004954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6004954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6004954 prefixEnd_6004954 := by exact prefixLift 6004954
  have htrace : WordTrace (prefixWord ++ tailWord_6004954) baseStart_6004954 baseEnd_6004954 := by
    simpa [prefixWord, tailWord_6004954, baseEnd_6004954] using wordTrace_append hprefix tailTrace_6004954
  have hstable : (prefixWord ++ tailWord_6004954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6004954).length < 2 ^ (prefixWord ++ tailWord_6004954).sum := by decide
  have hdescent : baseEnd_6004954 < baseStart_6004954 := by decide
  rcases family_descends (prefixWord ++ tailWord_6004954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6004961 : List Nat := [1, 2, 3, 1, 3, 1, 1, 3, 1, 5, 2]
def baseStart_6004961 : Nat := 118140960795 + 6004961 * 2 ^ 59
def prefixEnd_6004961 : Nat := 4983230072969 + 3 ^ 40 * 6004961 * 2
def baseEnd_6004961 : Nat := 3083431304503585296171193

theorem tailTrace_6004961 : CollatzResearch.WordTrace tailWord_6004961 prefixEnd_6004961 3083431304503585296171193 := by
  unfold tailWord_6004961
  simp only [CollatzResearch.WordTrace]
  refine ⟨219018920798059337534454737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146012613865372891689636491 219018920798059337534454737)
  ·
    refine ⟨164264190598544503150841053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219018920798059337534454737 164264190598544503150841053)
    ·
      refine ⟨61599071474454188681565395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164264190598544503150841053 61599071474454188681565395)
      ·
        refine ⟨92398607211681283022348093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61599071474454188681565395 92398607211681283022348093)
        ·
          refine ⟨34649477704380481133380535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92398607211681283022348093 34649477704380481133380535)
          ·
            refine ⟨51974216556570721700070803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34649477704380481133380535 51974216556570721700070803)
            ·
              refine ⟨77961324834856082550106205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51974216556570721700070803 77961324834856082550106205)
              ·
                refine ⟨29235496813071030956289827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77961324834856082550106205 29235496813071030956289827)
                ·
                  refine ⟨43853245219606546434434741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29235496813071030956289827 43853245219606546434434741)
                  ·
                    refine ⟨4111241739338113728228257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43853245219606546434434741 4111241739338113728228257)
                    ·
                      refine ⟨3083431304503585296171193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4111241739338113728228257 3083431304503585296171193)
                      ·
                        rfl

theorem cell23_6004961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 5, 2].length) (baseStart_6004961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6004961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6004961 prefixEnd_6004961 := by exact prefixLift 6004961
  have htrace : WordTrace (prefixWord ++ tailWord_6004961) baseStart_6004961 baseEnd_6004961 := by
    simpa [prefixWord, tailWord_6004961, baseEnd_6004961] using wordTrace_append hprefix tailTrace_6004961
  have hstable : (prefixWord ++ tailWord_6004961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6004961).length < 2 ^ (prefixWord ++ tailWord_6004961).sum := by decide
  have hdescent : baseEnd_6004961 < baseStart_6004961 := by decide
  rcases family_descends (prefixWord ++ tailWord_6004961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6004978 : List Nat := [3, 2, 1, 3, 2, 1, 1, 1, 4, 3, 2]
def baseStart_6004978 : Nat := 118140960795 + 6004978 * 2 ^ 59
def prefixEnd_6004978 : Nat := 4983230072969 + 3 ^ 40 * 6004978 * 2
def baseEnd_6004978 : Nat := 3083440033674711729658615

theorem tailTrace_6004978 : CollatzResearch.WordTrace tailWord_6004978 prefixEnd_6004978 3083440033674711729658615 := by
  unfold tailWord_6004978
  simp only [CollatzResearch.WordTrace]
  refine ⟨54754885209749437359455897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146013027225998499625215725 54754885209749437359455897)
  ·
    refine ⟨41066163907312078019591923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54754885209749437359455897 41066163907312078019591923)
    ·
      refine ⟨61599245860968117029387885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41066163907312078019591923 61599245860968117029387885)
      ·
        refine ⟨23099717197863043886020457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61599245860968117029387885 23099717197863043886020457)
        ·
          refine ⟨17324787898397282914515343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23099717197863043886020457 17324787898397282914515343)
          ·
            refine ⟨25987181847595924371773015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17324787898397282914515343 25987181847595924371773015)
            ·
              refine ⟨38980772771393886557659523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25987181847595924371773015 38980772771393886557659523)
              ·
                refine ⟨58471159157090829836489285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38980772771393886557659523 58471159157090829836489285)
                ·
                  refine ⟨10963342341954530594341741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58471159157090829836489285 10963342341954530594341741)
                  ·
                    refine ⟨4111253378232948972878153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10963342341954530594341741 4111253378232948972878153)
                    ·
                      refine ⟨3083440033674711729658615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4111253378232948972878153 3083440033674711729658615)
                      ·
                        rfl

theorem cell23_6004978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 4, 3, 2].length) (baseStart_6004978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6004978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6004978 prefixEnd_6004978 := by exact prefixLift 6004978
  have htrace : WordTrace (prefixWord ++ tailWord_6004978) baseStart_6004978 baseEnd_6004978 := by
    simpa [prefixWord, tailWord_6004978, baseEnd_6004978] using wordTrace_append hprefix tailTrace_6004978
  have hstable : (prefixWord ++ tailWord_6004978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6004978).length < 2 ^ (prefixWord ++ tailWord_6004978).sum := by decide
  have hdescent : baseEnd_6004978 < baseStart_6004978 := by decide
  rcases family_descends (prefixWord ++ tailWord_6004978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6005004 : List Nat := [2, 2, 1, 2, 2, 2, 1, 3, 1, 1, 6]
def baseStart_6005004 : Nat := 118140960795 + 6005004 * 2 ^ 59
def prefixEnd_6005004 : Nat := 4983230072969 + 3 ^ 40 * 6005004 * 2
def baseEnd_6005004 : Nat := 3083453384171728627933495

theorem tailTrace_6005004 : CollatzResearch.WordTrace tailWord_6005004 prefixEnd_6005004 3083453384171728627933495 := by
  unfold tailWord_6005004
  simp only [CollatzResearch.WordTrace]
  refine ⟨109510244568451777939135033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146013659424602370585513377 109510244568451777939135033)
  ·
    refine ⟨82132683426338833454351275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109510244568451777939135033 82132683426338833454351275)
    ·
      refine ⟨123199025139508250181526913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82132683426338833454351275 123199025139508250181526913)
      ·
        refine ⟨92399268854631187636145185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123199025139508250181526913 92399268854631187636145185)
        ·
          refine ⟨69299451640973390727108889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92399268854631187636145185 69299451640973390727108889)
          ·
            refine ⟨51974588730730043045331667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69299451640973390727108889 51974588730730043045331667)
            ·
              refine ⟨77961883096095064567997501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51974588730730043045331667 77961883096095064567997501)
              ·
                refine ⟨29235706161035649212999063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77961883096095064567997501 29235706161035649212999063)
                ·
                  refine ⟨43853559241553473819498595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29235706161035649212999063 43853559241553473819498595)
                  ·
                    refine ⟨65780338862330210729247893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43853559241553473819498595 65780338862330210729247893)
                    ·
                      refine ⟨3083453384171728627933495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65780338862330210729247893 3083453384171728627933495)
                      ·
                        rfl

theorem cell23_6005004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 1, 1, 6].length) (baseStart_6005004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6005004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6005004 prefixEnd_6005004 := by exact prefixLift 6005004
  have htrace : WordTrace (prefixWord ++ tailWord_6005004) baseStart_6005004 baseEnd_6005004 := by
    simpa [prefixWord, tailWord_6005004, baseEnd_6005004] using wordTrace_append hprefix tailTrace_6005004
  have hstable : (prefixWord ++ tailWord_6005004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6005004).length < 2 ^ (prefixWord ++ tailWord_6005004).sum := by decide
  have hdescent : baseEnd_6005004 < baseStart_6005004 := by decide
  rcases family_descends (prefixWord ++ tailWord_6005004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6005022 : List Nat := [4, 3, 2, 1, 1, 2, 3, 1, 1, 5]
def baseStart_6005022 : Nat := 118140960795 + 6005022 * 2 ^ 59
def prefixEnd_6005022 : Nat := 4983230072969 + 3 ^ 40 * 6005022 * 2
def baseEnd_6005022 : Nat := 1027820875607836519169471

theorem tailTrace_6005022 : CollatzResearch.WordTrace tailWord_6005022 prefixEnd_6005022 1027820875607836519169471 := by
  unfold tailWord_6005022
  simp only [CollatzResearch.WordTrace]
  refine ⟨27377643206354793119053165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146014097100558896634950213 27377643206354793119053165)
  ·
    refine ⟨10266616202383047419644937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27377643206354793119053165 10266616202383047419644937)
    ·
      refine ⟨7699962151787285564733703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10266616202383047419644937 7699962151787285564733703)
      ·
        refine ⟨11549943227680928347100555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7699962151787285564733703 11549943227680928347100555)
        ·
          refine ⟨17324914841521392520650833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11549943227680928347100555 17324914841521392520650833)
          ·
            refine ⟨12993686131141044390488125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17324914841521392520650833 12993686131141044390488125)
            ·
              refine ⟨4872632299177891646433047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12993686131141044390488125 4872632299177891646433047)
              ·
                refine ⟨7308948448766837469649571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4872632299177891646433047 7308948448766837469649571)
                ·
                  refine ⟨10963422673150256204474357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7308948448766837469649571 10963422673150256204474357)
                  ·
                    refine ⟨1027820875607836519169471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10963422673150256204474357 1027820875607836519169471)
                    ·
                      rfl

theorem cell23_6005022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_6005022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6005022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6005022 prefixEnd_6005022 := by exact prefixLift 6005022
  have htrace : WordTrace (prefixWord ++ tailWord_6005022) baseStart_6005022 baseEnd_6005022 := by
    simpa [prefixWord, tailWord_6005022, baseEnd_6005022] using wordTrace_append hprefix tailTrace_6005022
  have hstable : (prefixWord ++ tailWord_6005022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6005022).length < 2 ^ (prefixWord ++ tailWord_6005022).sum := by decide
  have hdescent : baseEnd_6005022 < baseStart_6005022 := by decide
  rcases family_descends (prefixWord ++ tailWord_6005022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6005028 : List Nat := [2, 3, 1, 3, 1, 4, 1, 1, 1, 1, 5]
def baseStart_6005028 : Nat := 118140960795 + 6005028 * 2 ^ 59
def prefixEnd_6005028 : Nat := 4983230072969 + 3 ^ 40 * 6005028 * 2
def baseEnd_6005028 : Nat := 3083465707707436534033385

theorem tailTrace_6005028 : CollatzResearch.WordTrace tailWord_6005028 prefixEnd_6005028 3083465707707436534033385 := by
  unfold tailWord_6005028
  simp only [CollatzResearch.WordTrace]
  refine ⟨109510682244408303988571869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146014242992544405318095825 109510682244408303988571869)
  ·
    refine ⟨41066505841653113995714451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109510682244408303988571869 41066505841653113995714451)
    ·
      refine ⟨61599758762479670993571677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41066505841653113995714451 61599758762479670993571677)
      ·
        refine ⟨23099909535929876622589379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61599758762479670993571677 23099909535929876622589379)
        ·
          refine ⟨34649864303894814933884069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23099909535929876622589379 34649864303894814933884069)
          ·
            refine ⟨6496849556980277800103263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34649864303894814933884069 6496849556980277800103263)
            ·
              refine ⟨9745274335470416700154895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6496849556980277800103263 9745274335470416700154895)
              ·
                refine ⟨14617911503205625050232343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9745274335470416700154895 14617911503205625050232343)
                ·
                  refine ⟨21926867254808437575348515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14617911503205625050232343 21926867254808437575348515)
                  ·
                    refine ⟨32890300882212656363022773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21926867254808437575348515 32890300882212656363022773)
                    ·
                      refine ⟨3083465707707436534033385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32890300882212656363022773 3083465707707436534033385)
                      ·
                        rfl

theorem cell23_6005028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_6005028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6005028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6005028 prefixEnd_6005028 := by exact prefixLift 6005028
  have htrace : WordTrace (prefixWord ++ tailWord_6005028) baseStart_6005028 baseEnd_6005028 := by
    simpa [prefixWord, tailWord_6005028, baseEnd_6005028] using wordTrace_append hprefix tailTrace_6005028
  have hstable : (prefixWord ++ tailWord_6005028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6005028).length < 2 ^ (prefixWord ++ tailWord_6005028).sum := by decide
  have hdescent : baseEnd_6005028 < baseStart_6005028 := by decide
  rcases family_descends (prefixWord ++ tailWord_6005028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6005068 : List Nat := [2, 2, 1, 3, 2, 1, 1, 3, 3, 3, 2]
def baseStart_6005068 : Nat := 118140960795 + 6005068 * 2 ^ 59
def prefixEnd_6005068 : Nat := 4983230072969 + 3 ^ 40 * 6005068 * 2
def baseEnd_6005068 : Nat := 3083486246933616377533201

theorem tailTrace_6005068 : CollatzResearch.WordTrace tailWord_6005068 prefixEnd_6005068 3083486246933616377533201 := by
  unfold tailWord_6005068
  simp only [CollatzResearch.WordTrace]
  refine ⟨109511411704335847404299929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146015215605781129872399905 109511411704335847404299929)
  ·
    refine ⟨82133558778251885553224947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109511411704335847404299929 82133558778251885553224947)
    ·
      refine ⟨123200338167377828329837421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82133558778251885553224947 123200338167377828329837421)
      ·
        refine ⟨46200126812766685623689033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123200338167377828329837421 46200126812766685623689033)
        ·
          refine ⟨34650095109575014217766775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46200126812766685623689033 34650095109575014217766775)
          ·
            refine ⟨51975142664362521326650163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34650095109575014217766775 51975142664362521326650163)
            ·
              refine ⟨77962713996543781989975245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51975142664362521326650163 77962713996543781989975245)
              ·
                refine ⟨29236017748703918246240717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77962713996543781989975245 29236017748703918246240717)
                ·
                  refine ⟨10963506655763969342340269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29236017748703918246240717 10963506655763969342340269)
                  ·
                    refine ⟨4111314995911488503377601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10963506655763969342340269 4111314995911488503377601)
                    ·
                      refine ⟨3083486246933616377533201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4111314995911488503377601 3083486246933616377533201)
                      ·
                        rfl

theorem cell23_6005068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 3, 3, 2].length) (baseStart_6005068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6005068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6005068 prefixEnd_6005068 := by exact prefixLift 6005068
  have htrace : WordTrace (prefixWord ++ tailWord_6005068) baseStart_6005068 baseEnd_6005068 := by
    simpa [prefixWord, tailWord_6005068, baseEnd_6005068] using wordTrace_append hprefix tailTrace_6005068
  have hstable : (prefixWord ++ tailWord_6005068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6005068).length < 2 ^ (prefixWord ++ tailWord_6005068).sum := by decide
  have hdescent : baseEnd_6005068 < baseStart_6005068 := by decide
  rcases family_descends (prefixWord ++ tailWord_6005068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6005115 : List Nat := [1, 1, 1, 1, 1, 9, 1, 1, 1, 4, 2]
def baseStart_6005115 : Nat := 118140960795 + 6005115 * 2 ^ 59
def prefixEnd_6005115 : Nat := 4983230072969 + 3 ^ 40 * 6005115 * 2
def baseEnd_6005115 : Nat := 3083510380524377693645485

theorem tailTrace_6005115 : CollatzResearch.WordTrace tailWord_6005115 prefixEnd_6005115 3083510380524377693645485 := by
  unfold tailWord_6005115
  simp only [CollatzResearch.WordTrace]
  refine ⟨219024537639501421835560799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146016358426334281223707199 219024537639501421835560799)
  ·
    refine ⟨328536806459252132753341199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219024537639501421835560799 328536806459252132753341199)
    ·
      refine ⟨492805209688878199130011799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328536806459252132753341199 492805209688878199130011799)
      ·
        refine ⟨739207814533317298695017699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 492805209688878199130011799 739207814533317298695017699)
        ·
          refine ⟨1108811721799975948042526549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 739207814533317298695017699 1108811721799975948042526549)
          ·
            refine ⟨6496943682421734070561679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1108811721799975948042526549 6496943682421734070561679)
            ·
              refine ⟨9745415523632601105842519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6496943682421734070561679 9745415523632601105842519)
              ·
                refine ⟨14618123285448901658763779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9745415523632601105842519 14618123285448901658763779)
                ·
                  refine ⟨21927184928173352488145669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14618123285448901658763779 21927184928173352488145669)
                  ·
                    refine ⟨4111347174032503591527313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21927184928173352488145669 4111347174032503591527313)
                    ·
                      refine ⟨3083510380524377693645485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4111347174032503591527313 3083510380524377693645485)
                      ·
                        rfl

theorem cell23_6005115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 1, 1, 4, 2].length) (baseStart_6005115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6005115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6005115 prefixEnd_6005115 := by exact prefixLift 6005115
  have htrace : WordTrace (prefixWord ++ tailWord_6005115) baseStart_6005115 baseEnd_6005115 := by
    simpa [prefixWord, tailWord_6005115, baseEnd_6005115] using wordTrace_append hprefix tailTrace_6005115
  have hstable : (prefixWord ++ tailWord_6005115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6005115).length < 2 ^ (prefixWord ++ tailWord_6005115).sum := by decide
  have hdescent : baseEnd_6005115 < baseStart_6005115 := by decide
  rcases family_descends (prefixWord ++ tailWord_6005115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6005155 : List Nat := [1, 1, 1, 4, 1, 5, 3, 2, 5]
def baseStart_6005155 : Nat := 118140960795 + 6005155 * 2 ^ 59
def prefixEnd_6005155 : Nat := 4983230072969 + 3 ^ 40 * 6005155 * 2
def baseEnd_6005155 : Nat := 342614546638950837460589

theorem tailTrace_6005155 : CollatzResearch.WordTrace tailWord_6005155 prefixEnd_6005155 342614546638950837460589 := by
  unfold tailWord_6005155
  simp only [CollatzResearch.WordTrace]
  refine ⟨219025996559356508667016919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146017331039571005778011279 219025996559356508667016919)
  ·
    refine ⟨328538994839034763000525379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219025996559356508667016919 328538994839034763000525379)
    ·
      refine ⟨492808492258552144500788069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328538994839034763000525379 492808492258552144500788069)
      ·
        refine ⟨92401592298478527093897763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 492808492258552144500788069 92401592298478527093897763)
        ·
          refine ⟨138602388447717790640846645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92401592298478527093897763 138602388447717790640846645)
          ·
            refine ⟨12993973916973542872579373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 138602388447717790640846645 12993973916973542872579373)
            ·
              refine ⟨4872740218865078577217265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12993973916973542872579373 4872740218865078577217265)
              ·
                refine ⟨3654555164148808932912949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4872740218865078577217265 3654555164148808932912949)
                ·
                  refine ⟨342614546638950837460589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3654555164148808932912949 342614546638950837460589)
                  ·
                    rfl

theorem cell23_6005155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 3, 2, 5].length) (baseStart_6005155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6005155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6005155 prefixEnd_6005155 := by exact prefixLift 6005155
  have htrace : WordTrace (prefixWord ++ tailWord_6005155) baseStart_6005155 baseEnd_6005155 := by
    simpa [prefixWord, tailWord_6005155, baseEnd_6005155] using wordTrace_append hprefix tailTrace_6005155
  have hstable : (prefixWord ++ tailWord_6005155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6005155).length < 2 ^ (prefixWord ++ tailWord_6005155).sum := by decide
  have hdescent : baseEnd_6005155 < baseStart_6005155 := by decide
  rcases family_descends (prefixWord ++ tailWord_6005155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6005272 : List Nat := [2, 1, 2, 3, 3, 2, 2, 1, 3, 1, 3]
def baseStart_6005272 : Nat := 118140960795 + 6005272 * 2 ^ 59
def prefixEnd_6005272 : Nat := 4983230072969 + 3 ^ 40 * 6005272 * 2
def baseEnd_6005272 : Nat := 3083590996987133579382263

theorem tailTrace_6005272 : CollatzResearch.WordTrace tailWord_6005272 prefixEnd_6005272 3083590996987133579382263 := by
  unfold tailWord_6005272
  simp only [CollatzResearch.WordTrace]
  refine ⟨109515131949966318824513035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146020175933288425099350713 109515131949966318824513035)
  ·
    refine ⟨164272697924949478236769553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109515131949966318824513035 164272697924949478236769553)
    ·
      refine ⟨123204523443712108677577165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164272697924949478236769553 123204523443712108677577165)
      ·
        refine ⟨46201696291392040754091437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123204523443712108677577165 46201696291392040754091437)
        ·
          refine ⟨17325636109272015282784289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46201696291392040754091437 17325636109272015282784289)
          ·
            refine ⟨12994227081954011462088217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17325636109272015282784289 12994227081954011462088217)
            ·
              refine ⟨9745670311465508596566163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12994227081954011462088217 9745670311465508596566163)
              ·
                refine ⟨14618505467198262894849245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9745670311465508596566163 14618505467198262894849245)
                ·
                  refine ⟨5481939550199348585568467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14618505467198262894849245 5481939550199348585568467)
                  ·
                    refine ⟨8222909325299022878352701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5481939550199348585568467 8222909325299022878352701)
                    ·
                      refine ⟨3083590996987133579382263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8222909325299022878352701 3083590996987133579382263)
                      ·
                        rfl

theorem cell23_6005272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 1, 3, 1, 3].length) (baseStart_6005272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6005272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6005272 prefixEnd_6005272 := by exact prefixLift 6005272
  have htrace : WordTrace (prefixWord ++ tailWord_6005272) baseStart_6005272 baseEnd_6005272 := by
    simpa [prefixWord, tailWord_6005272, baseEnd_6005272] using wordTrace_append hprefix tailTrace_6005272
  have hstable : (prefixWord ++ tailWord_6005272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6005272).length < 2 ^ (prefixWord ++ tailWord_6005272).sum := by decide
  have hdescent : baseEnd_6005272 < baseStart_6005272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6005272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6005325 : List Nat := [1, 6, 1, 1, 2, 1, 1, 2, 1, 1, 6]
def baseStart_6005325 : Nat := 118140960795 + 6005325 * 2 ^ 59
def prefixEnd_6005325 : Nat := 4983230072969 + 3 ^ 40 * 6005325 * 2
def baseEnd_6005325 : Nat := 3083618211461821872019519

theorem tailTrace_6005325 : CollatzResearch.WordTrace tailWord_6005325 prefixEnd_6005325 3083618211461821872019519 := by
  unfold tailWord_6005325
  simp only [CollatzResearch.WordTrace]
  refine ⟨219032196968740627700705429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146021464645827085133803619 219032196968740627700705429)
  ·
    refine ⟨10267134232909716923470567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 219032196968740627700705429 10267134232909716923470567)
    ·
      refine ⟨15400701349364575385205851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10267134232909716923470567 15400701349364575385205851)
      ·
        refine ⟨23101052024046863077808777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15400701349364575385205851 23101052024046863077808777)
        ·
          refine ⟨17325789018035147308356583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23101052024046863077808777 17325789018035147308356583)
          ·
            refine ⟨25988683527052720962534875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17325789018035147308356583 25988683527052720962534875)
            ·
              refine ⟨38983025290579081443802313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25988683527052720962534875 38983025290579081443802313)
              ·
                refine ⟨29237268967934311082851735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38983025290579081443802313 29237268967934311082851735)
                ·
                  refine ⟨43855903451901466624277603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29237268967934311082851735 43855903451901466624277603)
                  ·
                    refine ⟨65783855177852199936416405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43855903451901466624277603 65783855177852199936416405)
                    ·
                      refine ⟨3083618211461821872019519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65783855177852199936416405 3083618211461821872019519)
                      ·
                        rfl

theorem cell23_6005325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_6005325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6005325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6005325 prefixEnd_6005325 := by exact prefixLift 6005325
  have htrace : WordTrace (prefixWord ++ tailWord_6005325) baseStart_6005325 baseEnd_6005325 := by
    simpa [prefixWord, tailWord_6005325, baseEnd_6005325] using wordTrace_append hprefix tailTrace_6005325
  have hstable : (prefixWord ++ tailWord_6005325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6005325).length < 2 ^ (prefixWord ++ tailWord_6005325).sum := by decide
  have hdescent : baseEnd_6005325 < baseStart_6005325 := by decide
  rcases family_descends (prefixWord ++ tailWord_6005325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6005328 : List Nat := [2, 1, 1, 1, 1, 3, 2, 1, 5, 3, 3]
def baseStart_6005328 : Nat := 118140960795 + 6005328 * 2 ^ 59
def prefixEnd_6005328 : Nat := 4983230072969 + 3 ^ 40 * 6005328 * 2
def baseEnd_6005328 : Nat := 3083619751903785360282005

theorem tailTrace_6005328 : CollatzResearch.WordTrace tailWord_6005328 prefixEnd_6005328 3083619751903785360282005 := by
  unfold tailWord_6005328
  simp only [CollatzResearch.WordTrace]
  refine ⟨109516153193864879606532319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146021537591819839475376425 109516153193864879606532319)
  ·
    refine ⟨164274229790797319409798479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109516153193864879606532319 164274229790797319409798479)
    ·
      refine ⟨246411344686195979114697719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164274229790797319409798479 246411344686195979114697719)
      ·
        refine ⟨369617017029293968672046579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246411344686195979114697719 369617017029293968672046579)
        ·
          refine ⟨554425525543940953008069869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 369617017029293968672046579 554425525543940953008069869)
          ·
            refine ⟨207909572078977857378026201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 554425525543940953008069869 207909572078977857378026201)
            ·
              refine ⟨155932179059233393033519651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 207909572078977857378026201 155932179059233393033519651)
              ·
                refine ⟨233898268588850089550279477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155932179059233393033519651 233898268588850089550279477)
                ·
                  refine ⟨21927962680204695895338701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 233898268588850089550279477 21927962680204695895338701)
                  ·
                    refine ⟨8222986005076760960752013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21927962680204695895338701 8222986005076760960752013)
                    ·
                      refine ⟨3083619751903785360282005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8222986005076760960752013 3083619751903785360282005)
                      ·
                        rfl

theorem cell23_6005328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 5, 3, 3].length) (baseStart_6005328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6005328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6005328 prefixEnd_6005328 := by exact prefixLift 6005328
  have htrace : WordTrace (prefixWord ++ tailWord_6005328) baseStart_6005328 baseEnd_6005328 := by
    simpa [prefixWord, tailWord_6005328, baseEnd_6005328] using wordTrace_append hprefix tailTrace_6005328
  have hstable : (prefixWord ++ tailWord_6005328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6005328).length < 2 ^ (prefixWord ++ tailWord_6005328).sum := by decide
  have hdescent : baseEnd_6005328 < baseStart_6005328 := by decide
  rcases family_descends (prefixWord ++ tailWord_6005328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6005329 : List Nat := [1, 2, 2, 1, 3, 5, 1, 1, 3, 2, 2]
def baseStart_6005329 : Nat := 118140960795 + 6005329 * 2 ^ 59
def prefixEnd_6005329 : Nat := 4983230072969 + 3 ^ 40 * 6005329 * 2
def baseEnd_6005329 : Nat := 3083620265384439856369501

theorem tailTrace_6005329 : CollatzResearch.WordTrace tailWord_6005329 prefixEnd_6005329 3083620265384439856369501 := by
  unfold tailWord_6005329
  simp only [CollatzResearch.WordTrace]
  refine ⟨219032342860726136383851041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146021561907150757589234027 219032342860726136383851041)
  ·
    refine ⟨164274257145544602287888281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219032342860726136383851041 164274257145544602287888281)
    ·
      refine ⟨123205692859158451715916211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164274257145544602287888281 123205692859158451715916211)
      ·
        refine ⟨184808539288737677573874317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123205692859158451715916211 184808539288737677573874317)
        ·
          refine ⟨69303202233276629090202869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184808539288737677573874317 69303202233276629090202869)
          ·
            refine ⟨6497175209369683977206519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69303202233276629090202869 6497175209369683977206519)
            ·
              refine ⟨9745762814054525965809779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6497175209369683977206519 9745762814054525965809779)
              ·
                refine ⟨14618644221081788948714669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9745762814054525965809779 14618644221081788948714669)
                ·
                  refine ⟨5481991582905670855768001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14618644221081788948714669 5481991582905670855768001)
                  ·
                    refine ⟨4111493687179253141826001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5481991582905670855768001 4111493687179253141826001)
                    ·
                      refine ⟨3083620265384439856369501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4111493687179253141826001 3083620265384439856369501)
                      ·
                        rfl

theorem cell23_6005329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 1, 3, 2, 2].length) (baseStart_6005329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6005329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6005329 prefixEnd_6005329 := by exact prefixLift 6005329
  have htrace : WordTrace (prefixWord ++ tailWord_6005329) baseStart_6005329 baseEnd_6005329 := by
    simpa [prefixWord, tailWord_6005329, baseEnd_6005329] using wordTrace_append hprefix tailTrace_6005329
  have hstable : (prefixWord ++ tailWord_6005329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6005329).length < 2 ^ (prefixWord ++ tailWord_6005329).sum := by decide
  have hdescent : baseEnd_6005329 < baseStart_6005329 := by decide
  rcases family_descends (prefixWord ++ tailWord_6005329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6005346 : List Nat := [3, 3, 2, 3, 1, 2, 1, 2, 1, 1, 4]
def baseStart_6005346 : Nat := 118140960795 + 6005346 * 2 ^ 59
def prefixEnd_6005346 : Nat := 4983230072969 + 3 ^ 40 * 6005346 * 2
def baseEnd_6005346 : Nat := 3083628994555566289856923

theorem tailTrace_6005346 : CollatzResearch.WordTrace tailWord_6005346 prefixEnd_6005346 3083628994555566289856923 := by
  unfold tailWord_6005346
  simp only [CollatzResearch.WordTrace]
  refine ⟨54758240725416137071804973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146021975267776365524813261 54758240725416137071804973)
  ·
    refine ⟨20534340272031051401926865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54758240725416137071804973 20534340272031051401926865)
    ·
      refine ⟨15400755204023288551445149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20534340272031051401926865 15400755204023288551445149)
      ·
        refine ⟨5775283201508733206791931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15400755204023288551445149 5775283201508733206791931)
        ·
          refine ⟨8662924802263099810187897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5775283201508733206791931 8662924802263099810187897)
          ·
            refine ⟨6497193601697324857640923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8662924802263099810187897 6497193601697324857640923)
            ·
              refine ⟨9745790402545987286461385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6497193601697324857640923 9745790402545987286461385)
              ·
                refine ⟨7309342801909490464846039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9745790402545987286461385 7309342801909490464846039)
                ·
                  refine ⟨10964014202864235697269059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7309342801909490464846039 10964014202864235697269059)
                  ·
                    refine ⟨16446021304296353545903589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10964014202864235697269059 16446021304296353545903589)
                    ·
                      refine ⟨3083628994555566289856923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16446021304296353545903589 3083628994555566289856923)
                      ·
                        rfl

theorem cell23_6005346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_6005346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6005346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6005346 prefixEnd_6005346 := by exact prefixLift 6005346
  have htrace : WordTrace (prefixWord ++ tailWord_6005346) baseStart_6005346 baseEnd_6005346 := by
    simpa [prefixWord, tailWord_6005346, baseEnd_6005346] using wordTrace_append hprefix tailTrace_6005346
  have hstable : (prefixWord ++ tailWord_6005346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6005346).length < 2 ^ (prefixWord ++ tailWord_6005346).sum := by decide
  have hdescent : baseEnd_6005346 < baseStart_6005346 := by decide
  rcases family_descends (prefixWord ++ tailWord_6005346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6005349 : List Nat := [1, 3, 1, 3, 4, 2, 1, 2, 1, 2, 3]
def baseStart_6005349 : Nat := 118140960795 + 6005349 * 2 ^ 59
def prefixEnd_6005349 : Nat := 4983230072969 + 3 ^ 40 * 6005349 * 2
def baseEnd_6005349 : Nat := 3083630534997529778119409

theorem tailTrace_6005349 : CollatzResearch.WordTrace tailWord_6005349 prefixEnd_6005349 3083630534997529778119409 := by
  unfold tailWord_6005349
  simp only [CollatzResearch.WordTrace]
  refine ⟨219033072320653679799579101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146022048213769119866386067 219033072320653679799579101)
  ·
    refine ⟨82137402120245129924842163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219033072320653679799579101 82137402120245129924842163)
    ·
      refine ⟨123206103180367694887263245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82137402120245129924842163 123206103180367694887263245)
      ·
        refine ⟨46202288692637885582723717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123206103180367694887263245 46202288692637885582723717)
        ·
          refine ⟨8662929129869603546760697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46202288692637885582723717 8662929129869603546760697)
          ·
            refine ⟨6497196847402202660070523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8662929129869603546760697 6497196847402202660070523)
            ·
              refine ⟨9745795271103303990105785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6497196847402202660070523 9745795271103303990105785)
              ·
                refine ⟨7309346453327477992579339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9745795271103303990105785 7309346453327477992579339)
                ·
                  refine ⟨10964019679991216988869009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7309346453327477992579339 10964019679991216988869009)
                  ·
                    refine ⟨8223014759993412741651757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10964019679991216988869009 8223014759993412741651757)
                    ·
                      refine ⟨3083630534997529778119409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8223014759993412741651757 3083630534997529778119409)
                      ·
                        rfl

theorem cell23_6005349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 2, 1, 2, 3].length) (baseStart_6005349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6005349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6005349 prefixEnd_6005349 := by exact prefixLift 6005349
  have htrace : WordTrace (prefixWord ++ tailWord_6005349) baseStart_6005349 baseEnd_6005349 := by
    simpa [prefixWord, tailWord_6005349, baseEnd_6005349] using wordTrace_append hprefix tailTrace_6005349
  have hstable : (prefixWord ++ tailWord_6005349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6005349).length < 2 ^ (prefixWord ++ tailWord_6005349).sum := by decide
  have hdescent : baseEnd_6005349 < baseStart_6005349 := by decide
  rcases family_descends (prefixWord ++ tailWord_6005349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6005362 : List Nat := [3, 2, 1, 2, 4, 1, 1, 2, 1, 3, 3]
def baseStart_6005362 : Nat := 118140960795 + 6005362 * 2 ^ 59
def prefixEnd_6005362 : Nat := 4983230072969 + 3 ^ 40 * 6005362 * 2
def baseEnd_6005362 : Nat := 3083637210246038227256849

theorem tailTrace_6005362 : CollatzResearch.WordTrace tailWord_6005362 prefixEnd_6005362 3083637210246038227256849 := by
  unfold tailWord_6005362
  simp only [CollatzResearch.WordTrace]
  refine ⟨54758386617401645754950585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146022364313071055346534893 54758386617401645754950585)
  ·
    refine ⟨41068789963051234316212939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54758386617401645754950585 41068789963051234316212939)
    ·
      refine ⟨61603184944576851474319409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41068789963051234316212939 61603184944576851474319409)
      ·
        refine ⟨46202388708432638605739557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61603184944576851474319409 46202388708432638605739557)
        ·
          refine ⟨8662947882831119738576167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46202388708432638605739557 8662947882831119738576167)
          ·
            refine ⟨12994421824246679607864251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8662947882831119738576167 12994421824246679607864251)
            ·
              refine ⟨19491632736370019411796377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12994421824246679607864251 19491632736370019411796377)
              ·
                refine ⟨14618724552277514558847283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19491632736370019411796377 14618724552277514558847283)
                ·
                  refine ⟨21928086828416271838270925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14618724552277514558847283 21928086828416271838270925)
                  ·
                    refine ⟨8223032560656101939351597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21928086828416271838270925 8223032560656101939351597)
                    ·
                      refine ⟨3083637210246038227256849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8223032560656101939351597 3083637210246038227256849)
                      ·
                        rfl

theorem cell23_6005362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 2, 1, 3, 3].length) (baseStart_6005362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6005362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6005362 prefixEnd_6005362 := by exact prefixLift 6005362
  have htrace : WordTrace (prefixWord ++ tailWord_6005362) baseStart_6005362 baseEnd_6005362 := by
    simpa [prefixWord, tailWord_6005362, baseEnd_6005362] using wordTrace_append hprefix tailTrace_6005362
  have hstable : (prefixWord ++ tailWord_6005362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6005362).length < 2 ^ (prefixWord ++ tailWord_6005362).sum := by decide
  have hdescent : baseEnd_6005362 < baseStart_6005362 := by decide
  rcases family_descends (prefixWord ++ tailWord_6005362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6005366 : List Nat := [5, 1, 1, 2, 3, 1, 3, 1, 1, 2, 3]
def baseStart_6005366 : Nat := 118140960795 + 6005366 * 2 ^ 59
def prefixEnd_6005366 : Nat := 4983230072969 + 3 ^ 40 * 6005366 * 2
def baseEnd_6005366 : Nat := 3083639264168656211606831

theorem tailTrace_6005366 : CollatzResearch.WordTrace tailWord_6005366 prefixEnd_6005366 3083639264168656211606831 := by
  unfold tailWord_6005366
  simp only [CollatzResearch.WordTrace]
  refine ⟨13689605772599505731434247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 146022461574394727801965301 13689605772599505731434247)
  ·
    refine ⟨20534408658899258597151371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13689605772599505731434247 20534408658899258597151371)
    ·
      refine ⟨30801612988348887895727057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20534408658899258597151371 30801612988348887895727057)
      ·
        refine ⟨23101209741261665921795293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30801612988348887895727057 23101209741261665921795293)
        ·
          refine ⟨8662953652973124720673235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23101209741261665921795293 8662953652973124720673235)
          ·
            refine ⟨12994430479459687081009853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8662953652973124720673235 12994430479459687081009853)
            ·
              refine ⟨4872911429797382655378695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12994430479459687081009853 4872911429797382655378695)
              ·
                refine ⟨7309367144696073983068043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4872911429797382655378695 7309367144696073983068043)
                ·
                  refine ⟨10964050717044110974602065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7309367144696073983068043 10964050717044110974602065)
                  ·
                    refine ⟨8223038037783083230951549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10964050717044110974602065 8223038037783083230951549)
                    ·
                      refine ⟨3083639264168656211606831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8223038037783083230951549 3083639264168656211606831)
                      ·
                        rfl

theorem cell23_6005366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 3, 1, 1, 2, 3].length) (baseStart_6005366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6005366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6005366 prefixEnd_6005366 := by exact prefixLift 6005366
  have htrace : WordTrace (prefixWord ++ tailWord_6005366) baseStart_6005366 baseEnd_6005366 := by
    simpa [prefixWord, tailWord_6005366, baseEnd_6005366] using wordTrace_append hprefix tailTrace_6005366
  have hstable : (prefixWord ++ tailWord_6005366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6005366).length < 2 ^ (prefixWord ++ tailWord_6005366).sum := by decide
  have hdescent : baseEnd_6005366 < baseStart_6005366 := by decide
  rcases family_descends (prefixWord ++ tailWord_6005366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6005372 : List Nat := [2, 2, 2, 1, 1, 2, 2, 5, 1, 3, 2]
def baseStart_6005372 : Nat := 118140960795 + 6005372 * 2 ^ 59
def prefixEnd_6005372 : Nat := 4983230072969 + 3 ^ 40 * 6005372 * 2
def baseEnd_6005372 : Nat := 3083642345052583188131803

theorem tailTrace_6005372 : CollatzResearch.WordTrace tailWord_6005372 prefixEnd_6005372 3083642345052583188131803 := by
  unfold tailWord_6005372
  simp only [CollatzResearch.WordTrace]
  refine ⟨109516955599785177363833185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146022607466380236485110913 109516955599785177363833185)
  ·
    refine ⟨82137716699838883022874889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109516955599785177363833185 82137716699838883022874889)
    ·
      refine ⟨61603287524879162267156167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82137716699838883022874889 61603287524879162267156167)
      ·
        refine ⟨92404931287318743400734251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61603287524879162267156167 92404931287318743400734251)
        ·
          refine ⟨138607396930978115101101377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92404931287318743400734251 138607396930978115101101377)
          ·
            refine ⟨103955547698233586325826033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138607396930978115101101377 103955547698233586325826033)
            ·
              refine ⟨77966660773675189744369525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103955547698233586325826033 77966660773675189744369525)
              ·
                refine ⟨7309374447532049038534643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77966660773675189744369525 7309374447532049038534643)
                ·
                  refine ⟨10964061671298073557801965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7309374447532049038534643 10964061671298073557801965)
                  ·
                    refine ⟨4111523126736777584175737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10964061671298073557801965 4111523126736777584175737)
                    ·
                      refine ⟨3083642345052583188131803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4111523126736777584175737 3083642345052583188131803)
                      ·
                        rfl

theorem cell23_6005372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 5, 1, 3, 2].length) (baseStart_6005372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6005372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6005372 prefixEnd_6005372 := by exact prefixLift 6005372
  have htrace : WordTrace (prefixWord ++ tailWord_6005372) baseStart_6005372 baseEnd_6005372 := by
    simpa [prefixWord, tailWord_6005372, baseEnd_6005372] using wordTrace_append hprefix tailTrace_6005372
  have hstable : (prefixWord ++ tailWord_6005372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6005372).length < 2 ^ (prefixWord ++ tailWord_6005372).sum := by decide
  have hdescent : baseEnd_6005372 < baseStart_6005372 := by decide
  rcases family_descends (prefixWord ++ tailWord_6005372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6005385 : List Nat := [1, 2, 1, 1, 4, 1, 1, 1, 5, 4, 2]
def baseStart_6005385 : Nat := 118140960795 + 6005385 * 2 ^ 59
def prefixEnd_6005385 : Nat := 4983230072969 + 3 ^ 40 * 6005385 * 2
def baseEnd_6005385 : Nat := 3083649020301091637269243

theorem tailTrace_6005385 : CollatzResearch.WordTrace tailWord_6005385 prefixEnd_6005385 3083649020301091637269243 := by
  unfold tailWord_6005385
  simp only [CollatzResearch.WordTrace]
  refine ⟨219034385348523257947889609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146022923565682171965259739 219034385348523257947889609)
  ·
    refine ⟨164275789011392443460917207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219034385348523257947889609 164275789011392443460917207)
    ·
      refine ⟨246413683517088665191375811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164275789011392443460917207 246413683517088665191375811)
      ·
        refine ⟨369620525275632997787063717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246413683517088665191375811 369620525275632997787063717)
        ·
          refine ⟨69303848489181187085074447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 369620525275632997787063717 69303848489181187085074447)
          ·
            refine ⟨103955772733771780627611671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69303848489181187085074447 103955772733771780627611671)
            ·
              refine ⟨155933659100657670941417507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103955772733771780627611671 155933659100657670941417507)
              ·
                refine ⟨233900488650986506412126261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155933659100657670941417507 233900488650986506412126261)
                ·
                  refine ⟨21928170811029984976136837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 233900488650986506412126261 21928170811029984976136837)
                  ·
                    refine ⟨4111532027068122183025657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21928170811029984976136837 4111532027068122183025657)
                    ·
                      refine ⟨3083649020301091637269243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4111532027068122183025657 3083649020301091637269243)
                      ·
                        rfl

theorem cell23_6005385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 5, 4, 2].length) (baseStart_6005385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6005385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6005385 prefixEnd_6005385 := by exact prefixLift 6005385
  have htrace : WordTrace (prefixWord ++ tailWord_6005385) baseStart_6005385 baseEnd_6005385 := by
    simpa [prefixWord, tailWord_6005385, baseEnd_6005385] using wordTrace_append hprefix tailTrace_6005385
  have hstable : (prefixWord ++ tailWord_6005385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6005385).length < 2 ^ (prefixWord ++ tailWord_6005385).sum := by decide
  have hdescent : baseEnd_6005385 < baseStart_6005385 := by decide
  rcases family_descends (prefixWord ++ tailWord_6005385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6005388 : List Nat := [2, 2, 1, 2, 1, 1, 2, 2, 4, 1, 5]
def baseStart_6005388 : Nat := 118140960795 + 6005388 * 2 ^ 59
def prefixEnd_6005388 : Nat := 4983230072969 + 3 ^ 40 * 6005388 * 2
def baseEnd_6005388 : Nat := 3083650560743055125531729

theorem tailTrace_6005388 : CollatzResearch.WordTrace tailWord_6005388 prefixEnd_6005388 3083650560743055125531729 := by
  unfold tailWord_6005388
  simp only [CollatzResearch.WordTrace]
  refine ⟨109517247383756194730124409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146022996511674926306832545 109517247383756194730124409)
  ·
    refine ⟨82137935537817146047593307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109517247383756194730124409 82137935537817146047593307)
    ·
      refine ⟨123206903306725719071389961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82137935537817146047593307 123206903306725719071389961)
      ·
        refine ⟨92405177480044289303542471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123206903306725719071389961 92405177480044289303542471)
        ·
          refine ⟨138607766220066433955313707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92405177480044289303542471 138607766220066433955313707)
          ·
            refine ⟨207911649330099650932970561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138607766220066433955313707 207911649330099650932970561)
            ·
              refine ⟨155933736997574738199727921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 207911649330099650932970561 155933736997574738199727921)
              ·
                refine ⟨116950302748181053649795941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 155933736997574738199727921 116950302748181053649795941)
                ·
                  refine ⟨21928181765283947559336739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 116950302748181053649795941 21928181765283947559336739)
                  ·
                    refine ⟨32892272647925921339005109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21928181765283947559336739 32892272647925921339005109)
                    ·
                      refine ⟨3083650560743055125531729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32892272647925921339005109 3083650560743055125531729)
                      ·
                        rfl

theorem cell23_6005388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 4, 1, 5].length) (baseStart_6005388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6005388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6005388 prefixEnd_6005388 := by exact prefixLift 6005388
  have htrace : WordTrace (prefixWord ++ tailWord_6005388) baseStart_6005388 baseEnd_6005388 := by
    simpa [prefixWord, tailWord_6005388, baseEnd_6005388] using wordTrace_append hprefix tailTrace_6005388
  have hstable : (prefixWord ++ tailWord_6005388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6005388).length < 2 ^ (prefixWord ++ tailWord_6005388).sum := by decide
  have hdescent : baseEnd_6005388 < baseStart_6005388 := by decide
  rcases family_descends (prefixWord ++ tailWord_6005388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6005430 : List Nat := [5, 1, 3, 1, 3, 1, 1, 2, 2, 1, 3]
def baseStart_6005430 : Nat := 118140960795 + 6005430 * 2 ^ 59
def prefixEnd_6005430 : Nat := 4983230072969 + 3 ^ 40 * 6005430 * 2
def baseEnd_6005430 : Nat := 3083672126930543961206537

theorem tailTrace_6005430 : CollatzResearch.WordTrace tailWord_6005430 prefixEnd_6005430 3083672126930543961206537 := by
  unfold tailWord_6005430
  simp only [CollatzResearch.WordTrace]
  refine ⟨13689751664585014414579859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 146024017755573487088851829 13689751664585014414579859)
  ·
    refine ⟨20534627496877521621869789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13689751664585014414579859 20534627496877521621869789)
    ·
      refine ⟨7700485311329070608201171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20534627496877521621869789 7700485311329070608201171)
      ·
        refine ⟨11550727966993605912301757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7700485311329070608201171 11550727966993605912301757)
        ·
          refine ⟨4331522987622602217113159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11550727966993605912301757 4331522987622602217113159)
          ·
            refine ⟨6497284481433903325669739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4331522987622602217113159 6497284481433903325669739)
            ·
              refine ⟨9745926722150854988504609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6497284481433903325669739 9745926722150854988504609)
              ·
                refine ⟨7309445041613141241378457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9745926722150854988504609 7309445041613141241378457)
                ·
                  refine ⟨5482083781209855931033843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7309445041613141241378457 5482083781209855931033843)
                  ·
                    refine ⟨8223125671814783896550765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5482083781209855931033843 8223125671814783896550765)
                    ·
                      refine ⟨3083672126930543961206537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8223125671814783896550765 3083672126930543961206537)
                      ·
                        rfl

theorem cell23_6005430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_6005430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6005430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6005430 prefixEnd_6005430 := by exact prefixLift 6005430
  have htrace : WordTrace (prefixWord ++ tailWord_6005430) baseStart_6005430 baseEnd_6005430 := by
    simpa [prefixWord, tailWord_6005430, baseEnd_6005430] using wordTrace_append hprefix tailTrace_6005430
  have hstable : (prefixWord ++ tailWord_6005430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6005430).length < 2 ^ (prefixWord ++ tailWord_6005430).sum := by decide
  have hdescent : baseEnd_6005430 < baseStart_6005430 := by decide
  rcases family_descends (prefixWord ++ tailWord_6005430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6005452 : List Nat := [2, 2, 1, 5, 1, 1, 2, 1, 2, 3, 3]
def baseStart_6005452 : Nat := 118140960795 + 6005452 * 2 ^ 59
def prefixEnd_6005452 : Nat := 4983230072969 + 3 ^ 40 * 6005452 * 2
def baseEnd_6005452 : Nat := 3083683423504942875131435

theorem tailTrace_6005452 : CollatzResearch.WordTrace tailWord_6005452 prefixEnd_6005452 3083683423504942875131435 := by
  unfold tailWord_6005452
  simp only [CollatzResearch.WordTrace]
  refine ⟨109518414519640264195289305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146024552692853685593719073 109518414519640264195289305)
  ·
    refine ⟨82138810889730198146466979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109518414519640264195289305 82138810889730198146466979)
    ·
      refine ⟨123208216334595297219700469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82138810889730198146466979 123208216334595297219700469)
      ·
        refine ⟨11550770281368309114346919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 123208216334595297219700469 11550770281368309114346919)
        ·
          refine ⟨17326155422052463671520379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11550770281368309114346919 17326155422052463671520379)
          ·
            refine ⟨25989233133078695507280569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17326155422052463671520379 25989233133078695507280569)
            ·
              refine ⟨19491924849809021630460427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25989233133078695507280569 19491924849809021630460427)
              ·
                refine ⟨29237887274713532445690641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19491924849809021630460427 29237887274713532445690641)
                ·
                  refine ⟨21928415456035149334267981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29237887274713532445690641 21928415456035149334267981)
                  ·
                    refine ⟨8223155796013181000350493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21928415456035149334267981 8223155796013181000350493)
                    ·
                      refine ⟨3083683423504942875131435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8223155796013181000350493 3083683423504942875131435)
                      ·
                        rfl

theorem cell23_6005452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_6005452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6005452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6005452 prefixEnd_6005452 := by exact prefixLift 6005452
  have htrace : WordTrace (prefixWord ++ tailWord_6005452) baseStart_6005452 baseEnd_6005452 := by
    simpa [prefixWord, tailWord_6005452, baseEnd_6005452] using wordTrace_append hprefix tailTrace_6005452
  have hstable : (prefixWord ++ tailWord_6005452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6005452).length < 2 ^ (prefixWord ++ tailWord_6005452).sum := by decide
  have hdescent : baseEnd_6005452 < baseStart_6005452 := by decide
  rcases family_descends (prefixWord ++ tailWord_6005452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6005453 : List Nat := [1, 6, 2, 1, 2, 2, 1, 1, 1, 4, 2]
def baseStart_6005453 : Nat := 118140960795 + 6005453 * 2 ^ 59
def prefixEnd_6005453 : Nat := 4983230072969 + 3 ^ 40 * 6005453 * 2
def baseEnd_6005453 : Nat := 3083683936985597371218931

theorem tailTrace_6005453 : CollatzResearch.WordTrace tailWord_6005453 prefixEnd_6005453 3083683936985597371218931 := by
  unfold tailWord_6005453
  simp only [CollatzResearch.WordTrace]
  refine ⟨219036865512276905561365013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146024577008184603707576675 219036865512276905561365013)
  ·
    refine ⟨10267353070887979948188985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 219036865512276905561365013 10267353070887979948188985)
    ·
      refine ⟨7700514803165984961141739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10267353070887979948188985 7700514803165984961141739)
      ·
        refine ⟨11550772204748977441712609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7700514803165984961141739 11550772204748977441712609)
        ·
          refine ⟨8663079153561733081284457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11550772204748977441712609 8663079153561733081284457)
          ·
            refine ⟨6497309365171299810963343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8663079153561733081284457 6497309365171299810963343)
            ·
              refine ⟨9745964047756949716445015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6497309365171299810963343 9745964047756949716445015)
              ·
                refine ⟨14618946071635424574667523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9745964047756949716445015 14618946071635424574667523)
                ·
                  refine ⟨21928419107453136862001285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14618946071635424574667523 21928419107453136862001285)
                  ·
                    refine ⟨4111578582647463161625241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21928419107453136862001285 4111578582647463161625241)
                    ·
                      refine ⟨3083683936985597371218931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4111578582647463161625241 3083683936985597371218931)
                      ·
                        rfl

theorem cell23_6005453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_6005453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6005453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6005453 prefixEnd_6005453 := by exact prefixLift 6005453
  have htrace : WordTrace (prefixWord ++ tailWord_6005453) baseStart_6005453 baseEnd_6005453 := by
    simpa [prefixWord, tailWord_6005453, baseEnd_6005453] using wordTrace_append hprefix tailTrace_6005453
  have hstable : (prefixWord ++ tailWord_6005453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6005453).length < 2 ^ (prefixWord ++ tailWord_6005453).sum := by decide
  have hdescent : baseEnd_6005453 < baseStart_6005453 := by decide
  rcases family_descends (prefixWord ++ tailWord_6005453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6005493 : List Nat := [1, 3, 6, 1, 2, 1, 1, 1, 7]
def baseStart_6005493 : Nat := 118140960795 + 6005493 * 2 ^ 59
def prefixEnd_6005493 : Nat := 4983230072969 + 3 ^ 40 * 6005493 * 2
def baseEnd_6005493 : Nat := 342633830690197468302083

theorem tailTrace_6005493 : CollatzResearch.WordTrace tailWord_6005493 prefixEnd_6005493 342633830690197468302083 := by
  unfold tailWord_6005493
  simp only [CollatzResearch.WordTrace]
  refine ⟨219038324432131992392821133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146025549621421328261880755 219038324432131992392821133)
  ·
    refine ⟨82139371662049497147307925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219038324432131992392821133 82139371662049497147307925)
    ·
      refine ⟨3850283046658570178780059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 82139371662049497147307925 3850283046658570178780059)
      ·
        refine ⟨5775424569987855268170089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3850283046658570178780059 5775424569987855268170089)
        ·
          refine ⟨4331568427490891451127567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5775424569987855268170089 4331568427490891451127567)
          ·
            refine ⟨6497352641236337176691351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4331568427490891451127567 6497352641236337176691351)
            ·
              refine ⟨9746028961854505765037027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6497352641236337176691351 9746028961854505765037027)
              ·
                refine ⟨14619043442781758647555541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9746028961854505765037027 14619043442781758647555541)
                ·
                  refine ⟨342633830690197468302083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14619043442781758647555541 342633830690197468302083)
                  ·
                    rfl

theorem cell23_6005493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 1, 7].length) (baseStart_6005493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6005493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6005493 prefixEnd_6005493 := by exact prefixLift 6005493
  have htrace : WordTrace (prefixWord ++ tailWord_6005493) baseStart_6005493 baseEnd_6005493 := by
    simpa [prefixWord, tailWord_6005493, baseEnd_6005493] using wordTrace_append hprefix tailTrace_6005493
  have hstable : (prefixWord ++ tailWord_6005493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6005493).length < 2 ^ (prefixWord ++ tailWord_6005493).sum := by decide
  have hdescent : baseEnd_6005493 < baseStart_6005493 := by decide
  rcases family_descends (prefixWord ++ tailWord_6005493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6005595 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 9, 2, 4]
def baseStart_6005595 : Nat := 118140960795 + 6005595 * 2 ^ 59
def prefixEnd_6005595 : Nat := 4983230072969 + 3 ^ 40 * 6005595 * 2
def baseEnd_6005595 : Nat := 3083756851238535815643277

theorem tailTrace_6005595 : CollatzResearch.WordTrace tailWord_6005595 prefixEnd_6005595 3083756851238535815643277 := by
  unfold tailWord_6005595
  simp only [CollatzResearch.WordTrace]
  refine ⟨219042044677762463813034239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146028029785174975875356159 219042044677762463813034239)
  ·
    refine ⟨328563067016643695719551359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219042044677762463813034239 328563067016643695719551359)
    ·
      refine ⟨492844600524965543579327039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328563067016643695719551359 492844600524965543579327039)
      ·
        refine ⟨739266900787448315368990559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 492844600524965543579327039 739266900787448315368990559)
        ·
          refine ⟨1108900351181172473053485839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 739266900787448315368990559 1108900351181172473053485839)
          ·
            refine ⟨1663350526771758709580228759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1108900351181172473053485839 1663350526771758709580228759)
            ·
              refine ⟨2495025790157638064370343139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1663350526771758709580228759 2495025790157638064370343139)
              ·
                refine ⟨3742538685236457096555514709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2495025790157638064370343139 3742538685236457096555514709)
                ·
                  refine ⟨21928937608807365800129969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 3742538685236457096555514709 21928937608807365800129969)
                  ·
                    refine ⟨16446703206605524350097477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21928937608807365800129969 16446703206605524350097477)
                    ·
                      refine ⟨3083756851238535815643277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16446703206605524350097477 3083756851238535815643277)
                      ·
                        rfl

theorem cell23_6005595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 2, 4].length) (baseStart_6005595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6005595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6005595 prefixEnd_6005595 := by exact prefixLift 6005595
  have htrace : WordTrace (prefixWord ++ tailWord_6005595) baseStart_6005595 baseEnd_6005595 := by
    simpa [prefixWord, tailWord_6005595, baseEnd_6005595] using wordTrace_append hprefix tailTrace_6005595
  have hstable : (prefixWord ++ tailWord_6005595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6005595).length < 2 ^ (prefixWord ++ tailWord_6005595).sum := by decide
  have hdescent : baseEnd_6005595 < baseStart_6005595 := by decide
  rcases family_descends (prefixWord ++ tailWord_6005595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6005596 : List Nat := [2, 2, 4, 2, 1, 1, 4, 1, 1, 5]
def baseStart_6005596 : Nat := 118140960795 + 6005596 * 2 ^ 59
def prefixEnd_6005596 : Nat := 4983230072969 + 3 ^ 40 * 6005596 * 2
def baseEnd_6005596 : Nat := 1027919121573063437243591

theorem tailTrace_6005596 : CollatzResearch.WordTrace tailWord_6005596 prefixEnd_6005596 1027919121573063437243591 := by
  unfold tailWord_6005596
  simp only [CollatzResearch.WordTrace]
  refine ⟨109521040575379420491910321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146028054100505893989213761 109521040575379420491910321)
  ·
    refine ⟨82140780431534565368932741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109521040575379420491910321 82140780431534565368932741)
    ·
      refine ⟨15401396330912731006674889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82140780431534565368932741 15401396330912731006674889)
      ·
        refine ⟨11551047248184548255006167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15401396330912731006674889 11551047248184548255006167)
        ·
          refine ⟨17326570872276822382509251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11551047248184548255006167 17326570872276822382509251)
          ·
            refine ⟨25989856308415233573763877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17326570872276822382509251 25989856308415233573763877)
            ·
              refine ⟨4873098057827856295080727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25989856308415233573763877 4873098057827856295080727)
              ·
                refine ⟨7309647086741784442621091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4873098057827856295080727 7309647086741784442621091)
                ·
                  refine ⟨10964470630112676663931637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7309647086741784442621091 10964470630112676663931637)
                  ·
                    refine ⟨1027919121573063437243591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10964470630112676663931637 1027919121573063437243591)
                    ·
                      rfl

theorem cell23_6005596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_6005596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6005596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6005596 prefixEnd_6005596 := by exact prefixLift 6005596
  have htrace : WordTrace (prefixWord ++ tailWord_6005596) baseStart_6005596 baseEnd_6005596 := by
    simpa [prefixWord, tailWord_6005596, baseEnd_6005596] using wordTrace_append hprefix tailTrace_6005596
  have hstable : (prefixWord ++ tailWord_6005596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6005596).length < 2 ^ (prefixWord ++ tailWord_6005596).sum := by decide
  have hdescent : baseEnd_6005596 < baseStart_6005596 := by decide
  rcases family_descends (prefixWord ++ tailWord_6005596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6005599 : List Nat := [1, 1, 2, 3, 1, 3, 1, 2, 5, 2, 2]
def baseStart_6005599 : Nat := 118140960795 + 6005599 * 2 ^ 59
def prefixEnd_6005599 : Nat := 4983230072969 + 3 ^ 40 * 6005599 * 2
def baseEnd_6005599 : Nat := 3083758905161153799993259

theorem tailTrace_6005599 : CollatzResearch.WordTrace tailWord_6005599 prefixEnd_6005599 3083758905161153799993259 := by
  unfold tailWord_6005599
  simp only [CollatzResearch.WordTrace]
  refine ⟨219042190569747972496179851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146028127046498648330786567 219042190569747972496179851)
  ·
    refine ⟨328563285854621958744269777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219042190569747972496179851 328563285854621958744269777)
    ·
      refine ⟨246422464390966469058202333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 328563285854621958744269777 246422464390966469058202333)
      ·
        refine ⟨92408424146612425896825875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 246422464390966469058202333 92408424146612425896825875)
        ·
          refine ⟨138612636219918638845238813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92408424146612425896825875 138612636219918638845238813)
          ·
            refine ⟨51979738582469489566964555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138612636219918638845238813 51979738582469489566964555)
            ·
              refine ⟨77969607873704234350446833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51979738582469489566964555 77969607873704234350446833)
              ·
                refine ⟨58477205905278175762835125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77969607873704234350446833 58477205905278175762835125)
                ·
                  refine ⟨5482238053619828977765793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58477205905278175762835125 5482238053619828977765793)
                  ·
                    refine ⟨4111678540214871733324345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5482238053619828977765793 4111678540214871733324345)
                    ·
                      refine ⟨3083758905161153799993259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4111678540214871733324345 3083758905161153799993259)
                      ·
                        rfl

theorem cell23_6005599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 5, 2, 2].length) (baseStart_6005599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6005599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6005599 prefixEnd_6005599 := by exact prefixLift 6005599
  have htrace : WordTrace (prefixWord ++ tailWord_6005599) baseStart_6005599 baseEnd_6005599 := by
    simpa [prefixWord, tailWord_6005599, baseEnd_6005599] using wordTrace_append hprefix tailTrace_6005599
  have hstable : (prefixWord ++ tailWord_6005599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6005599).length < 2 ^ (prefixWord ++ tailWord_6005599).sum := by decide
  have hdescent : baseEnd_6005599 < baseStart_6005599 := by decide
  rcases family_descends (prefixWord ++ tailWord_6005599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6005632 : List Nat := [2, 1, 1, 2, 1, 2, 2, 5, 1, 3, 3]
def baseStart_6005632 : Nat := 118140960795 + 6005632 * 2 ^ 59
def prefixEnd_6005632 : Nat := 4983230072969 + 3 ^ 40 * 6005632 * 2
def baseEnd_6005632 : Nat := 3083775850022752170880607

theorem tailTrace_6005632 : CollatzResearch.WordTrace tailWord_6005632 prefixEnd_6005632 3083775850022752170880607 := by
  unfold tailWord_6005632
  simp only [CollatzResearch.WordTrace]
  refine ⟨109521697089314209566065575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146028929452418946088087433 109521697089314209566065575)
  ·
    refine ⟨164282545633971314349098363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109521697089314209566065575 164282545633971314349098363)
    ·
      refine ⟨246423818450956971523647545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164282545633971314349098363 246423818450956971523647545)
      ·
        refine ⟨184817863838217728642735659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246423818450956971523647545 184817863838217728642735659)
        ·
          refine ⟨277226795757326592964103489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184817863838217728642735659 277226795757326592964103489)
          ·
            refine ⟨207920096817994944723077617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 277226795757326592964103489 207920096817994944723077617)
            ·
              refine ⟨155940072613496208542308213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 207920096817994944723077617 155940072613496208542308213)
              ·
                refine ⟨14619381807515269550841395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 155940072613496208542308213 14619381807515269550841395)
                ·
                  refine ⟨21929072711272904326262093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14619381807515269550841395 21929072711272904326262093)
                  ·
                    refine ⟨8223402266727339122348285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21929072711272904326262093 8223402266727339122348285)
                    ·
                      refine ⟨3083775850022752170880607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8223402266727339122348285 3083775850022752170880607)
                      ·
                        rfl

theorem cell23_6005632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 5, 1, 3, 3].length) (baseStart_6005632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6005632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6005632 prefixEnd_6005632 := by exact prefixLift 6005632
  have htrace : WordTrace (prefixWord ++ tailWord_6005632) baseStart_6005632 baseEnd_6005632 := by
    simpa [prefixWord, tailWord_6005632, baseEnd_6005632] using wordTrace_append hprefix tailTrace_6005632
  have hstable : (prefixWord ++ tailWord_6005632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6005632).length < 2 ^ (prefixWord ++ tailWord_6005632).sum := by decide
  have hdescent : baseEnd_6005632 < baseStart_6005632 := by decide
  rcases family_descends (prefixWord ++ tailWord_6005632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6005639 : List Nat := [1, 1, 4, 2, 3, 3, 2, 7]
def baseStart_6005639 : Nat := 118140960795 + 6005639 * 2 ^ 59
def prefixEnd_6005639 : Nat := 4983230072969 + 3 ^ 40 * 6005639 * 2
def baseEnd_6005639 : Nat := 114214053495827171981225

theorem tailTrace_6005639 : CollatzResearch.WordTrace tailWord_6005639 prefixEnd_6005639 114214053495827171981225 := by
  unfold tailWord_6005639
  simp only [CollatzResearch.WordTrace]
  refine ⟨219043649489603059327635971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146029099659735372885090647 219043649489603059327635971)
  ·
    refine ⟨328565474234404588991453957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219043649489603059327635971 328565474234404588991453957)
    ·
      refine ⟨61606026418950860435897617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 328565474234404588991453957 61606026418950860435897617)
      ·
        refine ⟨46204519814213145326923213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61606026418950860435897617 46204519814213145326923213)
        ·
          refine ⟨17326694930329929497596205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46204519814213145326923213 17326694930329929497596205)
          ·
            refine ⟨6497510598873723561598577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17326694930329929497596205 6497510598873723561598577)
            ·
              refine ⟨4873132949155292671198933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6497510598873723561598577 4873132949155292671198933)
              ·
                refine ⟨114214053495827171981225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4873132949155292671198933 114214053495827171981225)
                ·
                  rfl

theorem cell23_6005639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 2, 7].length) (baseStart_6005639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6005639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6005639 prefixEnd_6005639 := by exact prefixLift 6005639
  have htrace : WordTrace (prefixWord ++ tailWord_6005639) baseStart_6005639 baseEnd_6005639 := by
    simpa [prefixWord, tailWord_6005639, baseEnd_6005639] using wordTrace_append hprefix tailTrace_6005639
  have hstable : (prefixWord ++ tailWord_6005639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6005639).length < 2 ^ (prefixWord ++ tailWord_6005639).sum := by decide
  have hdescent : baseEnd_6005639 < baseStart_6005639 := by decide
  rcases family_descends (prefixWord ++ tailWord_6005639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6005666 : List Nat := [3, 3, 1, 2, 2, 1, 2, 1, 4, 1, 3]
def baseStart_6005666 : Nat := 118140960795 + 6005666 * 2 ^ 59
def prefixEnd_6005666 : Nat := 4983230072969 + 3 ^ 40 * 6005666 * 2
def baseEnd_6005666 : Nat := 3083793308365005037855451

theorem tailTrace_6005666 : CollatzResearch.WordTrace tailWord_6005666 prefixEnd_6005666 3083793308365005037855451 := by
  unfold tailWord_6005666
  simp only [CollatzResearch.WordTrace]
  refine ⟨54761158565126310734717213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146029756173670161959245901 54761158565126310734717213)
  ·
    refine ⟨20535434461922366525518955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54761158565126310734717213 20535434461922366525518955)
    ·
      refine ⟨30803151692883549788278433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20535434461922366525518955 30803151692883549788278433)
      ·
        refine ⟨23102363769662662341208825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30803151692883549788278433 23102363769662662341208825)
        ·
          refine ⟨17326772827246996755906619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23102363769662662341208825 17326772827246996755906619)
          ·
            refine ⟨25990159240870495133859929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17326772827246996755906619 25990159240870495133859929)
            ·
              refine ⟨19492619430652871350394947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25990159240870495133859929 19492619430652871350394947)
              ·
                refine ⟨29238929145979307025592421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19492619430652871350394947 29238929145979307025592421)
                ·
                  refine ⟨5482299214871120067298579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29238929145979307025592421 5482299214871120067298579)
                  ·
                    refine ⟨8223448822306680100947869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5482299214871120067298579 8223448822306680100947869)
                    ·
                      refine ⟨3083793308365005037855451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8223448822306680100947869 3083793308365005037855451)
                      ·
                        rfl

theorem cell23_6005666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_6005666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6005666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6005666 prefixEnd_6005666 := by exact prefixLift 6005666
  have htrace : WordTrace (prefixWord ++ tailWord_6005666) baseStart_6005666 baseEnd_6005666 := by
    simpa [prefixWord, tailWord_6005666, baseEnd_6005666] using wordTrace_append hprefix tailTrace_6005666
  have hstable : (prefixWord ++ tailWord_6005666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6005666).length < 2 ^ (prefixWord ++ tailWord_6005666).sum := by decide
  have hdescent : baseEnd_6005666 < baseStart_6005666 := by decide
  rcases family_descends (prefixWord ++ tailWord_6005666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6005677 : List Nat := [1, 5, 2, 3, 2, 1, 2, 1, 2, 4]
def baseStart_6005677 : Nat := 118140960795 + 6005677 * 2 ^ 59
def prefixEnd_6005677 : Nat := 4983230072969 + 3 ^ 40 * 6005677 * 2
def baseEnd_6005677 : Nat := 1027932985550734831605967

theorem tailTrace_6005677 : CollatzResearch.WordTrace tailWord_6005677 prefixEnd_6005677 1027932985550734831605967 := by
  unfold tailWord_6005677
  simp only [CollatzResearch.WordTrace]
  refine ⟨219045035463465391817519285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146030023642310261211679523 219045035463465391817519285)
  ·
    refine ⟨20535472074699880482892433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 219045035463465391817519285 20535472074699880482892433)
    ·
      refine ⟨15401604056024910362169325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20535472074699880482892433 15401604056024910362169325)
      ·
        refine ⟨5775601521009341385813497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15401604056024910362169325 5775601521009341385813497)
        ·
          refine ⟨4331701140757006039360123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5775601521009341385813497 4331701140757006039360123)
          ·
            refine ⟨6497551711135509059040185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4331701140757006039360123 6497551711135509059040185)
            ·
              refine ⟨4873163783351631794280139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6497551711135509059040185 4873163783351631794280139)
              ·
                refine ⟨7309745675027447691420209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4873163783351631794280139 7309745675027447691420209)
                ·
                  refine ⟨5482309256270585768565157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7309745675027447691420209 5482309256270585768565157)
                  ·
                    refine ⟨1027932985550734831605967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5482309256270585768565157 1027932985550734831605967)
                    ·
                      rfl

theorem cell23_6005677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_6005677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6005677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6005677 prefixEnd_6005677 := by exact prefixLift 6005677
  have htrace : WordTrace (prefixWord ++ tailWord_6005677) baseStart_6005677 baseEnd_6005677 := by
    simpa [prefixWord, tailWord_6005677, baseEnd_6005677] using wordTrace_append hprefix tailTrace_6005677
  have hstable : (prefixWord ++ tailWord_6005677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6005677).length < 2 ^ (prefixWord ++ tailWord_6005677).sum := by decide
  have hdescent : baseEnd_6005677 < baseStart_6005677 := by decide
  rcases family_descends (prefixWord ++ tailWord_6005677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6005746 : List Nat := [3, 2, 1, 5, 1, 1, 1, 2, 7]
def baseStart_6005746 : Nat := 118140960795 + 6005746 * 2 ^ 59
def prefixEnd_6005746 : Nat := 4983230072969 + 3 ^ 40 * 6005746 * 2
def baseEnd_6005746 : Nat := 342648265201929413872787

theorem tailTrace_6005746 : CollatzResearch.WordTrace tailWord_6005746 prefixEnd_6005746 342648265201929413872787 := by
  unfold tailWord_6005746
  simp only [CollatzResearch.WordTrace]
  refine ⟨54761888025053854150445273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146031701400143611067854061 54761888025053854150445273)
  ·
    refine ⟨41071416018790390612833955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54761888025053854150445273 41071416018790390612833955)
    ·
      refine ⟨61607124028185585919250933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41071416018790390612833955 61607124028185585919250933)
      ·
        refine ⟨5775667877642398679929775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61607124028185585919250933 5775667877642398679929775)
        ·
          refine ⟨8663501816463598019894663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5775667877642398679929775 8663501816463598019894663)
          ·
            refine ⟨12995252724695397029841995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8663501816463598019894663 12995252724695397029841995)
            ·
              refine ⟨19492879087043095544762993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12995252724695397029841995 19492879087043095544762993)
              ·
                refine ⟨14619659315282321658572245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19492879087043095544762993 14619659315282321658572245)
                ·
                  refine ⟨342648265201929413872787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14619659315282321658572245 342648265201929413872787)
                  ·
                    rfl

theorem cell23_6005746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 2, 7].length) (baseStart_6005746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6005746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6005746 prefixEnd_6005746 := by exact prefixLift 6005746
  have htrace : WordTrace (prefixWord ++ tailWord_6005746) baseStart_6005746 baseEnd_6005746 := by
    simpa [prefixWord, tailWord_6005746, baseEnd_6005746] using wordTrace_append hprefix tailTrace_6005746
  have hstable : (prefixWord ++ tailWord_6005746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6005746).length < 2 ^ (prefixWord ++ tailWord_6005746).sum := by decide
  have hdescent : baseEnd_6005746 < baseStart_6005746 := by decide
  rcases family_descends (prefixWord ++ tailWord_6005746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6005806 : List Nat := [4, 1, 3, 1, 1, 1, 1, 4, 3, 4]
def baseStart_6005806 : Nat := 118140960795 + 6005806 * 2 ^ 59
def prefixEnd_6005806 : Nat := 4983230072969 + 3 ^ 40 * 6005806 * 2
def baseEnd_6005806 : Nat := 1027955065218878163368269

theorem tailTrace_6005806 : CollatzResearch.WordTrace tailWord_6005806 prefixEnd_6005806 1027955065218878163368269 := by
  unfold tailWord_6005806
  simp only [CollatzResearch.WordTrace]
  refine ⟨27381217559999755856120659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146033160319998697899310181 27381217559999755856120659)
  ·
    refine ⟨41071826339999633784180989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27381217559999755856120659 41071826339999633784180989)
    ·
      refine ⟨15401934877499862669067871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41071826339999633784180989 15401934877499862669067871)
      ·
        refine ⟨23102902316249794003601807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15401934877499862669067871 23102902316249794003601807)
        ·
          refine ⟨34654353474374691005402711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23102902316249794003601807 34654353474374691005402711)
          ·
            refine ⟨51981530211562036508104067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34654353474374691005402711 51981530211562036508104067)
            ·
              refine ⟨77972295317343054762156101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51981530211562036508104067 77972295317343054762156101)
              ·
                refine ⟨14619805372001822767904269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77972295317343054762156101 14619805372001822767904269)
                ·
                  refine ⟨5482427014500683537964101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14619805372001822767904269 5482427014500683537964101)
                  ·
                    refine ⟨1027955065218878163368269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5482427014500683537964101 1027955065218878163368269)
                    ·
                      rfl

theorem cell23_6005806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_6005806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6005806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6005806 prefixEnd_6005806 := by exact prefixLift 6005806
  have htrace : WordTrace (prefixWord ++ tailWord_6005806) baseStart_6005806 baseEnd_6005806 := by
    simpa [prefixWord, tailWord_6005806, baseEnd_6005806] using wordTrace_append hprefix tailTrace_6005806
  have hstable : (prefixWord ++ tailWord_6005806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6005806).length < 2 ^ (prefixWord ++ tailWord_6005806).sum := by decide
  have hdescent : baseEnd_6005806 < baseStart_6005806 := by decide
  rcases family_descends (prefixWord ++ tailWord_6005806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6005853 : List Nat := [1, 4, 4, 1, 2, 1, 1, 3, 6]
def baseStart_6005853 : Nat := 118140960795 + 6005853 * 2 ^ 59
def prefixEnd_6005853 : Nat := 4983230072969 + 3 ^ 40 * 6005853 * 2
def baseEnd_6005853 : Nat := 342654369916377311801899

theorem tailTrace_6005853 : CollatzResearch.WordTrace tailWord_6005853 prefixEnd_6005853 342654369916377311801899 := by
  unfold tailWord_6005853
  simp only [CollatzResearch.WordTrace]
  refine ⟨219051454710827773875926213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146034303140551849250617475 219051454710827773875926213)
  ·
    refine ⟨41072147758280207601736165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 219051454710827773875926213 41072147758280207601736165)
    ·
      refine ⟨7701027704677538925325531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41072147758280207601736165 7701027704677538925325531)
      ·
        refine ⟨11551541557016308387988297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7701027704677538925325531 11551541557016308387988297)
        ·
          refine ⟨8663656167762231290991223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11551541557016308387988297 8663656167762231290991223)
          ·
            refine ⟨12995484251643346936486835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8663656167762231290991223 12995484251643346936486835)
            ·
              refine ⟨19493226377465020404730253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12995484251643346936486835 19493226377465020404730253)
              ·
                refine ⟨7309959891549382651773845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19493226377465020404730253 7309959891549382651773845)
                ·
                  refine ⟨342654369916377311801899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7309959891549382651773845 342654369916377311801899)
                  ·
                    rfl

theorem cell23_6005853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 3, 6].length) (baseStart_6005853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6005853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6005853 prefixEnd_6005853 := by exact prefixLift 6005853
  have htrace : WordTrace (prefixWord ++ tailWord_6005853) baseStart_6005853 baseEnd_6005853 := by
    simpa [prefixWord, tailWord_6005853, baseEnd_6005853] using wordTrace_append hprefix tailTrace_6005853
  have hstable : (prefixWord ++ tailWord_6005853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6005853).length < 2 ^ (prefixWord ++ tailWord_6005853).sum := by decide
  have hdescent : baseEnd_6005853 < baseStart_6005853 := by decide
  rcases family_descends (prefixWord ++ tailWord_6005853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6005856 : List Nat := [2, 1, 1, 3, 2, 2, 1, 2, 4, 3, 2]
def baseStart_6005856 : Nat := 118140960795 + 6005856 * 2 ^ 59
def prefixEnd_6005856 : Nat := 4983230072969 + 3 ^ 40 * 6005856 * 2
def baseEnd_6005856 : Nat := 3083890869689359294479577

theorem tailTrace_6005856 : CollatzResearch.WordTrace tailWord_6005856 prefixEnd_6005856 3083890869689359294479577 := by
  unfold tailWord_6005856
  simp only [CollatzResearch.WordTrace]
  refine ⟨109525782064908452694142711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146034376086544603592190281 109525782064908452694142711)
  ·
    refine ⟨164288673097362679041214067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109525782064908452694142711 164288673097362679041214067)
    ·
      refine ⟨246433009646044018561821101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164288673097362679041214067 246433009646044018561821101)
      ·
        refine ⟨92412378617266506960682913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 246433009646044018561821101 92412378617266506960682913)
        ·
          refine ⟨69309283962949880220512185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92412378617266506960682913 69309283962949880220512185)
          ·
            refine ⟨51981962972212410165384139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69309283962949880220512185 51981962972212410165384139)
            ·
              refine ⟨77972944458318615248076209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51981962972212410165384139 77972944458318615248076209)
              ·
                refine ⟨58479708343738961436057157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77972944458318615248076209 58479708343738961436057157)
                ·
                  refine ⟨10964945314451055269260717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58479708343738961436057157 10964945314451055269260717)
                  ·
                    refine ⟨4111854492919145725972769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10964945314451055269260717 4111854492919145725972769)
                    ·
                      refine ⟨3083890869689359294479577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4111854492919145725972769 3083890869689359294479577)
                      ·
                        rfl

theorem cell23_6005856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 4, 3, 2].length) (baseStart_6005856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6005856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6005856 prefixEnd_6005856 := by exact prefixLift 6005856
  have htrace : WordTrace (prefixWord ++ tailWord_6005856) baseStart_6005856 baseEnd_6005856 := by
    simpa [prefixWord, tailWord_6005856, baseEnd_6005856] using wordTrace_append hprefix tailTrace_6005856
  have hstable : (prefixWord ++ tailWord_6005856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6005856).length < 2 ^ (prefixWord ++ tailWord_6005856).sum := by decide
  have hdescent : baseEnd_6005856 < baseStart_6005856 := by decide
  rcases family_descends (prefixWord ++ tailWord_6005856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6005866 : List Nat := [3, 1, 3, 2, 2, 2, 1, 1, 3, 5]
def baseStart_6005866 : Nat := 118140960795 + 6005866 * 2 ^ 59
def prefixEnd_6005866 : Nat := 4983230072969 + 3 ^ 40 * 6005866 * 2
def baseEnd_6005866 : Nat := 1027965334831968085118177

theorem tailTrace_6005866 : CollatzResearch.WordTrace tailWord_6005866 prefixEnd_6005866 1027965334831968085118177 := by
  unfold tailWord_6005866
  simp only [CollatzResearch.WordTrace]
  refine ⟨54762982214945169274037363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146034619239853784730766301 54762982214945169274037363)
  ·
    refine ⟨82144473322417753911056045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54762982214945169274037363 82144473322417753911056045)
    ·
      refine ⟨30804177495906657716646017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82144473322417753911056045 30804177495906657716646017)
      ·
        refine ⟨23103133121929993287484513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30804177495906657716646017 23103133121929993287484513)
        ·
          refine ⟨17327349841447494965613385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23103133121929993287484513 17327349841447494965613385)
          ·
            refine ⟨12995512381085621224210039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17327349841447494965613385 12995512381085621224210039)
            ·
              refine ⟨19493268571628431836315059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12995512381085621224210039 19493268571628431836315059)
              ·
                refine ⟨29239902857442647754472589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19493268571628431836315059 29239902857442647754472589)
                ·
                  refine ⟨10964963571540992907927221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29239902857442647754472589 10964963571540992907927221)
                  ·
                    refine ⟨1027965334831968085118177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10964963571540992907927221 1027965334831968085118177)
                    ·
                      rfl

theorem cell23_6005866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_6005866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6005866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6005866 prefixEnd_6005866 := by exact prefixLift 6005866
  have htrace : WordTrace (prefixWord ++ tailWord_6005866) baseStart_6005866 baseEnd_6005866 := by
    simpa [prefixWord, tailWord_6005866, baseEnd_6005866] using wordTrace_append hprefix tailTrace_6005866
  have hstable : (prefixWord ++ tailWord_6005866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6005866).length < 2 ^ (prefixWord ++ tailWord_6005866).sum := by decide
  have hdescent : baseEnd_6005866 < baseStart_6005866 := by decide
  rcases family_descends (prefixWord ++ tailWord_6005866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6005879 : List Nat := [1, 1, 3, 1, 1, 4, 3, 2, 1, 6]
def baseStart_6005879 : Nat := 118140960795 + 6005879 * 2 ^ 59
def prefixEnd_6005879 : Nat := 4983230072969 + 3 ^ 40 * 6005879 * 2
def baseEnd_6005879 : Nat := 1027967559914804234830657

theorem tailTrace_6005879 : CollatzResearch.WordTrace tailWord_6005879 prefixEnd_6005879 1027967559914804234830657 := by
  unfold tailWord_6005879
  simp only [CollatzResearch.WordTrace]
  refine ⟨219052403008733580316372691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146034935339155720210915127 219052403008733580316372691)
  ·
    refine ⟨328578604513100370474559037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219052403008733580316372691 328578604513100370474559037)
    ·
      refine ⟨123216976692412638927959639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 328578604513100370474559037 123216976692412638927959639)
      ·
        refine ⟨184825465038618958391939459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123216976692412638927959639 184825465038618958391939459)
        ·
          refine ⟨277238197557928437587909189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184825465038618958391939459 277238197557928437587909189)
          ·
            refine ⟨51982162042111582047732973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 277238197557928437587909189 51982162042111582047732973)
            ·
              refine ⟨19493310765791843267899865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51982162042111582047732973 19493310765791843267899865)
              ·
                refine ⟨14619983074343882450924899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19493310765791843267899865 14619983074343882450924899)
                ·
                  refine ⟨21929974611515823676387349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14619983074343882450924899 21929974611515823676387349)
                  ·
                    refine ⟨1027967559914804234830657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21929974611515823676387349 1027967559914804234830657)
                    ·
                      rfl

theorem cell23_6005879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 2, 1, 6].length) (baseStart_6005879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6005879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6005879 prefixEnd_6005879 := by exact prefixLift 6005879
  have htrace : WordTrace (prefixWord ++ tailWord_6005879) baseStart_6005879 baseEnd_6005879 := by
    simpa [prefixWord, tailWord_6005879, baseEnd_6005879] using wordTrace_append hprefix tailTrace_6005879
  have hstable : (prefixWord ++ tailWord_6005879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6005879).length < 2 ^ (prefixWord ++ tailWord_6005879).sum := by decide
  have hdescent : baseEnd_6005879 < baseStart_6005879 := by decide
  rcases family_descends (prefixWord ++ tailWord_6005879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6005897 : List Nat := [1, 2, 1, 1, 4, 5, 2, 2, 1, 1, 3]
def baseStart_6005897 : Nat := 118140960795 + 6005897 * 2 ^ 59
def prefixEnd_6005897 : Nat := 4983230072969 + 3 ^ 40 * 6005897 * 2
def baseEnd_6005897 : Nat := 3083911922396193634066889

theorem tailTrace_6005897 : CollatzResearch.WordTrace tailWord_6005897 prefixEnd_6005897 3083911922396193634066889 := by
  unfold tailWord_6005897
  simp only [CollatzResearch.WordTrace]
  refine ⟨219053059522668369390527945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146035373015112246260351963 219053059522668369390527945)
  ·
    refine ⟨164289794642001277042895959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219053059522668369390527945 164289794642001277042895959)
    ·
      refine ⟨246434691963001915564343939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164289794642001277042895959 246434691963001915564343939)
      ·
        refine ⟨369652037944502873346515909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246434691963001915564343939 369652037944502873346515909)
        ·
          refine ⟨69309757114594288752471733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 369652037944502873346515909 69309757114594288752471733)
          ·
            refine ⟨6497789729493214570544225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69309757114594288752471733 6497789729493214570544225)
            ·
              refine ⟨4873342297119910927908169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6497789729493214570544225 4873342297119910927908169)
              ·
                refine ⟨3655006722839933195931127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4873342297119910927908169 3655006722839933195931127)
                ·
                  refine ⟨5482510084259899793896691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3655006722839933195931127 5482510084259899793896691)
                  ·
                    refine ⟨8223765126389849690845037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5482510084259899793896691 8223765126389849690845037)
                    ·
                      refine ⟨3083911922396193634066889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8223765126389849690845037 3083911922396193634066889)
                      ·
                        rfl

theorem cell23_6005897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 2, 2, 1, 1, 3].length) (baseStart_6005897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6005897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6005897 prefixEnd_6005897 := by exact prefixLift 6005897
  have htrace : WordTrace (prefixWord ++ tailWord_6005897) baseStart_6005897 baseEnd_6005897 := by
    simpa [prefixWord, tailWord_6005897, baseEnd_6005897] using wordTrace_append hprefix tailTrace_6005897
  have hstable : (prefixWord ++ tailWord_6005897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6005897).length < 2 ^ (prefixWord ++ tailWord_6005897).sum := by decide
  have hdescent : baseEnd_6005897 < baseStart_6005897 := by decide
  rcases family_descends (prefixWord ++ tailWord_6005897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6005916 : List Nat := [2, 2, 3, 2, 1, 2, 1, 3, 1, 2, 4]
def baseStart_6005916 : Nat := 118140960795 + 6005916 * 2 ^ 59
def prefixEnd_6005916 : Nat := 4983230072969 + 3 ^ 40 * 6005916 * 2
def baseEnd_6005916 : Nat := 3083921678528629059729301

theorem tailTrace_6005916 : CollatzResearch.WordTrace tailWord_6005916 prefixEnd_6005916 3083921678528629059729301 := by
  unfold tailWord_6005916
  simp only [CollatzResearch.WordTrace]
  refine ⟨109526876254799767817734801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146035835006399690423646401 109526876254799767817734801)
  ·
    refine ⟨82145157191099825863301101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109526876254799767817734801 82145157191099825863301101)
    ·
      refine ⟨30804433946662434698737913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82145157191099825863301101 30804433946662434698737913)
      ·
        refine ⟨23103325459996826024053435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30804433946662434698737913 23103325459996826024053435)
        ·
          refine ⟨34654988189995239036080153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23103325459996826024053435 34654988189995239036080153)
          ·
            refine ⟨25991241142496429277060115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34654988189995239036080153 25991241142496429277060115)
            ·
              refine ⟨38986861713744643915590173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25991241142496429277060115 38986861713744643915590173)
              ·
                refine ⟨14620073142654241468346315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38986861713744643915590173 14620073142654241468346315)
                ·
                  refine ⟨21930109713981362202519473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14620073142654241468346315 21930109713981362202519473)
                  ·
                    refine ⟨16447582285486021651889605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21930109713981362202519473 16447582285486021651889605)
                    ·
                      refine ⟨3083921678528629059729301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16447582285486021651889605 3083921678528629059729301)
                      ·
                        rfl

theorem cell23_6005916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_6005916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6005916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6005916 prefixEnd_6005916 := by exact prefixLift 6005916
  have htrace : WordTrace (prefixWord ++ tailWord_6005916) baseStart_6005916 baseEnd_6005916 := by
    simpa [prefixWord, tailWord_6005916, baseEnd_6005916] using wordTrace_append hprefix tailTrace_6005916
  have hstable : (prefixWord ++ tailWord_6005916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6005916).length < 2 ^ (prefixWord ++ tailWord_6005916).sum := by decide
  have hdescent : baseEnd_6005916 < baseStart_6005916 := by decide
  rcases family_descends (prefixWord ++ tailWord_6005916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6005936 : List Nat := [2, 1, 1, 1, 2, 1, 2, 3, 6, 1, 3]
def baseStart_6005936 : Nat := 118140960795 + 6005936 * 2 ^ 59
def prefixEnd_6005936 : Nat := 4983230072969 + 3 ^ 40 * 6005936 * 2
def baseEnd_6005936 : Nat := 3083931948141718981479209

theorem tailTrace_6005936 : CollatzResearch.WordTrace tailWord_6005936 prefixEnd_6005936 3083931948141718981479209 := by
  unfold tailWord_6005936
  simp only [CollatzResearch.WordTrace]
  refine ⟨109527240984763539525598831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146036321313018052700798441 109527240984763539525598831)
  ·
    refine ⟨164290861477145309288398247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109527240984763539525598831 164290861477145309288398247)
    ·
      refine ⟨246436292215717963932597371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164290861477145309288398247 246436292215717963932597371)
      ·
        refine ⟨369654438323576945898896057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246436292215717963932597371 369654438323576945898896057)
        ·
          refine ⟨277240828742682709424172043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 369654438323576945898896057 277240828742682709424172043)
          ·
            refine ⟨415861243114024064136258065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277240828742682709424172043 415861243114024064136258065)
            ·
              refine ⟨311895932335518048102193549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 415861243114024064136258065 311895932335518048102193549)
              ·
                refine ⟨116960974625819268038322581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 311895932335518048102193549 116960974625819268038322581)
                ·
                  refine ⟨5482545685585278189296371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 116960974625819268038322581 5482545685585278189296371)
                  ·
                    refine ⟨8223818528377917283944557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5482545685585278189296371 8223818528377917283944557)
                    ·
                      refine ⟨3083931948141718981479209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8223818528377917283944557 3083931948141718981479209)
                      ·
                        rfl

theorem cell23_6005936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 6, 1, 3].length) (baseStart_6005936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6005936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6005936 prefixEnd_6005936 := by exact prefixLift 6005936
  have htrace : WordTrace (prefixWord ++ tailWord_6005936) baseStart_6005936 baseEnd_6005936 := by
    simpa [prefixWord, tailWord_6005936, baseEnd_6005936] using wordTrace_append hprefix tailTrace_6005936
  have hstable : (prefixWord ++ tailWord_6005936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6005936).length < 2 ^ (prefixWord ++ tailWord_6005936).sum := by decide
  have hdescent : baseEnd_6005936 < baseStart_6005936 := by decide
  rcases family_descends (prefixWord ++ tailWord_6005936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6005937 : List Nat := [1, 2, 2, 5, 1, 1, 1, 5, 1, 2, 2]
def baseStart_6005937 : Nat := 118140960795 + 6005937 * 2 ^ 59
def prefixEnd_6005937 : Nat := 4983230072969 + 3 ^ 40 * 6005937 * 2
def baseEnd_6005937 : Nat := 3083932461622373477566705

theorem tailTrace_6005937 : CollatzResearch.WordTrace tailWord_6005937 prefixEnd_6005937 3083932461622373477566705 := by
  unfold tailWord_6005937
  simp only [CollatzResearch.WordTrace]
  refine ⟨219054518442523456221984065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146036345628348970814656043 219054518442523456221984065)
  ·
    refine ⟨164290888831892592166488049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219054518442523456221984065 164290888831892592166488049)
    ·
      refine ⟨123218166623919444124866037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164290888831892592166488049 123218166623919444124866037)
      ·
        refine ⟨11551703120992447886706191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 123218166623919444124866037 11551703120992447886706191)
        ·
          refine ⟨17327554681488671830059287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11551703120992447886706191 17327554681488671830059287)
          ·
            refine ⟨25991332022233007745088931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17327554681488671830059287 25991332022233007745088931)
            ·
              refine ⟨38986998033349511617633397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25991332022233007745088931 38986998033349511617633397)
              ·
                refine ⟨3655031065626516714153131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38986998033349511617633397 3655031065626516714153131)
                ·
                  refine ⟨5482546598439775071229697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3655031065626516714153131 5482546598439775071229697)
                  ·
                    refine ⟨4111909948829831303422273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5482546598439775071229697 4111909948829831303422273)
                    ·
                      refine ⟨3083932461622373477566705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4111909948829831303422273 3083932461622373477566705)
                      ·
                        rfl

theorem cell23_6005937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_6005937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6005937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6005937 prefixEnd_6005937 := by exact prefixLift 6005937
  have htrace : WordTrace (prefixWord ++ tailWord_6005937) baseStart_6005937 baseEnd_6005937 := by
    simpa [prefixWord, tailWord_6005937, baseEnd_6005937] using wordTrace_append hprefix tailTrace_6005937
  have hstable : (prefixWord ++ tailWord_6005937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6005937).length < 2 ^ (prefixWord ++ tailWord_6005937).sum := by decide
  have hdescent : baseEnd_6005937 < baseStart_6005937 := by decide
  rcases family_descends (prefixWord ++ tailWord_6005937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6005959 : List Nat := [1, 1, 4, 1, 1, 1, 1, 3, 1, 5, 4]
def baseStart_6005959 : Nat := 118140960795 + 6005959 * 2 ^ 59
def prefixEnd_6005959 : Nat := 4983230072969 + 3 ^ 40 * 6005959 * 2
def baseEnd_6005959 : Nat := 3083943758196772391491603

theorem tailTrace_6005959 : CollatzResearch.WordTrace tailWord_6005959 prefixEnd_6005959 3083943758196772391491603 := by
  unfold tailWord_6005959
  simp only [CollatzResearch.WordTrace]
  refine ⟨219055320848443753979284931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146036880565629169319523287 219055320848443753979284931)
  ·
    refine ⟨328582981272665630968927397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219055320848443753979284931 328582981272665630968927397)
    ·
      refine ⟨61609308988624805806673887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 328582981272665630968927397 61609308988624805806673887)
      ·
        refine ⟨92413963482937208710010831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61609308988624805806673887 92413963482937208710010831)
        ·
          refine ⟨138620945224405813065016247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92413963482937208710010831 138620945224405813065016247)
          ·
            refine ⟨207931417836608719597524371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138620945224405813065016247 207931417836608719597524371)
            ·
              refine ⟨311897126754913079396286557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207931417836608719597524371 311897126754913079396286557)
              ·
                refine ⟨116961422533092404773607459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 311897126754913079396286557 116961422533092404773607459)
                ·
                  refine ⟨175442133799638607160411189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116961422533092404773607459 175442133799638607160411189)
                  ·
                    refine ⟨16447700043716119421288549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 175442133799638607160411189 16447700043716119421288549)
                    ·
                      refine ⟨3083943758196772391491603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16447700043716119421288549 3083943758196772391491603)
                      ·
                        rfl

theorem cell23_6005959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 5, 4].length) (baseStart_6005959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6005959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6005959 prefixEnd_6005959 := by exact prefixLift 6005959
  have htrace : WordTrace (prefixWord ++ tailWord_6005959) baseStart_6005959 baseEnd_6005959 := by
    simpa [prefixWord, tailWord_6005959, baseEnd_6005959] using wordTrace_append hprefix tailTrace_6005959
  have hstable : (prefixWord ++ tailWord_6005959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6005959).length < 2 ^ (prefixWord ++ tailWord_6005959).sum := by decide
  have hdescent : baseEnd_6005959 < baseStart_6005959 := by decide
  rcases family_descends (prefixWord ++ tailWord_6005959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6005996 : List Nat := [2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 5]
def baseStart_6005996 : Nat := 118140960795 + 6005996 * 2 ^ 59
def prefixEnd_6005996 : Nat := 4983230072969 + 3 ^ 40 * 6005996 * 2
def baseEnd_6005996 : Nat := 3083962756980988746728933

theorem tailTrace_6005996 : CollatzResearch.WordTrace tailWord_6005996 prefixEnd_6005996 3083962756980988746728933 := by
  unfold tailWord_6005996
  simp only [CollatzResearch.WordTrace]
  refine ⟨109528335174654854649190921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146037780232873139532254561 109528335174654854649190921)
  ·
    refine ⟨82146251380991140986893191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109528335174654854649190921 82146251380991140986893191)
    ·
      refine ⟨123219377071486711480339787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82146251380991140986893191 123219377071486711480339787)
      ·
        refine ⟨184829065607230067220509681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123219377071486711480339787 184829065607230067220509681)
        ·
          refine ⟨138621799205422550415382261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184829065607230067220509681 138621799205422550415382261)
          ·
            refine ⟨12995793675508364101442087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 138621799205422550415382261 12995793675508364101442087)
            ·
              refine ⟨19493690513262546152163131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12995793675508364101442087 19493690513262546152163131)
              ·
                refine ⟨29240535769893819228244697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19493690513262546152163131 29240535769893819228244697)
                ·
                  refine ⟨21930401827420364421183523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29240535769893819228244697 21930401827420364421183523)
                  ·
                    refine ⟨32895602741130546631775285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21930401827420364421183523 32895602741130546631775285)
                    ·
                      refine ⟨3083962756980988746728933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32895602741130546631775285 3083962756980988746728933)
                      ·
                        rfl

theorem cell23_6005996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 5].length) (baseStart_6005996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6005996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6005996 prefixEnd_6005996 := by exact prefixLift 6005996
  have htrace : WordTrace (prefixWord ++ tailWord_6005996) baseStart_6005996 baseEnd_6005996 := by
    simpa [prefixWord, tailWord_6005996, baseEnd_6005996] using wordTrace_append hprefix tailTrace_6005996
  have hstable : (prefixWord ++ tailWord_6005996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6005996).length < 2 ^ (prefixWord ++ tailWord_6005996).sum := by decide
  have hdescent : baseEnd_6005996 < baseStart_6005996 := by decide
  rcases family_descends (prefixWord ++ tailWord_6005996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6006009 : List Nat := [1, 2, 1, 3, 1, 1, 3, 1, 1, 2, 7]
def baseStart_6006009 : Nat := 118140960795 + 6006009 * 2 ^ 59
def prefixEnd_6006009 : Nat := 4983230072969 + 3 ^ 40 * 6006009 * 2
def baseEnd_6006009 : Nat := 3083969432229497195866373

theorem tailTrace_6006009 : CollatzResearch.WordTrace tailWord_6006009 prefixEnd_6006009 3083969432229497195866373 := by
  unfold tailWord_6006009
  simp only [CollatzResearch.WordTrace]
  refine ⟨219057144498262612518605081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146038096332175075012403387 219057144498262612518605081)
  ·
    refine ⟨164292858373696959388953811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219057144498262612518605081 164292858373696959388953811)
    ·
      refine ⟨246439287560545439083430717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164292858373696959388953811 246439287560545439083430717)
      ·
        refine ⟨92414732835204539656286519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 246439287560545439083430717 92414732835204539656286519)
        ·
          refine ⟨138622099252806809484429779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92414732835204539656286519 138622099252806809484429779)
          ·
            refine ⟨207933148879210214226644669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138622099252806809484429779 207933148879210214226644669)
            ·
              refine ⟨77974930829703830334991751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 207933148879210214226644669 77974930829703830334991751)
              ·
                refine ⟨116962396244555745502487627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77974930829703830334991751 116962396244555745502487627)
                ·
                  refine ⟨175443594366833618253731441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116962396244555745502487627 175443594366833618253731441)
                  ·
                    refine ⟨131582695775125213690298581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 175443594366833618253731441 131582695775125213690298581)
                    ·
                      refine ⟨3083969432229497195866373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 131582695775125213690298581 3083969432229497195866373)
                      ·
                        rfl

theorem cell23_6006009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_6006009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6006009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6006009 prefixEnd_6006009 := by exact prefixLift 6006009
  have htrace : WordTrace (prefixWord ++ tailWord_6006009) baseStart_6006009 baseEnd_6006009 := by
    simpa [prefixWord, tailWord_6006009, baseEnd_6006009] using wordTrace_append hprefix tailTrace_6006009
  have hstable : (prefixWord ++ tailWord_6006009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6006009).length < 2 ^ (prefixWord ++ tailWord_6006009).sum := by decide
  have hdescent : baseEnd_6006009 < baseStart_6006009 := by decide
  rcases family_descends (prefixWord ++ tailWord_6006009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6006010 : List Nat := [3, 1, 1, 1, 1, 4, 2, 4, 2, 2, 2]
def baseStart_6006010 : Nat := 118140960795 + 6006010 * 2 ^ 59
def prefixEnd_6006010 : Nat := 4983230072969 + 3 ^ 40 * 6006010 * 2
def baseEnd_6006010 : Nat := 3083969945710151691953869

theorem tailTrace_6006010 : CollatzResearch.WordTrace tailWord_6006010 prefixEnd_6006010 3083969945710151691953869 := by
  unfold tailWord_6006010
  simp only [CollatzResearch.WordTrace]
  refine ⟨54764295242814747422347871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146038120647505993126260989 54764295242814747422347871)
  ·
    refine ⟨82146442864222121133521807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54764295242814747422347871 82146442864222121133521807)
    ·
      refine ⟨123219664296333181700282711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82146442864222121133521807 123219664296333181700282711)
      ·
        refine ⟨184829496444499772550424067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123219664296333181700282711 184829496444499772550424067)
        ·
          refine ⟨277244244666749658825636101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184829496444499772550424067 277244244666749658825636101)
          ·
            refine ⟨51983295875015561029806769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 277244244666749658825636101 51983295875015561029806769)
            ·
              refine ⟨38987471906261670772355077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51983295875015561029806769 38987471906261670772355077)
              ·
                refine ⟨7310150982424063269816577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38987471906261670772355077 7310150982424063269816577)
                ·
                  refine ⟨5482613236818047452362433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7310150982424063269816577 5482613236818047452362433)
                  ·
                    refine ⟨4111959927613535589271825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5482613236818047452362433 4111959927613535589271825)
                    ·
                      refine ⟨3083969945710151691953869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4111959927613535589271825 3083969945710151691953869)
                      ·
                        rfl

theorem cell23_6006010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 4, 2, 2, 2].length) (baseStart_6006010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6006010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6006010 prefixEnd_6006010 := by exact prefixLift 6006010
  have htrace : WordTrace (prefixWord ++ tailWord_6006010) baseStart_6006010 baseEnd_6006010 := by
    simpa [prefixWord, tailWord_6006010, baseEnd_6006010] using wordTrace_append hprefix tailTrace_6006010
  have hstable : (prefixWord ++ tailWord_6006010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6006010).length < 2 ^ (prefixWord ++ tailWord_6006010).sum := by decide
  have hdescent : baseEnd_6006010 < baseStart_6006010 := by decide
  rcases family_descends (prefixWord ++ tailWord_6006010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6006026 : List Nat := [3, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3]
def baseStart_6006026 : Nat := 118140960795 + 6006026 * 2 ^ 59
def prefixEnd_6006026 : Nat := 4983230072969 + 3 ^ 40 * 6006026 * 2
def baseEnd_6006026 : Nat := 3083978161400623629353795

theorem tailTrace_6006026 : CollatzResearch.WordTrace tailWord_6006026 prefixEnd_6006026 3083978161400623629353795 := by
  unfold tailWord_6006026
  simp only [CollatzResearch.WordTrace]
  refine ⟨54764441134800256105493483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146038509692800682947982621 54764441134800256105493483)
  ·
    refine ⟨82146661702200384158240225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54764441134800256105493483 82146661702200384158240225)
    ·
      refine ⟨61609996276650288118680169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82146661702200384158240225 61609996276650288118680169)
      ·
        refine ⟨46207497207487716089010127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61609996276650288118680169 46207497207487716089010127)
        ·
          refine ⟨69311245811231574133515191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46207497207487716089010127 69311245811231574133515191)
          ·
            refine ⟨103966868716847361200272787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69311245811231574133515191 103966868716847361200272787)
            ·
              refine ⟨155950303075271041800409181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103966868716847361200272787 155950303075271041800409181)
              ·
                refine ⟨58481363653226640675153443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 155950303075271041800409181 58481363653226640675153443)
                ·
                  refine ⟨87722045479839961012730165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58481363653226640675153443 87722045479839961012730165)
                  ·
                    refine ⟨8223941763734996344943453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 87722045479839961012730165 8223941763734996344943453)
                    ·
                      refine ⟨3083978161400623629353795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8223941763734996344943453 3083978161400623629353795)
                      ·
                        rfl

theorem cell23_6006026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3].length) (baseStart_6006026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6006026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6006026 prefixEnd_6006026 := by exact prefixLift 6006026
  have htrace : WordTrace (prefixWord ++ tailWord_6006026) baseStart_6006026 baseEnd_6006026 := by
    simpa [prefixWord, tailWord_6006026, baseEnd_6006026] using wordTrace_append hprefix tailTrace_6006026
  have hstable : (prefixWord ++ tailWord_6006026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6006026).length < 2 ^ (prefixWord ++ tailWord_6006026).sum := by decide
  have hdescent : baseEnd_6006026 < baseStart_6006026 := by decide
  rcases family_descends (prefixWord ++ tailWord_6006026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6006027 : List Nat := [1, 1, 1, 1, 5, 3, 4, 1, 2, 2, 2]
def baseStart_6006027 : Nat := 118140960795 + 6006027 * 2 ^ 59
def prefixEnd_6006027 : Nat := 4983230072969 + 3 ^ 40 * 6006027 * 2
def baseEnd_6006027 : Nat := 3083978674881278125441291

theorem tailTrace_6006027 : CollatzResearch.WordTrace tailWord_6006027 prefixEnd_6006027 3083978674881278125441291 := by
  unfold tailWord_6006027
  simp only [CollatzResearch.WordTrace]
  refine ⟨219057801012197401592760335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146038534008131601061840223 219057801012197401592760335)
  ·
    refine ⟨328586701518296102389140503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219057801012197401592760335 328586701518296102389140503)
    ·
      refine ⟨492880052277444153583710755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328586701518296102389140503 492880052277444153583710755)
      ·
        refine ⟨739320078416166230375566133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 492880052277444153583710755 739320078416166230375566133)
        ·
          refine ⟨69311257351515584097709325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 739320078416166230375566133 69311257351515584097709325)
          ·
            refine ⟨25991721506818344036640997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69311257351515584097709325 25991721506818344036640997)
            ·
              refine ⟨4873447782528439506870187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25991721506818344036640997 4873447782528439506870187)
              ·
                refine ⟨7310171673792659260305281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4873447782528439506870187 7310171673792659260305281)
                ·
                  refine ⟨5482628755344494445228961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7310171673792659260305281 5482628755344494445228961)
                  ·
                    refine ⟨4111971566508370833921721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5482628755344494445228961 4111971566508370833921721)
                    ·
                      refine ⟨3083978674881278125441291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4111971566508370833921721 3083978674881278125441291)
                      ·
                        rfl

theorem cell23_6006027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 4, 1, 2, 2, 2].length) (baseStart_6006027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6006027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6006027 prefixEnd_6006027 := by exact prefixLift 6006027
  have htrace : WordTrace (prefixWord ++ tailWord_6006027) baseStart_6006027 baseEnd_6006027 := by
    simpa [prefixWord, tailWord_6006027, baseEnd_6006027] using wordTrace_append hprefix tailTrace_6006027
  have hstable : (prefixWord ++ tailWord_6006027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6006027).length < 2 ^ (prefixWord ++ tailWord_6006027).sum := by decide
  have hdescent : baseEnd_6006027 < baseStart_6006027 := by decide
  rcases family_descends (prefixWord ++ tailWord_6006027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6006059 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 3, 10]
def baseStart_6006059 : Nat := 118140960795 + 6006059 * 2 ^ 59
def prefixEnd_6006059 : Nat := 4983230072969 + 3 ^ 40 * 6006059 * 2
def baseEnd_6006059 : Nat := 1027998368754074000080381

theorem tailTrace_6006059 : CollatzResearch.WordTrace tailWord_6006059 prefixEnd_6006059 1027998368754074000080381 := by
  unfold tailWord_6006059
  simp only [CollatzResearch.WordTrace]
  refine ⟨219058968148081471057925231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146039312098720980705283487 219058968148081471057925231)
  ·
    refine ⟨328588452222122206586887847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219058968148081471057925231 328588452222122206586887847)
    ·
      refine ⟨492882678333183309880331771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328588452222122206586887847 492882678333183309880331771)
      ·
        refine ⟨739324017499774964820497657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 492882678333183309880331771 739324017499774964820497657)
        ·
          refine ⟨554493013124831223615373243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 739324017499774964820497657 554493013124831223615373243)
          ·
            refine ⟨831739519687246835423059865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 554493013124831223615373243 831739519687246835423059865)
            ·
              refine ⟨623804639765435126567294899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 831739519687246835423059865 623804639765435126567294899)
              ·
                refine ⟨935706959648152689850942349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 623804639765435126567294899 935706959648152689850942349)
                ·
                  refine ⟨350890109868057258694103381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 935706959648152689850942349 350890109868057258694103381)
                  ·
                    refine ⟨1027998368754074000080381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 350890109868057258694103381 1027998368754074000080381)
                    ·
                      rfl

theorem cell23_6006059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 10].length) (baseStart_6006059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6006059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6006059 prefixEnd_6006059 := by exact prefixLift 6006059
  have htrace : WordTrace (prefixWord ++ tailWord_6006059) baseStart_6006059 baseEnd_6006059 := by
    simpa [prefixWord, tailWord_6006059, baseEnd_6006059] using wordTrace_append hprefix tailTrace_6006059
  have hstable : (prefixWord ++ tailWord_6006059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6006059).length < 2 ^ (prefixWord ++ tailWord_6006059).sum := by decide
  have hdescent : baseEnd_6006059 < baseStart_6006059 := by decide
  rcases family_descends (prefixWord ++ tailWord_6006059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6006103 : List Nat := [1, 1, 3, 2, 3, 3, 1, 1, 1, 4, 3]
def baseStart_6006103 : Nat := 118140960795 + 6006103 * 2 ^ 59
def prefixEnd_6006103 : Nat := 4983230072969 + 3 ^ 40 * 6006103 * 2
def baseEnd_6006103 : Nat := 3084017699411019828090941

theorem tailTrace_6006103 : CollatzResearch.WordTrace tailWord_6006103 prefixEnd_6006103 3084017699411019828090941 := by
  unfold tailWord_6006103
  simp only [CollatzResearch.WordTrace]
  refine ⟨219060572959922066572526963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146040381973281377715017975 219060572959922066572526963)
  ·
    refine ⟨328590859439883099858790445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219060572959922066572526963 328590859439883099858790445)
    ·
      refine ⟨123221572289956162447046417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 328590859439883099858790445 123221572289956162447046417)
      ·
        refine ⟨92416179217467121835284813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123221572289956162447046417 92416179217467121835284813)
        ·
          refine ⟨34656067206550170688231805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92416179217467121835284813 34656067206550170688231805)
          ·
            refine ⟨12996025202456314008086927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34656067206550170688231805 12996025202456314008086927)
            ·
              refine ⟨19494037803684471012130391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12996025202456314008086927 19494037803684471012130391)
              ·
                refine ⟨29241056705526706518195587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19494037803684471012130391 29241056705526706518195587)
                ·
                  refine ⟨43861585058290059777293381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29241056705526706518195587 43861585058290059777293381)
                  ·
                    refine ⟨8224047198429386208242509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43861585058290059777293381 8224047198429386208242509)
                    ·
                      refine ⟨3084017699411019828090941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8224047198429386208242509 3084017699411019828090941)
                      ·
                        rfl

theorem cell23_6006103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 4, 3].length) (baseStart_6006103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6006103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6006103 prefixEnd_6006103 := by exact prefixLift 6006103
  have htrace : WordTrace (prefixWord ++ tailWord_6006103) baseStart_6006103 baseEnd_6006103 := by
    simpa [prefixWord, tailWord_6006103, baseEnd_6006103] using wordTrace_append hprefix tailTrace_6006103
  have hstable : (prefixWord ++ tailWord_6006103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6006103).length < 2 ^ (prefixWord ++ tailWord_6006103).sum := by decide
  have hdescent : baseEnd_6006103 < baseStart_6006103 := by decide
  rcases family_descends (prefixWord ++ tailWord_6006103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6006193 : List Nat := [1, 2, 2, 4, 1, 1, 1, 4, 1, 1, 5]
def baseStart_6006193 : Nat := 118140960795 + 6006193 * 2 ^ 59
def prefixEnd_6006193 : Nat := 4983230072969 + 3 ^ 40 * 6006193 * 2
def baseEnd_6006193 : Nat := 3084063912669924475965527

theorem tailTrace_6006193 : CollatzResearch.WordTrace tailWord_6006193 prefixEnd_6006193 3084063912669924475965527 := by
  unfold tailWord_6006193
  simp only [CollatzResearch.WordTrace]
  refine ⟨219063855529596011943303233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146042570353064007962202155 219063855529596011943303233)
  ·
    refine ⟨164297891647197008957477425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219063855529596011943303233 164297891647197008957477425)
    ·
      refine ⟨123223418735397756718108069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164297891647197008957477425 123223418735397756718108069)
      ·
        refine ⟨23104391012887079384645263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123223418735397756718108069 23104391012887079384645263)
        ·
          refine ⟨34656586519330619076967895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23104391012887079384645263 34656586519330619076967895)
          ·
            refine ⟨51984879778995928615451843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34656586519330619076967895 51984879778995928615451843)
            ·
              refine ⟨77977319668493892923177765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51984879778995928615451843 77977319668493892923177765)
              ·
                refine ⟨14620747437842604923095831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77977319668493892923177765 14620747437842604923095831)
                ·
                  refine ⟨21931121156763907384643747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14620747437842604923095831 21931121156763907384643747)
                  ·
                    refine ⟨32896681735145861076965621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21931121156763907384643747 32896681735145861076965621)
                    ·
                      refine ⟨3084063912669924475965527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32896681735145861076965621 3084063912669924475965527)
                      ·
                        rfl

theorem cell23_6006193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_6006193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6006193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6006193 prefixEnd_6006193 := by exact prefixLift 6006193
  have htrace : WordTrace (prefixWord ++ tailWord_6006193) baseStart_6006193 baseEnd_6006193 := by
    simpa [prefixWord, tailWord_6006193, baseEnd_6006193] using wordTrace_append hprefix tailTrace_6006193
  have hstable : (prefixWord ++ tailWord_6006193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6006193).length < 2 ^ (prefixWord ++ tailWord_6006193).sum := by decide
  have hdescent : baseEnd_6006193 < baseStart_6006193 := by decide
  rcases family_descends (prefixWord ++ tailWord_6006193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6006204 : List Nat := [2, 2, 2, 4, 3, 1, 1, 2, 1, 5]
def baseStart_6006204 : Nat := 118140960795 + 6006204 * 2 ^ 59
def prefixEnd_6006204 : Nat := 4983230072969 + 3 ^ 40 * 6006204 * 2
def baseEnd_6006204 : Nat := 1028023186985707977642659

theorem tailTrace_6006204 : CollatzResearch.WordTrace tailWord_6006204 prefixEnd_6006204 1028023186985707977642659 := by
  unfold tailWord_6006204
  simp only [CollatzResearch.WordTrace]
  refine ⟨109532128366278080410976833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146042837821704107214635777 109532128366278080410976833)
  ·
    refine ⟨82149096274708560308232625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109532128366278080410976833 82149096274708560308232625)
    ·
      refine ⟨61611822206031420231174469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82149096274708560308232625 61611822206031420231174469)
      ·
        refine ⟨11552216663630891293345213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61611822206031420231174469 11552216663630891293345213)
        ·
          refine ⟨4332081248861584235004455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11552216663630891293345213 4332081248861584235004455)
          ·
            refine ⟨6498121873292376352506683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4332081248861584235004455 6498121873292376352506683)
            ·
              refine ⟨9747182809938564528760025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6498121873292376352506683 9747182809938564528760025)
              ·
                refine ⟨7310387107453923396570019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9747182809938564528760025 7310387107453923396570019)
                ·
                  refine ⟨10965580661180885094855029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7310387107453923396570019 10965580661180885094855029)
                  ·
                    refine ⟨1028023186985707977642659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10965580661180885094855029 1028023186985707977642659)
                    ·
                      rfl

theorem cell23_6006204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 2, 1, 5].length) (baseStart_6006204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6006204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6006204 prefixEnd_6006204 := by exact prefixLift 6006204
  have htrace : WordTrace (prefixWord ++ tailWord_6006204) baseStart_6006204 baseEnd_6006204 := by
    simpa [prefixWord, tailWord_6006204, baseEnd_6006204] using wordTrace_append hprefix tailTrace_6006204
  have hstable : (prefixWord ++ tailWord_6006204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6006204).length < 2 ^ (prefixWord ++ tailWord_6006204).sum := by decide
  have hdescent : baseEnd_6006204 < baseStart_6006204 := by decide
  rcases family_descends (prefixWord ++ tailWord_6006204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6006220 : List Nat := [2, 2, 1, 4, 2, 2, 1, 2, 1, 2, 4]
def baseStart_6006220 : Nat := 118140960795 + 6006220 * 2 ^ 59
def prefixEnd_6006220 : Nat := 4983230072969 + 3 ^ 40 * 6006220 * 2
def baseEnd_6006220 : Nat := 3084077776647595870327903

theorem tailTrace_6006220 : CollatzResearch.WordTrace tailWord_6006220 prefixEnd_6006220 3084077776647595870327903 := by
  unfold tailWord_6006220
  simp only [CollatzResearch.WordTrace]
  refine ⟨109532420150249097777268057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146043226866998797036357409 109532420150249097777268057)
  ·
    refine ⟨82149315112686823332951043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109532420150249097777268057 82149315112686823332951043)
    ·
      refine ⟨123223972669030234999426565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82149315112686823332951043 123223972669030234999426565)
      ·
        refine ⟨23104494875443169062392481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123223972669030234999426565 23104494875443169062392481)
        ·
          refine ⟨17328371156582376796794361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23104494875443169062392481 17328371156582376796794361)
          ·
            refine ⟨12996278367436782597595771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17328371156582376796794361 12996278367436782597595771)
            ·
              refine ⟨19494417551155173896393657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12996278367436782597595771 19494417551155173896393657)
              ·
                refine ⟨14620813163366380422295243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19494417551155173896393657 14620813163366380422295243)
                ·
                  refine ⟨21931219745049570633442865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14620813163366380422295243 21931219745049570633442865)
                  ·
                    refine ⟨16448414808787177975082149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21931219745049570633442865 16448414808787177975082149)
                    ·
                      refine ⟨3084077776647595870327903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16448414808787177975082149 3084077776647595870327903)
                      ·
                        rfl

theorem cell23_6006220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_6006220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6006220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6006220 prefixEnd_6006220 := by exact prefixLift 6006220
  have htrace : WordTrace (prefixWord ++ tailWord_6006220) baseStart_6006220 baseEnd_6006220 := by
    simpa [prefixWord, tailWord_6006220, baseEnd_6006220] using wordTrace_append hprefix tailTrace_6006220
  have hstable : (prefixWord ++ tailWord_6006220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6006220).length < 2 ^ (prefixWord ++ tailWord_6006220).sum := by decide
  have hdescent : baseEnd_6006220 < baseStart_6006220 := by decide
  rcases family_descends (prefixWord ++ tailWord_6006220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6006223 : List Nat := [1, 1, 2, 1, 1, 4, 3, 1, 3, 3, 3]
def baseStart_6006223 : Nat := 118140960795 + 6006223 * 2 ^ 59
def prefixEnd_6006223 : Nat := 4983230072969 + 3 ^ 40 * 6006223 * 2
def baseEnd_6006223 : Nat := 3084079317089559358590389

theorem tailTrace_6006223 : CollatzResearch.WordTrace tailWord_6006223 prefixEnd_6006223 3084079317089559358590389 := by
  unfold tailWord_6006223
  simp only [CollatzResearch.WordTrace]
  refine ⟨219064949719487327066895323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146043299812991551377930215 219064949719487327066895323)
  ·
    refine ⟨328597424579230990600342985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219064949719487327066895323 328597424579230990600342985)
    ·
      refine ⟨246448068434423242950257239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 328597424579230990600342985 246448068434423242950257239)
      ·
        refine ⟨369672102651634864425385859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246448068434423242950257239 369672102651634864425385859)
        ·
          refine ⟨554508153977452296638078789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 369672102651634864425385859 554508153977452296638078789)
          ·
            refine ⟨103970278870772305619639773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 554508153977452296638078789 103970278870772305619639773)
            ·
              refine ⟨38988854576539614607364915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103970278870772305619639773 38988854576539614607364915)
              ·
                refine ⟨58483281864809421911047373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38988854576539614607364915 58483281864809421911047373)
                ·
                  refine ⟨21931230699303533216642765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58483281864809421911047373 21931230699303533216642765)
                  ·
                    refine ⟨8224211512238824956241037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21931230699303533216642765 8224211512238824956241037)
                    ·
                      refine ⟨3084079317089559358590389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8224211512238824956241037 3084079317089559358590389)
                      ·
                        rfl

theorem cell23_6006223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 3, 3, 3].length) (baseStart_6006223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6006223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6006223 prefixEnd_6006223 := by exact prefixLift 6006223
  have htrace : WordTrace (prefixWord ++ tailWord_6006223) baseStart_6006223 baseEnd_6006223 := by
    simpa [prefixWord, tailWord_6006223, baseEnd_6006223] using wordTrace_append hprefix tailTrace_6006223
  have hstable : (prefixWord ++ tailWord_6006223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6006223).length < 2 ^ (prefixWord ++ tailWord_6006223).sum := by decide
  have hdescent : baseEnd_6006223 < baseStart_6006223 := by decide
  rcases family_descends (prefixWord ++ tailWord_6006223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6006241 : List Nat := [1, 2, 3, 1, 2, 3, 4, 2, 1, 2, 2]
def baseStart_6006241 : Nat := 118140960795 + 6006241 * 2 ^ 59
def prefixEnd_6006241 : Nat := 4983230072969 + 3 ^ 40 * 6006241 * 2
def baseEnd_6006241 : Nat := 3084088559741340288165307

theorem tailTrace_6006241 : CollatzResearch.WordTrace tailWord_6006241 prefixEnd_6006241 3084088559741340288165307 := by
  unfold tailWord_6006241
  simp only [CollatzResearch.WordTrace]
  refine ⟨219065606233422116141050577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146043737488948077427367051 219065606233422116141050577)
  ·
    refine ⟨164299204675066587105787933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219065606233422116141050577 164299204675066587105787933)
    ·
      refine ⟨61612201753149970164670475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164299204675066587105787933 61612201753149970164670475)
      ·
        refine ⟨92418302629724955247005713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61612201753149970164670475 92418302629724955247005713)
        ·
          refine ⟨69313726972293716435254285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92418302629724955247005713 69313726972293716435254285)
          ·
            refine ⟨25992647614610143663220357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69313726972293716435254285 25992647614610143663220357)
            ·
              refine ⟨4873621427739401936853817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25992647614610143663220357 4873621427739401936853817)
              ·
                refine ⟨3655216070804551452640363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4873621427739401936853817 3655216070804551452640363)
                ·
                  refine ⟨5482824106206827178960545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3655216070804551452640363 5482824106206827178960545)
                  ·
                    refine ⟨4112118079655120384220409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5482824106206827178960545 4112118079655120384220409)
                    ·
                      refine ⟨3084088559741340288165307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4112118079655120384220409 3084088559741340288165307)
                      ·
                        rfl

theorem cell23_6006241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 4, 2, 1, 2, 2].length) (baseStart_6006241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6006241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6006241 prefixEnd_6006241 := by exact prefixLift 6006241
  have htrace : WordTrace (prefixWord ++ tailWord_6006241) baseStart_6006241 baseEnd_6006241 := by
    simpa [prefixWord, tailWord_6006241, baseEnd_6006241] using wordTrace_append hprefix tailTrace_6006241
  have hstable : (prefixWord ++ tailWord_6006241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6006241).length < 2 ^ (prefixWord ++ tailWord_6006241).sum := by decide
  have hdescent : baseEnd_6006241 < baseStart_6006241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6006241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6006243 : List Nat := [1, 1, 1, 6, 2, 1, 1, 1, 2, 7]
def baseStart_6006243 : Nat := 118140960795 + 6006243 * 2 ^ 59
def prefixEnd_6006243 : Nat := 4983230072969 + 3 ^ 40 * 6006243 * 2
def baseEnd_6006243 : Nat := 1028029862234216426780099

theorem tailTrace_6006243 : CollatzResearch.WordTrace tailWord_6006243 prefixEnd_6006243 1028029862234216426780099 := by
  unfold tailWord_6006243
  simp only [CollatzResearch.WordTrace]
  refine ⟨219065679179414870482623383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146043786119609913655082255 219065679179414870482623383)
  ·
    refine ⟨328598518769122305723935075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219065679179414870482623383 328598518769122305723935075)
    ·
      refine ⟨492897778153683458585902613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328598518769122305723935075 492897778153683458585902613)
      ·
        refine ⟨23104583350953912121214185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 492897778153683458585902613 23104583350953912121214185)
        ·
          refine ⟨17328437513215434090910639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23104583350953912121214185 17328437513215434090910639)
          ·
            refine ⟨25992656269823151136365959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17328437513215434090910639 25992656269823151136365959)
            ·
              refine ⟨38988984404734726704548939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25992656269823151136365959 38988984404734726704548939)
              ·
                refine ⟨58483476607102090056823409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38988984404734726704548939 58483476607102090056823409)
                ·
                  refine ⟨43862607455326567542617557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58483476607102090056823409 43862607455326567542617557)
                  ·
                    refine ⟨1028029862234216426780099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43862607455326567542617557 1028029862234216426780099)
                    ·
                      rfl

theorem cell23_6006243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 7].length) (baseStart_6006243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6006243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6006243 prefixEnd_6006243 := by exact prefixLift 6006243
  have htrace : WordTrace (prefixWord ++ tailWord_6006243) baseStart_6006243 baseEnd_6006243 := by
    simpa [prefixWord, tailWord_6006243, baseEnd_6006243] using wordTrace_append hprefix tailTrace_6006243
  have hstable : (prefixWord ++ tailWord_6006243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6006243).length < 2 ^ (prefixWord ++ tailWord_6006243).sum := by decide
  have hdescent : baseEnd_6006243 < baseStart_6006243 := by decide
  rcases family_descends (prefixWord ++ tailWord_6006243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6006257 : List Nat := [1, 2, 2, 2, 3, 2, 2, 3, 2, 1, 3]
def baseStart_6006257 : Nat := 118140960795 + 6006257 * 2 ^ 59
def prefixEnd_6006257 : Nat := 4983230072969 + 3 ^ 40 * 6006257 * 2
def baseEnd_6006257 : Nat := 3084096775431812225565233

theorem tailTrace_6006257 : CollatzResearch.WordTrace tailWord_6006257 prefixEnd_6006257 3084096775431812225565233 := by
  unfold tailWord_6006257
  simp only [CollatzResearch.WordTrace]
  refine ⟨219066189801364150873633025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146044126534242767249088683 219066189801364150873633025)
  ·
    refine ⟨164299642351023113155224769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219066189801364150873633025 164299642351023113155224769)
    ·
      refine ⟨123224731763267334866418577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164299642351023113155224769 123224731763267334866418577)
      ·
        refine ⟨92418548822450501149813933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123224731763267334866418577 92418548822450501149813933)
        ·
          refine ⟨34656955808418937931180225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92418548822450501149813933 34656955808418937931180225)
          ·
            refine ⟨25992716856314203448385169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34656955808418937931180225 25992716856314203448385169)
            ·
              refine ⟨19494537642235652586288877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25992716856314203448385169 19494537642235652586288877)
              ·
                refine ⟨7310451615838369719858329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19494537642235652586288877 7310451615838369719858329)
                ·
                  refine ⟨5482838711878777289893747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7310451615838369719858329 5482838711878777289893747)
                  ·
                    refine ⟨8224258067818165934840621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5482838711878777289893747 8224258067818165934840621)
                    ·
                      refine ⟨3084096775431812225565233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8224258067818165934840621 3084096775431812225565233)
                      ·
                        rfl

theorem cell23_6006257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 3, 2, 1, 3].length) (baseStart_6006257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6006257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6006257 prefixEnd_6006257 := by exact prefixLift 6006257
  have htrace : WordTrace (prefixWord ++ tailWord_6006257) baseStart_6006257 baseEnd_6006257 := by
    simpa [prefixWord, tailWord_6006257, baseEnd_6006257] using wordTrace_append hprefix tailTrace_6006257
  have hstable : (prefixWord ++ tailWord_6006257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6006257).length < 2 ^ (prefixWord ++ tailWord_6006257).sum := by decide
  have hdescent : baseEnd_6006257 < baseStart_6006257 := by decide
  rcases family_descends (prefixWord ++ tailWord_6006257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6006278 : List Nat := [6, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3]
def baseStart_6006278 : Nat := 118140960795 + 6006278 * 2 ^ 59
def prefixEnd_6006278 : Nat := 4983230072969 + 3 ^ 40 * 6006278 * 2
def baseEnd_6006278 : Nat := 3084107558525556643402637

theorem tailTrace_6006278 : CollatzResearch.WordTrace tailWord_6006278 prefixEnd_6006278 3084107558525556643402637 := by
  unfold tailWord_6006278
  simp only [CollatzResearch.WordTrace]
  refine ⟨6845842366696502233129609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 146044637156192047640098325 6845842366696502233129609)
  ·
    refine ⟨5134381775022376674847207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6845842366696502233129609 5134381775022376674847207)
    ·
      refine ⟨7701572662533565012270811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5134381775022376674847207 7701572662533565012270811)
      ·
        refine ⟨11552358993800347518406217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7701572662533565012270811 11552358993800347518406217)
        ·
          refine ⟨8664269245350260638804663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11552358993800347518406217 8664269245350260638804663)
          ·
            refine ⟨12996403868025390958206995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8664269245350260638804663 12996403868025390958206995)
            ·
              refine ⟨19494605802038086437310493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12996403868025390958206995 19494605802038086437310493)
              ·
                refine ⟨7310477175764282413991435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19494605802038086437310493 7310477175764282413991435)
                ·
                  refine ⟨10965715763646423620987153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7310477175764282413991435 10965715763646423620987153)
                  ·
                    refine ⟨8224286822734817715740365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10965715763646423620987153 8224286822734817715740365)
                    ·
                      refine ⟨3084107558525556643402637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8224286822734817715740365 3084107558525556643402637)
                      ·
                        rfl

theorem cell23_6006278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_6006278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6006278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6006278 prefixEnd_6006278 := by exact prefixLift 6006278
  have htrace : WordTrace (prefixWord ++ tailWord_6006278) baseStart_6006278 baseEnd_6006278 := by
    simpa [prefixWord, tailWord_6006278, baseEnd_6006278] using wordTrace_append hprefix tailTrace_6006278
  have hstable : (prefixWord ++ tailWord_6006278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6006278).length < 2 ^ (prefixWord ++ tailWord_6006278).sum := by decide
  have hdescent : baseEnd_6006278 < baseStart_6006278 := by decide
  rcases family_descends (prefixWord ++ tailWord_6006278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6006284 : List Nat := [2, 2, 1, 2, 5, 1, 1, 3, 1, 3, 2]
def baseStart_6006284 : Nat := 118140960795 + 6006284 * 2 ^ 59
def prefixEnd_6006284 : Nat := 4983230072969 + 3 ^ 40 * 6006284 * 2
def baseEnd_6006284 : Nat := 3084110639409483619927609

theorem tailTrace_6006284 : CollatzResearch.WordTrace tailWord_6006284 prefixEnd_6006284 3084110639409483619927609 := by
  unfold tailWord_6006284
  simp only [CollatzResearch.WordTrace]
  refine ⟨109533587286133167242432953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146044783048177556323243937 109533587286133167242432953)
  ·
    refine ⟨82150190464599875431824715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109533587286133167242432953 82150190464599875431824715)
    ·
      refine ⟨123225285696899813147737073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82150190464599875431824715 123225285696899813147737073)
      ·
        refine ⟨92418964272674859860802805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123225285696899813147737073 92418964272674859860802805)
        ·
          refine ⟨8664277900563268111950263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 92418964272674859860802805 8664277900563268111950263)
          ·
            refine ⟨12996416850844902167925395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8664277900563268111950263 12996416850844902167925395)
            ·
              refine ⟨19494625276267353251888093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12996416850844902167925395 19494625276267353251888093)
              ·
                refine ⟨7310484478600257469458035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19494625276267353251888093 7310484478600257469458035)
                ·
                  refine ⟨10965726717900386204187053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7310484478600257469458035 10965726717900386204187053)
                  ·
                    refine ⟨4112147519212644826570145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10965726717900386204187053 4112147519212644826570145)
                    ·
                      refine ⟨3084110639409483619927609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4112147519212644826570145 3084110639409483619927609)
                      ·
                        rfl

theorem cell23_6006284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 3, 1, 3, 2].length) (baseStart_6006284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6006284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6006284 prefixEnd_6006284 := by exact prefixLift 6006284
  have htrace : WordTrace (prefixWord ++ tailWord_6006284) baseStart_6006284 baseEnd_6006284 := by
    simpa [prefixWord, tailWord_6006284, baseEnd_6006284] using wordTrace_append hprefix tailTrace_6006284
  have hstable : (prefixWord ++ tailWord_6006284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6006284).length < 2 ^ (prefixWord ++ tailWord_6006284).sum := by decide
  have hdescent : baseEnd_6006284 < baseStart_6006284 := by decide
  rcases family_descends (prefixWord ++ tailWord_6006284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6006303 : List Nat := [1, 1, 2, 4, 1, 1, 3, 3, 7]
def baseStart_6006303 : Nat := 118140960795 + 6006303 * 2 ^ 59
def prefixEnd_6006303 : Nat := 4983230072969 + 3 ^ 40 * 6006303 * 2
def baseEnd_6006303 : Nat := 342680043949102116176669

theorem tailTrace_6006303 : CollatzResearch.WordTrace tailWord_6006303 prefixEnd_6006303 342680043949102116176669 := by
  unfold tailWord_6006303
  simp only [CollatzResearch.WordTrace]
  refine ⟨219067867559197500729807563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146045245039465000486538375 219067867559197500729807563)
  ·
    refine ⟨328601801338796251094711345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219067867559197500729807563 328601801338796251094711345)
    ·
      refine ⟨246451351004097188321033509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 328601801338796251094711345 246451351004097188321033509)
      ·
        refine ⟨46209628313268222810193783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 246451351004097188321033509 46209628313268222810193783)
        ·
          refine ⟨69314442469902334215290675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46209628313268222810193783 69314442469902334215290675)
          ·
            refine ⟨103971663704853501322936013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69314442469902334215290675 103971663704853501322936013)
            ·
              refine ⟨38989373889320062996101005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103971663704853501322936013 38989373889320062996101005)
              ·
                refine ⟨14621015208495023623537877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38989373889320062996101005 14621015208495023623537877)
                ·
                  refine ⟨342680043949102116176669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14621015208495023623537877 342680043949102116176669)
                  ·
                    rfl

theorem cell23_6006303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 3, 7].length) (baseStart_6006303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6006303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6006303 prefixEnd_6006303 := by exact prefixLift 6006303
  have htrace : WordTrace (prefixWord ++ tailWord_6006303) baseStart_6006303 baseEnd_6006303 := by
    simpa [prefixWord, tailWord_6006303, baseEnd_6006303] using wordTrace_append hprefix tailTrace_6006303
  have hstable : (prefixWord ++ tailWord_6006303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6006303).length < 2 ^ (prefixWord ++ tailWord_6006303).sum := by decide
  have hdescent : baseEnd_6006303 < baseStart_6006303 := by decide
  rcases family_descends (prefixWord ++ tailWord_6006303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6006354 : List Nat := [3, 2, 2, 1, 2, 3, 3, 2, 5]
def baseStart_6006354 : Nat := 118140960795 + 6006354 * 2 ^ 59
def prefixEnd_6006354 : Nat := 4983230072969 + 3 ^ 40 * 6006354 * 2
def baseEnd_6006354 : Nat := 342682953672810927339143

theorem tailTrace_6006354 : CollatzResearch.WordTrace tailWord_6006354 prefixEnd_6006354 342682953672810927339143 := by
  unfold tailWord_6006354
  simp only [CollatzResearch.WordTrace]
  refine ⟨54767431920503184109978529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146046485121341824293276077 54767431920503184109978529)
  ·
    refine ⟨41075573940377388082483897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54767431920503184109978529 41075573940377388082483897)
    ·
      refine ⟨30806680455283041061862923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41075573940377388082483897 30806680455283041061862923)
      ·
        refine ⟨46210020682924561592794385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30806680455283041061862923 46210020682924561592794385)
        ·
          refine ⟨34657515512193421194595789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46210020682924561592794385 34657515512193421194595789)
          ·
            refine ⟨12996568317072532947973421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34657515512193421194595789 12996568317072532947973421)
            ·
              refine ⟨4873713118902199855490033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12996568317072532947973421 4873713118902199855490033)
              ·
                refine ⟨3655284839176649891617525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4873713118902199855490033 3655284839176649891617525)
                ·
                  refine ⟨342682953672810927339143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3655284839176649891617525 342682953672810927339143)
                  ·
                    rfl

theorem cell23_6006354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 3, 2, 5].length) (baseStart_6006354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6006354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6006354 prefixEnd_6006354 := by exact prefixLift 6006354
  have htrace : WordTrace (prefixWord ++ tailWord_6006354) baseStart_6006354 baseEnd_6006354 := by
    simpa [prefixWord, tailWord_6006354, baseEnd_6006354] using wordTrace_append hprefix tailTrace_6006354
  have hstable : (prefixWord ++ tailWord_6006354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6006354).length < 2 ^ (prefixWord ++ tailWord_6006354).sum := by decide
  have hdescent : baseEnd_6006354 < baseStart_6006354 := by decide
  rcases family_descends (prefixWord ++ tailWord_6006354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6006380 : List Nat := [2, 2, 1, 1, 3, 1, 1, 3, 5, 4]
def baseStart_6006380 : Nat := 118140960795 + 6006380 * 2 ^ 59
def prefixEnd_6006380 : Nat := 4983230072969 + 3 ^ 40 * 6006380 * 2
def baseEnd_6006380 : Nat := 1028053311184105081442389

theorem tailTrace_6006380 : CollatzResearch.WordTrace tailWord_6006380 prefixEnd_6006380 1028053311184105081442389 := by
  unfold tailWord_6006380
  simp only [CollatzResearch.WordTrace]
  refine ⟨109535337989959271440180297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146047117319945695253573729 109535337989959271440180297)
  ·
    refine ⟨82151503492469453580135223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109535337989959271440180297 82151503492469453580135223)
    ·
      refine ⟨123227255238704180370202835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82151503492469453580135223 123227255238704180370202835)
      ·
        refine ⟨184840882858056270555304253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123227255238704180370202835 184840882858056270555304253)
        ·
          refine ⟨69315331071771101458239095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184840882858056270555304253 69315331071771101458239095)
          ·
            refine ⟨103972996607656652187358643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69315331071771101458239095 103972996607656652187358643)
            ·
              refine ⟨155959494911484978281037965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103972996607656652187358643 155959494911484978281037965)
              ·
                refine ⟨58484810591806866855389237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 155959494911484978281037965 58484810591806866855389237)
                ·
                  refine ⟨5482950992981893767692741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58484810591806866855389237 5482950992981893767692741)
                  ·
                    refine ⟨1028053311184105081442389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5482950992981893767692741 1028053311184105081442389)
                    ·
                      rfl

theorem cell23_6006380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 4].length) (baseStart_6006380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6006380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6006380 prefixEnd_6006380 := by exact prefixLift 6006380
  have htrace : WordTrace (prefixWord ++ tailWord_6006380) baseStart_6006380 baseEnd_6006380 := by
    simpa [prefixWord, tailWord_6006380, baseEnd_6006380] using wordTrace_append hprefix tailTrace_6006380
  have hstable : (prefixWord ++ tailWord_6006380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6006380).length < 2 ^ (prefixWord ++ tailWord_6006380).sum := by decide
  have hdescent : baseEnd_6006380 < baseStart_6006380 := by decide
  rcases family_descends (prefixWord ++ tailWord_6006380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6006383 : List Nat := [1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 6]
def baseStart_6006383 : Nat := 118140960795 + 6006383 * 2 ^ 59
def prefixEnd_6006383 : Nat := 4983230072969 + 3 ^ 40 * 6006383 * 2
def baseEnd_6006383 : Nat := 3084161473994278732589653

theorem tailTrace_6006383 : CollatzResearch.WordTrace tailWord_6006383 prefixEnd_6006383 3084161473994278732589653 := by
  unfold tailWord_6006383
  simp only [CollatzResearch.WordTrace]
  refine ⟨219070785398907674392719803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146047190265938449595146535 219070785398907674392719803)
  ·
    refine ⟨328606178098361511589079705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219070785398907674392719803 328606178098361511589079705)
    ·
      refine ⟨246454633573771133691809779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 328606178098361511589079705 246454633573771133691809779)
      ·
        refine ⟨369681950360656700537714669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246454633573771133691809779 369681950360656700537714669)
        ·
          refine ⟨138630731385246262701643001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 369681950360656700537714669 138630731385246262701643001)
          ·
            refine ⟨103973048538934697026232251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138630731385246262701643001 103973048538934697026232251)
            ·
              refine ⟨155959572808402045539348377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103973048538934697026232251 155959572808402045539348377)
              ·
                refine ⟨116969679606301534154511283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 155959572808402045539348377 116969679606301534154511283)
                ·
                  refine ⟨175454519409452301231766925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116969679606301534154511283 175454519409452301231766925)
                  ·
                    refine ⟨65795444778544612961912597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 175454519409452301231766925 65795444778544612961912597)
                    ·
                      refine ⟨3084161473994278732589653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65795444778544612961912597 3084161473994278732589653)
                      ·
                        rfl

theorem cell23_6006383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 6].length) (baseStart_6006383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6006383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6006383 prefixEnd_6006383 := by exact prefixLift 6006383
  have htrace : WordTrace (prefixWord ++ tailWord_6006383) baseStart_6006383 baseEnd_6006383 := by
    simpa [prefixWord, tailWord_6006383, baseEnd_6006383] using wordTrace_append hprefix tailTrace_6006383
  have hstable : (prefixWord ++ tailWord_6006383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6006383).length < 2 ^ (prefixWord ++ tailWord_6006383).sum := by decide
  have hdescent : baseEnd_6006383 < baseStart_6006383 := by decide
  rcases family_descends (prefixWord ++ tailWord_6006383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6006407 : List Nat := [1, 1, 4, 2, 1, 3, 2, 2, 2, 2, 3]
def baseStart_6006407 : Nat := 118140960795 + 6006407 * 2 ^ 59
def prefixEnd_6006407 : Nat := 4983230072969 + 3 ^ 40 * 6006407 * 2
def baseEnd_6006407 : Nat := 3084173797529986638689543

theorem tailTrace_6006407 : CollatzResearch.WordTrace tailWord_6006407 prefixEnd_6006407 3084173797529986638689543 := by
  unfold tailWord_6006407
  simp only [CollatzResearch.WordTrace]
  refine ⟨219071660750820726491593475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146047773833880484327728983 219071660750820726491593475)
  ·
    refine ⟨328607491126231089737390213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219071660750820726491593475 328607491126231089737390213)
    ·
      refine ⟨61613904586168329325760665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 328607491126231089737390213 61613904586168329325760665)
      ·
        refine ⟨46210428439626246994320499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61613904586168329325760665 46210428439626246994320499)
        ·
          refine ⟨69315642659439370491480749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46210428439626246994320499 69315642659439370491480749)
          ·
            refine ⟨25993365997289763934305281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69315642659439370491480749 25993365997289763934305281)
            ·
              refine ⟨19495024497967322950728961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25993365997289763934305281 19495024497967322950728961)
              ·
                refine ⟨14621268373475492213046721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19495024497967322950728961 14621268373475492213046721)
                ·
                  refine ⟨10965951280106619159785041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14621268373475492213046721 10965951280106619159785041)
                  ·
                    refine ⟨8224463460079964369838781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10965951280106619159785041 8224463460079964369838781)
                    ·
                      refine ⟨3084173797529986638689543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8224463460079964369838781 3084173797529986638689543)
                      ·
                        rfl

theorem cell23_6006407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 2, 2, 2, 3].length) (baseStart_6006407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6006407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6006407 prefixEnd_6006407 := by exact prefixLift 6006407
  have htrace : WordTrace (prefixWord ++ tailWord_6006407) baseStart_6006407 baseEnd_6006407 := by
    simpa [prefixWord, tailWord_6006407, baseEnd_6006407] using wordTrace_append hprefix tailTrace_6006407
  have hstable : (prefixWord ++ tailWord_6006407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6006407).length < 2 ^ (prefixWord ++ tailWord_6006407).sum := by decide
  have hdescent : baseEnd_6006407 < baseStart_6006407 := by decide
  rcases family_descends (prefixWord ++ tailWord_6006407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6006437 : List Nat := [1, 3, 1, 2, 1, 2, 3, 1, 5, 1, 3]
def baseStart_6006437 : Nat := 118140960795 + 6006437 * 2 ^ 59
def prefixEnd_6006437 : Nat := 4983230072969 + 3 ^ 40 * 6006437 * 2
def baseEnd_6006437 : Nat := 3084189201949621521314405

theorem tailTrace_6006437 : CollatzResearch.WordTrace tailWord_6006437 prefixEnd_6006437 3084189201949621521314405 := by
  unfold tailWord_6006437
  simp only [CollatzResearch.WordTrace]
  refine ⟨219072754940712041615185565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146048503293808027743457043 219072754940712041615185565)
  ·
    refine ⟨82152283102767015605694587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219072754940712041615185565 82152283102767015605694587)
    ·
      refine ⟨123228424654150523408541881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82152283102767015605694587 123228424654150523408541881)
      ·
        refine ⟨92421318490612892556406411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123228424654150523408541881 92421318490612892556406411)
        ·
          refine ⟨138631977735919338834609617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92421318490612892556406411 138631977735919338834609617)
          ·
            refine ⟨103973983301939504125957213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138631977735919338834609617 103973983301939504125957213)
            ·
              refine ⟨38990243738227314047233955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103973983301939504125957213 38990243738227314047233955)
              ·
                refine ⟨58485365607340971070850933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38990243738227314047233955 58485365607340971070850933)
                ·
                  refine ⟨5483003025688216037892275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58485365607340971070850933 5483003025688216037892275)
                  ·
                    refine ⟨8224504538532324056838413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5483003025688216037892275 8224504538532324056838413)
                    ·
                      refine ⟨3084189201949621521314405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8224504538532324056838413 3084189201949621521314405)
                      ·
                        rfl

theorem cell23_6006437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 5, 1, 3].length) (baseStart_6006437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6006437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6006437 prefixEnd_6006437 := by exact prefixLift 6006437
  have htrace : WordTrace (prefixWord ++ tailWord_6006437) baseStart_6006437 baseEnd_6006437 := by
    simpa [prefixWord, tailWord_6006437, baseEnd_6006437] using wordTrace_append hprefix tailTrace_6006437
  have hstable : (prefixWord ++ tailWord_6006437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6006437).length < 2 ^ (prefixWord ++ tailWord_6006437).sum := by decide
  have hdescent : baseEnd_6006437 < baseStart_6006437 := by decide
  rcases family_descends (prefixWord ++ tailWord_6006437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6006447 : List Nat := [1, 1, 2, 1, 2, 4, 3, 1, 1, 5, 2]
def baseStart_6006447 : Nat := 118140960795 + 6006447 * 2 ^ 59
def prefixEnd_6006447 : Nat := 4983230072969 + 3 ^ 40 * 6006447 * 2
def baseEnd_6006447 : Nat := 3084194336756166482189359

theorem tailTrace_6006447 : CollatzResearch.WordTrace tailWord_6006447 prefixEnd_6006447 3084194336756166482189359 := by
  unfold tailWord_6006447
  simp only [CollatzResearch.WordTrace]
  refine ⟨219073119670675813323049595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146048746447117208882033063 219073119670675813323049595)
  ·
    refine ⟨328609679506013719984574393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219073119670675813323049595 328609679506013719984574393)
    ·
      refine ⟨246457259629510289988430795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 328609679506013719984574393 246457259629510289988430795)
      ·
        refine ⟨369685889444265434982646193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246457259629510289988430795 369685889444265434982646193)
        ·
          refine ⟨277264417083199076236984645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 369685889444265434982646193 277264417083199076236984645)
          ·
            refine ⟨51987078203099826794434621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 277264417083199076236984645 51987078203099826794434621)
            ·
              refine ⟨19495154326162435047912983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51987078203099826794434621 19495154326162435047912983)
              ·
                refine ⟨29242731489243652571869475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19495154326162435047912983 29242731489243652571869475)
                ·
                  refine ⟨43864097233865478857804213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29242731489243652571869475 43864097233865478857804213)
                  ·
                    refine ⟨4112259115674888642919145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43864097233865478857804213 4112259115674888642919145)
                    ·
                      refine ⟨3084194336756166482189359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4112259115674888642919145 3084194336756166482189359)
                      ·
                        rfl

theorem cell23_6006447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 5, 2].length) (baseStart_6006447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6006447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6006447 prefixEnd_6006447 := by exact prefixLift 6006447
  have htrace : WordTrace (prefixWord ++ tailWord_6006447) baseStart_6006447 baseEnd_6006447 := by
    simpa [prefixWord, tailWord_6006447, baseEnd_6006447] using wordTrace_append hprefix tailTrace_6006447
  have hstable : (prefixWord ++ tailWord_6006447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6006447).length < 2 ^ (prefixWord ++ tailWord_6006447).sum := by decide
  have hdescent : baseEnd_6006447 < baseStart_6006447 := by decide
  rcases family_descends (prefixWord ++ tailWord_6006447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6006480 : List Nat := [2, 1, 1, 1, 1, 2, 1, 3, 2, 6, 3]
def baseStart_6006480 : Nat := 118140960795 + 6006480 * 2 ^ 59
def prefixEnd_6006480 : Nat := 4983230072969 + 3 ^ 40 * 6006480 * 2
def baseEnd_6006480 : Nat := 3084211281617764853076707

theorem tailTrace_6006480 : CollatzResearch.WordTrace tailWord_6006480 prefixEnd_6006480 3084211281617764853076707 := by
  unfold tailWord_6006480
  simp only [CollatzResearch.WordTrace]
  refine ⟨109537161639778129979500447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146049548853037506639333929 109537161639778129979500447)
  ·
    refine ⟨164305742459667194969250671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109537161639778129979500447 164305742459667194969250671)
    ·
      refine ⟨246458613689500792453876007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164305742459667194969250671 246458613689500792453876007)
      ·
        refine ⟨369687920534251188680814011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246458613689500792453876007 369687920534251188680814011)
        ·
          refine ⟨554531880801376783021221017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 369687920534251188680814011 554531880801376783021221017)
          ·
            refine ⟨415898910601032587265915763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 554531880801376783021221017 415898910601032587265915763)
            ·
              refine ⟨623848365901548880898873645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 415898910601032587265915763 623848365901548880898873645)
              ·
                refine ⟨233943137213080830337077617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 623848365901548880898873645 233943137213080830337077617)
                ·
                  refine ⟨175457352909810622752808213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 233943137213080830337077617 175457352909810622752808213)
                  ·
                    refine ⟨8224563417647372941537885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 175457352909810622752808213 8224563417647372941537885)
                    ·
                      refine ⟨3084211281617764853076707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8224563417647372941537885 3084211281617764853076707)
                      ·
                        rfl

theorem cell23_6006480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 2, 6, 3].length) (baseStart_6006480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6006480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6006480 prefixEnd_6006480 := by exact prefixLift 6006480
  have htrace : WordTrace (prefixWord ++ tailWord_6006480) baseStart_6006480 baseEnd_6006480 := by
    simpa [prefixWord, tailWord_6006480, baseEnd_6006480] using wordTrace_append hprefix tailTrace_6006480
  have hstable : (prefixWord ++ tailWord_6006480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6006480).length < 2 ^ (prefixWord ++ tailWord_6006480).sum := by decide
  have hdescent : baseEnd_6006480 < baseStart_6006480 := by decide
  rcases family_descends (prefixWord ++ tailWord_6006480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6006500 : List Nat := [2, 3, 1, 1, 1, 3, 3, 9]
def baseStart_6006500 : Nat := 118140960795 + 6006500 * 2 ^ 59
def prefixEnd_6006500 : Nat := 4983230072969 + 3 ^ 40 * 6006500 * 2
def baseEnd_6006500 : Nat := 114230427823364991660245

theorem tailTrace_6006500 : CollatzResearch.WordTrace tailWord_6006500 prefixEnd_6006500 114230427823364991660245 := by
  unfold tailWord_6006500
  simp only [CollatzResearch.WordTrace]
  refine ⟨109537526369741901687364477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146050035159655868916485969 109537526369741901687364477)
  ·
    refine ⟨41076572388653213132761679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109537526369741901687364477 41076572388653213132761679)
    ·
      refine ⟨61614858582979819699142519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41076572388653213132761679 61614858582979819699142519)
      ·
        refine ⟨92422287874469729548713779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61614858582979819699142519 92422287874469729548713779)
        ·
          refine ⟨138633431811704594323070669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92422287874469729548713779 138633431811704594323070669)
          ·
            refine ⟨51987536929389222871151501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138633431811704594323070669 51987536929389222871151501)
            ·
              refine ⟨19495326348520958576681813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51987536929389222871151501 19495326348520958576681813)
              ·
                refine ⟨114230427823364991660245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19495326348520958576681813 114230427823364991660245)
                ·
                  rfl

theorem cell23_6006500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 9].length) (baseStart_6006500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6006500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6006500 prefixEnd_6006500 := by exact prefixLift 6006500
  have htrace : WordTrace (prefixWord ++ tailWord_6006500) baseStart_6006500 baseEnd_6006500 := by
    simpa [prefixWord, tailWord_6006500, baseEnd_6006500] using wordTrace_append hprefix tailTrace_6006500
  have hstable : (prefixWord ++ tailWord_6006500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6006500).length < 2 ^ (prefixWord ++ tailWord_6006500).sum := by decide
  have hdescent : baseEnd_6006500 < baseStart_6006500 := by decide
  rcases family_descends (prefixWord ++ tailWord_6006500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6006514 : List Nat := [3, 2, 1, 3, 1, 1, 1, 5, 1, 2, 3]
def baseStart_6006514 : Nat := 118140960795 + 6006514 * 2 ^ 59
def prefixEnd_6006514 : Nat := 4983230072969 + 3 ^ 40 * 6006514 * 2
def baseEnd_6006514 : Nat := 3084228739960017720051551

theorem tailTrace_6006514 : CollatzResearch.WordTrace tailWord_6006514 prefixEnd_6006514 3084228739960017720051551 := by
  unfold tailWord_6006514
  simp only [CollatzResearch.WordTrace]
  refine ⟨54768890840358270941434649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146050375574288722510492397 54768890840358270941434649)
  ·
    refine ⟨41076668130268703206075987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54768890840358270941434649 41076668130268703206075987)
    ·
      refine ⟨61615002195403054809113981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41076668130268703206075987 61615002195403054809113981)
      ·
        refine ⟨23105625823276145553417743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61615002195403054809113981 23105625823276145553417743)
        ·
          refine ⟨34658438734914218330126615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23105625823276145553417743 34658438734914218330126615)
          ·
            refine ⟨51987658102371327495189923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34658438734914218330126615 51987658102371327495189923)
            ·
              refine ⟨77981487153556991242784885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51987658102371327495189923 77981487153556991242784885)
              ·
                refine ⟨7310764420645967929011083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77981487153556991242784885 7310764420645967929011083)
                ·
                  refine ⟨10966146630968951893516625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7310764420645967929011083 10966146630968951893516625)
                  ·
                    refine ⟨8224609973226713920137469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10966146630968951893516625 8224609973226713920137469)
                    ·
                      refine ⟨3084228739960017720051551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8224609973226713920137469 3084228739960017720051551)
                      ·
                        rfl

theorem cell23_6006514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_6006514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6006514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6006514 prefixEnd_6006514 := by exact prefixLift 6006514
  have htrace : WordTrace (prefixWord ++ tailWord_6006514) baseStart_6006514 baseEnd_6006514 := by
    simpa [prefixWord, tailWord_6006514, baseEnd_6006514] using wordTrace_append hprefix tailTrace_6006514
  have hstable : (prefixWord ++ tailWord_6006514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6006514).length < 2 ^ (prefixWord ++ tailWord_6006514).sum := by decide
  have hdescent : baseEnd_6006514 < baseStart_6006514 := by decide
  rcases family_descends (prefixWord ++ tailWord_6006514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6006537 : List Nat := [1, 2, 1, 1, 3, 2, 1, 1, 2, 7, 2]
def baseStart_6006537 : Nat := 118140960795 + 6006537 * 2 ^ 59
def prefixEnd_6006537 : Nat := 4983230072969 + 3 ^ 40 * 6006537 * 2
def baseEnd_6006537 : Nat := 3084240550015071130063945

theorem tailTrace_6006537 : CollatzResearch.WordTrace tailWord_6006537 prefixEnd_6006537 3084240550015071130063945 := by
  unfold tailWord_6006537
  simp only [CollatzResearch.WordTrace]
  refine ⟨219076402240349758693825865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146050934826899839129217243 219076402240349758693825865)
  ·
    refine ⟨164307301680262319020369399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219076402240349758693825865 164307301680262319020369399)
    ·
      refine ⟨246460952520393478530554099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164307301680262319020369399 246460952520393478530554099)
      ·
        refine ⟨369691428780590217795831149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246460952520393478530554099 369691428780590217795831149)
        ·
          refine ⟨138634285792721331673436681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 369691428780590217795831149 138634285792721331673436681)
          ·
            refine ⟨103975714344540998755077511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138634285792721331673436681 103975714344540998755077511)
            ·
              refine ⟨155963571516811498132616267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103975714344540998755077511 155963571516811498132616267)
              ·
                refine ⟨233945357275217247198924401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155963571516811498132616267 233945357275217247198924401)
                ·
                  refine ⟨175459017956412935399193301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 233945357275217247198924401 175459017956412935399193301)
                  ·
                    refine ⟨4112320733353428173418593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 175459017956412935399193301 4112320733353428173418593)
                    ·
                      refine ⟨3084240550015071130063945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4112320733353428173418593 3084240550015071130063945)
                      ·
                        rfl

theorem cell23_6006537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 7, 2].length) (baseStart_6006537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6006537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6006537 prefixEnd_6006537 := by exact prefixLift 6006537
  have htrace : WordTrace (prefixWord ++ tailWord_6006537) baseStart_6006537 baseEnd_6006537 := by
    simpa [prefixWord, tailWord_6006537, baseEnd_6006537] using wordTrace_append hprefix tailTrace_6006537
  have hstable : (prefixWord ++ tailWord_6006537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6006537).length < 2 ^ (prefixWord ++ tailWord_6006537).sum := by decide
  have hdescent : baseEnd_6006537 < baseStart_6006537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6006537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6006558 : List Nat := [4, 3, 2, 2, 1, 1, 1, 2, 1, 2, 4]
def baseStart_6006558 : Nat := 118140960795 + 6006558 * 2 ^ 59
def prefixEnd_6006558 : Nat := 4983230072969 + 3 ^ 40 * 6006558 * 2
def baseEnd_6006558 : Nat := 3084251333108815547901349

theorem tailTrace_6006558 : CollatzResearch.WordTrace tailWord_6006558 prefixEnd_6006558 3084251333108815547901349 := by
  unfold tailWord_6006558
  simp only [CollatzResearch.WordTrace]
  refine ⟨27384646021659209910042541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146051445448849119520226885 27384646021659209910042541)
  ·
    refine ⟨10269242258122203716265953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27384646021659209910042541 10269242258122203716265953)
    ·
      refine ⟨7701931693591652787199465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10269242258122203716265953 7701931693591652787199465)
      ·
        refine ⟨5776448770193739590399599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7701931693591652787199465 5776448770193739590399599)
        ·
          refine ⟨8664673155290609385599399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5776448770193739590399599 8664673155290609385599399)
          ·
            refine ⟨12997009732935914078399099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8664673155290609385599399 12997009732935914078399099)
            ·
              refine ⟨19495514599403871117598649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12997009732935914078399099 19495514599403871117598649)
              ·
                refine ⟨14621635949552903338198987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19495514599403871117598649 14621635949552903338198987)
                ·
                  refine ⟨21932453924329355007298481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14621635949552903338198987 21932453924329355007298481)
                  ·
                    refine ⟨16449340443247016255473861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21932453924329355007298481 16449340443247016255473861)
                    ·
                      refine ⟨3084251333108815547901349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16449340443247016255473861 3084251333108815547901349)
                      ·
                        rfl

theorem cell23_6006558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_6006558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6006558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6006558 prefixEnd_6006558 := by exact prefixLift 6006558
  have htrace : WordTrace (prefixWord ++ tailWord_6006558) baseStart_6006558 baseEnd_6006558 := by
    simpa [prefixWord, tailWord_6006558, baseEnd_6006558] using wordTrace_append hprefix tailTrace_6006558
  have hstable : (prefixWord ++ tailWord_6006558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6006558).length < 2 ^ (prefixWord ++ tailWord_6006558).sum := by decide
  have hdescent : baseEnd_6006558 < baseStart_6006558 := by decide
  rcases family_descends (prefixWord ++ tailWord_6006558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6006597 : List Nat := [1, 3, 1, 1, 1, 2, 5, 1, 2, 2, 4]
def baseStart_6006597 : Nat := 118140960795 + 6006597 * 2 ^ 59
def prefixEnd_6006597 : Nat := 4983230072969 + 3 ^ 40 * 6006597 * 2
def baseEnd_6006597 : Nat := 3084271358854340895313669

theorem tailTrace_6006597 : CollatzResearch.WordTrace tailWord_6006597 prefixEnd_6006597 3084271358854340895313669 := by
  unfold tailWord_6006597
  simp only [CollatzResearch.WordTrace]
  refine ⟨219078590620132388941010045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146052393746754925960673363 219078590620132388941010045)
  ·
    refine ⟨82154471482549645852878767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219078590620132388941010045 82154471482549645852878767)
    ·
      refine ⟨123231707223824468779318151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82154471482549645852878767 123231707223824468779318151)
      ·
        refine ⟨184847560835736703168977227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123231707223824468779318151 184847560835736703168977227)
        ·
          refine ⟨277271341253605054753465841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184847560835736703168977227 277271341253605054753465841)
          ·
            refine ⟨207953505940203791065099381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 277271341253605054753465841 207953505940203791065099381)
            ·
              refine ⟨19495641181894105412353067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 207953505940203791065099381 19495641181894105412353067)
              ·
                refine ⟨29243461772841158118529601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19495641181894105412353067 29243461772841158118529601)
                ·
                  refine ⟨21932596329630868588897201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29243461772841158118529601 21932596329630868588897201)
                  ·
                    refine ⟨16449447247223151441672901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21932596329630868588897201 16449447247223151441672901)
                    ·
                      refine ⟨3084271358854340895313669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16449447247223151441672901 3084271358854340895313669)
                      ·
                        rfl

theorem cell23_6006597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 2, 2, 4].length) (baseStart_6006597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6006597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6006597 prefixEnd_6006597 := by exact prefixLift 6006597
  have htrace : WordTrace (prefixWord ++ tailWord_6006597) baseStart_6006597 baseEnd_6006597 := by
    simpa [prefixWord, tailWord_6006597, baseEnd_6006597] using wordTrace_append hprefix tailTrace_6006597
  have hstable : (prefixWord ++ tailWord_6006597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6006597).length < 2 ^ (prefixWord ++ tailWord_6006597).sum := by decide
  have hdescent : baseEnd_6006597 < baseStart_6006597 := by decide
  rcases family_descends (prefixWord ++ tailWord_6006597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6006601 : List Nat := [1, 2, 1, 1, 2, 4, 1, 5, 2, 2, 2]
def baseStart_6006601 : Nat := 118140960795 + 6006601 * 2 ^ 59
def prefixEnd_6006601 : Nat := 4983230072969 + 3 ^ 40 * 6006601 * 2
def baseEnd_6006601 : Nat := 3084273412776958879663651

theorem tailTrace_6006601 : CollatzResearch.WordTrace tailWord_6006601 prefixEnd_6006601 3084273412776958879663651 := by
  unfold tailWord_6006601
  simp only [CollatzResearch.WordTrace]
  refine ⟨219078736512117897624155657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146052491008078598416103771 219078736512117897624155657)
  ·
    refine ⟨164309052384088423218116743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219078736512117897624155657 164309052384088423218116743)
    ·
      refine ⟨246463578576132634827175115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164309052384088423218116743 246463578576132634827175115)
      ·
        refine ⟨369695367864198952240762673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246463578576132634827175115 369695367864198952240762673)
        ·
          refine ⟨277271525898149214180572005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 369695367864198952240762673 277271525898149214180572005)
          ·
            refine ⟨51988411105902977658857251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 277271525898149214180572005 51988411105902977658857251)
            ·
              refine ⟨77982616658854466488285877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51988411105902977658857251 77982616658854466488285877)
              ·
                refine ⟨7310870311767606233276801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77982616658854466488285877 7310870311767606233276801)
                ·
                  refine ⟨5483152733825704674957601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7310870311767606233276801 5483152733825704674957601)
                  ·
                    refine ⟨4112364550369278506218201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5483152733825704674957601 4112364550369278506218201)
                    ·
                      refine ⟨3084273412776958879663651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4112364550369278506218201 3084273412776958879663651)
                      ·
                        rfl

theorem cell23_6006601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 5, 2, 2, 2].length) (baseStart_6006601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6006601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6006601 prefixEnd_6006601 := by exact prefixLift 6006601
  have htrace : WordTrace (prefixWord ++ tailWord_6006601) baseStart_6006601 baseEnd_6006601 := by
    simpa [prefixWord, tailWord_6006601, baseEnd_6006601] using wordTrace_append hprefix tailTrace_6006601
  have hstable : (prefixWord ++ tailWord_6006601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6006601).length < 2 ^ (prefixWord ++ tailWord_6006601).sum := by decide
  have hdescent : baseEnd_6006601 < baseStart_6006601 := by decide
  rcases family_descends (prefixWord ++ tailWord_6006601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6006617 : List Nat := [1, 2, 1, 2, 2, 3, 1, 2, 1, 5, 3]
def baseStart_6006617 : Nat := 118140960795 + 6006617 * 2 ^ 59
def prefixEnd_6006617 : Nat := 4983230072969 + 3 ^ 40 * 6006617 * 2
def baseEnd_6006617 : Nat := 3084281628467430817063577

theorem tailTrace_6006617 : CollatzResearch.WordTrace tailWord_6006617 prefixEnd_6006617 3084281628467430817063577 := by
  unfold tailWord_6006617
  simp only [CollatzResearch.WordTrace]
  refine ⟨219079320080059932356738105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146052880053373288237825403 219079320080059932356738105)
  ·
    refine ⟨164309490060044949267553579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219079320080059932356738105 164309490060044949267553579)
    ·
      refine ⟨246464235090067423901330369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164309490060044949267553579 246464235090067423901330369)
      ·
        refine ⟨184848176317550567925997777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246464235090067423901330369 184848176317550567925997777)
        ·
          refine ⟨138636132238162925944498333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184848176317550567925997777 138636132238162925944498333)
          ·
            refine ⟨51988549589311097229186875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138636132238162925944498333 51988549589311097229186875)
            ·
              refine ⟨77982824383966645843780313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51988549589311097229186875 77982824383966645843780313)
              ·
                refine ⟨58487118287974984382835235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77982824383966645843780313 58487118287974984382835235)
                ·
                  refine ⟨87730677431962476574252853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58487118287974984382835235 87730677431962476574252853)
                  ·
                    refine ⟨8224751009246482178836205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 87730677431962476574252853 8224751009246482178836205)
                    ·
                      refine ⟨3084281628467430817063577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8224751009246482178836205 3084281628467430817063577)
                      ·
                        rfl

theorem cell23_6006617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 5, 3].length) (baseStart_6006617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6006617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6006617 prefixEnd_6006617 := by exact prefixLift 6006617
  have htrace : WordTrace (prefixWord ++ tailWord_6006617) baseStart_6006617 baseEnd_6006617 := by
    simpa [prefixWord, tailWord_6006617, baseEnd_6006617] using wordTrace_append hprefix tailTrace_6006617
  have hstable : (prefixWord ++ tailWord_6006617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6006617).length < 2 ^ (prefixWord ++ tailWord_6006617).sum := by decide
  have hdescent : baseEnd_6006617 < baseStart_6006617 := by decide
  rcases family_descends (prefixWord ++ tailWord_6006617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6006624 : List Nat := [2, 1, 1, 3, 3, 2, 1, 5, 5]
def baseStart_6006624 : Nat := 118140960795 + 6006624 * 2 ^ 59
def prefixEnd_6006624 : Nat := 4983230072969 + 3 ^ 40 * 6006624 * 2
def baseEnd_6006624 : Nat := 342698358092445809964005

theorem tailTrace_6006624 : CollatzResearch.WordTrace tailWord_6006624 prefixEnd_6006624 342698358092445809964005 := by
  unfold tailWord_6006624
  simp only [CollatzResearch.WordTrace]
  refine ⟨109539787695517286276121463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146053050260689715034828617 109539787695517286276121463)
  ·
    refine ⟨164309681543275929414182195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109539787695517286276121463 164309681543275929414182195)
    ·
      refine ⟨246464522314913894121273293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164309681543275929414182195 246464522314913894121273293)
      ·
        refine ⟨92424195868092710295477485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 246464522314913894121273293 92424195868092710295477485)
        ·
          refine ⟨34659073450534766360804057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92424195868092710295477485 34659073450534766360804057)
          ·
            refine ⟨25994305087901074770603043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34659073450534766360804057 25994305087901074770603043)
            ·
              refine ⟨38991457631851612155904565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25994305087901074770603043 38991457631851612155904565)
              ·
                refine ⟨3655449152986088639616053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38991457631851612155904565 3655449152986088639616053)
                ·
                  refine ⟨342698358092445809964005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3655449152986088639616053 342698358092445809964005)
                  ·
                    rfl

theorem cell23_6006624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 5, 5].length) (baseStart_6006624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6006624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6006624 prefixEnd_6006624 := by exact prefixLift 6006624
  have htrace : WordTrace (prefixWord ++ tailWord_6006624) baseStart_6006624 baseEnd_6006624 := by
    simpa [prefixWord, tailWord_6006624, baseEnd_6006624] using wordTrace_append hprefix tailTrace_6006624
  have hstable : (prefixWord ++ tailWord_6006624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6006624).length < 2 ^ (prefixWord ++ tailWord_6006624).sum := by decide
  have hdescent : baseEnd_6006624 < baseStart_6006624 := by decide
  rcases family_descends (prefixWord ++ tailWord_6006624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6006737 : List Nat := [1, 2, 2, 1, 2, 1, 2, 1, 2, 4, 5]
def baseStart_6006737 : Nat := 118140960795 + 6006737 * 2 ^ 59
def prefixEnd_6006737 : Nat := 4983230072969 + 3 ^ 40 * 6006737 * 2
def baseEnd_6006737 : Nat := 3084343246145970347563025

theorem tailTrace_6006737 : CollatzResearch.WordTrace tailWord_6006737 prefixEnd_6006737 3084343246145970347563025 := by
  unfold tailWord_6006737
  simp only [CollatzResearch.WordTrace]
  refine ⟨219083696839625192851106465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146055797893083461900737643 219083696839625192851106465)
  ·
    refine ⟨164312772629718894638329849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219083696839625192851106465 164312772629718894638329849)
    ·
      refine ⟨123234579472289170978747387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164312772629718894638329849 123234579472289170978747387)
      ·
        refine ⟨184851869208433756468121081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123234579472289170978747387 184851869208433756468121081)
        ·
          refine ⟨138638901906325317351090811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184851869208433756468121081 138638901906325317351090811)
          ·
            refine ⟨207958352859487976026636217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138638901906325317351090811 207958352859487976026636217)
            ·
              refine ⟨155968764644615982019977163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 207958352859487976026636217 155968764644615982019977163)
              ·
                refine ⟨233953146966923973029965745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155968764644615982019977163 233953146966923973029965745)
                ·
                  refine ⟨175464860225192979772474309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 233953146966923973029965745 175464860225192979772474309)
                  ·
                    refine ⟨32899661292223683707338933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 175464860225192979772474309 32899661292223683707338933)
                    ·
                      refine ⟨3084343246145970347563025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32899661292223683707338933 3084343246145970347563025)
                      ·
                        rfl

theorem cell23_6006737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 4, 5].length) (baseStart_6006737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6006737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6006737 prefixEnd_6006737 := by exact prefixLift 6006737
  have htrace : WordTrace (prefixWord ++ tailWord_6006737) baseStart_6006737 baseEnd_6006737 := by
    simpa [prefixWord, tailWord_6006737, baseEnd_6006737] using wordTrace_append hprefix tailTrace_6006737
  have hstable : (prefixWord ++ tailWord_6006737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6006737).length < 2 ^ (prefixWord ++ tailWord_6006737).sum := by decide
  have hdescent : baseEnd_6006737 < baseStart_6006737 := by decide
  rcases family_descends (prefixWord ++ tailWord_6006737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6006787 : List Nat := [1, 1, 1, 3, 2, 1, 1, 13]
def baseStart_6006787 : Nat := 118140960795 + 6006787 * 2 ^ 59
def prefixEnd_6006787 : Nat := 4983230072969 + 3 ^ 40 * 6006787 * 2
def baseEnd_6006787 : Nat := 114235885932544264886585

theorem tailTrace_6006787 : CollatzResearch.WordTrace tailWord_6006787 prefixEnd_6006787 114235885932544264886585 := by
  unfold tailWord_6006787
  simp only [CollatzResearch.WordTrace]
  refine ⟨219085520489444051390426615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146057013659629367593617743 219085520489444051390426615)
  ·
    refine ⟨328628280734166077085639923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219085520489444051390426615 328628280734166077085639923)
    ·
      refine ⟨492942421101249115628459885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328628280734166077085639923 492942421101249115628459885)
      ·
        refine ⟨184853407912968418360672457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 492942421101249115628459885 184853407912968418360672457)
        ·
          refine ⟨138640055934726313770504343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184853407912968418360672457 138640055934726313770504343)
          ·
            refine ⟨207960083902089470655756515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138640055934726313770504343 207960083902089470655756515)
            ·
              refine ⟨311940125853134205983634773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207960083902089470655756515 311940125853134205983634773)
              ·
                refine ⟨114235885932544264886585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 311940125853134205983634773 114235885932544264886585)
                ·
                  rfl

theorem cell23_6006787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 13].length) (baseStart_6006787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6006787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6006787 prefixEnd_6006787 := by exact prefixLift 6006787
  have htrace : WordTrace (prefixWord ++ tailWord_6006787) baseStart_6006787 baseEnd_6006787 := by
    simpa [prefixWord, tailWord_6006787, baseEnd_6006787] using wordTrace_append hprefix tailTrace_6006787
  have hstable : (prefixWord ++ tailWord_6006787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6006787).length < 2 ^ (prefixWord ++ tailWord_6006787).sum := by decide
  have hdescent : baseEnd_6006787 < baseStart_6006787 := by decide
  rcases family_descends (prefixWord ++ tailWord_6006787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6006798 : List Nat := [4, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2]
def baseStart_6006798 : Nat := 118140960795 + 6006798 * 2 ^ 59
def prefixEnd_6006798 : Nat := 4983230072969 + 3 ^ 40 * 6006798 * 2
def baseEnd_6006798 : Nat := 3084374568465894608900245

theorem tailTrace_6006798 : CollatzResearch.WordTrace tailWord_6006798 prefixEnd_6006798 3084374568465894608900245 := by
  unfold tailWord_6006798
  simp only [CollatzResearch.WordTrace]
  refine ⟨27385740211550525033634631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146057281128269466846051365 27385740211550525033634631)
  ·
    refine ⟨41078610317325787550451947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27385740211550525033634631 41078610317325787550451947)
    ·
      refine ⟨61617915475988681325677921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41078610317325787550451947 61617915475988681325677921)
      ·
        refine ⟨46213436606991510994258441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61617915475988681325677921 46213436606991510994258441)
        ·
          refine ⟨34660077455243633245693831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46213436606991510994258441 34660077455243633245693831)
          ·
            refine ⟨51990116182865449868540747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34660077455243633245693831 51990116182865449868540747)
            ·
              refine ⟨77985174274298174802811121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51990116182865449868540747 77985174274298174802811121)
              ·
                refine ⟨58488880705723631102108341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77985174274298174802811121 58488880705723631102108341)
                ·
                  refine ⟨5483332566161590415822657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58488880705723631102108341 5483332566161590415822657)
                  ·
                    refine ⟨4112499424621192811866993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5483332566161590415822657 4112499424621192811866993)
                    ·
                      refine ⟨3084374568465894608900245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4112499424621192811866993 3084374568465894608900245)
                      ·
                        rfl

theorem cell23_6006798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2].length) (baseStart_6006798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6006798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6006798 prefixEnd_6006798 := by exact prefixLift 6006798
  have htrace : WordTrace (prefixWord ++ tailWord_6006798) baseStart_6006798 baseEnd_6006798 := by
    simpa [prefixWord, tailWord_6006798, baseEnd_6006798] using wordTrace_append hprefix tailTrace_6006798
  have hstable : (prefixWord ++ tailWord_6006798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6006798).length < 2 ^ (prefixWord ++ tailWord_6006798).sum := by decide
  have hdescent : baseEnd_6006798 < baseStart_6006798 := by decide
  rcases family_descends (prefixWord ++ tailWord_6006798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6006815 : List Nat := [1, 1, 2, 4, 1, 2, 1, 6, 1, 2, 2]
def baseStart_6006815 : Nat := 118140960795 + 6006815 * 2 ^ 59
def prefixEnd_6006815 : Nat := 4983230072969 + 3 ^ 40 * 6006815 * 2
def baseEnd_6006815 : Nat := 3084383297637021042387667

theorem tailTrace_6006815 : CollatzResearch.WordTrace tailWord_6006815 prefixEnd_6006815 3084383297637021042387667 := by
  unfold tailWord_6006815
  simp only [CollatzResearch.WordTrace]
  refine ⟨219086541733342612172445899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146057694488895074781630599 219086541733342612172445899)
  ·
    refine ⟨328629812600013918258668849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219086541733342612172445899 328629812600013918258668849)
    ·
      refine ⟨246472359450010438694001637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 328629812600013918258668849 246472359450010438694001637)
      ·
        refine ⟨46213567396876957255125307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 246472359450010438694001637 46213567396876957255125307)
        ·
          refine ⟨69320351095315435882687961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46213567396876957255125307 69320351095315435882687961)
          ·
            refine ⟨51990263321486576912015971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69320351095315435882687961 51990263321486576912015971)
            ·
              refine ⟨77985394982229865368023957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51990263321486576912015971 77985394982229865368023957)
              ·
                refine ⟨3655565389792024939126123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 77985394982229865368023957 3655565389792024939126123)
                ·
                  refine ⟨5483348084688037408689185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3655565389792024939126123 5483348084688037408689185)
                  ·
                    refine ⟨4112511063516028056516889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5483348084688037408689185 4112511063516028056516889)
                    ·
                      refine ⟨3084383297637021042387667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4112511063516028056516889 3084383297637021042387667)
                      ·
                        rfl

theorem cell23_6006815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 6, 1, 2, 2].length) (baseStart_6006815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6006815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6006815 prefixEnd_6006815 := by exact prefixLift 6006815
  have htrace : WordTrace (prefixWord ++ tailWord_6006815) baseStart_6006815 baseEnd_6006815 := by
    simpa [prefixWord, tailWord_6006815, baseEnd_6006815] using wordTrace_append hprefix tailTrace_6006815
  have hstable : (prefixWord ++ tailWord_6006815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6006815).length < 2 ^ (prefixWord ++ tailWord_6006815).sum := by decide
  have hdescent : baseEnd_6006815 < baseStart_6006815 := by decide
  rcases family_descends (prefixWord ++ tailWord_6006815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6006844 : List Nat := [2, 2, 2, 2, 2, 1, 1, 1, 1, 4, 5]
def baseStart_6006844 : Nat := 118140960795 + 6006844 * 2 ^ 59
def prefixEnd_6006844 : Nat := 4983230072969 + 3 ^ 40 * 6006844 * 2
def baseEnd_6006844 : Nat := 3084398188576001428925033

theorem tailTrace_6006844 : CollatzResearch.WordTrace tailWord_6006844 prefixEnd_6006844 3084398188576001428925033 := by
  unfold tailWord_6006844
  simp only [CollatzResearch.WordTrace]
  refine ⟨109543799725118775062625793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146058399633491700083501057 109543799725118775062625793)
  ·
    refine ⟨82157849793839081296969345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109543799725118775062625793 82157849793839081296969345)
    ·
      refine ⟨61618387345379310972727009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82157849793839081296969345 61618387345379310972727009)
      ·
        refine ⟨46213790509034483229545257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61618387345379310972727009 46213790509034483229545257)
        ·
          refine ⟨34660342881775862422158943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46213790509034483229545257 34660342881775862422158943)
          ·
            refine ⟨51990514322663793633238415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34660342881775862422158943 51990514322663793633238415)
            ·
              refine ⟨77985771483995690449857623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51990514322663793633238415 77985771483995690449857623)
              ·
                refine ⟨116978657225993535674786435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77985771483995690449857623 116978657225993535674786435)
                ·
                  refine ⟨175467985838990303512179653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116978657225993535674786435 175467985838990303512179653)
                  ·
                    refine ⟨32900247344810681908533685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 175467985838990303512179653 32900247344810681908533685)
                    ·
                      refine ⟨3084398188576001428925033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32900247344810681908533685 3084398188576001428925033)
                      ·
                        rfl

theorem cell23_6006844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_6006844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6006844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6006844 prefixEnd_6006844 := by exact prefixLift 6006844
  have htrace : WordTrace (prefixWord ++ tailWord_6006844) baseStart_6006844 baseEnd_6006844 := by
    simpa [prefixWord, tailWord_6006844, baseEnd_6006844] using wordTrace_append hprefix tailTrace_6006844
  have hstable : (prefixWord ++ tailWord_6006844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6006844).length < 2 ^ (prefixWord ++ tailWord_6006844).sum := by decide
  have hdescent : baseEnd_6006844 < baseStart_6006844 := by decide
  rcases family_descends (prefixWord ++ tailWord_6006844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6006849 : List Nat := [1, 2, 5, 1, 2, 3, 1, 3, 1, 2, 2]
def baseStart_6006849 : Nat := 118140960795 + 6006849 * 2 ^ 59
def prefixEnd_6006849 : Nat := 4983230072969 + 3 ^ 40 * 6006849 * 2
def baseEnd_6006849 : Nat := 3084400755979273909362511

theorem tailTrace_6006849 : CollatzResearch.WordTrace tailWord_6006849 prefixEnd_6006849 3084400755979273909362511 := by
  unfold tailWord_6006849
  simp only [CollatzResearch.WordTrace]
  refine ⟨219087781815219435979183601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146058521210146290652789067 219087781815219435979183601)
  ·
    refine ⟨164315836361414576984387701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219087781815219435979183601 164315836361414576984387701)
    ·
      refine ⟨15404609658882616592286347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 164315836361414576984387701 15404609658882616592286347)
      ·
        refine ⟨23106914488323924888429521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15404609658882616592286347 23106914488323924888429521)
        ·
          refine ⟨17330185866242943666322141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23106914488323924888429521 17330185866242943666322141)
          ·
            refine ⟨6498819699841103874870803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17330185866242943666322141 6498819699841103874870803)
            ·
              refine ⟨9748229549761655812306205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6498819699841103874870803 9748229549761655812306205)
              ·
                refine ⟨3655586081160620929614827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9748229549761655812306205 3655586081160620929614827)
                ·
                  refine ⟨5483379121740931394422241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3655586081160620929614827 5483379121740931394422241)
                  ·
                    refine ⟨4112534341305698545816681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5483379121740931394422241 4112534341305698545816681)
                    ·
                      refine ⟨3084400755979273909362511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4112534341305698545816681 3084400755979273909362511)
                      ·
                        rfl

theorem cell23_6006849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 3, 1, 2, 2].length) (baseStart_6006849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6006849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6006849 prefixEnd_6006849 := by exact prefixLift 6006849
  have htrace : WordTrace (prefixWord ++ tailWord_6006849) baseStart_6006849 baseEnd_6006849 := by
    simpa [prefixWord, tailWord_6006849, baseEnd_6006849] using wordTrace_append hprefix tailTrace_6006849
  have hstable : (prefixWord ++ tailWord_6006849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6006849).length < 2 ^ (prefixWord ++ tailWord_6006849).sum := by decide
  have hdescent : baseEnd_6006849 < baseStart_6006849 := by decide
  rcases family_descends (prefixWord ++ tailWord_6006849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6006861 : List Nat := [1, 6, 1, 1, 1, 1, 1, 2, 2, 2, 5]
def baseStart_6006861 : Nat := 118140960795 + 6006861 * 2 ^ 59
def prefixEnd_6006861 : Nat := 4983230072969 + 3 ^ 40 * 6006861 * 2
def baseEnd_6006861 : Nat := 3084406917747127862412455

theorem tailTrace_6006861 : CollatzResearch.WordTrace tailWord_6006861 prefixEnd_6006861 3084406917747127862412455 := by
  unfold tailWord_6006861
  simp only [CollatzResearch.WordTrace]
  refine ⟨219088219491175962028620437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146058812994117308019080291 219088219491175962028620437)
  ·
    refine ⟨10269760288648873220091583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 219088219491175962028620437 10269760288648873220091583)
    ·
      refine ⟨15404640432973309830137375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10269760288648873220091583 15404640432973309830137375)
      ·
        refine ⟨23106960649459964745206063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15404640432973309830137375 23106960649459964745206063)
        ·
          refine ⟨34660440974189947117809095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23106960649459964745206063 34660440974189947117809095)
          ·
            refine ⟨51990661461284920676713643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34660440974189947117809095 51990661461284920676713643)
            ·
              refine ⟨77985992191927381015070465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51990661461284920676713643 77985992191927381015070465)
              ·
                refine ⟨58489494143945535761302849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77985992191927381015070465 58489494143945535761302849)
                ·
                  refine ⟨43867120607959151820977137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58489494143945535761302849 43867120607959151820977137)
                  ·
                    refine ⟨32900340455969363865732853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43867120607959151820977137 32900340455969363865732853)
                    ·
                      refine ⟨3084406917747127862412455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32900340455969363865732853 3084406917747127862412455)
                      ·
                        rfl

theorem cell23_6006861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_6006861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6006861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6006861 prefixEnd_6006861 := by exact prefixLift 6006861
  have htrace : WordTrace (prefixWord ++ tailWord_6006861) baseStart_6006861 baseEnd_6006861 := by
    simpa [prefixWord, tailWord_6006861, baseEnd_6006861] using wordTrace_append hprefix tailTrace_6006861
  have hstable : (prefixWord ++ tailWord_6006861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6006861).length < 2 ^ (prefixWord ++ tailWord_6006861).sum := by decide
  have hdescent : baseEnd_6006861 < baseStart_6006861 := by decide
  rcases family_descends (prefixWord ++ tailWord_6006861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6006874 : List Nat := [3, 1, 1, 2, 1, 1, 3, 2, 1, 3, 5]
def baseStart_6006874 : Nat := 118140960795 + 6006874 * 2 ^ 59
def prefixEnd_6006874 : Nat := 4983230072969 + 3 ^ 40 * 6006874 * 2
def baseEnd_6006874 : Nat := 3084413592995636311549895

theorem tailTrace_6006874 : CollatzResearch.WordTrace tailWord_6006874 prefixEnd_6006874 3084413592995636311549895 := by
  unfold tailWord_6006874
  simp only [CollatzResearch.WordTrace]
  refine ⟨54772173410032216312210919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146059129093419243499229117 54772173410032216312210919)
  ·
    refine ⟨82158260115048324468316379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54772173410032216312210919 82158260115048324468316379)
    ·
      refine ⟨123237390172572486702474569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82158260115048324468316379 123237390172572486702474569)
      ·
        refine ⟨92428042629429365026855927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123237390172572486702474569 92428042629429365026855927)
        ·
          refine ⟨138642063944144047540283891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92428042629429365026855927 138642063944144047540283891)
          ·
            refine ⟨207963095916216071310425837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138642063944144047540283891 207963095916216071310425837)
            ·
              refine ⟨77986160968581026741409689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 207963095916216071310425837 77986160968581026741409689)
              ·
                refine ⟨58489620726435770056057267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77986160968581026741409689 58489620726435770056057267)
                ·
                  refine ⟨87734431089653655084085901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58489620726435770056057267 87734431089653655084085901)
                  ·
                    refine ⟨32900411658620120656532213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 87734431089653655084085901 32900411658620120656532213)
                    ·
                      refine ⟨3084413592995636311549895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32900411658620120656532213 3084413592995636311549895)
                      ·
                        rfl

theorem cell23_6006874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_6006874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6006874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6006874 prefixEnd_6006874 := by exact prefixLift 6006874
  have htrace : WordTrace (prefixWord ++ tailWord_6006874) baseStart_6006874 baseEnd_6006874 := by
    simpa [prefixWord, tailWord_6006874, baseEnd_6006874] using wordTrace_append hprefix tailTrace_6006874
  have hstable : (prefixWord ++ tailWord_6006874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6006874).length < 2 ^ (prefixWord ++ tailWord_6006874).sum := by decide
  have hdescent : baseEnd_6006874 < baseStart_6006874 := by decide
  rcases family_descends (prefixWord ++ tailWord_6006874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6006882 : List Nat := [3, 3, 2, 2, 2, 1, 1, 3, 2, 1, 3]
def baseStart_6006882 : Nat := 118140960795 + 6006882 * 2 ^ 59
def prefixEnd_6006882 : Nat := 4983230072969 + 3 ^ 40 * 6006882 * 2
def baseEnd_6006882 : Nat := 3084417700840872280249859

theorem tailTrace_6006882 : CollatzResearch.WordTrace tailWord_6006882 prefixEnd_6006882 3084417700840872280249859 := by
  unfold tailWord_6006882
  simp only [CollatzResearch.WordTrace]
  refine ⟨54772246356024970653783725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146059323616066588410089933 54772246356024970653783725)
  ·
    refine ⟨20539592383509363995168897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54772246356024970653783725 20539592383509363995168897)
    ·
      refine ⟨15404694287632022996376673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20539592383509363995168897 15404694287632022996376673)
      ·
        refine ⟨11553520715724017247282505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15404694287632022996376673 11553520715724017247282505)
        ·
          refine ⟨8665140536793012935461879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11553520715724017247282505 8665140536793012935461879)
          ·
            refine ⟨12997710805189519403192819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8665140536793012935461879 12997710805189519403192819)
            ·
              refine ⟨19496566207784279104789229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12997710805189519403192819 19496566207784279104789229)
              ·
                refine ⟨7311212327919104664295961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19496566207784279104789229 7311212327919104664295961)
                ·
                  refine ⟨5483409245939328498221971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7311212327919104664295961 5483409245939328498221971)
                  ·
                    refine ⟨8225113868908992747332957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5483409245939328498221971 8225113868908992747332957)
                    ·
                      refine ⟨3084417700840872280249859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8225113868908992747332957 3084417700840872280249859)
                      ·
                        rfl

theorem cell23_6006882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_6006882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6006882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6006882 prefixEnd_6006882 := by exact prefixLift 6006882
  have htrace : WordTrace (prefixWord ++ tailWord_6006882) baseStart_6006882 baseEnd_6006882 := by
    simpa [prefixWord, tailWord_6006882, baseEnd_6006882] using wordTrace_append hprefix tailTrace_6006882
  have hstable : (prefixWord ++ tailWord_6006882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6006882).length < 2 ^ (prefixWord ++ tailWord_6006882).sum := by decide
  have hdescent : baseEnd_6006882 < baseStart_6006882 := by decide
  rcases family_descends (prefixWord ++ tailWord_6006882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6006921 : List Nat := [1, 2, 1, 1, 4, 2, 2, 2, 2, 3, 3]
def baseStart_6006921 : Nat := 118140960795 + 6006921 * 2 ^ 59
def prefixEnd_6006921 : Nat := 4983230072969 + 3 ^ 40 * 6006921 * 2
def baseEnd_6006921 : Nat := 3084437726586397627662179

theorem tailTrace_6006921 : CollatzResearch.WordTrace tailWord_6006921 prefixEnd_6006921 3084437726586397627662179 := by
  unfold tailWord_6006921
  simp only [CollatzResearch.WordTrace]
  refine ⟨219090407870958592275804617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146060271913972394850536411 219090407870958592275804617)
  ·
    refine ⟨164317805903218944206853463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219090407870958592275804617 164317805903218944206853463)
    ·
      refine ⟨246476708854828416310280195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164317805903218944206853463 246476708854828416310280195)
      ·
        refine ⟨369715063282242624465420293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246476708854828416310280195 369715063282242624465420293)
        ·
          refine ⟨69321574365420492087266305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 369715063282242624465420293 69321574365420492087266305)
          ·
            refine ⟨51991180774065369065449729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69321574365420492087266305 51991180774065369065449729)
            ·
              refine ⟨38993385580549026799087297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51991180774065369065449729 38993385580549026799087297)
              ·
                refine ⟨29245039185411770099315473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38993385580549026799087297 29245039185411770099315473)
                ·
                  refine ⟨21933779389058827574486605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29245039185411770099315473 21933779389058827574486605)
                  ·
                    refine ⟨8225167270897060340432477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21933779389058827574486605 8225167270897060340432477)
                    ·
                      refine ⟨3084437726586397627662179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8225167270897060340432477 3084437726586397627662179)
                      ·
                        rfl

theorem cell23_6006921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 2, 3, 3].length) (baseStart_6006921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6006921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6006921 prefixEnd_6006921 := by exact prefixLift 6006921
  have htrace : WordTrace (prefixWord ++ tailWord_6006921) baseStart_6006921 baseEnd_6006921 := by
    simpa [prefixWord, tailWord_6006921, baseEnd_6006921] using wordTrace_append hprefix tailTrace_6006921
  have hstable : (prefixWord ++ tailWord_6006921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6006921).length < 2 ^ (prefixWord ++ tailWord_6006921).sum := by decide
  have hdescent : baseEnd_6006921 < baseStart_6006921 := by decide
  rcases family_descends (prefixWord ++ tailWord_6006921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6006922 : List Nat := [3, 1, 2, 3, 1, 3, 2, 2, 2, 2, 2]
def baseStart_6006922 : Nat := 118140960795 + 6006922 * 2 ^ 59
def prefixEnd_6006922 : Nat := 4983230072969 + 3 ^ 40 * 6006922 * 2
def baseEnd_6006922 : Nat := 3084438240067052123749675

theorem tailTrace_6006922 : CollatzResearch.WordTrace tailWord_6006922 prefixEnd_6006922 3084438240067052123749675 := by
  unfold tailWord_6006922
  simp only [CollatzResearch.WordTrace]
  refine ⟨54772611085988742361647755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146060296229303312964394013 54772611085988742361647755)
  ·
    refine ⟨82158916628983113542471633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54772611085988742361647755 82158916628983113542471633)
    ·
      refine ⟨61619187471737335156853725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82158916628983113542471633 61619187471737335156853725)
      ·
        refine ⟨23107195301901500683820147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61619187471737335156853725 23107195301901500683820147)
        ·
          refine ⟨34660792952852251025730221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23107195301901500683820147 34660792952852251025730221)
          ·
            refine ⟨12997797357319594134648833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34660792952852251025730221 12997797357319594134648833)
            ·
              refine ⟨9748348017989695600986625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12997797357319594134648833 9748348017989695600986625)
              ·
                refine ⟨7311261013492271700739969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9748348017989695600986625 7311261013492271700739969)
                ·
                  refine ⟨5483445760119203775554977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7311261013492271700739969 5483445760119203775554977)
                  ·
                    refine ⟨4112584320089402831666233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5483445760119203775554977 4112584320089402831666233)
                    ·
                      refine ⟨3084438240067052123749675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4112584320089402831666233 3084438240067052123749675)
                      ·
                        rfl

theorem cell23_6006922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 2, 2, 2, 2].length) (baseStart_6006922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6006922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6006922 prefixEnd_6006922 := by exact prefixLift 6006922
  have htrace : WordTrace (prefixWord ++ tailWord_6006922) baseStart_6006922 baseEnd_6006922 := by
    simpa [prefixWord, tailWord_6006922, baseEnd_6006922] using wordTrace_append hprefix tailTrace_6006922
  have hstable : (prefixWord ++ tailWord_6006922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6006922).length < 2 ^ (prefixWord ++ tailWord_6006922).sum := by decide
  have hdescent : baseEnd_6006922 < baseStart_6006922 := by decide
  rcases family_descends (prefixWord ++ tailWord_6006922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6006924 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 5, 7]
def baseStart_6006924 : Nat := 118140960795 + 6006924 * 2 ^ 59
def prefixEnd_6006924 : Nat := 4983230072969 + 3 ^ 40 * 6006924 * 2
def baseEnd_6006924 : Nat := 1028146422342787038641555

theorem tailTrace_6006924 : CollatzResearch.WordTrace tailWord_6006924 prefixEnd_6006924 1028146422342787038641555 := by
  unfold tailWord_6006924
  simp only [CollatzResearch.WordTrace]
  refine ⟨109545258644973861894081913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146060344859965149192109217 109545258644973861894081913)
  ·
    refine ⟨82158943983730396420561435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109545258644973861894081913 82158943983730396420561435)
    ·
      refine ⟨123238415975595594630842153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82158943983730396420561435 123238415975595594630842153)
      ·
        refine ⟨92428811981696695973131615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123238415975595594630842153 92428811981696695973131615)
        ·
          refine ⟨138643217972545043959697423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92428811981696695973131615 138643217972545043959697423)
          ·
            refine ⟨207964826958817565939546135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138643217972545043959697423 207964826958817565939546135)
            ·
              refine ⟨311947240438226348909319203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207964826958817565939546135 311947240438226348909319203)
              ·
                refine ⟨467920860657339523363978805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 311947240438226348909319203 467920860657339523363978805)
                ·
                  refine ⟨43867580686625580315373013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 467920860657339523363978805 43867580686625580315373013)
                  ·
                    refine ⟨1028146422342787038641555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43867580686625580315373013 1028146422342787038641555)
                    ·
                      rfl

theorem cell23_6006924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 5, 7].length) (baseStart_6006924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6006924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6006924 prefixEnd_6006924 := by exact prefixLift 6006924
  have htrace : WordTrace (prefixWord ++ tailWord_6006924) baseStart_6006924 baseEnd_6006924 := by
    simpa [prefixWord, tailWord_6006924, baseEnd_6006924] using wordTrace_append hprefix tailTrace_6006924
  have hstable : (prefixWord ++ tailWord_6006924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6006924).length < 2 ^ (prefixWord ++ tailWord_6006924).sum := by decide
  have hdescent : baseEnd_6006924 < baseStart_6006924 := by decide
  rcases family_descends (prefixWord ++ tailWord_6006924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6006971 : List Nat := [1, 1, 1, 1, 1, 2, 5, 2, 5, 4]
def baseStart_6006971 : Nat := 118140960795 + 6006971 * 2 ^ 59
def prefixEnd_6006971 : Nat := 4983230072969 + 3 ^ 40 * 6006971 * 2
def baseEnd_6006971 : Nat := 1028154466873040810678983

theorem tailTrace_6006971 : CollatzResearch.WordTrace tailWord_6006971 prefixEnd_6006971 1028154466873040810678983 := by
  unfold tailWord_6006971
  simp only [CollatzResearch.WordTrace]
  refine ⟨219092231520777450815124767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146061487680518300543416511 219092231520777450815124767)
  ·
    refine ⟨328638347281166176222687151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219092231520777450815124767 328638347281166176222687151)
    ·
      refine ⟨492957520921749264334030727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328638347281166176222687151 492957520921749264334030727)
      ·
        refine ⟨739436281382623896501046091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 492957520921749264334030727 739436281382623896501046091)
        ·
          refine ⟨1109154422073935844751569137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 739436281382623896501046091 1109154422073935844751569137)
          ·
            refine ⟨831865816555451883563676853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1109154422073935844751569137 831865816555451883563676853)
            ·
              refine ⟨77987420302073614084094705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 831865816555451883563676853 77987420302073614084094705)
              ·
                refine ⟨58490565226555210563071029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77987420302073614084094705 58490565226555210563071029)
                ·
                  refine ⟨5483490489989550990287909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58490565226555210563071029 5483490489989550990287909)
                  ·
                    refine ⟨1028154466873040810678983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5483490489989550990287909 1028154466873040810678983)
                    ·
                      rfl

theorem cell23_6006971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 5, 4].length) (baseStart_6006971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6006971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6006971 prefixEnd_6006971 := by exact prefixLift 6006971
  have htrace : WordTrace (prefixWord ++ tailWord_6006971) baseStart_6006971 baseEnd_6006971 := by
    simpa [prefixWord, tailWord_6006971, baseEnd_6006971] using wordTrace_append hprefix tailTrace_6006971
  have hstable : (prefixWord ++ tailWord_6006971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6006971).length < 2 ^ (prefixWord ++ tailWord_6006971).sum := by decide
  have hdescent : baseEnd_6006971 < baseStart_6006971 := by decide
  rcases family_descends (prefixWord ++ tailWord_6006971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6007001 : List Nat := [1, 2, 1, 2, 3, 1, 2, 5, 6]
def baseStart_6007001 : Nat := 118140960795 + 6007001 * 2 ^ 59
def prefixEnd_6007001 : Nat := 4983230072969 + 3 ^ 40 * 6007001 * 2
def baseEnd_6007001 : Nat := 342719867226528590517979

theorem tailTrace_6007001 : CollatzResearch.WordTrace tailWord_6007001 prefixEnd_6007001 342719867226528590517979 := by
  unfold tailWord_6007001
  simp only [CollatzResearch.WordTrace]
  refine ⟨219093325710668765938716857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146062217140445843959144571 219093325710668765938716857)
  ·
    refine ⟨164319994283001574454037643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219093325710668765938716857 164319994283001574454037643)
    ·
      refine ⟨246479991424502361681056465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164319994283001574454037643 246479991424502361681056465)
      ·
        refine ⟨184859993568376771260792349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246479991424502361681056465 184859993568376771260792349)
        ·
          refine ⟨69322497588141289222797131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184859993568376771260792349 69322497588141289222797131)
          ·
            refine ⟨103983746382211933834195697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69322497588141289222797131 103983746382211933834195697)
            ·
              refine ⟨77987809786658950375646773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103983746382211933834195697 77987809786658950375646773)
              ·
                refine ⟨7311357167499276597716885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77987809786658950375646773 7311357167499276597716885)
                ·
                  refine ⟨342719867226528590517979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7311357167499276597716885 342719867226528590517979)
                  ·
                    rfl

theorem cell23_6007001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 5, 6].length) (baseStart_6007001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6007001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6007001 prefixEnd_6007001 := by exact prefixLift 6007001
  have htrace : WordTrace (prefixWord ++ tailWord_6007001) baseStart_6007001 baseEnd_6007001 := by
    simpa [prefixWord, tailWord_6007001, baseEnd_6007001] using wordTrace_append hprefix tailTrace_6007001
  have hstable : (prefixWord ++ tailWord_6007001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6007001).length < 2 ^ (prefixWord ++ tailWord_6007001).sum := by decide
  have hdescent : baseEnd_6007001 < baseStart_6007001 := by decide
  rcases family_descends (prefixWord ++ tailWord_6007001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6007005 : List Nat := [1, 4, 3, 2, 1, 1, 2, 2, 3, 4]
def baseStart_6007005 : Nat := 118140960795 + 6007005 * 2 ^ 59
def prefixEnd_6007005 : Nat := 4983230072969 + 3 ^ 40 * 6007005 * 2
def baseEnd_6007005 : Nat := 1028160286320458433003931

theorem tailTrace_6007005 : CollatzResearch.WordTrace tailWord_6007005 prefixEnd_6007005 1028160286320458433003931 := by
  unfold tailWord_6007005
  simp only [CollatzResearch.WordTrace]
  refine ⟨219093471602654274621862469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146062314401769516414574979 219093471602654274621862469)
  ·
    refine ⟨41080025925497676491599213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 219093471602654274621862469 41080025925497676491599213)
    ·
      refine ⟨15405009722061628684349705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41080025925497676491599213 15405009722061628684349705)
      ·
        refine ⟨11553757291546221513262279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15405009722061628684349705 11553757291546221513262279)
        ·
          refine ⟨17330635937319332269893419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11553757291546221513262279 17330635937319332269893419)
          ·
            refine ⟨25995953905978998404840129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17330635937319332269893419 25995953905978998404840129)
            ·
              refine ⟨19496965429484248803630097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25995953905978998404840129 19496965429484248803630097)
              ·
                refine ⟨14622724072113186602722573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19496965429484248803630097 14622724072113186602722573)
                ·
                  refine ⟨5483521527042444976020965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14622724072113186602722573 5483521527042444976020965)
                  ·
                    refine ⟨1028160286320458433003931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5483521527042444976020965 1028160286320458433003931)
                    ·
                      rfl

theorem cell23_6007005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_6007005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6007005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6007005 prefixEnd_6007005 := by exact prefixLift 6007005
  have htrace : WordTrace (prefixWord ++ tailWord_6007005) baseStart_6007005 baseEnd_6007005 := by
    simpa [prefixWord, tailWord_6007005, baseEnd_6007005] using wordTrace_append hprefix tailTrace_6007005
  have hstable : (prefixWord ++ tailWord_6007005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6007005).length < 2 ^ (prefixWord ++ tailWord_6007005).sum := by decide
  have hdescent : baseEnd_6007005 < baseStart_6007005 := by decide
  rcases family_descends (prefixWord ++ tailWord_6007005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6007072 : List Nat := [2, 1, 1, 5, 2, 2, 2, 1, 2, 3, 2]
def baseStart_6007072 : Nat := 118140960795 + 6007072 * 2 ^ 59
def prefixEnd_6007072 : Nat := 4983230072969 + 3 ^ 40 * 6007072 * 2
def baseEnd_6007072 : Nat := 3084515262165226536873985

theorem tailTrace_6007072 : CollatzResearch.WordTrace tailWord_6007072 prefixEnd_6007072 3084515262165226536873985 := by
  unfold tailWord_6007072
  simp only [CollatzResearch.WordTrace]
  refine ⟨109547957646705772532275735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146063943528941030043034313 109547957646705772532275735)
  ·
    refine ⟨164321936470058658798413603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109547957646705772532275735 164321936470058658798413603)
    ·
      refine ⟨246482904705087988197620405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164321936470058658798413603 246482904705087988197620405)
      ·
        refine ⟨23107772316101998893526913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 246482904705087988197620405 23107772316101998893526913)
        ·
          refine ⟨17330829237076499170145185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23107772316101998893526913 17330829237076499170145185)
          ·
            refine ⟨12998121927807374377608889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17330829237076499170145185 12998121927807374377608889)
            ·
              refine ⟨9748591445855530783206667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12998121927807374377608889 9748591445855530783206667)
              ·
                refine ⟨14622887168783296174810001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9748591445855530783206667 14622887168783296174810001)
                ·
                  refine ⟨10967165376587472131107501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14622887168783296174810001 10967165376587472131107501)
                  ·
                    refine ⟨4112687016220302049165313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10967165376587472131107501 4112687016220302049165313)
                    ·
                      refine ⟨3084515262165226536873985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4112687016220302049165313 3084515262165226536873985)
                      ·
                        rfl

theorem cell23_6007072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 1, 2, 3, 2].length) (baseStart_6007072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6007072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6007072 prefixEnd_6007072 := by exact prefixLift 6007072
  have htrace : WordTrace (prefixWord ++ tailWord_6007072) baseStart_6007072 baseEnd_6007072 := by
    simpa [prefixWord, tailWord_6007072, baseEnd_6007072] using wordTrace_append hprefix tailTrace_6007072
  have hstable : (prefixWord ++ tailWord_6007072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6007072).length < 2 ^ (prefixWord ++ tailWord_6007072).sum := by decide
  have hdescent : baseEnd_6007072 < baseStart_6007072 := by decide
  rcases family_descends (prefixWord ++ tailWord_6007072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6007125 : List Nat := [1, 3, 2, 2, 4, 1, 3, 7]
def baseStart_6007125 : Nat := 118140960795 + 6007125 * 2 ^ 59
def prefixEnd_6007125 : Nat := 4983230072969 + 3 ^ 40 * 6007125 * 2
def baseEnd_6007125 : Nat := 114242313949626475167083

theorem tailTrace_6007125 : CollatzResearch.WordTrace tailWord_6007125 prefixEnd_6007125 114242313949626475167083 := by
  unfold tailWord_6007125
  simp only [CollatzResearch.WordTrace]
  refine ⟨219097848362219535116230829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146065232241479690077487219 219097848362219535116230829)
  ·
    refine ⟨82161693135832325668586561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219097848362219535116230829 82161693135832325668586561)
    ·
      refine ⟨61621269851874244251439921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82161693135832325668586561 61621269851874244251439921)
      ·
        refine ⟨46215952388905683188579941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61621269851874244251439921 46215952388905683188579941)
        ·
          refine ⟨8665491072919815597858739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46215952388905683188579941 8665491072919815597858739)
          ·
            refine ⟨12998236609379723396788109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8665491072919815597858739 12998236609379723396788109)
            ·
              refine ⟨4874338728517396273795541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12998236609379723396788109 4874338728517396273795541)
              ·
                refine ⟨114242313949626475167083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4874338728517396273795541 114242313949626475167083)
                ·
                  rfl

theorem cell23_6007125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 3, 7].length) (baseStart_6007125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6007125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6007125 prefixEnd_6007125 := by exact prefixLift 6007125
  have htrace : WordTrace (prefixWord ++ tailWord_6007125) baseStart_6007125 baseEnd_6007125 := by
    simpa [prefixWord, tailWord_6007125, baseEnd_6007125] using wordTrace_append hprefix tailTrace_6007125
  have hstable : (prefixWord ++ tailWord_6007125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6007125).length < 2 ^ (prefixWord ++ tailWord_6007125).sum := by decide
  have hdescent : baseEnd_6007125 < baseStart_6007125 := by decide
  rcases family_descends (prefixWord ++ tailWord_6007125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6007136 : List Nat := [2, 1, 1, 3, 5, 1, 2, 3, 1, 2, 2]
def baseStart_6007136 : Nat := 118140960795 + 6007136 * 2 ^ 59
def prefixEnd_6007136 : Nat := 4983230072969 + 3 ^ 40 * 6007136 * 2
def baseEnd_6007136 : Nat := 3084548124927114286473691

theorem tailTrace_6007136 : CollatzResearch.WordTrace tailWord_6007136 prefixEnd_6007136 3084548124927114286473691 := by
  unfold tailWord_6007136
  simp only [CollatzResearch.WordTrace]
  refine ⟨109549124782589841997440631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146065499710119789329920841 109549124782589841997440631)
  ·
    refine ⟨164323687173884762996160947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109549124782589841997440631 164323687173884762996160947)
    ·
      refine ⟨246485530760827144494241421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164323687173884762996160947 246485530760827144494241421)
      ·
        refine ⟨92432074035310179185340533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 246485530760827144494241421 92432074035310179185340533)
        ·
          refine ⟨8665506940810329298625675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 92432074035310179185340533 8665506940810329298625675)
          ·
            refine ⟨12998260411215493947938513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8665506940810329298625675 12998260411215493947938513)
            ·
              refine ⟨9748695308411620460953885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12998260411215493947938513 9748695308411620460953885)
              ·
                refine ⟨3655760740654357672857707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9748695308411620460953885 3655760740654357672857707)
                ·
                  refine ⟨5483641110981536509286561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3655760740654357672857707 5483641110981536509286561)
                  ·
                    refine ⟨4112730833236152381964921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5483641110981536509286561 4112730833236152381964921)
                    ·
                      refine ⟨3084548124927114286473691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4112730833236152381964921 3084548124927114286473691)
                      ·
                        rfl

theorem cell23_6007136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 3, 1, 2, 2].length) (baseStart_6007136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6007136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6007136 prefixEnd_6007136 := by exact prefixLift 6007136
  have htrace : WordTrace (prefixWord ++ tailWord_6007136) baseStart_6007136 baseEnd_6007136 := by
    simpa [prefixWord, tailWord_6007136, baseEnd_6007136] using wordTrace_append hprefix tailTrace_6007136
  have hstable : (prefixWord ++ tailWord_6007136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6007136).length < 2 ^ (prefixWord ++ tailWord_6007136).sum := by decide
  have hdescent : baseEnd_6007136 < baseStart_6007136 := by decide
  rcases family_descends (prefixWord ++ tailWord_6007136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6007152 : List Nat := [2, 1, 1, 1, 4, 3, 3, 2, 2, 1, 3]
def baseStart_6007152 : Nat := 118140960795 + 6007152 * 2 ^ 59
def prefixEnd_6007152 : Nat := 4983230072969 + 3 ^ 40 * 6007152 * 2
def baseEnd_6007152 : Nat := 3084556340617586223873617

theorem tailTrace_6007152 : CollatzResearch.WordTrace tailWord_6007152 prefixEnd_6007152 3084556340617586223873617 := by
  unfold tailWord_6007152
  simp only [CollatzResearch.WordTrace]
  refine ⟨109549416566560859363731855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146065888755414479151642473 109549416566560859363731855)
  ·
    refine ⟨164324124849841289045597783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109549416566560859363731855 164324124849841289045597783)
    ·
      refine ⟨246486187274761933568396675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164324124849841289045597783 246486187274761933568396675)
      ·
        refine ⟨369729280912142900352595013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246486187274761933568396675 369729280912142900352595013)
        ·
          refine ⟨69324240171026793816111565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 369729280912142900352595013 69324240171026793816111565)
          ·
            refine ⟨25996590064135047681041837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69324240171026793816111565 25996590064135047681041837)
            ·
              refine ⟨9748721274050642880390689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25996590064135047681041837 9748721274050642880390689)
              ·
                refine ⟨7311540955537982160293017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9748721274050642880390689 7311540955537982160293017)
                ·
                  refine ⟨5483655716653486620219763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7311540955537982160293017 5483655716653486620219763)
                  ·
                    refine ⟨8225483574980229930329645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5483655716653486620219763 8225483574980229930329645)
                    ·
                      refine ⟨3084556340617586223873617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8225483574980229930329645 3084556340617586223873617)
                      ·
                        rfl

theorem cell23_6007152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 2, 2, 1, 3].length) (baseStart_6007152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6007152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6007152 prefixEnd_6007152 := by exact prefixLift 6007152
  have htrace : WordTrace (prefixWord ++ tailWord_6007152) baseStart_6007152 baseEnd_6007152 := by
    simpa [prefixWord, tailWord_6007152, baseEnd_6007152] using wordTrace_append hprefix tailTrace_6007152
  have hstable : (prefixWord ++ tailWord_6007152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6007152).length < 2 ^ (prefixWord ++ tailWord_6007152).sum := by decide
  have hdescent : baseEnd_6007152 < baseStart_6007152 := by decide
  rcases family_descends (prefixWord ++ tailWord_6007152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6007220 : List Nat := [2, 5, 2, 2, 1, 2, 2, 1, 2, 1, 3]
def baseStart_6007220 : Nat := 118140960795 + 6007220 * 2 ^ 59
def prefixEnd_6007220 : Nat := 4983230072969 + 3 ^ 40 * 6007220 * 2
def baseEnd_6007220 : Nat := 3084591257302091957823305

theorem tailTrace_6007220 : CollatzResearch.WordTrace tailWord_6007220 prefixEnd_6007220 3084591257302091957823305 := by
  unfold tailWord_6007220
  simp only [CollatzResearch.WordTrace]
  refine ⟨109550656648437683170469557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146067542197916910893959409 109550656648437683170469557)
  ·
    refine ⟨10270374060791032797231521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 109550656648437683170469557 10270374060791032797231521)
    ·
      refine ⟨7702780545593274597923641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10270374060791032797231521 7702780545593274597923641)
      ·
        refine ⟨5777085409194955948442731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7702780545593274597923641 5777085409194955948442731)
        ·
          refine ⟨8665628113792433922664097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5777085409194955948442731 8665628113792433922664097)
          ·
            refine ⟨6499221085344325441998073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8665628113792433922664097 6499221085344325441998073)
            ·
              refine ⟨4874415814008244081498555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6499221085344325441998073 4874415814008244081498555)
              ·
                refine ⟨7311623721012366122247833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4874415814008244081498555 7311623721012366122247833)
                ·
                  refine ⟨5483717790759274591685875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7311623721012366122247833 5483717790759274591685875)
                  ·
                    refine ⟨8225576686138911887528813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5483717790759274591685875 8225576686138911887528813)
                    ·
                      refine ⟨3084591257302091957823305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8225576686138911887528813 3084591257302091957823305)
                      ·
                        rfl

theorem cell23_6007220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_6007220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6007220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6007220 prefixEnd_6007220 := by exact prefixLift 6007220
  have htrace : WordTrace (prefixWord ++ tailWord_6007220) baseStart_6007220 baseEnd_6007220 := by
    simpa [prefixWord, tailWord_6007220, baseEnd_6007220] using wordTrace_append hprefix tailTrace_6007220
  have hstable : (prefixWord ++ tailWord_6007220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6007220).length < 2 ^ (prefixWord ++ tailWord_6007220).sum := by decide
  have hdescent : baseEnd_6007220 < baseStart_6007220 := by decide
  rcases family_descends (prefixWord ++ tailWord_6007220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6007265 : List Nat := [1, 2, 3, 1, 2, 2, 1, 4, 2, 1, 4]
def baseStart_6007265 : Nat := 118140960795 + 6007265 * 2 ^ 59
def prefixEnd_6007265 : Nat := 4983230072969 + 3 ^ 40 * 6007265 * 2
def baseEnd_6007265 : Nat := 3084614363931544281760597

theorem tailTrace_6007265 : CollatzResearch.WordTrace tailWord_6007265 prefixEnd_6007265 3084614363931544281760597 := by
  unfold tailWord_6007265
  simp only [CollatzResearch.WordTrace]
  refine ⟨219102954581712339026327249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146068636387808226017551499 219102954581712339026327249)
  ·
    refine ⟨164327215936284254269745437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219102954581712339026327249 164327215936284254269745437)
    ·
      refine ⟨61622705976106595351154539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164327215936284254269745437 61622705976106595351154539)
      ·
        refine ⟨92434058964159893026731809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61622705976106595351154539 92434058964159893026731809)
        ·
          refine ⟨69325544223119919770048857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92434058964159893026731809 69325544223119919770048857)
          ·
            refine ⟨51994158167339939827536643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69325544223119919770048857 51994158167339939827536643)
            ·
              refine ⟨77991237251009909741304965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51994158167339939827536643 77991237251009909741304965)
              ·
                refine ⟨14623356984564358076494681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77991237251009909741304965 14623356984564358076494681)
                ·
                  refine ⟨10967517738423268557371011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14623356984564358076494681 10967517738423268557371011)
                  ·
                    refine ⟨16451276607634902836056517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10967517738423268557371011 16451276607634902836056517)
                    ·
                      refine ⟨3084614363931544281760597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16451276607634902836056517 3084614363931544281760597)
                      ·
                        rfl

theorem cell23_6007265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 4, 2, 1, 4].length) (baseStart_6007265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6007265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6007265 prefixEnd_6007265 := by exact prefixLift 6007265
  have htrace : WordTrace (prefixWord ++ tailWord_6007265) baseStart_6007265 baseEnd_6007265 := by
    simpa [prefixWord, tailWord_6007265, baseEnd_6007265] using wordTrace_append hprefix tailTrace_6007265
  have hstable : (prefixWord ++ tailWord_6007265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6007265).length < 2 ^ (prefixWord ++ tailWord_6007265).sum := by decide
  have hdescent : baseEnd_6007265 < baseStart_6007265 := by decide
  rcases family_descends (prefixWord ++ tailWord_6007265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6007266 : List Nat := [3, 3, 3, 2, 1, 1, 1, 4, 5]
def baseStart_6007266 : Nat := 118140960795 + 6007266 * 2 ^ 59
def prefixEnd_6007266 : Nat := 4983230072969 + 3 ^ 40 * 6007266 * 2
def baseEnd_6007266 : Nat := 342734986379133197538677

theorem tailTrace_6007266 : CollatzResearch.WordTrace tailWord_6007266 prefixEnd_6007266 342734986379133197538677 := by
  unfold tailWord_6007266
  simp only [CollatzResearch.WordTrace]
  refine ⟨54775747763677179049278413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146068660703139144131409101 54775747763677179049278413)
  ·
    refine ⟨20540905411378942143479405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54775747763677179049278413 20540905411378942143479405)
    ·
      refine ⟨7702839529267103303804777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20540905411378942143479405 7702839529267103303804777)
      ·
        refine ⟨5777129646950327477853583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7702839529267103303804777 5777129646950327477853583)
        ·
          refine ⟨8665694470425491216780375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5777129646950327477853583 8665694470425491216780375)
          ·
            refine ⟨12998541705638236825170563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8665694470425491216780375 12998541705638236825170563)
            ·
              refine ⟨19497812558457355237755845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12998541705638236825170563 19497812558457355237755845)
              ·
                refine ⟨3655839854710754107079221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19497812558457355237755845 3655839854710754107079221)
                ·
                  refine ⟨342734986379133197538677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3655839854710754107079221 342734986379133197538677)
                  ·
                    rfl

theorem cell23_6007266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 4, 5].length) (baseStart_6007266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6007266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6007266 prefixEnd_6007266 := by exact prefixLift 6007266
  have htrace : WordTrace (prefixWord ++ tailWord_6007266) baseStart_6007266 baseEnd_6007266 := by
    simpa [prefixWord, tailWord_6007266, baseEnd_6007266] using wordTrace_append hprefix tailTrace_6007266
  have hstable : (prefixWord ++ tailWord_6007266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6007266).length < 2 ^ (prefixWord ++ tailWord_6007266).sum := by decide
  have hdescent : baseEnd_6007266 < baseStart_6007266 := by decide
  rcases family_descends (prefixWord ++ tailWord_6007266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6007275 : List Nat := [1, 1, 1, 1, 2, 3, 4, 3, 3, 4]
def baseStart_6007275 : Nat := 118140960795 + 6007275 * 2 ^ 59
def prefixEnd_6007275 : Nat := 4983230072969 + 3 ^ 40 * 6007275 * 2
def baseEnd_6007275 : Nat := 1028206499579363080878517

theorem tailTrace_6007275 : CollatzResearch.WordTrace tailWord_6007275 prefixEnd_6007275 1028206499579363080878517 := by
  unfold tailWord_6007275
  simp only [CollatzResearch.WordTrace]
  refine ⟨219103319311676110734191279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146068879541117407156127519 219103319311676110734191279)
  ·
    refine ⟨328654978967514166101286919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219103319311676110734191279 328654978967514166101286919)
    ·
      refine ⟨492982468451271249151930379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328654978967514166101286919 492982468451271249151930379)
      ·
        refine ⟨739473702676906873727895569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 492982468451271249151930379 739473702676906873727895569)
        ·
          refine ⟨554605277007680155295921677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 739473702676906873727895569 554605277007680155295921677)
          ·
            refine ⟨207976978877880058235970629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 554605277007680155295921677 207976978877880058235970629)
            ·
              refine ⟨38995683539602510919244493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 207976978877880058235970629 38995683539602510919244493)
              ·
                refine ⟨14623381327350941594716685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38995683539602510919244493 14623381327350941594716685)
                ·
                  refine ⟨5483767997756603098018757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14623381327350941594716685 5483767997756603098018757)
                  ·
                    refine ⟨1028206499579363080878517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5483767997756603098018757 1028206499579363080878517)
                    ·
                      rfl

theorem cell23_6007275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 3, 3, 4].length) (baseStart_6007275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6007275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6007275 prefixEnd_6007275 := by exact prefixLift 6007275
  have htrace : WordTrace (prefixWord ++ tailWord_6007275) baseStart_6007275 baseEnd_6007275 := by
    simpa [prefixWord, tailWord_6007275, baseEnd_6007275] using wordTrace_append hprefix tailTrace_6007275
  have hstable : (prefixWord ++ tailWord_6007275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6007275).length < 2 ^ (prefixWord ++ tailWord_6007275).sum := by decide
  have hdescent : baseEnd_6007275 < baseStart_6007275 := by decide
  rcases family_descends (prefixWord ++ tailWord_6007275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6007325 : List Nat := [1, 4, 2, 2, 1, 2, 1, 1, 1, 2, 6]
def baseStart_6007325 : Nat := 118140960795 + 6007325 * 2 ^ 59
def prefixEnd_6007325 : Nat := 4983230072969 + 3 ^ 40 * 6007325 * 2
def baseEnd_6007325 : Nat := 3084645172770814047010321

theorem tailTrace_6007325 : CollatzResearch.WordTrace tailWord_6007325 prefixEnd_6007325 3084645172770814047010321 := by
  unfold tailWord_6007325
  simp only [CollatzResearch.WordTrace]
  refine ⟨219105142961494969273511429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146070095307663312849007619 219105142961494969273511429)
  ·
    refine ⟨41082214305280306738783393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 219105142961494969273511429 41082214305280306738783393)
    ·
      refine ⟨30811660728960230054087545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41082214305280306738783393 30811660728960230054087545)
      ·
        refine ⟨23108745546720172540565659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30811660728960230054087545 23108745546720172540565659)
        ·
          refine ⟨34663118320080258810848489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23108745546720172540565659 34663118320080258810848489)
          ·
            refine ⟨25997338740060194108136367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34663118320080258810848489 25997338740060194108136367)
            ·
              refine ⟨38996008110090291162204551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25997338740060194108136367 38996008110090291162204551)
              ·
                refine ⟨58494012165135436743306827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38996008110090291162204551 58494012165135436743306827)
                ·
                  refine ⟨87741018247703155114960241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58494012165135436743306827 87741018247703155114960241)
                  ·
                    refine ⟨65805763685777366336220181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 87741018247703155114960241 65805763685777366336220181)
                    ·
                      refine ⟨3084645172770814047010321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65805763685777366336220181 3084645172770814047010321)
                      ·
                        rfl

theorem cell23_6007325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_6007325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6007325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6007325 prefixEnd_6007325 := by exact prefixLift 6007325
  have htrace : WordTrace (prefixWord ++ tailWord_6007325) baseStart_6007325 baseEnd_6007325 := by
    simpa [prefixWord, tailWord_6007325, baseEnd_6007325] using wordTrace_append hprefix tailTrace_6007325
  have hstable : (prefixWord ++ tailWord_6007325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6007325).length < 2 ^ (prefixWord ++ tailWord_6007325).sum := by decide
  have hdescent : baseEnd_6007325 < baseStart_6007325 := by decide
  rcases family_descends (prefixWord ++ tailWord_6007325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6007352 : List Nat := [2, 1, 2, 1, 4, 1, 4, 2, 1, 5]
def baseStart_6007352 : Nat := 118140960795 + 6007352 * 2 ^ 59
def prefixEnd_6007352 : Nat := 4983230072969 + 3 ^ 40 * 6007352 * 2
def baseEnd_6007352 : Nat := 1028219678916161813790899

theorem tailTrace_6007352 : CollatzResearch.WordTrace tailWord_6007352 prefixEnd_6007352 1028219678916161813790899 := by
  unfold tailWord_6007352
  simp only [CollatzResearch.WordTrace]
  refine ⟨109553063866198576442372155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146070751821598101923162873 109553063866198576442372155)
  ·
    refine ⟨164329595799297864663558233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109553063866198576442372155 164329595799297864663558233)
    ·
      refine ⟨123247196849473398497668675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164329595799297864663558233 123247196849473398497668675)
      ·
        refine ⟨184870795274210097746503013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123247196849473398497668675 184870795274210097746503013)
        ·
          refine ⟨34663274113914393327469315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 184870795274210097746503013 34663274113914393327469315)
          ·
            refine ⟨51994911170871589991203973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34663274113914393327469315 51994911170871589991203973)
            ·
              refine ⟨9749045844538423123350745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51994911170871589991203973 9749045844538423123350745)
              ·
                refine ⟨7311784383403817342513059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9749045844538423123350745 7311784383403817342513059)
                ·
                  refine ⟨10967676575105726013769589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7311784383403817342513059 10967676575105726013769589)
                  ·
                    refine ⟨1028219678916161813790899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10967676575105726013769589 1028219678916161813790899)
                    ·
                      rfl

theorem cell23_6007352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 2, 1, 5].length) (baseStart_6007352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6007352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6007352 prefixEnd_6007352 := by exact prefixLift 6007352
  have htrace : WordTrace (prefixWord ++ tailWord_6007352) baseStart_6007352 baseEnd_6007352 := by
    simpa [prefixWord, tailWord_6007352, baseEnd_6007352] using wordTrace_append hprefix tailTrace_6007352
  have hstable : (prefixWord ++ tailWord_6007352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6007352).length < 2 ^ (prefixWord ++ tailWord_6007352).sum := by decide
  have hdescent : baseEnd_6007352 < baseStart_6007352 := by decide
  rcases family_descends (prefixWord ++ tailWord_6007352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6007372 : List Nat := [2, 2, 1, 3, 1, 2, 1, 5, 1, 1, 4]
def baseStart_6007372 : Nat := 118140960795 + 6007372 * 2 ^ 59
def prefixEnd_6007372 : Nat := 4983230072969 + 3 ^ 40 * 6007372 * 2
def baseEnd_6007372 : Nat := 3084669306361575363122605

theorem tailTrace_6007372 : CollatzResearch.WordTrace tailWord_6007372 prefixEnd_6007372 3084669306361575363122605 := by
  unfold tailWord_6007372
  simp only [CollatzResearch.WordTrace]
  refine ⟨109553428596162348150236185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146071238128216464200314913 109553428596162348150236185)
  ·
    refine ⟨82165071447121761112677139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109553428596162348150236185 82165071447121761112677139)
    ·
      refine ⟨123247607170682641669015709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82165071447121761112677139 123247607170682641669015709)
      ·
        refine ⟨46217852689005990625880891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123247607170682641669015709 46217852689005990625880891)
        ·
          refine ⟨69326779033508985938821337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46217852689005990625880891 69326779033508985938821337)
          ·
            refine ⟨51995084275131739454116003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69326779033508985938821337 51995084275131739454116003)
            ·
              refine ⟨77992626412697609181174005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51995084275131739454116003 77992626412697609181174005)
              ·
                refine ⟨7311808726190400860735063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77992626412697609181174005 7311808726190400860735063)
                ·
                  refine ⟨10967713089285601291102595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7311808726190400860735063 10967713089285601291102595)
                  ·
                    refine ⟨16451569633928401936653893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10967713089285601291102595 16451569633928401936653893)
                    ·
                      refine ⟨3084669306361575363122605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16451569633928401936653893 3084669306361575363122605)
                      ·
                        rfl

theorem cell23_6007372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 5, 1, 1, 4].length) (baseStart_6007372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6007372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6007372 prefixEnd_6007372 := by exact prefixLift 6007372
  have htrace : WordTrace (prefixWord ++ tailWord_6007372) baseStart_6007372 baseEnd_6007372 := by
    simpa [prefixWord, tailWord_6007372, baseEnd_6007372] using wordTrace_append hprefix tailTrace_6007372
  have hstable : (prefixWord ++ tailWord_6007372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6007372).length < 2 ^ (prefixWord ++ tailWord_6007372).sum := by decide
  have hdescent : baseEnd_6007372 < baseStart_6007372 := by decide
  rcases family_descends (prefixWord ++ tailWord_6007372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6007375 : List Nat := [1, 1, 2, 1, 1, 2, 5, 3, 1, 1, 5]
def baseStart_6007375 : Nat := 118140960795 + 6007375 * 2 ^ 59
def prefixEnd_6007375 : Nat := 4983230072969 + 3 ^ 40 * 6007375 * 2
def baseEnd_6007375 : Nat := 3084670846803538851385091

theorem tailTrace_6007375 : CollatzResearch.WordTrace tailWord_6007375 prefixEnd_6007375 3084670846803538851385091 := by
  unfold tailWord_6007375
  simp only [CollatzResearch.WordTrace]
  refine ⟨219106966611313827812831579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146071311074209218541887719 219106966611313827812831579)
  ·
    refine ⟨328660449916970741719247369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219106966611313827812831579 328660449916970741719247369)
    ·
      refine ⟨246495337437728056289435527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 328660449916970741719247369 246495337437728056289435527)
      ·
        refine ⟨369743006156592084434153291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246495337437728056289435527 369743006156592084434153291)
        ·
          refine ⟨554614509234888126651229937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 369743006156592084434153291 554614509234888126651229937)
          ·
            refine ⟨415960881926166094988422453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 554614509234888126651229937 415960881926166094988422453)
            ·
              refine ⟨38996332680578071405164605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 415960881926166094988422453 38996332680578071405164605)
              ·
                refine ⟨14623624755216776776936727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38996332680578071405164605 14623624755216776776936727)
                ·
                  refine ⟨21935437132825165165405091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14623624755216776776936727 21935437132825165165405091)
                  ·
                    refine ⟨32903155699237747748107637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21935437132825165165405091 32903155699237747748107637)
                    ·
                      refine ⟨3084670846803538851385091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32903155699237747748107637 3084670846803538851385091)
                      ·
                        rfl

theorem cell23_6007375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 3, 1, 1, 5].length) (baseStart_6007375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6007375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6007375 prefixEnd_6007375 := by exact prefixLift 6007375
  have htrace : WordTrace (prefixWord ++ tailWord_6007375) baseStart_6007375 baseEnd_6007375 := by
    simpa [prefixWord, tailWord_6007375, baseEnd_6007375] using wordTrace_append hprefix tailTrace_6007375
  have hstable : (prefixWord ++ tailWord_6007375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6007375).length < 2 ^ (prefixWord ++ tailWord_6007375).sum := by decide
  have hdescent : baseEnd_6007375 < baseStart_6007375 := by decide
  rcases family_descends (prefixWord ++ tailWord_6007375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6007390 : List Nat := [4, 4, 1, 2, 1, 2, 2, 1, 6]
def baseStart_6007390 : Nat := 118140960795 + 6007390 * 2 ^ 59
def prefixEnd_6007390 : Nat := 4983230072969 + 3 ^ 40 * 6007390 * 2
def baseEnd_6007390 : Nat := 342742061001484032521947

theorem tailTrace_6007390 : CollatzResearch.WordTrace tailWord_6007390 prefixEnd_6007390 342742061001484032521947 := by
  unfold tailWord_6007390
  simp only [CollatzResearch.WordTrace]
  refine ⟨27388439213282435671828453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146071675804172990249751749 27388439213282435671828453)
  ·
    refine ⟨5135332352490456688467835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27388439213282435671828453 5135332352490456688467835)
    ·
      refine ⟨7702998528735685032701753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5135332352490456688467835 7702998528735685032701753)
      ·
        refine ⟨5777248896551763774526315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7702998528735685032701753 5777248896551763774526315)
        ·
          refine ⟨8665873344827645661789473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5777248896551763774526315 8665873344827645661789473)
          ·
            refine ⟨6499405008620734246342105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8665873344827645661789473 6499405008620734246342105)
            ·
              refine ⟨4874553756465550684756579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6499405008620734246342105 4874553756465550684756579)
              ·
                refine ⟨7311830634698326027134869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4874553756465550684756579 7311830634698326027134869)
                ·
                  refine ⟨342742061001484032521947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7311830634698326027134869 342742061001484032521947)
                  ·
                    rfl

theorem cell23_6007390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_6007390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6007390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6007390 prefixEnd_6007390 := by exact prefixLift 6007390
  have htrace : WordTrace (prefixWord ++ tailWord_6007390) baseStart_6007390 baseEnd_6007390 := by
    simpa [prefixWord, tailWord_6007390, baseEnd_6007390] using wordTrace_append hprefix tailTrace_6007390
  have hstable : (prefixWord ++ tailWord_6007390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6007390).length < 2 ^ (prefixWord ++ tailWord_6007390).sum := by decide
  have hdescent : baseEnd_6007390 < baseStart_6007390 := by decide
  rcases family_descends (prefixWord ++ tailWord_6007390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6007395 : List Nat := [1, 1, 1, 5, 1, 2, 4, 8]
def baseStart_6007395 : Nat := 118140960795 + 6007395 * 2 ^ 59
def prefixEnd_6007395 : Nat := 4983230072969 + 3 ^ 40 * 6007395 * 2
def baseEnd_6007395 : Nat := 114247448756171436042037

theorem tailTrace_6007395 : CollatzResearch.WordTrace tailWord_6007395 prefixEnd_6007395 114247448756171436042037 := by
  unfold tailWord_6007395
  simp only [CollatzResearch.WordTrace]
  refine ⟨219107696071241371228559639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146071797380827580819039759 219107696071241371228559639)
  ·
    refine ⟨328661544106862056842839459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219107696071241371228559639 328661544106862056842839459)
    ·
      refine ⟨492992316160293085264259189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328661544106862056842839459 492992316160293085264259189)
      ·
        refine ⟨46218029640027476743524299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 492992316160293085264259189 46218029640027476743524299)
        ·
          refine ⟨69327044460041215115286449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46218029640027476743524299 69327044460041215115286449)
          ·
            refine ⟨51995283345030911336464837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69327044460041215115286449 51995283345030911336464837)
            ·
              refine ⟨9749115627193295875587157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51995283345030911336464837 9749115627193295875587157)
              ·
                refine ⟨114247448756171436042037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9749115627193295875587157 114247448756171436042037)
                ·
                  rfl

theorem cell23_6007395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 8].length) (baseStart_6007395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6007395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6007395 prefixEnd_6007395 := by exact prefixLift 6007395
  have htrace : WordTrace (prefixWord ++ tailWord_6007395) baseStart_6007395 baseEnd_6007395 := by
    simpa [prefixWord, tailWord_6007395, baseEnd_6007395] using wordTrace_append hprefix tailTrace_6007395
  have hstable : (prefixWord ++ tailWord_6007395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6007395).length < 2 ^ (prefixWord ++ tailWord_6007395).sum := by decide
  have hdescent : baseEnd_6007395 < baseStart_6007395 := by decide
  rcases family_descends (prefixWord ++ tailWord_6007395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6007402 : List Nat := [3, 1, 3, 2, 1, 1, 2, 3, 1, 2, 4]
def baseStart_6007402 : Nat := 118140960795 + 6007402 * 2 ^ 59
def prefixEnd_6007402 : Nat := 4983230072969 + 3 ^ 40 * 6007402 * 2
def baseEnd_6007402 : Nat := 3084684710781210245747467

theorem tailTrace_6007402 : CollatzResearch.WordTrace tailWord_6007402 prefixEnd_6007402 3084684710781210245747467 := by
  unfold tailWord_6007402
  simp only [CollatzResearch.WordTrace]
  refine ⟨54776987845554002856016115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146071967588144007616042973 54776987845554002856016115)
  ·
    refine ⟨82165481768331004284024173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54776987845554002856016115 82165481768331004284024173)
    ·
      refine ⟨30812055663124126606509065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82165481768331004284024173 30812055663124126606509065)
      ·
        refine ⟨23109041747343094954881799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30812055663124126606509065 23109041747343094954881799)
        ·
          refine ⟨34663562621014642432322699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23109041747343094954881799 34663562621014642432322699)
          ·
            refine ⟨51995343931521963648484049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34663562621014642432322699 51995343931521963648484049)
            ·
              refine ⟨38996507948641472736363037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51995343931521963648484049 38996507948641472736363037)
              ·
                refine ⟨14623690480740552276136139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38996507948641472736363037 14623690480740552276136139)
                ·
                  refine ⟨21935535721110828414204209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14623690480740552276136139 21935535721110828414204209)
                  ·
                    refine ⟨16451651790833121310653157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21935535721110828414204209 16451651790833121310653157)
                    ·
                      refine ⟨3084684710781210245747467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16451651790833121310653157 3084684710781210245747467)
                      ·
                        rfl

theorem cell23_6007402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_6007402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6007402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6007402 prefixEnd_6007402 := by exact prefixLift 6007402
  have htrace : WordTrace (prefixWord ++ tailWord_6007402) baseStart_6007402 baseEnd_6007402 := by
    simpa [prefixWord, tailWord_6007402, baseEnd_6007402] using wordTrace_append hprefix tailTrace_6007402
  have hstable : (prefixWord ++ tailWord_6007402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6007402).length < 2 ^ (prefixWord ++ tailWord_6007402).sum := by decide
  have hdescent : baseEnd_6007402 < baseStart_6007402 := by decide
  rcases family_descends (prefixWord ++ tailWord_6007402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6007406 : List Nat := [4, 1, 2, 2, 2, 3, 1, 2, 1, 1, 4]
def baseStart_6007406 : Nat := 118140960795 + 6007406 * 2 ^ 59
def prefixEnd_6007406 : Nat := 4983230072969 + 3 ^ 40 * 6007406 * 2
def baseEnd_6007406 : Nat := 3084686764703828230097449

theorem tailTrace_6007406 : CollatzResearch.WordTrace tailWord_6007406 prefixEnd_6007406 3084686764703828230097449 := by
  unfold tailWord_6007406
  simp only [CollatzResearch.WordTrace]
  refine ⟨27388512159275190013401259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146072064849467680071473381 27388512159275190013401259)
  ·
    refine ⟨41082768238912785020101889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27388512159275190013401259 41082768238912785020101889)
    ·
      refine ⟨30812076179184588765076417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41082768238912785020101889 30812076179184588765076417)
      ·
        refine ⟨23109057134388441573807313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30812076179184588765076417 23109057134388441573807313)
        ·
          refine ⟨17331792850791331180355485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23109057134388441573807313 17331792850791331180355485)
          ·
            refine ⟨6499422319046749192633307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17331792850791331180355485 6499422319046749192633307)
            ·
              refine ⟨9749133478570123788949961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6499422319046749192633307 9749133478570123788949961)
              ·
                refine ⟨7311850108927592841712471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9749133478570123788949961 7311850108927592841712471)
                ·
                  refine ⟨10967775163391389262568707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7311850108927592841712471 10967775163391389262568707)
                  ·
                    refine ⟨16451662745087083893853061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10967775163391389262568707 16451662745087083893853061)
                    ·
                      refine ⟨3084686764703828230097449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16451662745087083893853061 3084686764703828230097449)
                      ·
                        rfl

theorem cell23_6007406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_6007406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6007406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6007406 prefixEnd_6007406 := by exact prefixLift 6007406
  have htrace : WordTrace (prefixWord ++ tailWord_6007406) baseStart_6007406 baseEnd_6007406 := by
    simpa [prefixWord, tailWord_6007406, baseEnd_6007406] using wordTrace_append hprefix tailTrace_6007406
  have hstable : (prefixWord ++ tailWord_6007406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6007406).length < 2 ^ (prefixWord ++ tailWord_6007406).sum := by decide
  have hdescent : baseEnd_6007406 < baseStart_6007406 := by decide
  rcases family_descends (prefixWord ++ tailWord_6007406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6007442 : List Nat := [3, 2, 3, 1, 2, 1, 1, 1, 2, 7]
def baseStart_6007442 : Nat := 118140960795 + 6007442 * 2 ^ 59
def prefixEnd_6007442 : Nat := 4983230072969 + 3 ^ 40 * 6007442 * 2
def baseEnd_6007442 : Nat := 1028235083335796696415761

theorem tailTrace_6007442 : CollatzResearch.WordTrace tailWord_6007442 prefixEnd_6007442 1028235083335796696415761 := by
  unfold tailWord_6007442
  simp only [CollatzResearch.WordTrace]
  refine ⟨54777352575517774563880145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146072940201380732170347053 54777352575517774563880145)
  ·
    refine ⟨41083014431638330922910109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54777352575517774563880145 41083014431638330922910109)
    ·
      refine ⟨15406130411864374096091291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41083014431638330922910109 15406130411864374096091291)
      ·
        refine ⟨23109195617796561144136937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15406130411864374096091291 23109195617796561144136937)
        ·
          refine ⟨17331896713347420858102703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23109195617796561144136937 17331896713347420858102703)
          ·
            refine ⟨25997845070021131287154055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17331896713347420858102703 25997845070021131287154055)
            ·
              refine ⟨38996767605031696930731083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25997845070021131287154055 38996767605031696930731083)
              ·
                refine ⟨58495151407547545396096625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38996767605031696930731083 58495151407547545396096625)
                ·
                  refine ⟨43871363555660659047072469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58495151407547545396096625 43871363555660659047072469)
                  ·
                    refine ⟨1028235083335796696415761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43871363555660659047072469 1028235083335796696415761)
                    ·
                      rfl

theorem cell23_6007442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_6007442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6007442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6007442 prefixEnd_6007442 := by exact prefixLift 6007442
  have htrace : WordTrace (prefixWord ++ tailWord_6007442) baseStart_6007442 baseEnd_6007442 := by
    simpa [prefixWord, tailWord_6007442, baseEnd_6007442] using wordTrace_append hprefix tailTrace_6007442
  have hstable : (prefixWord ++ tailWord_6007442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6007442).length < 2 ^ (prefixWord ++ tailWord_6007442).sum := by decide
  have hdescent : baseEnd_6007442 < baseStart_6007442 := by decide
  rcases family_descends (prefixWord ++ tailWord_6007442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6007495 : List Nat := [1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 9]
def baseStart_6007495 : Nat := 118140960795 + 6007495 * 2 ^ 59
def prefixEnd_6007495 : Nat := 4983230072969 + 3 ^ 40 * 6007495 * 2
def baseEnd_6007495 : Nat := 3084732464482078381884539

theorem tailTrace_6007495 : CollatzResearch.WordTrace tailWord_6007495 prefixEnd_6007495 3084732464482078381884539 := by
  unfold tailWord_6007495
  simp only [CollatzResearch.WordTrace]
  refine ⟨219111343370879088307199939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146074228913919392204799959 219111343370879088307199939)
  ·
    refine ⟨328667015056318632460799909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219111343370879088307199939 328667015056318632460799909)
    ·
      refine ⟨61625065323059743586399983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 328667015056318632460799909 61625065323059743586399983)
      ·
        refine ⟨92437597984589615379599975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61625065323059743586399983 92437597984589615379599975)
        ·
          refine ⟨138656396976884423069399963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92437597984589615379599975 138656396976884423069399963)
          ·
            refine ⟨207984595465326634604099945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138656396976884423069399963 207984595465326634604099945)
            ·
              refine ⟨155988446598994975953074959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 207984595465326634604099945 155988446598994975953074959)
              ·
                refine ⟨233982669898492463929612439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155988446598994975953074959 233982669898492463929612439)
                ·
                  refine ⟨350974004847738695894418659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 233982669898492463929612439 350974004847738695894418659)
                  ·
                    refine ⟨526461007271608043841627989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 350974004847738695894418659 526461007271608043841627989)
                    ·
                      refine ⟨3084732464482078381884539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 526461007271608043841627989 3084732464482078381884539)
                      ·
                        rfl

theorem cell23_6007495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_6007495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6007495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6007495 prefixEnd_6007495 := by exact prefixLift 6007495
  have htrace : WordTrace (prefixWord ++ tailWord_6007495) baseStart_6007495 baseEnd_6007495 := by
    simpa [prefixWord, tailWord_6007495, baseEnd_6007495] using wordTrace_append hprefix tailTrace_6007495
  have hstable : (prefixWord ++ tailWord_6007495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6007495).length < 2 ^ (prefixWord ++ tailWord_6007495).sum := by decide
  have hdescent : baseEnd_6007495 < baseStart_6007495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6007495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6007496 : List Nat := [2, 1, 3, 1, 2, 4, 1, 1, 4, 2, 2]
def baseStart_6007496 : Nat := 118140960795 + 6007496 * 2 ^ 59
def prefixEnd_6007496 : Nat := 4983230072969 + 3 ^ 40 * 6007496 * 2
def baseEnd_6007496 : Nat := 3084732977962732877972035

theorem tailTrace_6007496 : CollatzResearch.WordTrace tailWord_6007496 prefixEnd_6007496 3084732977962732877972035 := by
  unfold tailWord_6007496
  simp only [CollatzResearch.WordTrace]
  refine ⟨109555689921937732738993171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146074253229250310318657561 109555689921937732738993171)
  ·
    refine ⟨164333534882906599108489757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109555689921937732738993171 164333534882906599108489757)
    ·
      refine ⟨61625075581089974665683659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164333534882906599108489757 61625075581089974665683659)
      ·
        refine ⟨92437613371634961998525489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61625075581089974665683659 92437613371634961998525489)
        ·
          refine ⟨69328210028726221498894117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92437613371634961998525489 69328210028726221498894117)
          ·
            refine ⟨12999039380386166531042647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69328210028726221498894117 12999039380386166531042647)
            ·
              refine ⟨19498559070579249796563971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12999039380386166531042647 19498559070579249796563971)
              ·
                refine ⟨29247838605868874694845957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19498559070579249796563971 29247838605868874694845957)
                ·
                  refine ⟨5483969738600414005283617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29247838605868874694845957 5483969738600414005283617)
                  ·
                    refine ⟨4112977303950310503962713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5483969738600414005283617 4112977303950310503962713)
                    ·
                      refine ⟨3084732977962732877972035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4112977303950310503962713 3084732977962732877972035)
                      ·
                        rfl

theorem cell23_6007496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 4, 2, 2].length) (baseStart_6007496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6007496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6007496 prefixEnd_6007496 := by exact prefixLift 6007496
  have htrace : WordTrace (prefixWord ++ tailWord_6007496) baseStart_6007496 baseEnd_6007496 := by
    simpa [prefixWord, tailWord_6007496, baseEnd_6007496] using wordTrace_append hprefix tailTrace_6007496
  have hstable : (prefixWord ++ tailWord_6007496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6007496).length < 2 ^ (prefixWord ++ tailWord_6007496).sum := by decide
  have hdescent : baseEnd_6007496 < baseStart_6007496 := by decide
  rcases family_descends (prefixWord ++ tailWord_6007496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6007502 : List Nat := [4, 1, 1, 1, 3, 2, 1, 3, 7]
def baseStart_6007502 : Nat := 118140960795 + 6007502 * 2 ^ 59
def prefixEnd_6007502 : Nat := 4983230072969 + 3 ^ 40 * 6007502 * 2
def baseEnd_6007502 : Nat := 342748450982962206055223

theorem tailTrace_6007502 : CollatzResearch.WordTrace tailWord_6007502 prefixEnd_6007502 342748450982962206055223 := by
  unfold tailWord_6007502
  simp only [CollatzResearch.WordTrace]
  refine ⟨27388949835231716062838095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146074399121235819001803173 27388949835231716062838095)
  ·
    refine ⟨41083424752847574094257143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27388949835231716062838095 41083424752847574094257143)
    ·
      refine ⟨61625137129271361141385715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41083424752847574094257143 61625137129271361141385715)
      ·
        refine ⟨92437705693907041712078573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61625137129271361141385715 92437705693907041712078573)
        ·
          refine ⟨34664139635215140642029465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92437705693907041712078573 34664139635215140642029465)
          ·
            refine ⟨25998104726411355481522099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34664139635215140642029465 25998104726411355481522099)
            ·
              refine ⟨38997157089617033222283149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25998104726411355481522099 38997157089617033222283149)
              ·
                refine ⟨14623933908606387458356181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38997157089617033222283149 14623933908606387458356181)
                ·
                  refine ⟨342748450982962206055223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14623933908606387458356181 342748450982962206055223)
                  ·
                    rfl

theorem cell23_6007502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 3, 7].length) (baseStart_6007502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6007502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6007502 prefixEnd_6007502 := by exact prefixLift 6007502
  have htrace : WordTrace (prefixWord ++ tailWord_6007502) baseStart_6007502 baseEnd_6007502 := by
    simpa [prefixWord, tailWord_6007502, baseEnd_6007502] using wordTrace_append hprefix tailTrace_6007502
  have hstable : (prefixWord ++ tailWord_6007502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6007502).length < 2 ^ (prefixWord ++ tailWord_6007502).sum := by decide
  have hdescent : baseEnd_6007502 < baseStart_6007502 := by decide
  rcases family_descends (prefixWord ++ tailWord_6007502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6007513 : List Nat := [1, 2, 1, 2, 3, 2, 5, 1, 2, 2, 2]
def baseStart_6007513 : Nat := 118140960795 + 6007513 * 2 ^ 59
def prefixEnd_6007513 : Nat := 4983230072969 + 3 ^ 40 * 6007513 * 2
def baseEnd_6007513 : Nat := 3084741707133859311459457

theorem tailTrace_6007513 : CollatzResearch.WordTrace tailWord_6007513 prefixEnd_6007513 3084741707133859311459457 := by
  unfold tailWord_6007513
  simp only [CollatzResearch.WordTrace]
  refine ⟨219111999884813877381355193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146074666589875918254236795 219111999884813877381355193)
  ·
    refine ⟨164333999913610408036016395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219111999884813877381355193 164333999913610408036016395)
    ·
      refine ⟨246500999870415612054024593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164333999913610408036016395 246500999870415612054024593)
      ·
        refine ⟨184875749902811709040518445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246500999870415612054024593 184875749902811709040518445)
        ·
          refine ⟨69328406213554390890194417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184875749902811709040518445 69328406213554390890194417)
          ·
            refine ⟨51996304660165793167645813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69328406213554390890194417 51996304660165793167645813)
            ·
              refine ⟨4874653561890543109466795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51996304660165793167645813 4874653561890543109466795)
              ·
                refine ⟨7311980342835814664200193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4874653561890543109466795 7311980342835814664200193)
                ·
                  refine ⟨5483985257126860998150145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7311980342835814664200193 5483985257126860998150145)
                  ·
                    refine ⟨4112988942845145748612609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5483985257126860998150145 4112988942845145748612609)
                    ·
                      refine ⟨3084741707133859311459457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4112988942845145748612609 3084741707133859311459457)
                      ·
                        rfl

theorem cell23_6007513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 5, 1, 2, 2, 2].length) (baseStart_6007513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6007513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6007513 prefixEnd_6007513 := by exact prefixLift 6007513
  have htrace : WordTrace (prefixWord ++ tailWord_6007513) baseStart_6007513 baseEnd_6007513 := by
    simpa [prefixWord, tailWord_6007513, baseEnd_6007513] using wordTrace_append hprefix tailTrace_6007513
  have hstable : (prefixWord ++ tailWord_6007513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6007513).length < 2 ^ (prefixWord ++ tailWord_6007513).sum := by decide
  have hdescent : baseEnd_6007513 < baseStart_6007513 := by decide
  rcases family_descends (prefixWord ++ tailWord_6007513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6007532 : List Nat := [2, 2, 1, 1, 2, 2, 1, 5, 2, 5]
def baseStart_6007532 : Nat := 118140960795 + 6007532 * 2 ^ 59
def prefixEnd_6007532 : Nat := 4983230072969 + 3 ^ 40 * 6007532 * 2
def baseEnd_6007532 : Nat := 1028250487755431579040623

theorem tailTrace_6007532 : CollatzResearch.WordTrace tailWord_6007532 prefixEnd_6007532 1028250487755431579040623 := by
  unfold tailWord_6007532
  simp only [CollatzResearch.WordTrace]
  refine ⟨109556346435872521813148425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146075128581163362417531233 109556346435872521813148425)
  ·
    refine ⟨82167259826904391359861319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109556346435872521813148425 82167259826904391359861319)
    ·
      refine ⟨123250889740356587039791979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82167259826904391359861319 123250889740356587039791979)
      ·
        refine ⟨184876334610534880559687969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123250889740356587039791979 184876334610534880559687969)
        ·
          refine ⟨138657250957901160419765977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184876334610534880559687969 138657250957901160419765977)
          ·
            refine ⟨103992938218425870314824483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138657250957901160419765977 103992938218425870314824483)
            ·
              refine ⟨155989407327638805472236725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103992938218425870314824483 155989407327638805472236725)
              ·
                refine ⟨14624006936966138013022193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 155989407327638805472236725 14624006936966138013022193)
                ·
                  refine ⟨10968005202724603509766645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14624006936966138013022193 10968005202724603509766645)
                  ·
                    refine ⟨1028250487755431579040623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10968005202724603509766645 1028250487755431579040623)
                    ·
                      rfl

theorem cell23_6007532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 5].length) (baseStart_6007532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6007532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6007532 prefixEnd_6007532 := by exact prefixLift 6007532
  have htrace : WordTrace (prefixWord ++ tailWord_6007532) baseStart_6007532 baseEnd_6007532 := by
    simpa [prefixWord, tailWord_6007532, baseEnd_6007532] using wordTrace_append hprefix tailTrace_6007532
  have hstable : (prefixWord ++ tailWord_6007532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6007532).length < 2 ^ (prefixWord ++ tailWord_6007532).sum := by decide
  have hdescent : baseEnd_6007532 < baseStart_6007532 := by decide
  rcases family_descends (prefixWord ++ tailWord_6007532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6007559 : List Nat := [1, 1, 4, 4, 1, 2, 1, 1, 1, 2, 5]
def baseStart_6007559 : Nat := 118140960795 + 6007559 * 2 ^ 59
def prefixEnd_6007559 : Nat := 4983230072969 + 3 ^ 40 * 6007559 * 2
def baseEnd_6007559 : Nat := 3084765327243966131484245

theorem tailTrace_6007559 : CollatzResearch.WordTrace tailWord_6007559 prefixEnd_6007559 3084765327243966131484245 := by
  unfold tailWord_6007559
  simp only [CollatzResearch.WordTrace]
  refine ⟨219113677642647227237529731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146075785095098151491686487 219113677642647227237529731)
  ·
    refine ⟨328670516463970840856294597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219113677642647227237529731 328670516463970840856294597)
    ·
      refine ⟨61625721836994532660555237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 328670516463970840856294597 61625721836994532660555237)
      ·
        refine ⟨11554822844436474873854107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61625721836994532660555237 11554822844436474873854107)
        ·
          refine ⟨17332234266654712310781161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11554822844436474873854107 17332234266654712310781161)
          ·
            refine ⟨12999175699991034233085871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17332234266654712310781161 12999175699991034233085871)
            ·
              refine ⟨19498763549986551349628807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12999175699991034233085871 19498763549986551349628807)
              ·
                refine ⟨29248145324979827024443211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19498763549986551349628807 29248145324979827024443211)
                ·
                  refine ⟨43872217987469740536664817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29248145324979827024443211 43872217987469740536664817)
                  ·
                    refine ⟨32904163490602305402498613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43872217987469740536664817 32904163490602305402498613)
                    ·
                      refine ⟨3084765327243966131484245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32904163490602305402498613 3084765327243966131484245)
                      ·
                        rfl

theorem cell23_6007559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_6007559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6007559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6007559 prefixEnd_6007559 := by exact prefixLift 6007559
  have htrace : WordTrace (prefixWord ++ tailWord_6007559) baseStart_6007559 baseEnd_6007559 := by
    simpa [prefixWord, tailWord_6007559, baseEnd_6007559] using wordTrace_append hprefix tailTrace_6007559
  have hstable : (prefixWord ++ tailWord_6007559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6007559).length < 2 ^ (prefixWord ++ tailWord_6007559).sum := by decide
  have hdescent : baseEnd_6007559 < baseStart_6007559 := by decide
  rcases family_descends (prefixWord ++ tailWord_6007559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6007569 : List Nat := [1, 2, 2, 1, 1, 3, 2, 3, 2, 4, 2]
def baseStart_6007569 : Nat := 118140960795 + 6007569 * 2 ^ 59
def prefixEnd_6007569 : Nat := 4983230072969 + 3 ^ 40 * 6007569 * 2
def baseEnd_6007569 : Nat := 3084770462050511092359199

theorem tailTrace_6007569 : CollatzResearch.WordTrace tailWord_6007569 prefixEnd_6007569 3084770462050511092359199 := by
  unfold tailWord_6007569
  simp only [CollatzResearch.WordTrace]
  refine ⟨219114042372610998945393761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146076028248407332630262507 219114042372610998945393761)
  ·
    refine ⟨164335531779458249209045321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219114042372610998945393761 164335531779458249209045321)
    ·
      refine ⟨123251648834593686906783991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164335531779458249209045321 123251648834593686906783991)
      ·
        refine ⟨184877473251890530360175987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123251648834593686906783991 184877473251890530360175987)
        ·
          refine ⟨277316209877835795540263981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184877473251890530360175987 277316209877835795540263981)
          ·
            refine ⟨103993578704188423327598993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 277316209877835795540263981 103993578704188423327598993)
            ·
              refine ⟨77995184028141317495699245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103993578704188423327598993 77995184028141317495699245)
              ·
                refine ⟨29248194010552994060887217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77995184028141317495699245 29248194010552994060887217)
                ·
                  refine ⟨21936145507914745545665413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29248194010552994060887217 21936145507914745545665413)
                  ·
                    refine ⟨4113027282734014789812265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21936145507914745545665413 4113027282734014789812265)
                    ·
                      refine ⟨3084770462050511092359199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4113027282734014789812265 3084770462050511092359199)
                      ·
                        rfl

theorem cell23_6007569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 4, 2].length) (baseStart_6007569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6007569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6007569 prefixEnd_6007569 := by exact prefixLift 6007569
  have htrace : WordTrace (prefixWord ++ tailWord_6007569) baseStart_6007569 baseEnd_6007569 := by
    simpa [prefixWord, tailWord_6007569, baseEnd_6007569] using wordTrace_append hprefix tailTrace_6007569
  have hstable : (prefixWord ++ tailWord_6007569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6007569).length < 2 ^ (prefixWord ++ tailWord_6007569).sum := by decide
  have hdescent : baseEnd_6007569 < baseStart_6007569 := by decide
  rcases family_descends (prefixWord ++ tailWord_6007569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6007586 : List Nat := [3, 3, 1, 1, 2, 3, 2, 1, 2, 1, 4]
def baseStart_6007586 : Nat := 118140960795 + 6007586 * 2 ^ 59
def prefixEnd_6007586 : Nat := 4983230072969 + 3 ^ 40 * 6007586 * 2
def baseEnd_6007586 : Nat := 3084779191221637525846621

theorem tailTrace_6007586 : CollatzResearch.WordTrace tailWord_6007586 prefixEnd_6007586 3084779191221637525846621 := by
  unfold tailWord_6007586
  simp only [CollatzResearch.WordTrace]
  refine ⟨54778665603387352712190653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146076441609032940565841741 54778665603387352712190653)
  ·
    refine ⟨20541999601270257267071495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54778665603387352712190653 20541999601270257267071495)
    ·
      refine ⟨30812999401905385900607243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20541999601270257267071495 30812999401905385900607243)
      ·
        refine ⟨46219499102858078850910865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30812999401905385900607243 46219499102858078850910865)
        ·
          refine ⟨34664624327143559138183149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46219499102858078850910865 34664624327143559138183149)
          ·
            refine ⟨12999234122678834676818681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34664624327143559138183149 12999234122678834676818681)
            ·
              refine ⟨9749425592009126007614011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12999234122678834676818681 9749425592009126007614011)
              ·
                refine ⟨14624138388013689011421017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9749425592009126007614011 14624138388013689011421017)
                ·
                  refine ⟨10968103791010266758565763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14624138388013689011421017 10968103791010266758565763)
                  ·
                    refine ⟨16452155686515400137848645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10968103791010266758565763 16452155686515400137848645)
                    ·
                      refine ⟨3084779191221637525846621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16452155686515400137848645 3084779191221637525846621)
                      ·
                        rfl

theorem cell23_6007586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 1, 2, 1, 4].length) (baseStart_6007586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6007586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6007586 prefixEnd_6007586 := by exact prefixLift 6007586
  have htrace : WordTrace (prefixWord ++ tailWord_6007586) baseStart_6007586 baseEnd_6007586 := by
    simpa [prefixWord, tailWord_6007586, baseEnd_6007586] using wordTrace_append hprefix tailTrace_6007586
  have hstable : (prefixWord ++ tailWord_6007586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6007586).length < 2 ^ (prefixWord ++ tailWord_6007586).sum := by decide
  have hdescent : baseEnd_6007586 < baseStart_6007586 := by decide
  rcases family_descends (prefixWord ++ tailWord_6007586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6007596 : List Nat := [2, 2, 1, 1, 1, 4, 2, 5, 1, 4]
def baseStart_6007596 : Nat := 118140960795 + 6007596 * 2 ^ 59
def prefixEnd_6007596 : Nat := 4983230072969 + 3 ^ 40 * 6007596 * 2
def baseEnd_6007596 : Nat := 1028261442009394162240525

theorem tailTrace_6007596 : CollatzResearch.WordTrace tailWord_6007596 prefixEnd_6007596 1028261442009394162240525 := by
  unfold tailWord_6007596
  simp only [CollatzResearch.WordTrace]
  refine ⟨109557513571756591278313321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146076684762342121704417761 109557513571756591278313321)
  ·
    refine ⟨82168135178817443458734991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109557513571756591278313321 82168135178817443458734991)
    ·
      refine ⟨123252202768226165188102487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82168135178817443458734991 123252202768226165188102487)
      ·
        refine ⟨184878304152339247782153731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123252202768226165188102487 184878304152339247782153731)
        ·
          refine ⟨277317456228508871673230597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184878304152339247782153731 277317456228508871673230597)
          ·
            refine ⟨51997023042845413438730737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 277317456228508871673230597 51997023042845413438730737)
            ·
              refine ⟨38997767282134060079048053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51997023042845413438730737 38997767282134060079048053)
              ·
                refine ⟨3656040682700068132410755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38997767282134060079048053 3656040682700068132410755)
                ·
                  refine ⟨5484061024050102198616133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3656040682700068132410755 5484061024050102198616133)
                  ·
                    refine ⟨1028261442009394162240525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5484061024050102198616133 1028261442009394162240525)
                    ·
                      rfl

theorem cell23_6007596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 5, 1, 4].length) (baseStart_6007596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6007596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6007596 prefixEnd_6007596 := by exact prefixLift 6007596
  have htrace : WordTrace (prefixWord ++ tailWord_6007596) baseStart_6007596 baseEnd_6007596 := by
    simpa [prefixWord, tailWord_6007596, baseEnd_6007596] using wordTrace_append hprefix tailTrace_6007596
  have hstable : (prefixWord ++ tailWord_6007596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6007596).length < 2 ^ (prefixWord ++ tailWord_6007596).sum := by decide
  have hdescent : baseEnd_6007596 < baseStart_6007596 := by decide
  rcases family_descends (prefixWord ++ tailWord_6007596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6007612 : List Nat := [2, 2, 2, 2, 1, 1, 1, 3, 1, 2, 6]
def baseStart_6007612 : Nat := 118140960795 + 6007612 * 2 ^ 59
def prefixEnd_6007612 : Nat := 4983230072969 + 3 ^ 40 * 6007612 * 2
def baseEnd_6007612 : Nat := 3084792541718654424121501

theorem tailTrace_6007612 : CollatzResearch.WordTrace tailWord_6007612 prefixEnd_6007612 3084792541718654424121501 := by
  unfold tailWord_6007612
  simp only [CollatzResearch.WordTrace]
  refine ⟨109557805355727608644604545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146077073807636811526139393 109557805355727608644604545)
  ·
    refine ⟨82168354016795706483453409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109557805355727608644604545 82168354016795706483453409)
    ·
      refine ⟨61626265512596779862590057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82168354016795706483453409 61626265512596779862590057)
      ·
        refine ⟨46219699134447584896942543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61626265512596779862590057 46219699134447584896942543)
        ·
          refine ⟨69329548701671377345413815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46219699134447584896942543 69329548701671377345413815)
          ·
            refine ⟨103994323052507066018120723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69329548701671377345413815 103994323052507066018120723)
            ·
              refine ⟨155991484578760599027181085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103994323052507066018120723 155991484578760599027181085)
              ·
                refine ⟨58496806717035224635192907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 155991484578760599027181085 58496806717035224635192907)
                ·
                  refine ⟨87745210075552836952789361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58496806717035224635192907 87745210075552836952789361)
                  ·
                    refine ⟨65808907556664627714592021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 87745210075552836952789361 65808907556664627714592021)
                    ·
                      refine ⟨3084792541718654424121501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65808907556664627714592021 3084792541718654424121501)
                      ·
                        rfl

theorem cell23_6007612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_6007612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6007612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6007612 prefixEnd_6007612 := by exact prefixLift 6007612
  have htrace : WordTrace (prefixWord ++ tailWord_6007612) baseStart_6007612 baseEnd_6007612 := by
    simpa [prefixWord, tailWord_6007612, baseEnd_6007612] using wordTrace_append hprefix tailTrace_6007612
  have hstable : (prefixWord ++ tailWord_6007612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6007612).length < 2 ^ (prefixWord ++ tailWord_6007612).sum := by decide
  have hdescent : baseEnd_6007612 < baseStart_6007612 := by decide
  rcases family_descends (prefixWord ++ tailWord_6007612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6007620 : List Nat := [2, 3, 4, 2, 1, 1, 1, 1, 2, 4, 2]
def baseStart_6007620 : Nat := 118140960795 + 6007620 * 2 ^ 59
def prefixEnd_6007620 : Nat := 4983230072969 + 3 ^ 40 * 6007620 * 2
def baseEnd_6007620 : Nat := 3084796649563890392821465

theorem tailTrace_6007620 : CollatzResearch.WordTrace tailWord_6007620 prefixEnd_6007620 3084796649563890392821465 := by
  unfold tailWord_6007620
  simp only [CollatzResearch.WordTrace]
  refine ⟨109557951247713117327750157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146077268330284156437000209 109557951247713117327750157)
  ·
    refine ⟨41084231717892418997906309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109557951247713117327750157 41084231717892418997906309)
    ·
      refine ⟨7703293447104828562107433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41084231717892418997906309 7703293447104828562107433)
      ·
        refine ⟨5777470085328621421580575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7703293447104828562107433 5777470085328621421580575)
        ·
          refine ⟨8666205127992932132370863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5777470085328621421580575 8666205127992932132370863)
          ·
            refine ⟨12999307691989398198556295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8666205127992932132370863 12999307691989398198556295)
            ·
              refine ⟨19498961537984097297834443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12999307691989398198556295 19498961537984097297834443)
              ·
                refine ⟨29248442306976145946751665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19498961537984097297834443 29248442306976145946751665)
                ·
                  refine ⟨21936331730232109460063749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29248442306976145946751665 21936331730232109460063749)
                  ·
                    refine ⟨4113062199418520523761953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21936331730232109460063749 4113062199418520523761953)
                    ·
                      refine ⟨3084796649563890392821465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4113062199418520523761953 3084796649563890392821465)
                      ·
                        rfl

theorem cell23_6007620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_6007620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6007620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6007620 prefixEnd_6007620 := by exact prefixLift 6007620
  have htrace : WordTrace (prefixWord ++ tailWord_6007620) baseStart_6007620 baseEnd_6007620 := by
    simpa [prefixWord, tailWord_6007620, baseEnd_6007620] using wordTrace_append hprefix tailTrace_6007620
  have hstable : (prefixWord ++ tailWord_6007620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6007620).length < 2 ^ (prefixWord ++ tailWord_6007620).sum := by decide
  have hdescent : baseEnd_6007620 < baseStart_6007620 := by decide
  rcases family_descends (prefixWord ++ tailWord_6007620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6007639 : List Nat := [1, 1, 3, 2, 4, 1, 2, 1, 3, 5]
def baseStart_6007639 : Nat := 118140960795 + 6007639 * 2 ^ 59
def prefixEnd_6007639 : Nat := 4983230072969 + 3 ^ 40 * 6007639 * 2
def baseEnd_6007639 : Nat := 1028268801898775272827959

theorem tailTrace_6007639 : CollatzResearch.WordTrace tailWord_6007639 prefixEnd_6007639 1028268801898775272827959 := by
  unfold tailWord_6007639
  simp only [CollatzResearch.WordTrace]
  refine ⟨219116595482357400900441971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146077730321571600600294647 219116595482357400900441971)
  ·
    refine ⟨328674893223536101350662957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219116595482357400900441971 328674893223536101350662957)
    ·
      refine ⟨123253084958826038006498609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 328674893223536101350662957 123253084958826038006498609)
      ·
        refine ⟨92439813719119528504873957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123253084958826038006498609 92439813719119528504873957)
        ·
          refine ⟨17332465072334911594663867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92439813719119528504873957 17332465072334911594663867)
          ·
            refine ⟨25998697608502367391995801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17332465072334911594663867 25998697608502367391995801)
            ·
              refine ⟨19499023206376775543996851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25998697608502367391995801 19499023206376775543996851)
              ·
                refine ⟨29248534809565163315995277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19499023206376775543996851 29248534809565163315995277)
                ·
                  refine ⟨10968200553586936243498229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29248534809565163315995277 10968200553586936243498229)
                  ·
                    refine ⟨1028268801898775272827959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10968200553586936243498229 1028268801898775272827959)
                    ·
                      rfl

theorem cell23_6007639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 3, 5].length) (baseStart_6007639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6007639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6007639 prefixEnd_6007639 := by exact prefixLift 6007639
  have htrace : WordTrace (prefixWord ++ tailWord_6007639) baseStart_6007639 baseEnd_6007639 := by
    simpa [prefixWord, tailWord_6007639, baseEnd_6007639] using wordTrace_append hprefix tailTrace_6007639
  have hstable : (prefixWord ++ tailWord_6007639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6007639).length < 2 ^ (prefixWord ++ tailWord_6007639).sum := by decide
  have hdescent : baseEnd_6007639 < baseStart_6007639 := by decide
  rcases family_descends (prefixWord ++ tailWord_6007639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6007653 : List Nat := [1, 3, 1, 3, 1, 1, 3, 5, 1, 1, 3]
def baseStart_6007653 : Nat := 118140960795 + 6007653 * 2 ^ 59
def prefixEnd_6007653 : Nat := 4983230072969 + 3 ^ 40 * 6007653 * 2
def baseEnd_6007653 : Nat := 3084813594425488763708813

theorem tailTrace_6007653 : CollatzResearch.WordTrace tailWord_6007653 prefixEnd_6007653 3084813594425488763708813 := by
  unfold tailWord_6007653
  simp only [CollatzResearch.WordTrace]
  refine ⟨219117106104306681291451613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146078070736204454194301075 219117106104306681291451613)
  ·
    refine ⟨82168914789115005484294355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219117106104306681291451613 82168914789115005484294355)
    ·
      refine ⟨123253372183672508226441533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82168914789115005484294355 123253372183672508226441533)
      ·
        refine ⟨46220014568877190584915575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123253372183672508226441533 46220014568877190584915575)
        ·
          refine ⟨69330021853315785877373363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46220014568877190584915575 69330021853315785877373363)
          ·
            refine ⟨103995032779973678816060045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69330021853315785877373363 103995032779973678816060045)
            ·
              refine ⟨38998137292490129556022517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103995032779973678816060045 38998137292490129556022517)
              ·
                refine ⟨3656075371170949645877111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38998137292490129556022517 3656075371170949645877111)
                ·
                  refine ⟨5484113056756424468815667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3656075371170949645877111 5484113056756424468815667)
                  ·
                    refine ⟨8226169585134636703223501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5484113056756424468815667 8226169585134636703223501)
                    ·
                      refine ⟨3084813594425488763708813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8226169585134636703223501 3084813594425488763708813)
                      ·
                        rfl

theorem cell23_6007653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 5, 1, 1, 3].length) (baseStart_6007653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6007653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6007653 prefixEnd_6007653 := by exact prefixLift 6007653
  have htrace : WordTrace (prefixWord ++ tailWord_6007653) baseStart_6007653 baseEnd_6007653 := by
    simpa [prefixWord, tailWord_6007653, baseEnd_6007653] using wordTrace_append hprefix tailTrace_6007653
  have hstable : (prefixWord ++ tailWord_6007653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6007653).length < 2 ^ (prefixWord ++ tailWord_6007653).sum := by decide
  have hdescent : baseEnd_6007653 < baseStart_6007653 := by decide
  rcases family_descends (prefixWord ++ tailWord_6007653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6007656 : List Nat := [2, 1, 4, 2, 1, 3, 1, 3, 1, 5]
def baseStart_6007656 : Nat := 118140960795 + 6007656 * 2 ^ 59
def prefixEnd_6007656 : Nat := 4983230072969 + 3 ^ 40 * 6007656 * 2
def baseEnd_6007656 : Nat := 1028271711622484083990433

theorem tailTrace_6007656 : CollatzResearch.WordTrace tailWord_6007656 prefixEnd_6007656 1028271711622484083990433 := by
  unfold tailWord_6007656
  simp only [CollatzResearch.WordTrace]
  refine ⟨109558607761647906401905411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146078143682197208535873881 109558607761647906401905411)
  ·
    refine ⟨164337911642471859602858117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109558607761647906401905411 164337911642471859602858117)
    ·
      refine ⟨30813358432963473675535897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 164337911642471859602858117 30813358432963473675535897)
      ·
        refine ⟨23110018824722605256651923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30813358432963473675535897 23110018824722605256651923)
        ·
          refine ⟨34665028237083907884977885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23110018824722605256651923 34665028237083907884977885)
          ·
            refine ⟨12999385588906465456866707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34665028237083907884977885 12999385588906465456866707)
            ·
              refine ⟨19499078383359698185300061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12999385588906465456866707 19499078383359698185300061)
              ·
                refine ⟨7312154393759886819487523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19499078383359698185300061 7312154393759886819487523)
                ·
                  refine ⟨10968231590639830229231285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7312154393759886819487523 10968231590639830229231285)
                  ·
                    refine ⟨1028271711622484083990433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10968231590639830229231285 1028271711622484083990433)
                    ·
                      rfl

theorem cell23_6007656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 3, 1, 5].length) (baseStart_6007656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6007656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6007656 prefixEnd_6007656 := by exact prefixLift 6007656
  have htrace : WordTrace (prefixWord ++ tailWord_6007656) baseStart_6007656 baseEnd_6007656 := by
    simpa [prefixWord, tailWord_6007656, baseEnd_6007656] using wordTrace_append hprefix tailTrace_6007656
  have hstable : (prefixWord ++ tailWord_6007656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6007656).length < 2 ^ (prefixWord ++ tailWord_6007656).sum := by decide
  have hdescent : baseEnd_6007656 < baseStart_6007656 := by decide
  rcases family_descends (prefixWord ++ tailWord_6007656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6007670 : List Nat := [5, 1, 1, 3, 1, 2, 2, 1, 3, 1, 3]
def baseStart_6007670 : Nat := 118140960795 + 6007670 * 2 ^ 59
def prefixEnd_6007670 : Nat := 4983230072969 + 3 ^ 40 * 6007670 * 2
def baseEnd_6007670 : Nat := 3084822323596615197196235

theorem tailTrace_6007670 : CollatzResearch.WordTrace tailWord_6007670 prefixEnd_6007670 3084822323596615197196235 := by
  unfold tailWord_6007670
  simp only [CollatzResearch.WordTrace]
  refine ⟨13694857884077818324676279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 146078484096830062129880309 13694857884077818324676279)
  ·
    refine ⟨20542286826116727487014419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13694857884077818324676279 20542286826116727487014419)
    ·
      refine ⟨30813430239175091230521629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20542286826116727487014419 30813430239175091230521629)
      ·
        refine ⟨11555036339690659211445611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30813430239175091230521629 11555036339690659211445611)
        ·
          refine ⟨17332554509535988817168417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11555036339690659211445611 17332554509535988817168417)
          ·
            refine ⟨12999415882151991612876313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17332554509535988817168417 12999415882151991612876313)
            ·
              refine ⟨9749561911613993709657235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12999415882151991612876313 9749561911613993709657235)
              ·
                refine ⟨14624342867420990564485853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9749561911613993709657235 14624342867420990564485853)
                ·
                  refine ⟨5484128575282871461682195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14624342867420990564485853 5484128575282871461682195)
                  ·
                    refine ⟨8226192862924307192523293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5484128575282871461682195 8226192862924307192523293)
                    ·
                      refine ⟨3084822323596615197196235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8226192862924307192523293 3084822323596615197196235)
                      ·
                        rfl

theorem cell23_6007670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_6007670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6007670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6007670 prefixEnd_6007670 := by exact prefixLift 6007670
  have htrace : WordTrace (prefixWord ++ tailWord_6007670) baseStart_6007670 baseEnd_6007670 := by
    simpa [prefixWord, tailWord_6007670, baseEnd_6007670] using wordTrace_append hprefix tailTrace_6007670
  have hstable : (prefixWord ++ tailWord_6007670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6007670).length < 2 ^ (prefixWord ++ tailWord_6007670).sum := by decide
  have hdescent : baseEnd_6007670 < baseStart_6007670 := by decide
  rcases family_descends (prefixWord ++ tailWord_6007670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6007679 : List Nat := [1, 1, 2, 2, 1, 1, 4, 1, 5, 2, 3]
def baseStart_6007679 : Nat := 118140960795 + 6007679 * 2 ^ 59
def prefixEnd_6007679 : Nat := 4983230072969 + 3 ^ 40 * 6007679 * 2
def baseEnd_6007679 : Nat := 3084826944922505661983693

theorem tailTrace_6007679 : CollatzResearch.WordTrace tailWord_6007679 prefixEnd_6007679 3084826944922505661983693 := by
  unfold tailWord_6007679
  simp only [CollatzResearch.WordTrace]
  refine ⟨219118054402212487731898091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146078702934808325154598727 219118054402212487731898091)
  ·
    refine ⟨328677081603318731597847137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219118054402212487731898091 328677081603318731597847137)
    ·
      refine ⟨246507811202489048698385353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 328677081603318731597847137 246507811202489048698385353)
      ·
        refine ⟨184880858401866786523789015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246507811202489048698385353 184880858401866786523789015)
        ·
          refine ⟨277321287602800179785683523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184880858401866786523789015 277321287602800179785683523)
          ·
            refine ⟨415981931404200269678525285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277321287602800179785683523 415981931404200269678525285)
            ·
              refine ⟨77996612138287550564723491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 415981931404200269678525285 77996612138287550564723491)
              ·
                refine ⟨116994918207431325847085237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77996612138287550564723491 116994918207431325847085237)
                ·
                  refine ⟨10968273581946686798164241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 116994918207431325847085237 10968273581946686798164241)
                  ·
                    refine ⟨8226205186460015098623181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10968273581946686798164241 8226205186460015098623181)
                    ·
                      refine ⟨3084826944922505661983693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8226205186460015098623181 3084826944922505661983693)
                      ·
                        rfl

theorem cell23_6007679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 5, 2, 3].length) (baseStart_6007679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6007679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6007679 prefixEnd_6007679 := by exact prefixLift 6007679
  have htrace : WordTrace (prefixWord ++ tailWord_6007679) baseStart_6007679 baseEnd_6007679 := by
    simpa [prefixWord, tailWord_6007679, baseEnd_6007679] using wordTrace_append hprefix tailTrace_6007679
  have hstable : (prefixWord ++ tailWord_6007679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6007679).length < 2 ^ (prefixWord ++ tailWord_6007679).sum := by decide
  have hdescent : baseEnd_6007679 < baseStart_6007679 := by decide
  rcases family_descends (prefixWord ++ tailWord_6007679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6007689 : List Nat := [1, 2, 1, 1, 5, 3, 1, 1, 1, 1, 6]
def baseStart_6007689 : Nat := 118140960795 + 6007689 * 2 ^ 59
def prefixEnd_6007689 : Nat := 4983230072969 + 3 ^ 40 * 6007689 * 2
def baseEnd_6007689 : Nat := 3084832079729050622858647

theorem tailTrace_6007689 : CollatzResearch.WordTrace tailWord_6007689 prefixEnd_6007689 3084832079729050622858647 := by
  unfold tailWord_6007689
  simp only [CollatzResearch.WordTrace]
  refine ⟨219118419132176259439762121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146078946088117506293174747 219118419132176259439762121)
  ·
    refine ⟨164338814349132194579821591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219118419132176259439762121 164338814349132194579821591)
    ·
      refine ⟨246508221523698291869732387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164338814349132194579821591 246508221523698291869732387)
      ·
        refine ⟨369762332285547437804598581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246508221523698291869732387 369762332285547437804598581)
        ·
          refine ⟨34665218651770072294181117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 369762332285547437804598581 34665218651770072294181117)
          ·
            refine ⟨12999456994413777110317919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34665218651770072294181117 12999456994413777110317919)
            ·
              refine ⟨19499185491620665665476879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12999456994413777110317919 19499185491620665665476879)
              ·
                refine ⟨29248778237430998498215319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19499185491620665665476879 29248778237430998498215319)
                ·
                  refine ⟨43873167356146497747322979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29248778237430998498215319 43873167356146497747322979)
                  ·
                    refine ⟨65809751034219746620984469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43873167356146497747322979 65809751034219746620984469)
                    ·
                      refine ⟨3084832079729050622858647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65809751034219746620984469 3084832079729050622858647)
                      ·
                        rfl

theorem cell23_6007689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 1, 6].length) (baseStart_6007689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6007689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6007689 prefixEnd_6007689 := by exact prefixLift 6007689
  have htrace : WordTrace (prefixWord ++ tailWord_6007689) baseStart_6007689 baseEnd_6007689 := by
    simpa [prefixWord, tailWord_6007689, baseEnd_6007689] using wordTrace_append hprefix tailTrace_6007689
  have hstable : (prefixWord ++ tailWord_6007689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6007689).length < 2 ^ (prefixWord ++ tailWord_6007689).sum := by decide
  have hdescent : baseEnd_6007689 < baseStart_6007689 := by decide
  rcases family_descends (prefixWord ++ tailWord_6007689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6007713 : List Nat := [1, 2, 3, 4, 1, 1, 2, 3, 1, 2, 3]
def baseStart_6007713 : Nat := 118140960795 + 6007713 * 2 ^ 59
def prefixEnd_6007713 : Nat := 4983230072969 + 3 ^ 40 * 6007713 * 2
def baseEnd_6007713 : Nat := 3084844403264758528958537

theorem tailTrace_6007713 : CollatzResearch.WordTrace tailWord_6007713 prefixEnd_6007713 3084844403264758528958537 := by
  unfold tailWord_6007713
  simp only [CollatzResearch.WordTrace]
  refine ⟨219119294484089311538635793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146079529656059541025757195 219119294484089311538635793)
  ·
    refine ⟨164339470863066983653976845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219119294484089311538635793 164339470863066983653976845)
    ·
      refine ⟨61627301573650118870241317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164339470863066983653976845 61627301573650118870241317)
      ·
        refine ⟨11555119045059397288170247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61627301573650118870241317 11555119045059397288170247)
        ·
          refine ⟨17332678567589095932255371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11555119045059397288170247 17332678567589095932255371)
          ·
            refine ⟨25999017851383643898383057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17332678567589095932255371 25999017851383643898383057)
            ·
              refine ⟨19499263388537732923787293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25999017851383643898383057 19499263388537732923787293)
              ·
                refine ⟨7312223770701649846420235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19499263388537732923787293 7312223770701649846420235)
                ·
                  refine ⟨10968335656052474769630353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7312223770701649846420235 10968335656052474769630353)
                  ·
                    refine ⟨8226251742039356077222765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10968335656052474769630353 8226251742039356077222765)
                    ·
                      refine ⟨3084844403264758528958537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8226251742039356077222765 3084844403264758528958537)
                      ·
                        rfl

theorem cell23_6007713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_6007713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6007713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6007713 prefixEnd_6007713 := by exact prefixLift 6007713
  have htrace : WordTrace (prefixWord ++ tailWord_6007713) baseStart_6007713 baseEnd_6007713 := by
    simpa [prefixWord, tailWord_6007713, baseEnd_6007713] using wordTrace_append hprefix tailTrace_6007713
  have hstable : (prefixWord ++ tailWord_6007713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6007713).length < 2 ^ (prefixWord ++ tailWord_6007713).sum := by decide
  have hdescent : baseEnd_6007713 < baseStart_6007713 := by decide
  rcases family_descends (prefixWord ++ tailWord_6007713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6007757 : List Nat := [1, 6, 3, 1, 1, 1, 1, 2, 1, 2, 4]
def baseStart_6007757 : Nat := 118140960795 + 6007757 * 2 ^ 59
def prefixEnd_6007757 : Nat := 4983230072969 + 3 ^ 40 * 6007757 * 2
def baseEnd_6007757 : Nat := 3084866996413556356808335

theorem tailTrace_6007757 : CollatzResearch.WordTrace tailWord_6007757 prefixEnd_6007757 3084866996413556356808335 := by
  unfold tailWord_6007757
  simp only [CollatzResearch.WordTrace]
  refine ⟨219120899295929907053237525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146080599530619938035491683 219120899295929907053237525)
  ·
    refine ⟨10271292154496714393120509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 219120899295929907053237525 10271292154496714393120509)
    ·
      refine ⟨3851734557936267897420191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10271292154496714393120509 3851734557936267897420191)
      ·
        refine ⟨5777601836904401846130287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3851734557936267897420191 5777601836904401846130287)
        ·
          refine ⟨8666402755356602769195431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5777601836904401846130287 8666402755356602769195431)
          ·
            refine ⟨12999604133034904153793147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8666402755356602769195431 12999604133034904153793147)
            ·
              refine ⟨19499406199552356230689721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12999604133034904153793147 19499406199552356230689721)
              ·
                refine ⟨14624554649664267173017291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19499406199552356230689721 14624554649664267173017291)
                ·
                  refine ⟨21936831974496400759525937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14624554649664267173017291 21936831974496400759525937)
                  ·
                    refine ⟨16452623980872300569644453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21936831974496400759525937 16452623980872300569644453)
                    ·
                      refine ⟨3084866996413556356808335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16452623980872300569644453 3084866996413556356808335)
                      ·
                        rfl

theorem cell23_6007757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_6007757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6007757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6007757 prefixEnd_6007757 := by exact prefixLift 6007757
  have htrace : WordTrace (prefixWord ++ tailWord_6007757) baseStart_6007757 baseEnd_6007757 := by
    simpa [prefixWord, tailWord_6007757, baseEnd_6007757] using wordTrace_append hprefix tailTrace_6007757
  have hstable : (prefixWord ++ tailWord_6007757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6007757).length < 2 ^ (prefixWord ++ tailWord_6007757).sum := by decide
  have hdescent : baseEnd_6007757 < baseStart_6007757 := by decide
  rcases family_descends (prefixWord ++ tailWord_6007757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6007786 : List Nat := [3, 1, 3, 1, 2, 2, 1, 1, 2, 4, 3]
def baseStart_6007786 : Nat := 118140960795 + 6007786 * 2 ^ 59
def prefixEnd_6007786 : Nat := 4983230072969 + 3 ^ 40 * 6007786 * 2
def baseEnd_6007786 : Nat := 3084881887352536743345701

theorem tailTrace_6007786 : CollatzResearch.WordTrace tailWord_6007786 prefixEnd_6007786 3084881887352536743345701 := by
  unfold tailWord_6007786
  simp only [CollatzResearch.WordTrace]
  refine ⟨54780489253206211251510803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146081304675216563337362141 54780489253206211251510803)
  ·
    refine ⟨82170733879809316877266205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54780489253206211251510803 82170733879809316877266205)
    ·
      refine ⟨30814025204928493828974827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82170733879809316877266205 30814025204928493828974827)
      ·
        refine ⟨46221037807392740743462241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30814025204928493828974827 46221037807392740743462241)
        ·
          refine ⟨34665778355544555557596681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46221037807392740743462241 34665778355544555557596681)
          ·
            refine ⟨25999333766658416668197511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34665778355544555557596681 25999333766658416668197511)
            ·
              refine ⟨38999000649987625002296267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25999333766658416668197511 38999000649987625002296267)
              ·
                refine ⟨58498500974981437503444401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38999000649987625002296267 58498500974981437503444401)
                ·
                  refine ⟨43873875731236078127583301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58498500974981437503444401 43873875731236078127583301)
                  ·
                    refine ⟨8226351699606764648921869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43873875731236078127583301 8226351699606764648921869)
                    ·
                      refine ⟨3084881887352536743345701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8226351699606764648921869 3084881887352536743345701)
                      ·
                        rfl

theorem cell23_6007786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 2, 4, 3].length) (baseStart_6007786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6007786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6007786 prefixEnd_6007786 := by exact prefixLift 6007786
  have htrace : WordTrace (prefixWord ++ tailWord_6007786) baseStart_6007786 baseEnd_6007786 := by
    simpa [prefixWord, tailWord_6007786, baseEnd_6007786] using wordTrace_append hprefix tailTrace_6007786
  have hstable : (prefixWord ++ tailWord_6007786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6007786).length < 2 ^ (prefixWord ++ tailWord_6007786).sum := by decide
  have hdescent : baseEnd_6007786 < baseStart_6007786 := by decide
  rcases family_descends (prefixWord ++ tailWord_6007786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6007893 : List Nat := [1, 3, 2, 2, 1, 2, 3, 2, 2, 2, 3]
def baseStart_6007893 : Nat := 118140960795 + 6007893 * 2 ^ 59
def prefixEnd_6007893 : Nat := 4983230072969 + 3 ^ 40 * 6007893 * 2
def baseEnd_6007893 : Nat := 3084936829782567824707709

theorem tailTrace_6007893 : CollatzResearch.WordTrace tailWord_6007893 prefixEnd_6007893 3084936829782567824707709 := by
  unfold tailWord_6007893
  simp only [CollatzResearch.WordTrace]
  refine ⟨219125859623437202280188333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146083906415624801520125555 219125859623437202280188333)
  ·
    refine ⟨82172197358788950855070625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219125859623437202280188333 82172197358788950855070625)
    ·
      refine ⟨61629148019091713141302969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82172197358788950855070625 61629148019091713141302969)
      ·
        refine ⟨46221861014318784855977227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61629148019091713141302969 46221861014318784855977227)
        ·
          refine ⟨69332791521478177283965841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46221861014318784855977227 69332791521478177283965841)
          ·
            refine ⟨51999593641108632962974381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69332791521478177283965841 51999593641108632962974381)
            ·
              refine ⟨19499847615415737361115393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51999593641108632962974381 19499847615415737361115393)
              ·
                refine ⟨14624885711561803020836545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19499847615415737361115393 14624885711561803020836545)
                ·
                  refine ⟨10968664283671352265627409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14624885711561803020836545 10968664283671352265627409)
                  ·
                    refine ⟨8226498212753514199220557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10968664283671352265627409 8226498212753514199220557)
                    ·
                      refine ⟨3084936829782567824707709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8226498212753514199220557 3084936829782567824707709)
                      ·
                        rfl

theorem cell23_6007893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 2, 2, 2, 3].length) (baseStart_6007893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6007893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6007893 prefixEnd_6007893 := by exact prefixLift 6007893
  have htrace : WordTrace (prefixWord ++ tailWord_6007893) baseStart_6007893 baseEnd_6007893 := by
    simpa [prefixWord, tailWord_6007893, baseEnd_6007893] using wordTrace_append hprefix tailTrace_6007893
  have hstable : (prefixWord ++ tailWord_6007893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6007893).length < 2 ^ (prefixWord ++ tailWord_6007893).sum := by decide
  have hdescent : baseEnd_6007893 < baseStart_6007893 := by decide
  rcases family_descends (prefixWord ++ tailWord_6007893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6007896 : List Nat := [2, 1, 2, 2, 1, 3, 2, 4, 6]
def baseStart_6007896 : Nat := 118140960795 + 6007896 * 2 ^ 59
def prefixEnd_6007896 : Nat := 4983230072969 + 3 ^ 40 * 6007896 * 2
def baseEnd_6007896 : Nat := 342770930024947923663355

theorem tailTrace_6007896 : CollatzResearch.WordTrace tailWord_6007896 prefixEnd_6007896 342770930024947923663355 := by
  unfold tailWord_6007896
  simp only [CollatzResearch.WordTrace]
  refine ⟨109562984521213166896273771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146083979361617555861698361 109562984521213166896273771)
  ·
    refine ⟨164344476781819750344410657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109562984521213166896273771 164344476781819750344410657)
    ·
      refine ⟨123258357586364812758307993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164344476781819750344410657 123258357586364812758307993)
      ·
        refine ⟨92443768189773609568730995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123258357586364812758307993 92443768189773609568730995)
        ·
          refine ⟨138665652284660414353096493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92443768189773609568730995 138665652284660414353096493)
          ·
            refine ⟨51999619606747655382411185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138665652284660414353096493 51999619606747655382411185)
            ·
              refine ⟨38999714705060741536808389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51999619606747655382411185 38999714705060741536808389)
              ·
                refine ⟨7312446507198889038151573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38999714705060741536808389 7312446507198889038151573)
                ·
                  refine ⟨342770930024947923663355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7312446507198889038151573 342770930024947923663355)
                  ·
                    rfl

theorem cell23_6007896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 4, 6].length) (baseStart_6007896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6007896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6007896 prefixEnd_6007896 := by exact prefixLift 6007896
  have htrace : WordTrace (prefixWord ++ tailWord_6007896) baseStart_6007896 baseEnd_6007896 := by
    simpa [prefixWord, tailWord_6007896, baseEnd_6007896] using wordTrace_append hprefix tailTrace_6007896
  have hstable : (prefixWord ++ tailWord_6007896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6007896).length < 2 ^ (prefixWord ++ tailWord_6007896).sum := by decide
  have hdescent : baseEnd_6007896 < baseStart_6007896 := by decide
  rcases family_descends (prefixWord ++ tailWord_6007896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6007913 : List Nat := [1, 2, 1, 1, 1, 6, 4, 1, 6]
def baseStart_6007913 : Nat := 118140960795 + 6007913 * 2 ^ 59
def prefixEnd_6007913 : Nat := 4983230072969 + 3 ^ 40 * 6007913 * 2
def baseEnd_6007913 : Nat := 342771899932850860717513

theorem tailTrace_6007913 : CollatzResearch.WordTrace tailWord_6007913 prefixEnd_6007913 342771899932850860717513 := by
  unfold tailWord_6007913
  simp only [CollatzResearch.WordTrace]
  refine ⟨219126589083364745695916393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146084392722243163797277595 219126589083364745695916393)
  ·
    refine ⟨164344941812523559271937295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219126589083364745695916393 164344941812523559271937295)
    ·
      refine ⟨246517412718785338907905943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164344941812523559271937295 246517412718785338907905943)
      ·
        refine ⟨369776119078178008361858915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246517412718785338907905943 369776119078178008361858915)
        ·
          refine ⟨554664178617267012542788373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 369776119078178008361858915 554664178617267012542788373)
          ·
            refine ⟨25999883372684391212943205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 554664178617267012542788373 25999883372684391212943205)
            ·
              refine ⟨4874978132378323352426851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25999883372684391212943205 4874978132378323352426851)
              ·
                refine ⟨7312467198567485028640277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4874978132378323352426851 7312467198567485028640277)
                ·
                  refine ⟨342771899932850860717513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7312467198567485028640277 342771899932850860717513)
                  ·
                    rfl

theorem cell23_6007913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 4, 1, 6].length) (baseStart_6007913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6007913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6007913 prefixEnd_6007913 := by exact prefixLift 6007913
  have htrace : WordTrace (prefixWord ++ tailWord_6007913) baseStart_6007913 baseEnd_6007913 := by
    simpa [prefixWord, tailWord_6007913, baseEnd_6007913] using wordTrace_append hprefix tailTrace_6007913
  have hstable : (prefixWord ++ tailWord_6007913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6007913).length < 2 ^ (prefixWord ++ tailWord_6007913).sum := by decide
  have hdescent : baseEnd_6007913 < baseStart_6007913 := by decide
  rcases family_descends (prefixWord ++ tailWord_6007913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6007973 : List Nat := [1, 3, 1, 2, 1, 5, 2, 1, 1, 6]
def baseStart_6007973 : Nat := 118140960795 + 6007973 * 2 ^ 59
def prefixEnd_6007973 : Nat := 4983230072969 + 3 ^ 40 * 6007973 * 2
def baseEnd_6007973 : Nat := 1028325969411642503902447

theorem tailTrace_6007973 : CollatzResearch.WordTrace tailWord_6007973 prefixEnd_6007973 1028325969411642503902447 := by
  unfold tailWord_6007973
  simp only [CollatzResearch.WordTrace]
  refine ⟨219128777463147375943100573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146085851642098250628733715 219128777463147375943100573)
  ·
    refine ⟨82173291548680265978662715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219128777463147375943100573 82173291548680265978662715)
    ·
      refine ⟨123259937323020398967994073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82173291548680265978662715 123259937323020398967994073)
      ·
        refine ⟨92444952992265299225995555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123259937323020398967994073 92444952992265299225995555)
        ·
          refine ⟨138667429488397948838993333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92444952992265299225995555 138667429488397948838993333)
          ·
            refine ⟨13000071514537307703655625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 138667429488397948838993333 13000071514537307703655625)
            ·
              refine ⟨9750053635902980777741719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13000071514537307703655625 9750053635902980777741719)
              ·
                refine ⟨14625080453854471166612579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9750053635902980777741719 14625080453854471166612579)
                ·
                  refine ⟨21937620680781706749918869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14625080453854471166612579 21937620680781706749918869)
                  ·
                    refine ⟨1028325969411642503902447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21937620680781706749918869 1028325969411642503902447)
                    ·
                      rfl

theorem cell23_6007973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 1, 1, 6].length) (baseStart_6007973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6007973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6007973 prefixEnd_6007973 := by exact prefixLift 6007973
  have htrace : WordTrace (prefixWord ++ tailWord_6007973) baseStart_6007973 baseEnd_6007973 := by
    simpa [prefixWord, tailWord_6007973, baseEnd_6007973] using wordTrace_append hprefix tailTrace_6007973
  have hstable : (prefixWord ++ tailWord_6007973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6007973).length < 2 ^ (prefixWord ++ tailWord_6007973).sum := by decide
  have hdescent : baseEnd_6007973 < baseStart_6007973 := by decide
  rcases family_descends (prefixWord ++ tailWord_6007973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6007983 : List Nat := [1, 1, 2, 1, 2, 3, 4, 1, 3, 2, 3]
def baseStart_6007983 : Nat := 118140960795 + 6007983 * 2 ^ 59
def prefixEnd_6007983 : Nat := 4983230072969 + 3 ^ 40 * 6007983 * 2
def baseEnd_6007983 : Nat := 3084983043041472472582295

theorem tailTrace_6007983 : CollatzResearch.WordTrace tailWord_6007983 prefixEnd_6007983 3084983043041472472582295 := by
  unfold tailWord_6007983
  simp only [CollatzResearch.WordTrace]
  refine ⟨219129142193111147650964603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146086094795407431767309735 219129142193111147650964603)
  ·
    refine ⟨328693713289666721476446905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219129142193111147650964603 328693713289666721476446905)
    ·
      refine ⟨246520284967250041107335179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 328693713289666721476446905 246520284967250041107335179)
      ·
        refine ⟨369780427450875061661002769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246520284967250041107335179 369780427450875061661002769)
        ·
          refine ⟨277335320588156296245752077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 369780427450875061661002769 277335320588156296245752077)
          ·
            refine ⟨104000745220558611092157029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 277335320588156296245752077 104000745220558611092157029)
            ·
              refine ⟨19500139728854739579779443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104000745220558611092157029 19500139728854739579779443)
              ·
                refine ⟨29250209593282109369669165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19500139728854739579779443 29250209593282109369669165)
                ·
                  refine ⟨10968828597480791013625937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29250209593282109369669165 10968828597480791013625937)
                  ·
                    refine ⟨8226621448110593260219453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10968828597480791013625937 8226621448110593260219453)
                    ·
                      refine ⟨3084983043041472472582295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8226621448110593260219453 3084983043041472472582295)
                      ·
                        rfl

theorem cell23_6007983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 3, 2, 3].length) (baseStart_6007983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6007983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6007983 prefixEnd_6007983 := by exact prefixLift 6007983
  have htrace : WordTrace (prefixWord ++ tailWord_6007983) baseStart_6007983 baseEnd_6007983 := by
    simpa [prefixWord, tailWord_6007983, baseEnd_6007983] using wordTrace_append hprefix tailTrace_6007983
  have hstable : (prefixWord ++ tailWord_6007983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6007983).length < 2 ^ (prefixWord ++ tailWord_6007983).sum := by decide
  have hdescent : baseEnd_6007983 < baseStart_6007983 := by decide
  rcases family_descends (prefixWord ++ tailWord_6007983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6007993 : List Nat := [1, 2, 1, 4, 1, 3, 2, 2, 1, 2, 4]
def baseStart_6007993 : Nat := 118140960795 + 6007993 * 2 ^ 59
def prefixEnd_6007993 : Nat := 4983230072969 + 3 ^ 40 * 6007993 * 2
def baseEnd_6007993 : Nat := 3084988177848017433457249

theorem tailTrace_6007993 : CollatzResearch.WordTrace tailWord_6007993 prefixEnd_6007993 3084988177848017433457249 := by
  unfold tailWord_6007993
  simp only [CollatzResearch.WordTrace]
  refine ⟨219129506923074919358828633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146086337948716612905885755 219129506923074919358828633)
  ·
    refine ⟨164347130192306189519121475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219129506923074919358828633 164347130192306189519121475)
    ·
      refine ⟨246520695288459284278682213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164347130192306189519121475 246520695288459284278682213)
      ·
        refine ⟨46222630366586115802252915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 246520695288459284278682213 46222630366586115802252915)
        ·
          refine ⟨69333945549879173703379373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46222630366586115802252915 69333945549879173703379373)
          ·
            refine ⟨26000229581204690138767265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69333945549879173703379373 26000229581204690138767265)
            ·
              refine ⟨19500172185903517604075449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26000229581204690138767265 19500172185903517604075449)
              ·
                refine ⟨14625129139427638203056587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19500172185903517604075449 14625129139427638203056587)
                ·
                  refine ⟨21937693709141457304584881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14625129139427638203056587 21937693709141457304584881)
                  ·
                    refine ⟨16453270281856092978438661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21937693709141457304584881 16453270281856092978438661)
                    ·
                      refine ⟨3084988177848017433457249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16453270281856092978438661 3084988177848017433457249)
                      ·
                        rfl

theorem cell23_6007993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_6007993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6007993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6007993 prefixEnd_6007993 := by exact prefixLift 6007993
  have htrace : WordTrace (prefixWord ++ tailWord_6007993) baseStart_6007993 baseEnd_6007993 := by
    simpa [prefixWord, tailWord_6007993, baseEnd_6007993] using wordTrace_append hprefix tailTrace_6007993
  have hstable : (prefixWord ++ tailWord_6007993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6007993).length < 2 ^ (prefixWord ++ tailWord_6007993).sum := by decide
  have hdescent : baseEnd_6007993 < baseStart_6007993 := by decide
  rcases family_descends (prefixWord ++ tailWord_6007993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6008014 : List Nat := [4, 1, 1, 1, 5, 1, 2, 1, 3, 2, 2]
def baseStart_6008014 : Nat := 118140960795 + 6008014 * 2 ^ 59
def prefixEnd_6008014 : Nat := 4983230072969 + 3 ^ 40 * 6008014 * 2
def baseEnd_6008014 : Nat := 3084998960941761851294653

theorem tailTrace_6008014 : CollatzResearch.WordTrace tailWord_6008014 prefixEnd_6008014 3084998960941761851294653 := by
  unfold tailWord_6008014
  simp only [CollatzResearch.WordTrace]
  refine ⟨27391284106999854993167887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146086848570665893296895397 27391284106999854993167887)
  ·
    refine ⟨41086926160499782489751831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27391284106999854993167887 41086926160499782489751831)
    ·
      refine ⟨61630389240749673734627747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41086926160499782489751831 61630389240749673734627747)
      ·
        refine ⟨92445583861124510601941621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61630389240749673734627747 92445583861124510601941621)
        ·
          refine ⟨8666773486980422868932027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 92445583861124510601941621 8666773486980422868932027)
          ·
            refine ⟨13000160230470634303398041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8666773486980422868932027 13000160230470634303398041)
            ·
              refine ⟨9750120172852975727548531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13000160230470634303398041 9750120172852975727548531)
              ·
                refine ⟨14625180259279463591322797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9750120172852975727548531 14625180259279463591322797)
                ·
                  refine ⟨5484442597229798846746049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14625180259279463591322797 5484442597229798846746049)
                  ·
                    refine ⟨4113331947922349135059537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5484442597229798846746049 4113331947922349135059537)
                    ·
                      refine ⟨3084998960941761851294653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4113331947922349135059537 3084998960941761851294653)
                      ·
                        rfl

theorem cell23_6008014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 1, 3, 2, 2].length) (baseStart_6008014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6008014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6008014 prefixEnd_6008014 := by exact prefixLift 6008014
  have htrace : WordTrace (prefixWord ++ tailWord_6008014) baseStart_6008014 baseEnd_6008014 := by
    simpa [prefixWord, tailWord_6008014, baseEnd_6008014] using wordTrace_append hprefix tailTrace_6008014
  have hstable : (prefixWord ++ tailWord_6008014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6008014).length < 2 ^ (prefixWord ++ tailWord_6008014).sum := by decide
  have hdescent : baseEnd_6008014 < baseStart_6008014 := by decide
  rcases family_descends (prefixWord ++ tailWord_6008014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6008037 : List Nat := [1, 3, 1, 4, 4, 1, 2, 7]
def baseStart_6008037 : Nat := 118140960795 + 6008037 * 2 ^ 59
def prefixEnd_6008037 : Nat := 4983230072969 + 3 ^ 40 * 6008037 * 2
def baseEnd_6008037 : Nat := 114259658185067231900261

theorem tailTrace_6008037 : CollatzResearch.WordTrace tailWord_6008037 prefixEnd_6008037 114259658185067231900261 := by
  unfold tailWord_6008037
  simp only [CollatzResearch.WordTrace]
  refine ⟨219131111734915514873430365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146087407823277009915620243 219131111734915514873430365)
  ·
    refine ⟨82174166900593318077536387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219131111734915514873430365 82174166900593318077536387)
    ·
      refine ⟨123261250350889977116304581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82174166900593318077536387 123261250350889977116304581)
      ·
        refine ⟨23111484440791870709307109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123261250350889977116304581 23111484440791870709307109)
        ·
          refine ⟨4333403332648475757995083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23111484440791870709307109 4333403332648475757995083)
          ·
            refine ⟨6500104998972713636992625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4333403332648475757995083 6500104998972713636992625)
            ·
              refine ⟨4875078749229535227744469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6500104998972713636992625 4875078749229535227744469)
              ·
                refine ⟨114259658185067231900261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4875078749229535227744469 114259658185067231900261)
                ·
                  rfl

theorem cell23_6008037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 2, 7].length) (baseStart_6008037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6008037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6008037 prefixEnd_6008037 := by exact prefixLift 6008037
  have htrace : WordTrace (prefixWord ++ tailWord_6008037) baseStart_6008037 baseEnd_6008037 := by
    simpa [prefixWord, tailWord_6008037, baseEnd_6008037] using wordTrace_append hprefix tailTrace_6008037
  have hstable : (prefixWord ++ tailWord_6008037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6008037).length < 2 ^ (prefixWord ++ tailWord_6008037).sum := by decide
  have hdescent : baseEnd_6008037 < baseStart_6008037 := by decide
  rcases family_descends (prefixWord ++ tailWord_6008037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6008073 : List Nat := [1, 2, 1, 1, 3, 3, 2, 1, 2, 4, 3]
def baseStart_6008073 : Nat := 118140960795 + 6008073 * 2 ^ 59
def prefixEnd_6008073 : Nat := 4983230072969 + 3 ^ 40 * 6008073 * 2
def baseEnd_6008073 : Nat := 3085029256300377120456881

theorem tailTrace_6008073 : CollatzResearch.WordTrace tailWord_6008073 prefixEnd_6008073 3085029256300377120456881 := by
  unfold tailWord_6008073
  simp only [CollatzResearch.WordTrace]
  refine ⟨219132424762785093021740873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146088283175190062014493915 219132424762785093021740873)
  ·
    refine ⟨164349318572088819766305655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219132424762785093021740873 164349318572088819766305655)
    ·
      refine ⟨246523977858133229649458483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164349318572088819766305655 246523977858133229649458483)
      ·
        refine ⟨369785966787199844474187725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246523977858133229649458483 369785966787199844474187725)
        ·
          refine ⟨138669737545199941677820397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 369785966787199844474187725 138669737545199941677820397)
          ·
            refine ⟨52001151579449978129182649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138669737545199941677820397 52001151579449978129182649)
            ·
              refine ⟨39000863684587483596886987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52001151579449978129182649 39000863684587483596886987)
              ·
                refine ⟨58501295526881225395330481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39000863684587483596886987 58501295526881225395330481)
                ·
                  refine ⟨43875971645160919046497861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58501295526881225395330481 43875971645160919046497861)
                  ·
                    refine ⟨8226744683467672321218349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43875971645160919046497861 8226744683467672321218349)
                    ·
                      refine ⟨3085029256300377120456881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8226744683467672321218349 3085029256300377120456881)
                      ·
                        rfl

theorem cell23_6008073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 4, 3].length) (baseStart_6008073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6008073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6008073 prefixEnd_6008073 := by exact prefixLift 6008073
  have htrace : WordTrace (prefixWord ++ tailWord_6008073) baseStart_6008073 baseEnd_6008073 := by
    simpa [prefixWord, tailWord_6008073, baseEnd_6008073] using wordTrace_append hprefix tailTrace_6008073
  have hstable : (prefixWord ++ tailWord_6008073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6008073).length < 2 ^ (prefixWord ++ tailWord_6008073).sum := by decide
  have hdescent : baseEnd_6008073 < baseStart_6008073 := by decide
  rcases family_descends (prefixWord ++ tailWord_6008073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6008121 : List Nat := [1, 2, 1, 6, 2, 1, 2, 2, 2, 2, 2]
def baseStart_6008121 : Nat := 118140960795 + 6008121 * 2 ^ 59
def prefixEnd_6008121 : Nat := 4983230072969 + 3 ^ 40 * 6008121 * 2
def baseEnd_6008121 : Nat := 3085053903371792932656661

theorem tailTrace_6008121 : CollatzResearch.WordTrace tailWord_6008121 prefixEnd_6008121 3085053903371792932656661 := by
  unfold tailWord_6008121
  simp only [CollatzResearch.WordTrace]
  refine ⟨219134175466611197219488217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146089450311074131479658811 219134175466611197219488217)
  ·
    refine ⟨164350631599958397914616163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219134175466611197219488217 164350631599958397914616163)
    ·
      refine ⟨246525947399937596871924245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164350631599958397914616163 246525947399937596871924245)
      ·
        refine ⟨11555903784372074853371449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 246525947399937596871924245 11555903784372074853371449)
        ·
          refine ⟨8666927838279056140028587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11555903784372074853371449 8666927838279056140028587)
          ·
            refine ⟨13000391757418584210042881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8666927838279056140028587 13000391757418584210042881)
            ·
              refine ⟨9750293818063938157532161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13000391757418584210042881 9750293818063938157532161)
              ·
                refine ⟨7312720363547953618149121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9750293818063938157532161 7312720363547953618149121)
                ·
                  refine ⟨5484540272660965213611841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7312720363547953618149121 5484540272660965213611841)
                  ·
                    refine ⟨4113405204495723910208881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5484540272660965213611841 4113405204495723910208881)
                    ·
                      refine ⟨3085053903371792932656661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4113405204495723910208881 3085053903371792932656661)
                      ·
                        rfl

theorem cell23_6008121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_6008121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6008121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6008121 prefixEnd_6008121 := by exact prefixLift 6008121
  have htrace : WordTrace (prefixWord ++ tailWord_6008121) baseStart_6008121 baseEnd_6008121 := by
    simpa [prefixWord, tailWord_6008121, baseEnd_6008121] using wordTrace_append hprefix tailTrace_6008121
  have hstable : (prefixWord ++ tailWord_6008121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6008121).length < 2 ^ (prefixWord ++ tailWord_6008121).sum := by decide
  have hdescent : baseEnd_6008121 < baseStart_6008121 := by decide
  rcases family_descends (prefixWord ++ tailWord_6008121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6008127 : List Nat := [1, 1, 2, 2, 4, 2, 4, 2, 5]
def baseStart_6008127 : Nat := 118140960795 + 6008127 * 2 ^ 59
def prefixEnd_6008127 : Nat := 4983230072969 + 3 ^ 40 * 6008127 * 2
def baseEnd_6008127 : Nat := 342784109361746656575737

theorem tailTrace_6008127 : CollatzResearch.WordTrace tailWord_6008127 prefixEnd_6008127 342784109361746656575737 := by
  unfold tailWord_6008127
  simp only [CollatzResearch.WordTrace]
  refine ⟨219134394304589460244206635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146089596203059640162804423 219134394304589460244206635)
  ·
    refine ⟨328701591456884190366309953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219134394304589460244206635 328701591456884190366309953)
    ·
      refine ⟨246526193592663142774732465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 328701591456884190366309953 246526193592663142774732465)
      ·
        refine ⟨184894645194497357081049349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246526193592663142774732465 184894645194497357081049349)
        ·
          refine ⟨34667745973968254452696753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 184894645194497357081049349 34667745973968254452696753)
          ·
            refine ⟨26000809480476190839522565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34667745973968254452696753 26000809480476190839522565)
            ·
              refine ⟨4875151777589285782410481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26000809480476190839522565 4875151777589285782410481)
              ·
                refine ⟨3656363833191964336807861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4875151777589285782410481 3656363833191964336807861)
                ·
                  refine ⟨342784109361746656575737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3656363833191964336807861 342784109361746656575737)
                  ·
                    rfl

theorem cell23_6008127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 4, 2, 5].length) (baseStart_6008127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6008127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6008127 prefixEnd_6008127 := by exact prefixLift 6008127
  have htrace : WordTrace (prefixWord ++ tailWord_6008127) baseStart_6008127 baseEnd_6008127 := by
    simpa [prefixWord, tailWord_6008127, baseEnd_6008127] using wordTrace_append hprefix tailTrace_6008127
  have hstable : (prefixWord ++ tailWord_6008127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6008127).length < 2 ^ (prefixWord ++ tailWord_6008127).sum := by decide
  have hdescent : baseEnd_6008127 < baseStart_6008127 := by decide
  rcases family_descends (prefixWord ++ tailWord_6008127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6008160 : List Nat := [2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 4]
def baseStart_6008160 : Nat := 118140960795 + 6008160 * 2 ^ 59
def prefixEnd_6008160 : Nat := 4983230072969 + 3 ^ 40 * 6008160 * 2
def baseEnd_6008160 : Nat := 3085073929117318280068981

theorem tailTrace_6008160 : CollatzResearch.WordTrace tailWord_6008160 prefixEnd_6008160 3085073929117318280068981 := by
  unfold tailWord_6008160
  simp only [CollatzResearch.WordTrace]
  refine ⟨109567798956734953440078967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146090398608979937920105289 109567798956734953440078967)
  ·
    refine ⟨164351698435102430160118451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109567798956734953440078967 164351698435102430160118451)
    ·
      refine ⟨246527547652653645240177677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164351698435102430160118451 246527547652653645240177677)
      ·
        refine ⟨92447830369745116965066629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 246527547652653645240177677 92447830369745116965066629)
        ·
          refine ⟨17333968194327209430949993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92447830369745116965066629 17333968194327209430949993)
          ·
            refine ⟨13000476145745407073212495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17333968194327209430949993 13000476145745407073212495)
            ·
              refine ⟨19500714218618110609818743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13000476145745407073212495 19500714218618110609818743)
              ·
                refine ⟨29251071327927165914728115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19500714218618110609818743 29251071327927165914728115)
                ·
                  refine ⟨43876606991890748872092173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29251071327927165914728115 43876606991890748872092173)
                  ·
                    refine ⟨16453727621959030827034565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43876606991890748872092173 16453727621959030827034565)
                    ·
                      refine ⟨3085073929117318280068981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16453727621959030827034565 3085073929117318280068981)
                      ·
                        rfl

theorem cell23_6008160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 4].length) (baseStart_6008160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6008160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6008160 prefixEnd_6008160 := by exact prefixLift 6008160
  have htrace : WordTrace (prefixWord ++ tailWord_6008160) baseStart_6008160 baseEnd_6008160 := by
    simpa [prefixWord, tailWord_6008160, baseEnd_6008160] using wordTrace_append hprefix tailTrace_6008160
  have hstable : (prefixWord ++ tailWord_6008160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6008160).length < 2 ^ (prefixWord ++ tailWord_6008160).sum := by decide
  have hdescent : baseEnd_6008160 < baseStart_6008160 := by decide
  rcases family_descends (prefixWord ++ tailWord_6008160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6008183 : List Nat := [1, 1, 3, 1, 1, 2, 5, 1, 8]
def baseStart_6008183 : Nat := 118140960795 + 6008183 * 2 ^ 59
def prefixEnd_6008183 : Nat := 4983230072969 + 3 ^ 40 * 6008183 * 2
def baseEnd_6008183 : Nat := 342787304352485743342375

theorem tailTrace_6008183 : CollatzResearch.WordTrace tailWord_6008183 prefixEnd_6008183 342787304352485743342375 := by
  unfold tailWord_6008183
  simp only [CollatzResearch.WordTrace]
  refine ⟨219136436792386581808245203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146090957861591054538830135 219136436792386581808245203)
  ·
    refine ⟨328704655188579872712367805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219136436792386581808245203 328704655188579872712367805)
    ·
      refine ⟨123264245695717452267137927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 328704655188579872712367805 123264245695717452267137927)
      ·
        refine ⟨184896368543576178400706891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123264245695717452267137927 184896368543576178400706891)
        ·
          refine ⟨277344552815364267601060337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184896368543576178400706891 277344552815364267601060337)
          ·
            refine ⟨208008414611523200700795253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 277344552815364267601060337 208008414611523200700795253)
            ·
              refine ⟨19500788869830300065699555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 208008414611523200700795253 19500788869830300065699555)
              ·
                refine ⟨29251183304745450098549333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19500788869830300065699555 29251183304745450098549333)
                ·
                  refine ⟨342787304352485743342375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29251183304745450098549333 342787304352485743342375)
                  ·
                    rfl

theorem cell23_6008183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 8].length) (baseStart_6008183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6008183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6008183 prefixEnd_6008183 := by exact prefixLift 6008183
  have htrace : WordTrace (prefixWord ++ tailWord_6008183) baseStart_6008183 baseEnd_6008183 := by
    simpa [prefixWord, tailWord_6008183, baseEnd_6008183] using wordTrace_append hprefix tailTrace_6008183
  have hstable : (prefixWord ++ tailWord_6008183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6008183).length < 2 ^ (prefixWord ++ tailWord_6008183).sum := by decide
  have hdescent : baseEnd_6008183 < baseStart_6008183 := by decide
  rcases family_descends (prefixWord ++ tailWord_6008183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6008187 : List Nat := [1, 1, 1, 1, 1, 6, 1, 6, 1, 4]
def baseStart_6008187 : Nat := 118140960795 + 6008187 * 2 ^ 59
def prefixEnd_6008187 : Nat := 4983230072969 + 3 ^ 40 * 6008187 * 2
def baseEnd_6008187 : Nat := 1028362597698329891477119

theorem tailTrace_6008187 : CollatzResearch.WordTrace tailWord_6008187 prefixEnd_6008187 1028362597698329891477119 := by
  unfold tailWord_6008187
  simp only [CollatzResearch.WordTrace]
  refine ⟨219136582684372090491390815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146091055122914726994260543 219136582684372090491390815)
  ·
    refine ⟨328704874026558135737086223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219136582684372090491390815 328704874026558135737086223)
    ·
      refine ⟨493057311039837203605629335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328704874026558135737086223 493057311039837203605629335)
      ·
        refine ⟨739585966559755805408444003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 493057311039837203605629335 739585966559755805408444003)
        ·
          refine ⟨1109378949839633708112666005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 739585966559755805408444003 1109378949839633708112666005)
          ·
            refine ⟨52002138273732830067781219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1109378949839633708112666005 52002138273732830067781219)
            ·
              refine ⟨78003207410599245101671829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52002138273732830067781219 78003207410599245101671829)
              ·
                refine ⟨3656400347371839614140867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 78003207410599245101671829 3656400347371839614140867)
                ·
                  refine ⟨5484600521057759421211301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3656400347371839614140867 5484600521057759421211301)
                  ·
                    refine ⟨1028362597698329891477119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5484600521057759421211301 1028362597698329891477119)
                    ·
                      rfl

theorem cell23_6008187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 6, 1, 4].length) (baseStart_6008187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6008187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6008187 prefixEnd_6008187 := by exact prefixLift 6008187
  have htrace : WordTrace (prefixWord ++ tailWord_6008187) baseStart_6008187 baseEnd_6008187 := by
    simpa [prefixWord, tailWord_6008187, baseEnd_6008187] using wordTrace_append hprefix tailTrace_6008187
  have hstable : (prefixWord ++ tailWord_6008187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6008187).length < 2 ^ (prefixWord ++ tailWord_6008187).sum := by decide
  have hdescent : baseEnd_6008187 < baseStart_6008187 := by decide
  rcases family_descends (prefixWord ++ tailWord_6008187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6008203 : List Nat := [1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 6]
def baseStart_6008203 : Nat := 118140960795 + 6008203 * 2 ^ 59
def prefixEnd_6008203 : Nat := 4983230072969 + 3 ^ 40 * 6008203 * 2
def baseEnd_6008203 : Nat := 3085096008785461611831283

theorem tailTrace_6008203 : CollatzResearch.WordTrace tailWord_6008203 prefixEnd_6008203 3085096008785461611831283 := by
  unfold tailWord_6008203
  simp only [CollatzResearch.WordTrace]
  refine ⟨219137166252314125223973263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146091444168209416815982175 219137166252314125223973263)
  ·
    refine ⟨328705749378471187835959895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219137166252314125223973263 328705749378471187835959895)
    ·
      refine ⟨493058624067706781753939843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328705749378471187835959895 493058624067706781753939843)
      ·
        refine ⟨739587936101560172630909765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 493058624067706781753939843 739587936101560172630909765)
        ·
          refine ⟨138672738019042532368295581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 739587936101560172630909765 138672738019042532368295581)
          ·
            refine ⟨52002276757140949638110843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138672738019042532368295581 52002276757140949638110843)
            ·
              refine ⟨78003415135711424457166265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52002276757140949638110843 78003415135711424457166265)
              ·
                refine ⟨58502561351783568342874699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78003415135711424457166265 58502561351783568342874699)
                ·
                  refine ⟨87753842027675352514312049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58502561351783568342874699 87753842027675352514312049)
                  ·
                    refine ⟨65815381520756514385734037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 87753842027675352514312049 65815381520756514385734037)
                    ·
                      refine ⟨3085096008785461611831283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65815381520756514385734037 3085096008785461611831283)
                      ·
                        rfl

theorem cell23_6008203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 6].length) (baseStart_6008203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6008203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6008203 prefixEnd_6008203 := by exact prefixLift 6008203
  have htrace : WordTrace (prefixWord ++ tailWord_6008203) baseStart_6008203 baseEnd_6008203 := by
    simpa [prefixWord, tailWord_6008203, baseEnd_6008203] using wordTrace_append hprefix tailTrace_6008203
  have hstable : (prefixWord ++ tailWord_6008203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6008203).length < 2 ^ (prefixWord ++ tailWord_6008203).sum := by decide
  have hdescent : baseEnd_6008203 < baseStart_6008203 := by decide
  rcases family_descends (prefixWord ++ tailWord_6008203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6008221 : List Nat := [1, 4, 2, 1, 3, 3, 1, 3, 1, 4]
def baseStart_6008221 : Nat := 118140960795 + 6008221 * 2 ^ 59
def prefixEnd_6008221 : Nat := 4983230072969 + 3 ^ 40 * 6008221 * 2
def baseEnd_6008221 : Nat := 1028368417145747513802067

theorem tailTrace_6008221 : CollatzResearch.WordTrace tailWord_6008221 prefixEnd_6008221 1028368417145747513802067 := by
  unfold tailWord_6008221
  simp only [CollatzResearch.WordTrace]
  refine ⟨219137822766248914298128517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146091881844165942865419011 219137822766248914298128517)
  ·
    refine ⟨41088341768671671430899097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 219137822766248914298128517 41088341768671671430899097)
    ·
      refine ⟨30816256326503753573174323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41088341768671671430899097 30816256326503753573174323)
      ·
        refine ⟨46224384489755630359761485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30816256326503753573174323 46224384489755630359761485)
        ·
          refine ⟨17334144183658361384910557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46224384489755630359761485 17334144183658361384910557)
          ·
            refine ⟨6500304068871885519341459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17334144183658361384910557 6500304068871885519341459)
            ·
              refine ⟨9750456103307828279012189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6500304068871885519341459 9750456103307828279012189)
              ·
                refine ⟨3656421038740435604629571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9750456103307828279012189 3656421038740435604629571)
                ·
                  refine ⟨5484631558110653406944357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3656421038740435604629571 5484631558110653406944357)
                  ·
                    refine ⟨1028368417145747513802067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5484631558110653406944357 1028368417145747513802067)
                    ·
                      rfl

theorem cell23_6008221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 3, 1, 4].length) (baseStart_6008221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6008221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6008221 prefixEnd_6008221 := by exact prefixLift 6008221
  have htrace : WordTrace (prefixWord ++ tailWord_6008221) baseStart_6008221 baseEnd_6008221 := by
    simpa [prefixWord, tailWord_6008221, baseEnd_6008221] using wordTrace_append hprefix tailTrace_6008221
  have hstable : (prefixWord ++ tailWord_6008221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6008221).length < 2 ^ (prefixWord ++ tailWord_6008221).sum := by decide
  have hdescent : baseEnd_6008221 < baseStart_6008221 := by decide
  rcases family_descends (prefixWord ++ tailWord_6008221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6008267 : List Nat := [1, 1, 1, 1, 3, 3, 5, 2, 1, 1, 4]
def baseStart_6008267 : Nat := 118140960795 + 6008267 * 2 ^ 59
def prefixEnd_6008267 : Nat := 4983230072969 + 3 ^ 40 * 6008267 * 2
def baseEnd_6008267 : Nat := 3085128871547349361430989

theorem tailTrace_6008267 : CollatzResearch.WordTrace tailWord_6008267 prefixEnd_6008267 3085128871547349361430989 := by
  unfold tailWord_6008267
  simp only [CollatzResearch.WordTrace]
  refine ⟨219139500524082264154303055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146093000349388176102868703 219139500524082264154303055)
  ·
    refine ⟨328709250786123396231454583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219139500524082264154303055 328709250786123396231454583)
    ·
      refine ⟨493063876179185094347181875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328709250786123396231454583 493063876179185094347181875)
      ·
        refine ⟨739595814268777641520772813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 493063876179185094347181875 739595814268777641520772813)
        ·
          refine ⟨277348430350791615570289805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 739595814268777641520772813 277348430350791615570289805)
          ·
            refine ⟨104005661381546855838858677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 277348430350791615570289805 104005661381546855838858677)
            ·
              refine ⟨9750530754520017734893001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 104005661381546855838858677 9750530754520017734893001)
              ·
                refine ⟨7312898065890013301169751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9750530754520017734893001 7312898065890013301169751)
                ·
                  refine ⟨10969347098835019951754627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7312898065890013301169751 10969347098835019951754627)
                  ·
                    refine ⟨16454020648252529927631941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10969347098835019951754627 16454020648252529927631941)
                    ·
                      refine ⟨3085128871547349361430989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16454020648252529927631941 3085128871547349361430989)
                      ·
                        rfl

theorem cell23_6008267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 2, 1, 1, 4].length) (baseStart_6008267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6008267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6008267 prefixEnd_6008267 := by exact prefixLift 6008267
  have htrace : WordTrace (prefixWord ++ tailWord_6008267) baseStart_6008267 baseEnd_6008267 := by
    simpa [prefixWord, tailWord_6008267, baseEnd_6008267] using wordTrace_append hprefix tailTrace_6008267
  have hstable : (prefixWord ++ tailWord_6008267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6008267).length < 2 ^ (prefixWord ++ tailWord_6008267).sum := by decide
  have hdescent : baseEnd_6008267 < baseStart_6008267 := by decide
  rcases family_descends (prefixWord ++ tailWord_6008267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6008270 : List Nat := [4, 1, 1, 1, 2, 1, 2, 2, 3, 1, 5]
def baseStart_6008270 : Nat := 118140960795 + 6008270 * 2 ^ 59
def prefixEnd_6008270 : Nat := 4983230072969 + 3 ^ 40 * 6008270 * 2
def baseEnd_6008270 : Nat := 3085130411989312849693475

theorem tailTrace_6008270 : CollatzResearch.WordTrace tailWord_6008270 prefixEnd_6008270 3085130411989312849693475 := by
  unfold tailWord_6008270
  simp only [CollatzResearch.WordTrace]
  refine ⟨27392451242883924458332783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146093073295380930444441509 27392451242883924458332783)
  ·
    refine ⟨41088676864325886687499175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27392451242883924458332783 41088676864325886687499175)
    ·
      refine ⟨61633015296488830031248763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41088676864325886687499175 61633015296488830031248763)
      ·
        refine ⟨92449522944733245046873145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61633015296488830031248763 92449522944733245046873145)
        ·
          refine ⟨69337142208549933785154859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92449522944733245046873145 69337142208549933785154859)
          ·
            refine ⟨104005713312824900677732289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69337142208549933785154859 104005713312824900677732289)
            ·
              refine ⟨78004284984618675508299217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104005713312824900677732289 78004284984618675508299217)
              ·
                refine ⟨58503213738464006631224413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78004284984618675508299217 58503213738464006631224413)
                ·
                  refine ⟨21938705151924002486709155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58503213738464006631224413 21938705151924002486709155)
                  ·
                    refine ⟨32908057727886003730063733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21938705151924002486709155 32908057727886003730063733)
                    ·
                      refine ⟨3085130411989312849693475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32908057727886003730063733 3085130411989312849693475)
                      ·
                        rfl

theorem cell23_6008270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 3, 1, 5].length) (baseStart_6008270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6008270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6008270 prefixEnd_6008270 := by exact prefixLift 6008270
  have htrace : WordTrace (prefixWord ++ tailWord_6008270) baseStart_6008270 baseEnd_6008270 := by
    simpa [prefixWord, tailWord_6008270, baseEnd_6008270] using wordTrace_append hprefix tailTrace_6008270
  have hstable : (prefixWord ++ tailWord_6008270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6008270).length < 2 ^ (prefixWord ++ tailWord_6008270).sum := by decide
  have hdescent : baseEnd_6008270 < baseStart_6008270 := by decide
  rcases family_descends (prefixWord ++ tailWord_6008270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6008280 : List Nat := [2, 1, 2, 2, 2, 1, 3, 1, 3, 2, 4]
def baseStart_6008280 : Nat := 118140960795 + 6008280 * 2 ^ 59
def prefixEnd_6008280 : Nat := 4983230072969 + 3 ^ 40 * 6008280 * 2
def baseEnd_6008280 : Nat := 3085135546795857810568429

theorem tailTrace_6008280 : CollatzResearch.WordTrace tailWord_6008280 prefixEnd_6008280 3085135546795857810568429 := by
  unfold tailWord_6008280
  simp only [CollatzResearch.WordTrace]
  refine ⟨109569987336517583687263147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146093316448690111583017529 109569987336517583687263147)
  ·
    refine ⟨164354981004776375530894721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109569987336517583687263147 164354981004776375530894721)
    ·
      refine ⟨123266235753582281648171041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164354981004776375530894721 123266235753582281648171041)
      ·
        refine ⟨92449676815186711236128281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123266235753582281648171041 92449676815186711236128281)
        ·
          refine ⟨69337257611390033427096211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92449676815186711236128281 69337257611390033427096211)
          ·
            refine ⟨104005886417085050140644317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69337257611390033427096211 104005886417085050140644317)
            ·
              refine ⟨39002207406406893802741619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104005886417085050140644317 39002207406406893802741619)
              ·
                refine ⟨58503311109610340704112429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39002207406406893802741619 58503311109610340704112429)
                ·
                  refine ⟨21938741666103877764042161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58503311109610340704112429 21938741666103877764042161)
                  ·
                    refine ⟨16454056249577908323031621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21938741666103877764042161 16454056249577908323031621)
                    ·
                      refine ⟨3085135546795857810568429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16454056249577908323031621 3085135546795857810568429)
                      ·
                        rfl

theorem cell23_6008280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 3, 2, 4].length) (baseStart_6008280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6008280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6008280 prefixEnd_6008280 := by exact prefixLift 6008280
  have htrace : WordTrace (prefixWord ++ tailWord_6008280) baseStart_6008280 baseEnd_6008280 := by
    simpa [prefixWord, tailWord_6008280, baseEnd_6008280] using wordTrace_append hprefix tailTrace_6008280
  have hstable : (prefixWord ++ tailWord_6008280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6008280).length < 2 ^ (prefixWord ++ tailWord_6008280).sum := by decide
  have hdescent : baseEnd_6008280 < baseStart_6008280 := by decide
  rcases family_descends (prefixWord ++ tailWord_6008280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6008290 : List Nat := [3, 3, 3, 14]
def baseStart_6008290 : Nat := 118140960795 + 6008290 * 2 ^ 59
def prefixEnd_6008290 : Nat := 4983230072969 + 3 ^ 40 * 6008290 * 2
def baseEnd_6008290 : Nat := 1410672465296023215109

theorem tailTrace_6008290 : CollatzResearch.WordTrace tailWord_6008290 prefixEnd_6008290 1410672465296023215109 := by
  unfold tailWord_6008290
  simp only [CollatzResearch.WordTrace]
  refine ⟨54785084850749734770597581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146093559601999292721593549 54785084850749734770597581)
  ·
    refine ⟨20544406819031150538974093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54785084850749734770597581 20544406819031150538974093)
    ·
      refine ⟨7704152557136681452115285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20544406819031150538974093 7704152557136681452115285)
      ·
        refine ⟨1410672465296023215109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 7704152557136681452115285 1410672465296023215109)
        ·
          rfl

theorem cell23_6008290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 14].length) (baseStart_6008290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6008290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6008290 prefixEnd_6008290 := by exact prefixLift 6008290
  have htrace : WordTrace (prefixWord ++ tailWord_6008290) baseStart_6008290 baseEnd_6008290 := by
    simpa [prefixWord, tailWord_6008290, baseEnd_6008290] using wordTrace_append hprefix tailTrace_6008290
  have hstable : (prefixWord ++ tailWord_6008290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6008290).length < 2 ^ (prefixWord ++ tailWord_6008290).sum := by decide
  have hdescent : baseEnd_6008290 < baseStart_6008290 := by decide
  rcases family_descends (prefixWord ++ tailWord_6008290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6008317 : List Nat := [1, 4, 1, 1, 1, 4, 1, 3, 1, 3, 3]
def baseStart_6008317 : Nat := 118140960795 + 6008317 * 2 ^ 59
def prefixEnd_6008317 : Nat := 4983230072969 + 3 ^ 40 * 6008317 * 2
def baseEnd_6008317 : Nat := 3085154545580074165805759

theorem tailTrace_6008317 : CollatzResearch.WordTrace tailWord_6008317 prefixEnd_6008317 3085154545580074165805759 := by
  unfold tailWord_6008317
  simp only [CollatzResearch.WordTrace]
  refine ⟨219141324173901122693623205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146094216115934081795748803 219141324173901122693623205)
  ·
    refine ⟨41088998282606460505054351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 219141324173901122693623205 41088998282606460505054351)
    ·
      refine ⟨61633497423909690757581527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41088998282606460505054351 61633497423909690757581527)
      ·
        refine ⟨92450246135864536136372291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61633497423909690757581527 92450246135864536136372291)
        ·
          refine ⟨138675369203796804204558437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92450246135864536136372291 138675369203796804204558437)
          ·
            refine ⟨26001631725711900788354707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 138675369203796804204558437 26001631725711900788354707)
            ·
              refine ⟨39002447588567851182532061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26001631725711900788354707 39002447588567851182532061)
              ·
                refine ⟨14625917845712944193449523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39002447588567851182532061 14625917845712944193449523)
                ·
                  refine ⟨21938876768569416290174285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14625917845712944193449523 21938876768569416290174285)
                  ·
                    refine ⟨8227078788213531108815357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21938876768569416290174285 8227078788213531108815357)
                    ·
                      refine ⟨3085154545580074165805759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8227078788213531108815357 3085154545580074165805759)
                      ·
                        rfl

theorem cell23_6008317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 3, 1, 3, 3].length) (baseStart_6008317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6008317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6008317 prefixEnd_6008317 := by exact prefixLift 6008317
  have htrace : WordTrace (prefixWord ++ tailWord_6008317) baseStart_6008317 baseEnd_6008317 := by
    simpa [prefixWord, tailWord_6008317, baseEnd_6008317] using wordTrace_append hprefix tailTrace_6008317
  have hstable : (prefixWord ++ tailWord_6008317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6008317).length < 2 ^ (prefixWord ++ tailWord_6008317).sum := by decide
  have hdescent : baseEnd_6008317 < baseStart_6008317 := by decide
  rcases family_descends (prefixWord ++ tailWord_6008317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6008324 : List Nat := [2, 3, 2, 3, 2, 1, 3, 7]
def baseStart_6008324 : Nat := 118140960795 + 6008324 * 2 ^ 59
def prefixEnd_6008324 : Nat := 4983230072969 + 3 ^ 40 * 6008324 * 2
def baseEnd_6008324 : Nat := 114265116294246505126601

theorem tailTrace_6008324 : CollatzResearch.WordTrace tailWord_6008324 prefixEnd_6008324 114265116294246505126601 := by
  unfold tailWord_6008324
  simp only [CollatzResearch.WordTrace]
  refine ⟨109570789742437881444564013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146094386323250508592752017 109570789742437881444564013)
  ·
    refine ⟨41089046153414205541711505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109570789742437881444564013 41089046153414205541711505)
    ·
      refine ⟨30816784615060654156283629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41089046153414205541711505 30816784615060654156283629)
      ·
        refine ⟨11556294230647745308606361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30816784615060654156283629 11556294230647745308606361)
        ·
          refine ⟨8667220672985808981454771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11556294230647745308606361 8667220672985808981454771)
          ·
            refine ⟨13000831009478713472182157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8667220672985808981454771 13000831009478713472182157)
            ·
              refine ⟨4875311628554517552068309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13000831009478713472182157 4875311628554517552068309)
              ·
                refine ⟨114265116294246505126601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4875311628554517552068309 114265116294246505126601)
                ·
                  rfl

theorem cell23_6008324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 3, 7].length) (baseStart_6008324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6008324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6008324 prefixEnd_6008324 := by exact prefixLift 6008324
  have htrace : WordTrace (prefixWord ++ tailWord_6008324) baseStart_6008324 baseEnd_6008324 := by
    simpa [prefixWord, tailWord_6008324, baseEnd_6008324] using wordTrace_append hprefix tailTrace_6008324
  have hstable : (prefixWord ++ tailWord_6008324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6008324).length < 2 ^ (prefixWord ++ tailWord_6008324).sum := by decide
  have hdescent : baseEnd_6008324 < baseStart_6008324 := by decide
  rcases family_descends (prefixWord ++ tailWord_6008324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6008477 : List Nat := [1, 4, 2, 1, 1, 1, 1, 2, 2, 4, 4]
def baseStart_6008477 : Nat := 118140960795 + 6008477 * 2 ^ 59
def prefixEnd_6008477 : Nat := 4983230072969 + 3 ^ 40 * 6008477 * 2
def baseEnd_6008477 : Nat := 3085236702484793539805023

theorem tailTrace_6008477 : CollatzResearch.WordTrace tailWord_6008477 prefixEnd_6008477 3085236702484793539805023 := by
  unfold tailWord_6008477
  simp only [CollatzResearch.WordTrace]
  refine ⟨219147159853321470019447685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146098106568880980012965123 219147159853321470019447685)
  ·
    refine ⟨41090092472497775628646441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 219147159853321470019447685 41090092472497775628646441)
    ·
      refine ⟨30817569354373331721484831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41090092472497775628646441 30817569354373331721484831)
      ·
        refine ⟨46226354031559997582227247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30817569354373331721484831 46226354031559997582227247)
        ·
          refine ⟨69339531047339996373340871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46226354031559997582227247 69339531047339996373340871)
          ·
            refine ⟨104009296571009994560011307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69339531047339996373340871 104009296571009994560011307)
            ·
              refine ⟨156013944856514991840016961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104009296571009994560011307 156013944856514991840016961)
              ·
                refine ⟨117010458642386243880012721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 156013944856514991840016961 117010458642386243880012721)
                ·
                  refine ⟨87757843981789682910009541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117010458642386243880012721 87757843981789682910009541)
                  ·
                    refine ⟨16454595746585565545626789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 87757843981789682910009541 16454595746585565545626789)
                    ·
                      refine ⟨3085236702484793539805023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16454595746585565545626789 3085236702484793539805023)
                      ·
                        rfl

theorem cell23_6008477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_6008477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6008477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6008477 prefixEnd_6008477 := by exact prefixLift 6008477
  have htrace : WordTrace (prefixWord ++ tailWord_6008477) baseStart_6008477 baseEnd_6008477 := by
    simpa [prefixWord, tailWord_6008477, baseEnd_6008477] using wordTrace_append hprefix tailTrace_6008477
  have hstable : (prefixWord ++ tailWord_6008477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6008477).length < 2 ^ (prefixWord ++ tailWord_6008477).sum := by decide
  have hdescent : baseEnd_6008477 < baseStart_6008477 := by decide
  rcases family_descends (prefixWord ++ tailWord_6008477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6008481 : List Nat := [1, 2, 3, 3, 2, 2, 1, 1, 2, 4, 2]
def baseStart_6008481 : Nat := 118140960795 + 6008481 * 2 ^ 59
def prefixEnd_6008481 : Nat := 4983230072969 + 3 ^ 40 * 6008481 * 2
def baseEnd_6008481 : Nat := 3085238756407411524155005

theorem tailTrace_6008481 : CollatzResearch.WordTrace tailWord_6008481 prefixEnd_6008481 3085238756407411524155005 := by
  unfold tailWord_6008481
  simp only [CollatzResearch.WordTrace]
  refine ⟨219147305745306978702593297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146098203830204652468395531 219147305745306978702593297)
  ·
    refine ⟨164360479308980234026944973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219147305745306978702593297 164360479308980234026944973)
    ·
      refine ⟨61635179740867587760104365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164360479308980234026944973 61635179740867587760104365)
      ·
        refine ⟨23113192402825345410039137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61635179740867587760104365 23113192402825345410039137)
        ·
          refine ⟨17334894302119009057529353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23113192402825345410039137 17334894302119009057529353)
          ·
            refine ⟨13001170726589256793147015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17334894302119009057529353 13001170726589256793147015)
            ·
              refine ⟨19501756089883885189720523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13001170726589256793147015 19501756089883885189720523)
              ·
                refine ⟨29252634134825827784580785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19501756089883885189720523 29252634134825827784580785)
                ·
                  refine ⟨21939475601119370838435589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29252634134825827784580785 21939475601119370838435589)
                  ·
                    refine ⟨4113651675209882032206673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21939475601119370838435589 4113651675209882032206673)
                    ·
                      refine ⟨3085238756407411524155005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4113651675209882032206673 3085238756407411524155005)
                      ·
                        rfl

theorem cell23_6008481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 2, 4, 2].length) (baseStart_6008481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6008481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6008481 prefixEnd_6008481 := by exact prefixLift 6008481
  have htrace : WordTrace (prefixWord ++ tailWord_6008481) baseStart_6008481 baseEnd_6008481 := by
    simpa [prefixWord, tailWord_6008481, baseEnd_6008481] using wordTrace_append hprefix tailTrace_6008481
  have hstable : (prefixWord ++ tailWord_6008481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6008481).length < 2 ^ (prefixWord ++ tailWord_6008481).sum := by decide
  have hdescent : baseEnd_6008481 < baseStart_6008481 := by decide
  rcases family_descends (prefixWord ++ tailWord_6008481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6008501 : List Nat := [1, 3, 3, 3, 2, 1, 1, 1, 1, 4, 3]
def baseStart_6008501 : Nat := 118140960795 + 6008501 * 2 ^ 59
def prefixEnd_6008501 : Nat := 4983230072969 + 3 ^ 40 * 6008501 * 2
def baseEnd_6008501 : Nat := 3085249026020501445904913

theorem tailTrace_6008501 : CollatzResearch.WordTrace tailWord_6008501 prefixEnd_6008501 3085249026020501445904913 := by
  unfold tailWord_6008501
  simp only [CollatzResearch.WordTrace]
  refine ⟨219148035205234522118321357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146098690136823014745547571 219148035205234522118321357)
  ·
    refine ⟨82180513201962945794370509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219148035205234522118321357 82180513201962945794370509)
    ·
      refine ⟨30817692450736104672888941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82180513201962945794370509 30817692450736104672888941)
      ·
        refine ⟨11556634669026039252333353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30817692450736104672888941 11556634669026039252333353)
        ·
          refine ⟨8667476001769529439250015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11556634669026039252333353 8667476001769529439250015)
          ·
            refine ⟨13001214002654294158875023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8667476001769529439250015 13001214002654294158875023)
            ·
              refine ⟨19501821003981441238312535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13001214002654294158875023 19501821003981441238312535)
              ·
                refine ⟨29252731505972161857468803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19501821003981441238312535 29252731505972161857468803)
                ·
                  refine ⟨43879097258958242786203205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29252731505972161857468803 43879097258958242786203205)
                  ·
                    refine ⟨8227330736054670522413101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43879097258958242786203205 8227330736054670522413101)
                    ·
                      refine ⟨3085249026020501445904913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8227330736054670522413101 3085249026020501445904913)
                      ·
                        rfl

theorem cell23_6008501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_6008501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6008501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6008501 prefixEnd_6008501 := by exact prefixLift 6008501
  have htrace : WordTrace (prefixWord ++ tailWord_6008501) baseStart_6008501 baseEnd_6008501 := by
    simpa [prefixWord, tailWord_6008501, baseEnd_6008501] using wordTrace_append hprefix tailTrace_6008501
  have hstable : (prefixWord ++ tailWord_6008501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6008501).length < 2 ^ (prefixWord ++ tailWord_6008501).sum := by decide
  have hdescent : baseEnd_6008501 < baseStart_6008501 := by decide
  rcases family_descends (prefixWord ++ tailWord_6008501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6008508 : List Nat := [2, 2, 2, 3, 1, 3, 2, 3, 1, 4]
def baseStart_6008508 : Nat := 118140960795 + 6008508 * 2 ^ 59
def prefixEnd_6008508 : Nat := 4983230072969 + 3 ^ 40 * 6008508 * 2
def baseEnd_6008508 : Nat := 1028417540128360972839127

theorem tailTrace_6008508 : CollatzResearch.WordTrace tailWord_6008508 prefixEnd_6008508 1028417540128360972839127 := by
  unfold tailWord_6008508
  simp only [CollatzResearch.WordTrace]
  refine ⟨109574145258104581156913089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146098860344139441542550785 109574145258104581156913089)
  ·
    refine ⟨82180608943578435867684817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109574145258104581156913089 82180608943578435867684817)
    ·
      refine ⟨61635456707683826900763613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82180608943578435867684817 61635456707683826900763613)
      ·
        refine ⟨23113296265381435087786355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61635456707683826900763613 23113296265381435087786355)
        ·
          refine ⟨34669944398072152631679533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23113296265381435087786355 34669944398072152631679533)
          ·
            refine ⟨13001229149277057236879825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34669944398072152631679533 13001229149277057236879825)
            ·
              refine ⟨9750921861957792927659869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13001229149277057236879825 9750921861957792927659869)
              ·
                refine ⟨3656595698234172347872451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9750921861957792927659869 3656595698234172347872451)
                ·
                  refine ⟨5484893547351258521808677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3656595698234172347872451 5484893547351258521808677)
                  ·
                    refine ⟨1028417540128360972839127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5484893547351258521808677 1028417540128360972839127)
                    ·
                      rfl

theorem cell23_6008508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 3, 1, 4].length) (baseStart_6008508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6008508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6008508 prefixEnd_6008508 := by exact prefixLift 6008508
  have htrace : WordTrace (prefixWord ++ tailWord_6008508) baseStart_6008508 baseEnd_6008508 := by
    simpa [prefixWord, tailWord_6008508, baseEnd_6008508] using wordTrace_append hprefix tailTrace_6008508
  have hstable : (prefixWord ++ tailWord_6008508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6008508).length < 2 ^ (prefixWord ++ tailWord_6008508).sum := by decide
  have hdescent : baseEnd_6008508 < baseStart_6008508 := by decide
  rcases family_descends (prefixWord ++ tailWord_6008508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6008525 : List Nat := [1, 6, 2, 1, 1, 1, 2, 4, 1, 4]
def baseStart_6008525 : Nat := 118140960795 + 6008525 * 2 ^ 59
def prefixEnd_6008525 : Nat := 4983230072969 + 3 ^ 40 * 6008525 * 2
def baseEnd_6008525 : Nat := 1028420449852069784001601

theorem tailTrace_6008525 : CollatzResearch.WordTrace tailWord_6008525 prefixEnd_6008525 1028420449852069784001601 := by
  unfold tailWord_6008525
  simp only [CollatzResearch.WordTrace]
  refine ⟨219148910557147574217195029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146099273704765049478130019 219148910557147574217195029)
  ·
    refine ⟨10272605182366292541431017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 219148910557147574217195029 10272605182366292541431017)
    ·
      refine ⟨7704453886774719406073263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10272605182366292541431017 7704453886774719406073263)
      ·
        refine ⟨11556680830162079109109895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7704453886774719406073263 11556680830162079109109895)
        ·
          refine ⟨17335021245243118663664843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11556680830162079109109895 17335021245243118663664843)
          ·
            refine ⟨26002531867864677995497265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17335021245243118663664843 26002531867864677995497265)
            ·
              refine ⟨19501898900898508496622949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26002531867864677995497265 19501898900898508496622949)
              ·
                refine ⟨3656606043918470343116803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19501898900898508496622949 3656606043918470343116803)
                ·
                  refine ⟨5484909065877705514675205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3656606043918470343116803 5484909065877705514675205)
                  ·
                    refine ⟨1028420449852069784001601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5484909065877705514675205 1028420449852069784001601)
                    ·
                      rfl

theorem cell23_6008525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_6008525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6008525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6008525 prefixEnd_6008525 := by exact prefixLift 6008525
  have htrace : WordTrace (prefixWord ++ tailWord_6008525) baseStart_6008525 baseEnd_6008525 := by
    simpa [prefixWord, tailWord_6008525, baseEnd_6008525] using wordTrace_append hprefix tailTrace_6008525
  have hstable : (prefixWord ++ tailWord_6008525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6008525).length < 2 ^ (prefixWord ++ tailWord_6008525).sum := by decide
  have hdescent : baseEnd_6008525 < baseStart_6008525 := by decide
  rcases family_descends (prefixWord ++ tailWord_6008525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6008554 : List Nat := [3, 1, 3, 1, 1, 1, 2, 3, 3, 1, 4]
def baseStart_6008554 : Nat := 118140960795 + 6008554 * 2 ^ 59
def prefixEnd_6008554 : Nat := 4983230072969 + 3 ^ 40 * 6008554 * 2
def baseEnd_6008554 : Nat := 3085276240495189738542169

theorem tailTrace_6008554 : CollatzResearch.WordTrace tailWord_6008554 prefixEnd_6008554 3085276240495189738542169 := by
  unfold tailWord_6008554
  simp only [CollatzResearch.WordTrace]
  refine ⟨54787492068510628042500179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146099978849361674780000477 54787492068510628042500179)
  ·
    refine ⟨82181238102765942063750269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54787492068510628042500179 82181238102765942063750269)
    ·
      refine ⟨30817964288537228273906351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82181238102765942063750269 30817964288537228273906351)
      ·
        refine ⟨46226946432805842410859527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30817964288537228273906351 46226946432805842410859527)
        ·
          refine ⟨69340419649208763616289291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46226946432805842410859527 69340419649208763616289291)
          ·
            refine ⟨104010629473813145424433937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69340419649208763616289291 104010629473813145424433937)
            ·
              refine ⟨78007972105359859068325453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104010629473813145424433937 78007972105359859068325453)
              ·
                refine ⟨29252989539509947150622045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78007972105359859068325453 29252989539509947150622045)
                ·
                  refine ⟨10969871077316230181483267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29252989539509947150622045 10969871077316230181483267)
                  ·
                    refine ⟨16454806615974345272224901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10969871077316230181483267 16454806615974345272224901)
                    ·
                      refine ⟨3085276240495189738542169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16454806615974345272224901 3085276240495189738542169)
                      ·
                        rfl

theorem cell23_6008554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_6008554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6008554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6008554 prefixEnd_6008554 := by exact prefixLift 6008554
  have htrace : WordTrace (prefixWord ++ tailWord_6008554) baseStart_6008554 baseEnd_6008554 := by
    simpa [prefixWord, tailWord_6008554, baseEnd_6008554] using wordTrace_append hprefix tailTrace_6008554
  have hstable : (prefixWord ++ tailWord_6008554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6008554).length < 2 ^ (prefixWord ++ tailWord_6008554).sum := by decide
  have hdescent : baseEnd_6008554 < baseStart_6008554 := by decide
  rcases family_descends (prefixWord ++ tailWord_6008554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6008577 : List Nat := [1, 2, 4, 1, 1, 1, 13]
def baseStart_6008577 : Nat := 118140960795 + 6008577 * 2 ^ 59
def prefixEnd_6008577 : Nat := 4983230072969 + 3 ^ 40 * 6008577 * 2
def baseEnd_6008577 : Nat := 38089975932719051216723

theorem tailTrace_6008577 : CollatzResearch.WordTrace tailWord_6008577 prefixEnd_6008577 38089975932719051216723 := by
  unfold tailWord_6008577
  simp only [CollatzResearch.WordTrace]
  refine ⟨219150807152959187098087985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146100538101972791398725323 219150807152959187098087985)
  ·
    refine ⟨164363105364719390323565989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219150807152959187098087985 164363105364719390323565989)
    ·
      refine ⟨30818082255884885685668623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 164363105364719390323565989 30818082255884885685668623)
      ·
        refine ⟨46227123383827328528502935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30818082255884885685668623 46227123383827328528502935)
        ·
          refine ⟨69340685075740992792754403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46227123383827328528502935 69340685075740992792754403)
          ·
            refine ⟨104011027613611489189131605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69340685075740992792754403 104011027613611489189131605)
            ·
              refine ⟨38089975932719051216723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 104011027613611489189131605 38089975932719051216723)
              ·
                rfl

theorem cell23_6008577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 13].length) (baseStart_6008577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6008577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6008577 prefixEnd_6008577 := by exact prefixLift 6008577
  have htrace : WordTrace (prefixWord ++ tailWord_6008577) baseStart_6008577 baseEnd_6008577 := by
    simpa [prefixWord, tailWord_6008577, baseEnd_6008577] using wordTrace_append hprefix tailTrace_6008577
  have hstable : (prefixWord ++ tailWord_6008577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6008577).length < 2 ^ (prefixWord ++ tailWord_6008577).sum := by decide
  have hdescent : baseEnd_6008577 < baseStart_6008577 := by decide
  rcases family_descends (prefixWord ++ tailWord_6008577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6008588 : List Nat := [2, 2, 1, 2, 2, 1, 5, 1, 3, 2, 2]
def baseStart_6008588 : Nat := 118140960795 + 6008588 * 2 ^ 59
def prefixEnd_6008588 : Nat := 4983230072969 + 3 ^ 40 * 6008588 * 2
def baseEnd_6008588 : Nat := 3085293698837442605517013

theorem tailTrace_6008588 : CollatzResearch.WordTrace tailWord_6008588 prefixEnd_6008588 3085293698837442605517013 := by
  unfold tailWord_6008588
  simp only [CollatzResearch.WordTrace]
  refine ⟨109575604177959667988369209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146100805570612890651158945 109575604177959667988369209)
  ·
    refine ⟨82181703133469750991276907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109575604177959667988369209 82181703133469750991276907)
    ·
      refine ⟨123272554700204626486915361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82181703133469750991276907 123272554700204626486915361)
      ·
        refine ⟨92454416025153469865186521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123272554700204626486915361 92454416025153469865186521)
        ·
          refine ⟨69340812018865102398889891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92454416025153469865186521 69340812018865102398889891)
          ·
            refine ⟨104011218028297653598334837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69340812018865102398889891 104011218028297653598334837)
            ·
              refine ⟨9751051690152905024843891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 104011218028297653598334837 9751051690152905024843891)
              ·
                refine ⟨14626577535229357537265837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9751051690152905024843891 14626577535229357537265837)
                ·
                  refine ⟨5484966575711009076474689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14626577535229357537265837 5484966575711009076474689)
                  ·
                    refine ⟨4113724931783256807356017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5484966575711009076474689 4113724931783256807356017)
                    ·
                      refine ⟨3085293698837442605517013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4113724931783256807356017 3085293698837442605517013)
                      ·
                        rfl

theorem cell23_6008588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 1, 3, 2, 2].length) (baseStart_6008588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6008588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6008588 prefixEnd_6008588 := by exact prefixLift 6008588
  have htrace : WordTrace (prefixWord ++ tailWord_6008588) baseStart_6008588 baseEnd_6008588 := by
    simpa [prefixWord, tailWord_6008588, baseEnd_6008588] using wordTrace_append hprefix tailTrace_6008588
  have hstable : (prefixWord ++ tailWord_6008588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6008588).length < 2 ^ (prefixWord ++ tailWord_6008588).sum := by decide
  have hdescent : baseEnd_6008588 < baseStart_6008588 := by decide
  rcases family_descends (prefixWord ++ tailWord_6008588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6008589 : List Nat := [1, 7, 2, 1, 1, 2, 2, 1, 6]
def baseStart_6008589 : Nat := 118140960795 + 6008589 * 2 ^ 59
def prefixEnd_6008589 : Nat := 4983230072969 + 3 ^ 40 * 6008589 * 2
def baseEnd_6008589 : Nat := 342810468035344122400501

theorem tailTrace_6008589 : CollatzResearch.WordTrace tailWord_6008589 prefixEnd_6008589 342810468035344122400501 := by
  unfold tailWord_6008589
  simp only [CollatzResearch.WordTrace]
  refine ⟨219151244828915713147524821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146100829885943808765016547 219151244828915713147524821)
  ·
    refine ⟨5136357300677712026895113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 219151244828915713147524821 5136357300677712026895113)
    ·
      refine ⟨3852267975508284020171335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5136357300677712026895113 3852267975508284020171335)
      ·
        refine ⟨5778401963262426030257003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3852267975508284020171335 5778401963262426030257003)
        ·
          refine ⟨8667602944893639045385505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5778401963262426030257003 8667602944893639045385505)
          ·
            refine ⟨6500702208670229284039129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8667602944893639045385505 6500702208670229284039129)
            ·
              refine ⟨4875526656502671963029347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6500702208670229284039129 4875526656502671963029347)
              ·
                refine ⟨7313289984754007944544021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4875526656502671963029347 7313289984754007944544021)
                ·
                  refine ⟨342810468035344122400501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7313289984754007944544021 342810468035344122400501)
                  ·
                    rfl

theorem cell23_6008589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_6008589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6008589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6008589 prefixEnd_6008589 := by exact prefixLift 6008589
  have htrace : WordTrace (prefixWord ++ tailWord_6008589) baseStart_6008589 baseEnd_6008589 := by
    simpa [prefixWord, tailWord_6008589, baseEnd_6008589] using wordTrace_append hprefix tailTrace_6008589
  have hstable : (prefixWord ++ tailWord_6008589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6008589).length < 2 ^ (prefixWord ++ tailWord_6008589).sum := by decide
  have hdescent : baseEnd_6008589 < baseStart_6008589 := by decide
  rcases family_descends (prefixWord ++ tailWord_6008589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6008639 : List Nat := [1, 1, 2, 2, 6, 2, 2, 2, 1, 2, 2]
def baseStart_6008639 : Nat := 118140960795 + 6008639 * 2 ^ 59
def prefixEnd_6008639 : Nat := 4983230072969 + 3 ^ 40 * 6008639 * 2
def baseEnd_6008639 : Nat := 3085319886350821905979279

theorem tailTrace_6008639 : CollatzResearch.WordTrace tailWord_6008639 prefixEnd_6008639 3085319886350821905979279 := by
  unfold tailWord_6008639
  simp only [CollatzResearch.WordTrace]
  refine ⟨219153068478734571686844971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146102045652489714457896647 219153068478734571686844971)
  ·
    refine ⟨328729602718101857530267457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219153068478734571686844971 328729602718101857530267457)
    ·
      refine ⟨246547202038576393147700593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 328729602718101857530267457 246547202038576393147700593)
      ·
        refine ⟨184910401528932294860775445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246547202038576393147700593 184910401528932294860775445)
        ·
          refine ⟨8667675071668701321598849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 184910401528932294860775445 8667675071668701321598849)
          ·
            refine ⟨6500756303751525991199137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8667675071668701321598849 6500756303751525991199137)
            ·
              refine ⟨4875567227813644493399353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6500756303751525991199137 4875567227813644493399353)
              ·
                refine ⟨3656675420860233370049515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4875567227813644493399353 3656675420860233370049515)
                ·
                  refine ⟨5485013131290350055074273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3656675420860233370049515 5485013131290350055074273)
                  ·
                    refine ⟨4113759848467762541305705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5485013131290350055074273 4113759848467762541305705)
                    ·
                      refine ⟨3085319886350821905979279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4113759848467762541305705 3085319886350821905979279)
                      ·
                        rfl

theorem cell23_6008639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 2, 2, 1, 2, 2].length) (baseStart_6008639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6008639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6008639 prefixEnd_6008639 := by exact prefixLift 6008639
  have htrace : WordTrace (prefixWord ++ tailWord_6008639) baseStart_6008639 baseEnd_6008639 := by
    simpa [prefixWord, tailWord_6008639, baseEnd_6008639] using wordTrace_append hprefix tailTrace_6008639
  have hstable : (prefixWord ++ tailWord_6008639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6008639).length < 2 ^ (prefixWord ++ tailWord_6008639).sum := by decide
  have hdescent : baseEnd_6008639 < baseStart_6008639 := by decide
  rcases family_descends (prefixWord ++ tailWord_6008639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6008682 : List Nat := [3, 1, 3, 4, 1, 1, 1, 3, 1, 3, 2]
def baseStart_6008682 : Nat := 118140960795 + 6008682 * 2 ^ 59
def prefixEnd_6008682 : Nat := 4983230072969 + 3 ^ 40 * 6008682 * 2
def baseEnd_6008682 : Nat := 3085341966018965237741581

theorem tailTrace_6008682 : CollatzResearch.WordTrace tailWord_6008682 prefixEnd_6008682 3085341966018965237741581 := by
  unfold tailWord_6008682
  simp only [CollatzResearch.WordTrace]
  refine ⟨54788659204394697507665075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146103091211719193353773533 54788659204394697507665075)
  ·
    refine ⟨82182988806592046261497613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54788659204394697507665075 82182988806592046261497613)
    ·
      refine ⟨30818620802472017348061605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82182988806592046261497613 30818620802472017348061605)
      ·
        refine ⟨5778491400463503252761551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30818620802472017348061605 5778491400463503252761551)
        ·
          refine ⟨8667737100695254879142327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5778491400463503252761551 8667737100695254879142327)
          ·
            refine ⟨13001605651042882318713491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8667737100695254879142327 13001605651042882318713491)
            ·
              refine ⟨19502408476564323478070237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13001605651042882318713491 19502408476564323478070237)
              ·
                refine ⟨7313403178711621304276339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19502408476564323478070237 7313403178711621304276339)
                ·
                  refine ⟨10970104768067431956414509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7313403178711621304276339 10970104768067431956414509)
                  ·
                    refine ⟨4113789288025286983655441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10970104768067431956414509 4113789288025286983655441)
                    ·
                      refine ⟨3085341966018965237741581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4113789288025286983655441 3085341966018965237741581)
                      ·
                        rfl

theorem cell23_6008682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_6008682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6008682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6008682 prefixEnd_6008682 := by exact prefixLift 6008682
  have htrace : WordTrace (prefixWord ++ tailWord_6008682) baseStart_6008682 baseEnd_6008682 := by
    simpa [prefixWord, tailWord_6008682, baseEnd_6008682] using wordTrace_append hprefix tailTrace_6008682
  have hstable : (prefixWord ++ tailWord_6008682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6008682).length < 2 ^ (prefixWord ++ tailWord_6008682).sum := by decide
  have hdescent : baseEnd_6008682 < baseStart_6008682 := by decide
  rcases family_descends (prefixWord ++ tailWord_6008682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6008712 : List Nat := [2, 1, 3, 3, 4, 1, 1, 1, 1, 4, 2]
def baseStart_6008712 : Nat := 118140960795 + 6008712 * 2 ^ 59
def prefixEnd_6008712 : Nat := 4983230072969 + 3 ^ 40 * 6008712 * 2
def baseEnd_6008712 : Nat := 3085357370438600120366443

theorem tailTrace_6008712 : CollatzResearch.WordTrace tailWord_6008712 prefixEnd_6008712 3085357370438600120366443 := by
  unfold tailWord_6008712
  simp only [CollatzResearch.WordTrace]
  refine ⟨109577865503735052577126195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146103820671646736769501593 109577865503735052577126195)
  ·
    refine ⟨164366798255602578865689293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109577865503735052577126195 164366798255602578865689293)
    ·
      refine ⟨61637549345850967074633485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164366798255602578865689293 61637549345850967074633485)
      ·
        refine ⟨23114081004694112652987557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61637549345850967074633485 23114081004694112652987557)
        ·
          refine ⟨4333890188380146122435167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23114081004694112652987557 4333890188380146122435167)
          ·
            refine ⟨6500835282570219183652751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4333890188380146122435167 6500835282570219183652751)
            ·
              refine ⟨9751252923855328775479127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6500835282570219183652751 9751252923855328775479127)
              ·
                refine ⟨14626879385782993163218691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9751252923855328775479127 14626879385782993163218691)
                ·
                  refine ⟨21940319078674489744828037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14626879385782993163218691 21940319078674489744828037)
                  ·
                    refine ⟨4113809827251466827155257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21940319078674489744828037 4113809827251466827155257)
                    ·
                      refine ⟨3085357370438600120366443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4113809827251466827155257 3085357370438600120366443)
                      ·
                        rfl

theorem cell23_6008712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 1, 1, 4, 2].length) (baseStart_6008712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6008712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6008712 prefixEnd_6008712 := by exact prefixLift 6008712
  have htrace : WordTrace (prefixWord ++ tailWord_6008712) baseStart_6008712 baseEnd_6008712 := by
    simpa [prefixWord, tailWord_6008712, baseEnd_6008712] using wordTrace_append hprefix tailTrace_6008712
  have hstable : (prefixWord ++ tailWord_6008712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6008712).length < 2 ^ (prefixWord ++ tailWord_6008712).sum := by decide
  have hdescent : baseEnd_6008712 < baseStart_6008712 := by decide
  rcases family_descends (prefixWord ++ tailWord_6008712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6008721 : List Nat := [1, 2, 2, 1, 1, 1, 4, 2, 2, 5, 2]
def baseStart_6008721 : Nat := 118140960795 + 6008721 * 2 ^ 59
def prefixEnd_6008721 : Nat := 4983230072969 + 3 ^ 40 * 6008721 * 2
def baseEnd_6008721 : Nat := 3085361991764490585153901

theorem tailTrace_6008721 : CollatzResearch.WordTrace tailWord_6008721 prefixEnd_6008721 3085361991764490585153901 := by
  unfold tailWord_6008721
  simp only [CollatzResearch.WordTrace]
  refine ⟨219156059264437499691330017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146104039509624999794220011 219156059264437499691330017)
  ·
    refine ⟨164367044448328124768497513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219156059264437499691330017 164367044448328124768497513)
    ·
      refine ⟨123275283336246093576373135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164367044448328124768497513 123275283336246093576373135)
      ·
        refine ⟨184912925004369140364559703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123275283336246093576373135 184912925004369140364559703)
        ·
          refine ⟨277369387506553710546839555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184912925004369140364559703 277369387506553710546839555)
          ·
            refine ⟨416054081259830565820259333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277369387506553710546839555 416054081259830565820259333)
            ·
              refine ⟨78010140236218231091298625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 416054081259830565820259333 78010140236218231091298625)
              ·
                refine ⟨58507605177163673318473969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78010140236218231091298625 58507605177163673318473969)
                ·
                  refine ⟨43880703882872754988855477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58507605177163673318473969 43880703882872754988855477)
                  ·
                    refine ⟨4113815989019320780205201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43880703882872754988855477 4113815989019320780205201)
                    ·
                      refine ⟨3085361991764490585153901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4113815989019320780205201 3085361991764490585153901)
                      ·
                        rfl

theorem cell23_6008721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 5, 2].length) (baseStart_6008721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6008721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6008721 prefixEnd_6008721 := by exact prefixLift 6008721
  have htrace : WordTrace (prefixWord ++ tailWord_6008721) baseStart_6008721 baseEnd_6008721 := by
    simpa [prefixWord, tailWord_6008721, baseEnd_6008721] using wordTrace_append hprefix tailTrace_6008721
  have hstable : (prefixWord ++ tailWord_6008721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6008721).length < 2 ^ (prefixWord ++ tailWord_6008721).sum := by decide
  have hdescent : baseEnd_6008721 < baseStart_6008721 := by decide
  rcases family_descends (prefixWord ++ tailWord_6008721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6008735 : List Nat := [1, 1, 2, 5, 3, 2, 1, 3, 5]
def baseStart_6008735 : Nat := 118140960795 + 6008735 * 2 ^ 59
def prefixEnd_6008735 : Nat := 4983230072969 + 3 ^ 40 * 6008735 * 2
def baseEnd_6008735 : Nat := 342818797832628170042093

theorem tailTrace_6008735 : CollatzResearch.WordTrace tailWord_6008735 prefixEnd_6008735 342818797832628170042093 := by
  unfold tailWord_6008735
  simp only [CollatzResearch.WordTrace]
  refine ⟨219156569886386780082339659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146104379924257853388226439 219156569886386780082339659)
  ·
    refine ⟨328734854829580170123509489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219156569886386780082339659 328734854829580170123509489)
    ·
      refine ⟨246551141122185127592632117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 328734854829580170123509489 246551141122185127592632117)
      ·
        refine ⟨23114169480204855711809261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 246551141122185127592632117 23114169480204855711809261)
        ·
          refine ⟨8667813555076820891928473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23114169480204855711809261 8667813555076820891928473)
          ·
            refine ⟨6500860166307615668946355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8667813555076820891928473 6500860166307615668946355)
            ·
              refine ⟨9751290249461423503419533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6500860166307615668946355 9751290249461423503419533)
              ·
                refine ⟨3656733843548033813782325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9751290249461423503419533 3656733843548033813782325)
                ·
                  refine ⟨342818797832628170042093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3656733843548033813782325 342818797832628170042093)
                  ·
                    rfl

theorem cell23_6008735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 3, 5].length) (baseStart_6008735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6008735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6008735 prefixEnd_6008735 := by exact prefixLift 6008735
  have htrace : WordTrace (prefixWord ++ tailWord_6008735) baseStart_6008735 baseEnd_6008735 := by
    simpa [prefixWord, tailWord_6008735, baseEnd_6008735] using wordTrace_append hprefix tailTrace_6008735
  have hstable : (prefixWord ++ tailWord_6008735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6008735).length < 2 ^ (prefixWord ++ tailWord_6008735).sum := by decide
  have hdescent : baseEnd_6008735 < baseStart_6008735 := by decide
  rcases family_descends (prefixWord ++ tailWord_6008735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6008751 : List Nat := [1, 1, 2, 1, 2, 2, 5, 2, 2, 1, 4]
def baseStart_6008751 : Nat := 118140960795 + 6008751 * 2 ^ 59
def prefixEnd_6008751 : Nat := 4983230072969 + 3 ^ 40 * 6008751 * 2
def baseEnd_6008751 : Nat := 3085377396184125467778763

theorem tailTrace_6008751 : CollatzResearch.WordTrace tailWord_6008751 prefixEnd_6008751 3085377396184125467778763 := by
  unfold tailWord_6008751
  simp only [CollatzResearch.WordTrace]
  refine ⟨219157153454328814814922107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146104768969552543209948071 219157153454328814814922107)
  ·
    refine ⟨328735730181493222222383161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219157153454328814814922107 328735730181493222222383161)
    ·
      refine ⟨246551797636119916666787371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 328735730181493222222383161 246551797636119916666787371)
      ·
        refine ⟨369827696454179875000181057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246551797636119916666787371 369827696454179875000181057)
        ·
          refine ⟨277370772340634906250135793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 369827696454179875000181057 277370772340634906250135793)
          ·
            refine ⟨208028079255476179687601845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 277370772340634906250135793 208028079255476179687601845)
            ·
              refine ⟨19502632430200891845712673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 208028079255476179687601845 19502632430200891845712673)
              ·
                refine ⟨14626974322650668884284505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19502632430200891845712673 14626974322650668884284505)
                ·
                  refine ⟨10970230741988001663213379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14626974322650668884284505 10970230741988001663213379)
                  ·
                    refine ⟨16455346112982002494820069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10970230741988001663213379 16455346112982002494820069)
                    ·
                      refine ⟨3085377396184125467778763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16455346112982002494820069 3085377396184125467778763)
                      ·
                        rfl

theorem cell23_6008751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 2, 2, 1, 4].length) (baseStart_6008751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6008751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6008751 prefixEnd_6008751 := by exact prefixLift 6008751
  have htrace : WordTrace (prefixWord ++ tailWord_6008751) baseStart_6008751 baseEnd_6008751 := by
    simpa [prefixWord, tailWord_6008751, baseEnd_6008751] using wordTrace_append hprefix tailTrace_6008751
  have hstable : (prefixWord ++ tailWord_6008751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6008751).length < 2 ^ (prefixWord ++ tailWord_6008751).sum := by decide
  have hdescent : baseEnd_6008751 < baseStart_6008751 := by decide
  rcases family_descends (prefixWord ++ tailWord_6008751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6008828 : List Nat := [2, 2, 2, 1, 2, 2, 2, 2, 1, 5, 2]
def baseStart_6008828 : Nat := 118140960795 + 6008828 * 2 ^ 59
def prefixEnd_6008828 : Nat := 4983230072969 + 3 ^ 40 * 6008828 * 2
def baseEnd_6008828 : Nat := 3085416934194521666515909

theorem tailTrace_6008828 : CollatzResearch.WordTrace tailWord_6008828 prefixEnd_6008828 3085416934194521666515909 := by
  unfold tailWord_6008828
  simp only [CollatzResearch.WordTrace]
  refine ⟨109579980937524928482737569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146106641250033237976983425 109579980937524928482737569)
  ·
    refine ⟨82184985703143696362053177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109579980937524928482737569 82184985703143696362053177)
    ·
      refine ⟨61638739277357772271539883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82184985703143696362053177 61638739277357772271539883)
      ·
        refine ⟨92458108916036658407309825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61638739277357772271539883 92458108916036658407309825)
        ·
          refine ⟨69343581687027493805482369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92458108916036658407309825 69343581687027493805482369)
          ·
            refine ⟨52007686265270620354111777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69343581687027493805482369 52007686265270620354111777)
            ·
              refine ⟨39005764698952965265583833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52007686265270620354111777 39005764698952965265583833)
              ·
                refine ⟨29254323524214723949187875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39005764698952965265583833 29254323524214723949187875)
                ·
                  refine ⟨43881485286322085923781813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29254323524214723949187875 43881485286322085923781813)
                  ·
                    refine ⟨4113889245592695555354545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43881485286322085923781813 4113889245592695555354545)
                    ·
                      refine ⟨3085416934194521666515909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4113889245592695555354545 3085416934194521666515909)
                      ·
                        rfl

theorem cell23_6008828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 1, 5, 2].length) (baseStart_6008828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6008828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6008828 prefixEnd_6008828 := by exact prefixLift 6008828
  have htrace : WordTrace (prefixWord ++ tailWord_6008828) baseStart_6008828 baseEnd_6008828 := by
    simpa [prefixWord, tailWord_6008828, baseEnd_6008828] using wordTrace_append hprefix tailTrace_6008828
  have hstable : (prefixWord ++ tailWord_6008828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6008828).length < 2 ^ (prefixWord ++ tailWord_6008828).sum := by decide
  have hdescent : baseEnd_6008828 < baseStart_6008828 := by decide
  rcases family_descends (prefixWord ++ tailWord_6008828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6008851 : List Nat := [1, 1, 1, 2, 1, 4, 4, 2, 1, 6]
def baseStart_6008851 : Nat := 118140960795 + 6008851 * 2 ^ 59
def prefixEnd_6008851 : Nat := 4983230072969 + 3 ^ 40 * 6008851 * 2
def baseEnd_6008851 : Nat := 1028476248083191692176101

theorem tailTrace_6008851 : CollatzResearch.WordTrace tailWord_6008851 prefixEnd_6008851 1028476248083191692176101 := by
  unfold tailWord_6008851
  simp only [CollatzResearch.WordTrace]
  refine ⟨219160800753966531893562407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146107200502644354595708271 219160800753966531893562407)
  ·
    refine ⟨328741201130949797840343611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219160800753966531893562407 328741201130949797840343611)
    ·
      refine ⟨493111801696424696760515417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328741201130949797840343611 493111801696424696760515417)
      ·
        refine ⟨369833851272318522570386563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 493111801696424696760515417 369833851272318522570386563)
        ·
          refine ⟨554750776908477783855579845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 369833851272318522570386563 554750776908477783855579845)
          ·
            refine ⟨104015770670339584472921221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 554750776908477783855579845 104015770670339584472921221)
            ·
              refine ⟨19502957000688672088672729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104015770670339584472921221 19502957000688672088672729)
              ·
                refine ⟨14627217750516504066504547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19502957000688672088672729 14627217750516504066504547)
                ·
                  refine ⟨21940826625774756099756821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14627217750516504066504547 21940826625774756099756821)
                  ·
                    refine ⟨1028476248083191692176101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21940826625774756099756821 1028476248083191692176101)
                    ·
                      rfl

theorem cell23_6008851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 2, 1, 6].length) (baseStart_6008851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6008851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6008851 prefixEnd_6008851 := by exact prefixLift 6008851
  have htrace : WordTrace (prefixWord ++ tailWord_6008851) baseStart_6008851 baseEnd_6008851 := by
    simpa [prefixWord, tailWord_6008851, baseEnd_6008851] using wordTrace_append hprefix tailTrace_6008851
  have hstable : (prefixWord ++ tailWord_6008851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6008851).length < 2 ^ (prefixWord ++ tailWord_6008851).sum := by decide
  have hdescent : baseEnd_6008851 < baseStart_6008851 := by decide
  rcases family_descends (prefixWord ++ tailWord_6008851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6008855 : List Nat := [1, 1, 3, 5, 2, 1, 1, 3, 1, 5]
def baseStart_6008855 : Nat := 118140960795 + 6008855 * 2 ^ 59
def prefixEnd_6008855 : Nat := 4983230072969 + 3 ^ 40 * 6008855 * 2
def baseEnd_6008855 : Nat := 1028476932724064353626095

theorem tailTrace_6008855 : CollatzResearch.WordTrace tailWord_6008855 prefixEnd_6008855 1028476932724064353626095 := by
  unfold tailWord_6008855
  simp only [CollatzResearch.WordTrace]
  refine ⟨219160946645952040576708019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146107297763968027051138679 219160946645952040576708019)
  ·
    refine ⟨328741419968928060865062029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219160946645952040576708019 328741419968928060865062029)
    ·
      refine ⟨123278032488348022824398261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 328741419968928060865062029 123278032488348022824398261)
      ·
        refine ⟨11557315545782627139787337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 123278032488348022824398261 11557315545782627139787337)
        ·
          refine ⟨8667986659336970354840503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11557315545782627139787337 8667986659336970354840503)
          ·
            refine ⟨13001979989005455532260755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8667986659336970354840503 13001979989005455532260755)
            ·
              refine ⟨19502969983508183298391133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13001979989005455532260755 19502969983508183298391133)
              ·
                refine ⟨7313613743815568736896675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19502969983508183298391133 7313613743815568736896675)
                ·
                  refine ⟨10970420615723353105345013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7313613743815568736896675 10970420615723353105345013)
                  ·
                    refine ⟨1028476932724064353626095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10970420615723353105345013 1028476932724064353626095)
                    ·
                      rfl

theorem cell23_6008855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 3, 1, 5].length) (baseStart_6008855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6008855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6008855 prefixEnd_6008855 := by exact prefixLift 6008855
  have htrace : WordTrace (prefixWord ++ tailWord_6008855) baseStart_6008855 baseEnd_6008855 := by
    simpa [prefixWord, tailWord_6008855, baseEnd_6008855] using wordTrace_append hprefix tailTrace_6008855
  have hstable : (prefixWord ++ tailWord_6008855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6008855).length < 2 ^ (prefixWord ++ tailWord_6008855).sum := by decide
  have hdescent : baseEnd_6008855 < baseStart_6008855 := by decide
  rcases family_descends (prefixWord ++ tailWord_6008855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6008878 : List Nat := [4, 1, 3, 1, 1, 2, 1, 1, 3, 1, 5]
def baseStart_6008878 : Nat := 118140960795 + 6008878 * 2 ^ 59
def prefixEnd_6008878 : Nat := 4983230072969 + 3 ^ 40 * 6008878 * 2
def baseEnd_6008878 : Nat := 3085442608227246470890679

theorem tailTrace_6008878 : CollatzResearch.WordTrace tailWord_6008878 prefixEnd_6008878 3085442608227246470890679 := by
  unfold tailWord_6008878
  simp only [CollatzResearch.WordTrace]
  refine ⟨27395223190608589438099411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146107857016579143669863525 27395223190608589438099411)
  ·
    refine ⟨41092834785912884157149117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27395223190608589438099411 41092834785912884157149117)
    ·
      refine ⟨15409813044717331558930919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41092834785912884157149117 15409813044717331558930919)
      ·
        refine ⟨23114719567075997338396379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15409813044717331558930919 23114719567075997338396379)
        ·
          refine ⟨34672079350613996007594569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23114719567075997338396379 34672079350613996007594569)
          ·
            refine ⟨26004059512960497005695927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34672079350613996007594569 26004059512960497005695927)
            ·
              refine ⟨39006089269440745508543891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26004059512960497005695927 39006089269440745508543891)
              ·
                refine ⟨58509133904161118262815837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39006089269440745508543891 58509133904161118262815837)
                ·
                  refine ⟨21940925214060419348555939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58509133904161118262815837 21940925214060419348555939)
                  ·
                    refine ⟨32911387821090629022833909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21940925214060419348555939 32911387821090629022833909)
                    ·
                      refine ⟨3085442608227246470890679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32911387821090629022833909 3085442608227246470890679)
                      ·
                        rfl

theorem cell23_6008878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_6008878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6008878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6008878 prefixEnd_6008878 := by exact prefixLift 6008878
  have htrace : WordTrace (prefixWord ++ tailWord_6008878) baseStart_6008878 baseEnd_6008878 := by
    simpa [prefixWord, tailWord_6008878, baseEnd_6008878] using wordTrace_append hprefix tailTrace_6008878
  have hstable : (prefixWord ++ tailWord_6008878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6008878).length < 2 ^ (prefixWord ++ tailWord_6008878).sum := by decide
  have hdescent : baseEnd_6008878 < baseStart_6008878 := by decide
  rcases family_descends (prefixWord ++ tailWord_6008878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6008888 : List Nat := [2, 1, 2, 1, 6, 1, 1, 1, 1, 1, 6]
def baseStart_6008888 : Nat := 118140960795 + 6008888 * 2 ^ 59
def prefixEnd_6008888 : Nat := 4983230072969 + 3 ^ 40 * 6008888 * 2
def baseEnd_6008888 : Nat := 3085447743033791431765633

theorem tailTrace_6008888 : CollatzResearch.WordTrace tailWord_6008888 prefixEnd_6008888 3085447743033791431765633 := by
  unfold tailWord_6008888
  simp only [CollatzResearch.WordTrace]
  refine ⟨109581075127416243606329659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146108100169888324808439545 109581075127416243606329659)
  ·
    refine ⟨164371612691124365409494489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109581075127416243606329659 164371612691124365409494489)
    ·
      refine ⟨123278709518343274057120867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164371612691124365409494489 123278709518343274057120867)
      ·
        refine ⟨184918064277514911085681301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123278709518343274057120867 184918064277514911085681301)
        ·
          refine ⟨8668034263008511457141311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 184918064277514911085681301 8668034263008511457141311)
          ·
            refine ⟨13002051394512767185711967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8668034263008511457141311 13002051394512767185711967)
            ·
              refine ⟨19503077091769150778567951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13002051394512767185711967 19503077091769150778567951)
              ·
                refine ⟨29254615637653726167851927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19503077091769150778567951 29254615637653726167851927)
                ·
                  refine ⟨43881923456480589251777891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29254615637653726167851927 43881923456480589251777891)
                  ·
                    refine ⟨65822885184720883877666837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43881923456480589251777891 65822885184720883877666837)
                    ·
                      refine ⟨3085447743033791431765633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65822885184720883877666837 3085447743033791431765633)
                      ·
                        rfl

theorem cell23_6008888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 1, 1, 6].length) (baseStart_6008888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6008888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6008888 prefixEnd_6008888 := by exact prefixLift 6008888
  have htrace : WordTrace (prefixWord ++ tailWord_6008888) baseStart_6008888 baseEnd_6008888 := by
    simpa [prefixWord, tailWord_6008888, baseEnd_6008888] using wordTrace_append hprefix tailTrace_6008888
  have hstable : (prefixWord ++ tailWord_6008888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6008888).length < 2 ^ (prefixWord ++ tailWord_6008888).sum := by decide
  have hdescent : baseEnd_6008888 < baseStart_6008888 := by decide
  rcases family_descends (prefixWord ++ tailWord_6008888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6008908 : List Nat := [2, 2, 1, 3, 1, 1, 2, 4, 1, 3, 3]
def baseStart_6008908 : Nat := 118140960795 + 6008908 * 2 ^ 59
def prefixEnd_6008908 : Nat := 4983230072969 + 3 ^ 40 * 6008908 * 2
def baseEnd_6008908 : Nat := 3085458012646881353515541

theorem tailTrace_6008908 : CollatzResearch.WordTrace tailWord_6008908 prefixEnd_6008908 3085458012646881353515541 := by
  unfold tailWord_6008908
  simp only [CollatzResearch.WordTrace]
  refine ⟨109581439857380015314193689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146108586476506687085591585 109581439857380015314193689)
  ·
    refine ⟨82186079893035011485645267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109581439857380015314193689 82186079893035011485645267)
    ·
      refine ⟨123279119839552517228467901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82186079893035011485645267 123279119839552517228467901)
      ·
        refine ⟨46229669939832193960675463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123279119839552517228467901 46229669939832193960675463)
        ·
          refine ⟨69344504909748290941013195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46229669939832193960675463 69344504909748290941013195)
          ·
            refine ⟨104016757364622436411519793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69344504909748290941013195 104016757364622436411519793)
            ·
              refine ⟨78012568023466827308639845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104016757364622436411519793 78012568023466827308639845)
              ·
                refine ⟨14627356504400030120369971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78012568023466827308639845 14627356504400030120369971)
                ·
                  refine ⟨21941034756600045180554957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14627356504400030120369971 21941034756600045180554957)
                  ·
                    refine ⟨8227888033725016942708109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21941034756600045180554957 8227888033725016942708109)
                    ·
                      refine ⟨3085458012646881353515541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8227888033725016942708109 3085458012646881353515541)
                      ·
                        rfl

theorem cell23_6008908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 4, 1, 3, 3].length) (baseStart_6008908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6008908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6008908 prefixEnd_6008908 := by exact prefixLift 6008908
  have htrace : WordTrace (prefixWord ++ tailWord_6008908) baseStart_6008908 baseEnd_6008908 := by
    simpa [prefixWord, tailWord_6008908, baseEnd_6008908] using wordTrace_append hprefix tailTrace_6008908
  have hstable : (prefixWord ++ tailWord_6008908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6008908).length < 2 ^ (prefixWord ++ tailWord_6008908).sum := by decide
  have hdescent : baseEnd_6008908 < baseStart_6008908 := by decide
  rcases family_descends (prefixWord ++ tailWord_6008908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6008921 : List Nat := [1, 2, 1, 2, 2, 1, 3, 2, 2, 2, 5]
def baseStart_6008921 : Nat := 118140960795 + 6008921 * 2 ^ 59
def prefixEnd_6008921 : Nat := 4983230072969 + 3 ^ 40 * 6008921 * 2
def baseEnd_6008921 : Nat := 3085464687895389802652981

theorem tailTrace_6008921 : CollatzResearch.WordTrace tailWord_6008921 prefixEnd_6008921 3085464687895389802652981 := by
  unfold tailWord_6008921
  simp only [CollatzResearch.WordTrace]
  refine ⟨219163353863712933848610617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146108902575808622565740411 219163353863712933848610617)
  ·
    refine ⟨164372515397784700386457963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219163353863712933848610617 164372515397784700386457963)
    ·
      refine ⟨246558773096677050579686945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164372515397784700386457963 246558773096677050579686945)
      ·
        refine ⟨184919079822507787934765209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246558773096677050579686945 184919079822507787934765209)
        ·
          refine ⟨138689309866880840951073907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184919079822507787934765209 138689309866880840951073907)
          ·
            refine ⟨208033964800321261426610861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138689309866880840951073907 208033964800321261426610861)
            ·
              refine ⟨78012736800120473034979073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 208033964800321261426610861 78012736800120473034979073)
              ·
                refine ⟨58509552600090354776234305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78012736800120473034979073 58509552600090354776234305)
                ·
                  refine ⟨43882164450067766082175729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58509552600090354776234305 43882164450067766082175729)
                  ·
                    refine ⟨32911623337550824561631797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43882164450067766082175729 32911623337550824561631797)
                    ·
                      refine ⟨3085464687895389802652981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32911623337550824561631797 3085464687895389802652981)
                      ·
                        rfl

theorem cell23_6008921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 2, 5].length) (baseStart_6008921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6008921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6008921 prefixEnd_6008921 := by exact prefixLift 6008921
  have htrace : WordTrace (prefixWord ++ tailWord_6008921) baseStart_6008921 baseEnd_6008921 := by
    simpa [prefixWord, tailWord_6008921, baseEnd_6008921] using wordTrace_append hprefix tailTrace_6008921
  have hstable : (prefixWord ++ tailWord_6008921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6008921).length < 2 ^ (prefixWord ++ tailWord_6008921).sum := by decide
  have hdescent : baseEnd_6008921 < baseStart_6008921 := by decide
  rcases family_descends (prefixWord ++ tailWord_6008921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6008935 : List Nat := [1, 1, 5, 1, 1, 2, 2, 2, 3, 3, 2]
def baseStart_6008935 : Nat := 118140960795 + 6008935 * 2 ^ 59
def prefixEnd_6008935 : Nat := 4983230072969 + 3 ^ 40 * 6008935 * 2
def baseEnd_6008935 : Nat := 3085471876624552747877917

theorem tailTrace_6008935 : CollatzResearch.WordTrace tailWord_6008935 prefixEnd_6008935 3085471876624552747877917 := by
  unfold tailWord_6008935
  simp only [CollatzResearch.WordTrace]
  refine ⟨219163864485662214239620259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146109242990441476159746839 219163864485662214239620259)
  ·
    refine ⟨328745796728493321359430389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219163864485662214239620259 328745796728493321359430389)
    ·
      refine ⟨30819918443296248877446599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 328745796728493321359430389 30819918443296248877446599)
      ·
        refine ⟨46229877664944373316169899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30819918443296248877446599 46229877664944373316169899)
        ·
          refine ⟨69344816497416559974254849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46229877664944373316169899 69344816497416559974254849)
          ·
            refine ⟨52008612373062419980691137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69344816497416559974254849 52008612373062419980691137)
            ·
              refine ⟨39006459279796814985518353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52008612373062419980691137 39006459279796814985518353)
              ·
                refine ⟨29254844459847611239138765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39006459279796814985518353 29254844459847611239138765)
                ·
                  refine ⟨10970566672442854214677037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29254844459847611239138765 10970566672442854214677037)
                  ·
                    refine ⟨4113962502166070330503889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10970566672442854214677037 4113962502166070330503889)
                    ·
                      refine ⟨3085471876624552747877917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4113962502166070330503889 3085471876624552747877917)
                      ·
                        rfl

theorem cell23_6008935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 3, 3, 2].length) (baseStart_6008935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6008935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6008935 prefixEnd_6008935 := by exact prefixLift 6008935
  have htrace : WordTrace (prefixWord ++ tailWord_6008935) baseStart_6008935 baseEnd_6008935 := by
    simpa [prefixWord, tailWord_6008935, baseEnd_6008935] using wordTrace_append hprefix tailTrace_6008935
  have hstable : (prefixWord ++ tailWord_6008935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6008935).length < 2 ^ (prefixWord ++ tailWord_6008935).sum := by decide
  have hdescent : baseEnd_6008935 < baseStart_6008935 := by decide
  rcases family_descends (prefixWord ++ tailWord_6008935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6008942 : List Nat := [4, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3]
def baseStart_6008942 : Nat := 118140960795 + 6008942 * 2 ^ 59
def prefixEnd_6008942 : Nat := 4983230072969 + 3 ^ 40 * 6008942 * 2
def baseEnd_6008942 : Nat := 3085475470989134220490385

theorem tailTrace_6008942 : CollatzResearch.WordTrace tailWord_6008942 prefixEnd_6008942 3085475470989134220490385 := by
  unfold tailWord_6008942
  simp only [CollatzResearch.WordTrace]
  refine ⟨27395514974579606804390635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146109413197757902956750053 27395514974579606804390635)
  ·
    refine ⟨41093272461869410206585953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27395514974579606804390635 41093272461869410206585953)
    ·
      refine ⟨30819954346402057654939465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41093272461869410206585953 30819954346402057654939465)
      ·
        refine ⟨23114965759801543241204599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30819954346402057654939465 23114965759801543241204599)
        ·
          refine ⟨34672448639702314861806899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23114965759801543241204599 34672448639702314861806899)
          ·
            refine ⟨52008672959553472292710349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34672448639702314861806899 52008672959553472292710349)
            ·
              refine ⟨19503252359832552109766381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52008672959553472292710349 19503252359832552109766381)
              ·
                refine ⟨7313719634937207041162393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19503252359832552109766381 7313719634937207041162393)
                ·
                  refine ⟨5485289726202905280871795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7313719634937207041162393 5485289726202905280871795)
                  ·
                    refine ⟨8227934589304357921307693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5485289726202905280871795 8227934589304357921307693)
                    ·
                      refine ⟨3085475470989134220490385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8227934589304357921307693 3085475470989134220490385)
                      ·
                        rfl

theorem cell23_6008942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_6008942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6008942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6008942 prefixEnd_6008942 := by exact prefixLift 6008942
  have htrace : WordTrace (prefixWord ++ tailWord_6008942) baseStart_6008942 baseEnd_6008942 := by
    simpa [prefixWord, tailWord_6008942, baseEnd_6008942] using wordTrace_append hprefix tailTrace_6008942
  have hstable : (prefixWord ++ tailWord_6008942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6008942).length < 2 ^ (prefixWord ++ tailWord_6008942).sum := by decide
  have hdescent : baseEnd_6008942 < baseStart_6008942 := by decide
  rcases family_descends (prefixWord ++ tailWord_6008942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6008965 : List Nat := [1, 3, 1, 1, 5, 1, 1, 1, 3, 4, 2]
def baseStart_6008965 : Nat := 118140960795 + 6008965 * 2 ^ 59
def prefixEnd_6008965 : Nat := 4983230072969 + 3 ^ 40 * 6008965 * 2
def baseEnd_6008965 : Nat := 3085487281044187630502779

theorem tailTrace_6008965 : CollatzResearch.WordTrace tailWord_6008965 prefixEnd_6008965 3085487281044187630502779 := by
  unfold tailWord_6008965
  simp only [CollatzResearch.WordTrace]
  refine ⟨219164958675553529363212349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146109972450369019575474899 219164958675553529363212349)
  ·
    refine ⟨82186859503332573511204631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219164958675553529363212349 82186859503332573511204631)
    ·
      refine ⟨123280289254998860266806947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82186859503332573511204631 123280289254998860266806947)
      ·
        refine ⟨184920433882498290400210421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123280289254998860266806947 184920433882498290400210421)
        ·
          refine ⟨17336290676484214725019727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 184920433882498290400210421 17336290676484214725019727)
          ·
            refine ⟨26004436014726322087529591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17336290676484214725019727 26004436014726322087529591)
            ·
              refine ⟨39006654022089483131294387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26004436014726322087529591 39006654022089483131294387)
              ·
                refine ⟨58509981033134224696941581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39006654022089483131294387 58509981033134224696941581)
                ·
                  refine ⟨21941242887425334261353093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58509981033134224696941581 21941242887425334261353093)
                  ·
                    refine ⟨4113983041392250174003705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21941242887425334261353093 4113983041392250174003705)
                    ·
                      refine ⟨3085487281044187630502779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4113983041392250174003705 3085487281044187630502779)
                      ·
                        rfl

theorem cell23_6008965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 3, 4, 2].length) (baseStart_6008965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6008965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6008965 prefixEnd_6008965 := by exact prefixLift 6008965
  have htrace : WordTrace (prefixWord ++ tailWord_6008965) baseStart_6008965 baseEnd_6008965 := by
    simpa [prefixWord, tailWord_6008965, baseEnd_6008965] using wordTrace_append hprefix tailTrace_6008965
  have hstable : (prefixWord ++ tailWord_6008965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6008965).length < 2 ^ (prefixWord ++ tailWord_6008965).sum := by decide
  have hdescent : baseEnd_6008965 < baseStart_6008965 := by decide
  rcases family_descends (prefixWord ++ tailWord_6008965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6008988 : List Nat := [2, 2, 3, 2, 1, 1, 2, 3, 7]
def baseStart_6008988 : Nat := 118140960795 + 6008988 * 2 ^ 59
def prefixEnd_6008988 : Nat := 4983230072969 + 3 ^ 40 * 6008988 * 2
def baseEnd_6008988 : Nat := 342833232344360115612797

theorem tailTrace_6008988 : CollatzResearch.WordTrace tailWord_6008988 prefixEnd_6008988 342833232344360115612797 := by
  unfold tailWord_6008988
  simp only [CollatzResearch.WordTrace]
  refine ⟨109582898777235102145649809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146110531702980136194199745 109582898777235102145649809)
  ·
    refine ⟨82187174082926326609237357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109582898777235102145649809 82187174082926326609237357)
    ·
      refine ⟨30820190281097372478464009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82187174082926326609237357 30820190281097372478464009)
      ·
        refine ⟨23115142710823029358848007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30820190281097372478464009 23115142710823029358848007)
        ·
          refine ⟨34672714066234544038272011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23115142710823029358848007 34672714066234544038272011)
          ·
            refine ⟨52009071099351816057408017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34672714066234544038272011 52009071099351816057408017)
            ·
              refine ⟨39006803324513862043056013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52009071099351816057408017 39006803324513862043056013)
              ·
                refine ⟨14627551246692698266146005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39006803324513862043056013 14627551246692698266146005)
                ·
                  refine ⟨342833232344360115612797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14627551246692698266146005 342833232344360115612797)
                  ·
                    rfl

theorem cell23_6008988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 3, 7].length) (baseStart_6008988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6008988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6008988 prefixEnd_6008988 := by exact prefixLift 6008988
  have htrace : WordTrace (prefixWord ++ tailWord_6008988) baseStart_6008988 baseEnd_6008988 := by
    simpa [prefixWord, tailWord_6008988, baseEnd_6008988] using wordTrace_append hprefix tailTrace_6008988
  have hstable : (prefixWord ++ tailWord_6008988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6008988).length < 2 ^ (prefixWord ++ tailWord_6008988).sum := by decide
  have hdescent : baseEnd_6008988 < baseStart_6008988 := by decide
  rcases family_descends (prefixWord ++ tailWord_6008988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6008999 : List Nat := [1, 1, 6, 2, 2, 1, 2, 1, 1, 4, 2]
def baseStart_6008999 : Nat := 118140960795 + 6008999 * 2 ^ 59
def prefixEnd_6008999 : Nat := 4983230072969 + 3 ^ 40 * 6008999 * 2
def baseEnd_6008999 : Nat := 3085504739386440497477623

theorem tailTrace_6008999 : CollatzResearch.WordTrace tailWord_6008999 prefixEnd_6008999 3085504739386440497477623 := by
  unfold tailWord_6008999
  simp only [CollatzResearch.WordTrace]
  refine ⟨219166198757430353169950051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146110799171620235446633367 219166198757430353169950051)
  ·
    refine ⟨328749298136145529754925077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219166198757430353169950051 328749298136145529754925077)
    ·
      refine ⟨15410123350131821707262113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 328749298136145529754925077 15410123350131821707262113)
      ·
        refine ⟨11557592512598866280446585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15410123350131821707262113 11557592512598866280446585)
        ·
          refine ⟨8668194384449149710334939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11557592512598866280446585 8668194384449149710334939)
          ·
            refine ⟨13002291576673724565502409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8668194384449149710334939 13002291576673724565502409)
            ·
              refine ⟨9751718682505293424126807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13002291576673724565502409 9751718682505293424126807)
              ·
                refine ⟨14627578023757940136190211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9751718682505293424126807 14627578023757940136190211)
                ·
                  refine ⟨21941367035636910204285317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14627578023757940136190211 21941367035636910204285317)
                  ·
                    refine ⟨4114006319181920663303497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21941367035636910204285317 4114006319181920663303497)
                    ·
                      refine ⟨3085504739386440497477623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4114006319181920663303497 3085504739386440497477623)
                      ·
                        rfl

theorem cell23_6008999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_6008999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6008999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6008999 prefixEnd_6008999 := by exact prefixLift 6008999
  have htrace : WordTrace (prefixWord ++ tailWord_6008999) baseStart_6008999 baseEnd_6008999 := by
    simpa [prefixWord, tailWord_6008999, baseEnd_6008999] using wordTrace_append hprefix tailTrace_6008999
  have hstable : (prefixWord ++ tailWord_6008999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6008999).length < 2 ^ (prefixWord ++ tailWord_6008999).sum := by decide
  have hdescent : baseEnd_6008999 < baseStart_6008999 := by decide
  rcases family_descends (prefixWord ++ tailWord_6008999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6009005 : List Nat := [1, 5, 2, 1, 2, 2, 1, 2, 7]
def baseStart_6009005 : Nat := 118140960795 + 6009005 * 2 ^ 59
def prefixEnd_6009005 : Nat := 4983230072969 + 3 ^ 40 * 6009005 * 2
def baseEnd_6009005 : Nat := 342834202252263052666955

theorem tailTrace_6009005 : CollatzResearch.WordTrace tailWord_6009005 prefixEnd_6009005 342834202252263052666955 := by
  unfold tailWord_6009005
  simp only [CollatzResearch.WordTrace]
  refine ⟨219166417595408616194668469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146110945063605744129778979 219166417595408616194668469)
  ·
    refine ⟨20546851649569557768250169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 219166417595408616194668469 20546851649569557768250169)
    ·
      refine ⟨15410138737177168326187627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20546851649569557768250169 15410138737177168326187627)
      ·
        refine ⟨23115208105765752489281441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15410138737177168326187627 23115208105765752489281441)
        ·
          refine ⟨17336406079324314366961081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23115208105765752489281441 17336406079324314366961081)
          ·
            refine ⟨13002304559493235775220811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17336406079324314366961081 13002304559493235775220811)
            ·
              refine ⟨19503456839239853662831217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13002304559493235775220811 19503456839239853662831217)
              ·
                refine ⟨14627592629429890247123413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19503456839239853662831217 14627592629429890247123413)
                ·
                  refine ⟨342834202252263052666955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14627592629429890247123413 342834202252263052666955)
                  ·
                    rfl

theorem cell23_6009005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 2, 7].length) (baseStart_6009005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6009005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6009005 prefixEnd_6009005 := by exact prefixLift 6009005
  have htrace : WordTrace (prefixWord ++ tailWord_6009005) baseStart_6009005 baseEnd_6009005 := by
    simpa [prefixWord, tailWord_6009005, baseEnd_6009005] using wordTrace_append hprefix tailTrace_6009005
  have hstable : (prefixWord ++ tailWord_6009005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6009005).length < 2 ^ (prefixWord ++ tailWord_6009005).sum := by decide
  have hdescent : baseEnd_6009005 < baseStart_6009005 := by decide
  rcases family_descends (prefixWord ++ tailWord_6009005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6009068 : List Nat := [2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 4]
def baseStart_6009068 : Nat := 118140960795 + 6009068 * 2 ^ 59
def prefixEnd_6009068 : Nat := 4983230072969 + 3 ^ 40 * 6009068 * 2
def baseEnd_6009068 : Nat := 3085540169551600727514805

theorem tailTrace_6009068 : CollatzResearch.WordTrace tailWord_6009068 prefixEnd_6009068 3085540169551600727514805 := by
  unfold tailWord_6009068
  simp only [CollatzResearch.WordTrace]
  refine ⟨109584357697090188977105929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146112476929453585302807905 109584357697090188977105929)
  ·
    refine ⟨82188268272817641732829447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109584357697090188977105929 82188268272817641732829447)
    ·
      refine ⟨123282402409226462599244171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82188268272817641732829447 123282402409226462599244171)
      ·
        refine ⟨184923603613839693898866257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123282402409226462599244171 184923603613839693898866257)
        ·
          refine ⟨138692702710379770424149693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184923603613839693898866257 138692702710379770424149693)
          ·
            refine ⟨52009763516392413909056135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138692702710379770424149693 52009763516392413909056135)
            ·
              refine ⟨78014645274588620863584203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52009763516392413909056135 78014645274588620863584203)
              ·
                refine ⟨117021967911882931295376305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78014645274588620863584203 117021967911882931295376305)
                ·
                  refine ⟨87766475933912198471532229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117021967911882931295376305 87766475933912198471532229)
                  ·
                    refine ⟨16456214237608537213412293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 87766475933912198471532229 16456214237608537213412293)
                    ·
                      refine ⟨3085540169551600727514805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16456214237608537213412293 3085540169551600727514805)
                      ·
                        rfl

theorem cell23_6009068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 4].length) (baseStart_6009068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6009068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6009068 prefixEnd_6009068 := by exact prefixLift 6009068
  have htrace : WordTrace (prefixWord ++ tailWord_6009068) baseStart_6009068 baseEnd_6009068 := by
    simpa [prefixWord, tailWord_6009068, baseEnd_6009068] using wordTrace_append hprefix tailTrace_6009068
  have hstable : (prefixWord ++ tailWord_6009068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6009068).length < 2 ^ (prefixWord ++ tailWord_6009068).sum := by decide
  have hdescent : baseEnd_6009068 < baseStart_6009068 := by decide
  rcases family_descends (prefixWord ++ tailWord_6009068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6009075 : List Nat := [1, 1, 1, 2, 2, 4, 2, 3, 2, 2, 3]
def baseStart_6009075 : Nat := 118140960795 + 6009075 * 2 ^ 59
def prefixEnd_6009075 : Nat := 4983230072969 + 3 ^ 40 * 6009075 * 2
def baseEnd_6009075 : Nat := 3085543763916182200127273

theorem tailTrace_6009075 : CollatzResearch.WordTrace tailWord_6009075 prefixEnd_6009075 3085543763916182200127273 := by
  unfold tailWord_6009075
  simp only [CollatzResearch.WordTrace]
  refine ⟨219168970705155018149716679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146112647136770012099811119 219168970705155018149716679)
  ·
    refine ⟨328753456057732527224575019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219168970705155018149716679 328753456057732527224575019)
    ·
      refine ⟨493130184086598790836862529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328753456057732527224575019 493130184086598790836862529)
      ·
        refine ⟨369847638064949093127646897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 493130184086598790836862529 369847638064949093127646897)
        ·
          refine ⟨277385728548711819845735173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 369847638064949093127646897 277385728548711819845735173)
          ·
            refine ⟨52009824102883466221075345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 277385728548711819845735173 52009824102883466221075345)
            ·
              refine ⟨39007368077162599665806509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52009824102883466221075345 39007368077162599665806509)
              ·
                refine ⟨14627763028935974874677441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39007368077162599665806509 14627763028935974874677441)
                ·
                  refine ⟨10970822271701981156008081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14627763028935974874677441 10970822271701981156008081)
                  ·
                    refine ⟨8228116703776485867006061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10970822271701981156008081 8228116703776485867006061)
                    ·
                      refine ⟨3085543763916182200127273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8228116703776485867006061 3085543763916182200127273)
                      ·
                        rfl

theorem cell23_6009075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 3, 2, 2, 3].length) (baseStart_6009075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6009075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6009075 prefixEnd_6009075 := by exact prefixLift 6009075
  have htrace : WordTrace (prefixWord ++ tailWord_6009075) baseStart_6009075 baseEnd_6009075 := by
    simpa [prefixWord, tailWord_6009075, baseEnd_6009075] using wordTrace_append hprefix tailTrace_6009075
  have hstable : (prefixWord ++ tailWord_6009075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6009075).length < 2 ^ (prefixWord ++ tailWord_6009075).sum := by decide
  have hdescent : baseEnd_6009075 < baseStart_6009075 := by decide
  rcases family_descends (prefixWord ++ tailWord_6009075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6009098 : List Nat := [3, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8]
def baseStart_6009098 : Nat := 118140960795 + 6009098 * 2 ^ 59
def prefixEnd_6009098 : Nat := 4983230072969 + 3 ^ 40 * 6009098 * 2
def baseEnd_6009098 : Nat := 3085555573971235610139667

theorem tailTrace_6009098 : CollatzResearch.WordTrace tailWord_6009098 prefixEnd_6009098 3085555573971235610139667 := by
  unfold tailWord_6009098
  simp only [CollatzResearch.WordTrace]
  refine ⟨54792452396017923269450987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146113206389381128718535965 54792452396017923269450987)
  ·
    refine ⟨82188678594026884904176481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54792452396017923269450987 82188678594026884904176481)
    ·
      refine ⟨61641508945520163678132361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82188678594026884904176481 61641508945520163678132361)
      ·
        refine ⟨46231131709140122758599271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61641508945520163678132361 46231131709140122758599271)
        ·
          refine ⟨69346697563710184137898907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46231131709140122758599271 69346697563710184137898907)
          ·
            refine ⟨104020046345565276206848361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69346697563710184137898907 104020046345565276206848361)
            ·
              refine ⟨78015034759173957155136271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104020046345565276206848361 78015034759173957155136271)
              ·
                refine ⟨117022552138760935732704407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78015034759173957155136271 117022552138760935732704407)
                ·
                  refine ⟨175533828208141403599056611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 117022552138760935732704407 175533828208141403599056611)
                  ·
                    refine ⟨263300742312212105398584917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 175533828208141403599056611 263300742312212105398584917)
                    ·
                      refine ⟨3085555573971235610139667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 263300742312212105398584917 3085555573971235610139667)
                      ·
                        rfl

theorem cell23_6009098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_6009098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6009098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6009098 prefixEnd_6009098 := by exact prefixLift 6009098
  have htrace : WordTrace (prefixWord ++ tailWord_6009098) baseStart_6009098 baseEnd_6009098 := by
    simpa [prefixWord, tailWord_6009098, baseEnd_6009098] using wordTrace_append hprefix tailTrace_6009098
  have hstable : (prefixWord ++ tailWord_6009098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6009098).length < 2 ^ (prefixWord ++ tailWord_6009098).sum := by decide
  have hdescent : baseEnd_6009098 < baseStart_6009098 := by decide
  rcases family_descends (prefixWord ++ tailWord_6009098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6009099 : List Nat := [1, 1, 1, 1, 5, 2, 5, 2, 1, 4]
def baseStart_6009099 : Nat := 118140960795 + 6009099 * 2 ^ 59
def prefixEnd_6009099 : Nat := 4983230072969 + 3 ^ 40 * 6009099 * 2
def baseEnd_6009099 : Nat := 1028518695817296702075721

theorem tailTrace_6009099 : CollatzResearch.WordTrace tailWord_6009099 prefixEnd_6009099 1028518695817296702075721 := by
  unfold tailWord_6009099
  simp only [CollatzResearch.WordTrace]
  refine ⟨219169846057068070248590351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146113230704712046832393567 219169846057068070248590351)
  ·
    refine ⟨328754769085602105372885527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219169846057068070248590351 328754769085602105372885527)
    ·
      refine ⟨493132153628403158059328291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328754769085602105372885527 493132153628403158059328291)
      ·
        refine ⟨739698230442604737088992437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 493132153628403158059328291 739698230442604737088992437)
        ·
          refine ⟨69346709103994194102093041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 739698230442604737088992437 69346709103994194102093041)
          ·
            refine ⟨52010031827995645576569781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69346709103994194102093041 52010031827995645576569781)
            ·
              refine ⟨4875940483874591772803417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52010031827995645576569781 4875940483874591772803417)
              ·
                refine ⟨3656955362905943829602563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4875940483874591772803417 3656955362905943829602563)
                ·
                  refine ⟨5485433044358915744403845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3656955362905943829602563 5485433044358915744403845)
                  ·
                    refine ⟨1028518695817296702075721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5485433044358915744403845 1028518695817296702075721)
                    ·
                      rfl

theorem cell23_6009099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 5, 2, 1, 4].length) (baseStart_6009099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6009099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6009099 prefixEnd_6009099 := by exact prefixLift 6009099
  have htrace : WordTrace (prefixWord ++ tailWord_6009099) baseStart_6009099 baseEnd_6009099 := by
    simpa [prefixWord, tailWord_6009099, baseEnd_6009099] using wordTrace_append hprefix tailTrace_6009099
  have hstable : (prefixWord ++ tailWord_6009099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6009099).length < 2 ^ (prefixWord ++ tailWord_6009099).sum := by decide
  have hdescent : baseEnd_6009099 < baseStart_6009099 := by decide
  rcases family_descends (prefixWord ++ tailWord_6009099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6009115 : List Nat := [1, 1, 1, 1, 1, 1, 6, 1, 3, 5, 2]
def baseStart_6009115 : Nat := 118140960795 + 6009115 * 2 ^ 59
def prefixEnd_6009115 : Nat := 4983230072969 + 3 ^ 40 * 6009115 * 2
def baseEnd_6009115 : Nat := 3085564303142362043627089

theorem tailTrace_6009115 : CollatzResearch.WordTrace tailWord_6009115 prefixEnd_6009115 3085564303142362043627089 := by
  unfold tailWord_6009115
  simp only [CollatzResearch.WordTrace]
  refine ⟨219170429625010104981172799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146113619750006736654115199 219170429625010104981172799)
  ·
    refine ⟨328755644437515157471759199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219170429625010104981172799 328755644437515157471759199)
    ·
      refine ⟨493133466656272736207638799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328755644437515157471759199 493133466656272736207638799)
      ·
        refine ⟨739700199984409104311458199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 493133466656272736207638799 739700199984409104311458199)
        ·
          refine ⟨1109550299976613656467187299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 739700199984409104311458199 1109550299976613656467187299)
          ·
            refine ⟨1664325449964920484700780949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1109550299976613656467187299 1664325449964920484700780949)
            ·
              refine ⟨78015255467105647720349107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1664325449964920484700780949 78015255467105647720349107)
              ·
                refine ⟨117022883200658471580523661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78015255467105647720349107 117022883200658471580523661)
                ·
                  refine ⟨43883581200246926842696373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 117022883200658471580523661 43883581200246926842696373)
                  ·
                    refine ⟨4114085737523149391502785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43883581200246926842696373 4114085737523149391502785)
                    ·
                      refine ⟨3085564303142362043627089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4114085737523149391502785 3085564303142362043627089)
                      ·
                        rfl

theorem cell23_6009115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 5, 2].length) (baseStart_6009115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6009115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6009115 prefixEnd_6009115 := by exact prefixLift 6009115
  have htrace : WordTrace (prefixWord ++ tailWord_6009115) baseStart_6009115 baseEnd_6009115 := by
    simpa [prefixWord, tailWord_6009115, baseEnd_6009115] using wordTrace_append hprefix tailTrace_6009115
  have hstable : (prefixWord ++ tailWord_6009115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6009115).length < 2 ^ (prefixWord ++ tailWord_6009115).sum := by decide
  have hdescent : baseEnd_6009115 < baseStart_6009115 := by decide
  rcases family_descends (prefixWord ++ tailWord_6009115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6009132 : List Nat := [2, 2, 1, 1, 1, 3, 3, 3, 2, 3, 2]
def baseStart_6009132 : Nat := 118140960795 + 6009132 * 2 ^ 59
def prefixEnd_6009132 : Nat := 4983230072969 + 3 ^ 40 * 6009132 * 2
def baseEnd_6009132 : Nat := 3085573032313488477114511

theorem tailTrace_6009132 : CollatzResearch.WordTrace tailWord_6009132 prefixEnd_6009132 3085573032313488477114511 := by
  unfold tailWord_6009132
  simp only [CollatzResearch.WordTrace]
  refine ⟨109585524832974258442270825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146114033110632344589694433 109585524832974258442270825)
  ·
    refine ⟨82189143624730693831703119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109585524832974258442270825 82189143624730693831703119)
    ·
      refine ⟨123283715437096040747554679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82189143624730693831703119 123283715437096040747554679)
      ·
        refine ⟨184925573155644061121332019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123283715437096040747554679 184925573155644061121332019)
        ·
          refine ⟨277388359733466091681998029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184925573155644061121332019 277388359733466091681998029)
          ·
            refine ⟨104020634900049784380749261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 277388359733466091681998029 104020634900049784380749261)
            ·
              refine ⟨39007738087518669142780973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104020634900049784380749261 39007738087518669142780973)
              ·
                refine ⟨14627901782819500928542865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39007738087518669142780973 14627901782819500928542865)
                ·
                  refine ⟨10970926337114625696407149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14627901782819500928542865 10970926337114625696407149)
                  ·
                    refine ⟨4114097376417984636152681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10970926337114625696407149 4114097376417984636152681)
                    ·
                      refine ⟨3085573032313488477114511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4114097376417984636152681 3085573032313488477114511)
                      ·
                        rfl

theorem cell23_6009132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 3, 2].length) (baseStart_6009132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6009132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6009132 prefixEnd_6009132 := by exact prefixLift 6009132
  have htrace : WordTrace (prefixWord ++ tailWord_6009132) baseStart_6009132 baseEnd_6009132 := by
    simpa [prefixWord, tailWord_6009132, baseEnd_6009132] using wordTrace_append hprefix tailTrace_6009132
  have hstable : (prefixWord ++ tailWord_6009132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6009132).length < 2 ^ (prefixWord ++ tailWord_6009132).sum := by decide
  have hdescent : baseEnd_6009132 < baseStart_6009132 := by decide
  rcases family_descends (prefixWord ++ tailWord_6009132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6009139 : List Nat := [1, 1, 1, 2, 5, 1, 2, 5, 1, 1, 3]
def baseStart_6009139 : Nat := 118140960795 + 6009139 * 2 ^ 59
def prefixEnd_6009139 : Nat := 4983230072969 + 3 ^ 40 * 6009139 * 2
def baseEnd_6009139 : Nat := 3085576626678069949726979

theorem tailTrace_6009139 : CollatzResearch.WordTrace tailWord_6009139 prefixEnd_6009139 3085576626678069949726979 := by
  unfold tailWord_6009139
  simp only [CollatzResearch.WordTrace]
  refine ⟨219171304976923157080046471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146114203317948771386697647 219171304976923157080046471)
  ·
    refine ⟨328756957465384735620069707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219171304976923157080046471 328756957465384735620069707)
    ·
      refine ⟨493135436198077103430104561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328756957465384735620069707 493135436198077103430104561)
      ·
        refine ⟨369851577148557827572578421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 493135436198077103430104561 369851577148557827572578421)
        ·
          refine ⟨34673585357677296334929227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 369851577148557827572578421 34673585357677296334929227)
          ·
            refine ⟨52010378036515944502393841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34673585357677296334929227 52010378036515944502393841)
            ·
              refine ⟨39007783527386958376795381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52010378036515944502393841 39007783527386958376795381)
              ·
                refine ⟨3656979705692527347824567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39007783527386958376795381 3656979705692527347824567)
                ·
                  refine ⟨5485469558538791021736851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3656979705692527347824567 5485469558538791021736851)
                  ·
                    refine ⟨8228204337808186532605277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5485469558538791021736851 8228204337808186532605277)
                    ·
                      refine ⟨3085576626678069949726979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8228204337808186532605277 3085576626678069949726979)
                      ·
                        rfl

theorem cell23_6009139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 5, 1, 1, 3].length) (baseStart_6009139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6009139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6009139 prefixEnd_6009139 := by exact prefixLift 6009139
  have htrace : WordTrace (prefixWord ++ tailWord_6009139) baseStart_6009139 baseEnd_6009139 := by
    simpa [prefixWord, tailWord_6009139, baseEnd_6009139] using wordTrace_append hprefix tailTrace_6009139
  have hstable : (prefixWord ++ tailWord_6009139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6009139).length < 2 ^ (prefixWord ++ tailWord_6009139).sum := by decide
  have hdescent : baseEnd_6009139 < baseStart_6009139 := by decide
  rcases family_descends (prefixWord ++ tailWord_6009139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6009155 : List Nat := [1, 1, 1, 3, 1, 3, 2, 3, 4, 4]
def baseStart_6009155 : Nat := 118140960795 + 6009155 * 2 ^ 59
def prefixEnd_6009155 : Nat := 4983230072969 + 3 ^ 40 * 6009155 * 2
def baseEnd_6009155 : Nat := 1028528280789513962375635

theorem tailTrace_6009155 : CollatzResearch.WordTrace tailWord_6009155 prefixEnd_6009155 1028528280789513962375635 := by
  unfold tailWord_6009155
  simp only [CollatzResearch.WordTrace]
  refine ⟨219171888544865191812628919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146114592363243461208419279 219171888544865191812628919)
  ·
    refine ⟨328757832817297787718943379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219171888544865191812628919 328757832817297787718943379)
    ·
      refine ⟨493136749225946681578415069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328757832817297787718943379 493136749225946681578415069)
      ·
        refine ⟨184926280959730005591905651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 493136749225946681578415069 184926280959730005591905651)
        ·
          refine ⟨277389421439595008387858477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184926280959730005591905651 277389421439595008387858477)
          ·
            refine ⟨104021033039848128145446929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 277389421439595008387858477 104021033039848128145446929)
            ·
              refine ⟨78015774779886096109085197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104021033039848128145446929 78015774779886096109085197)
              ·
                refine ⟨29255915542457286040906949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78015774779886096109085197 29255915542457286040906949)
                ·
                  refine ⟨5485484164210741132670053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29255915542457286040906949 5485484164210741132670053)
                  ·
                    refine ⟨1028528280789513962375635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5485484164210741132670053 1028528280789513962375635)
                    ·
                      rfl

theorem cell23_6009155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 4].length) (baseStart_6009155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6009155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6009155 prefixEnd_6009155 := by exact prefixLift 6009155
  have htrace : WordTrace (prefixWord ++ tailWord_6009155) baseStart_6009155 baseEnd_6009155 := by
    simpa [prefixWord, tailWord_6009155, baseEnd_6009155] using wordTrace_append hprefix tailTrace_6009155
  have hstable : (prefixWord ++ tailWord_6009155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6009155).length < 2 ^ (prefixWord ++ tailWord_6009155).sum := by decide
  have hdescent : baseEnd_6009155 < baseStart_6009155 := by decide
  rcases family_descends (prefixWord ++ tailWord_6009155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6009172 : List Nat := [2, 4, 1, 1, 2, 3, 2, 1, 1, 6]
def baseStart_6009172 : Nat := 118140960795 + 6009172 * 2 ^ 59
def prefixEnd_6009172 : Nat := 4983230072969 + 3 ^ 40 * 6009172 * 2
def baseEnd_6009172 : Nat := 1028531190513222773538109

theorem tailTrace_6009172 : CollatzResearch.WordTrace tailWord_6009172 prefixEnd_6009172 1028531190513222773538109 := by
  unfold tailWord_6009172
  simp only [CollatzResearch.WordTrace]
  refine ⟨109586254292901801857998885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146115005723869069143998513 109586254292901801857998885)
  ·
    refine ⟨20547422679919087848374791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109586254292901801857998885 20547422679919087848374791)
    ·
      refine ⟨30821134019878631772562187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20547422679919087848374791 30821134019878631772562187)
      ·
        refine ⟨46231701029817947658843281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30821134019878631772562187 46231701029817947658843281)
        ·
          refine ⟨34673775772363460744132461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46231701029817947658843281 34673775772363460744132461)
          ·
            refine ⟨13002665914636297779049673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34673775772363460744132461 13002665914636297779049673)
            ·
              refine ⟨9751999435977223334287255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13002665914636297779049673 9751999435977223334287255)
              ·
                refine ⟨14627999153965835001430883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9751999435977223334287255 14627999153965835001430883)
                ·
                  refine ⟨21941998730948752502146325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14627999153965835001430883 21941998730948752502146325)
                  ·
                    refine ⟨1028531190513222773538109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21941998730948752502146325 1028531190513222773538109)
                    ·
                      rfl

theorem cell23_6009172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 1, 1, 6].length) (baseStart_6009172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6009172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6009172 prefixEnd_6009172 := by exact prefixLift 6009172
  have htrace : WordTrace (prefixWord ++ tailWord_6009172) baseStart_6009172 baseEnd_6009172 := by
    simpa [prefixWord, tailWord_6009172, baseEnd_6009172] using wordTrace_append hprefix tailTrace_6009172
  have hstable : (prefixWord ++ tailWord_6009172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6009172).length < 2 ^ (prefixWord ++ tailWord_6009172).sum := by decide
  have hdescent : baseEnd_6009172 < baseStart_6009172 := by decide
  rcases family_descends (prefixWord ++ tailWord_6009172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6009192 : List Nat := [2, 1, 4, 2, 2, 1, 2, 2, 1, 2, 4]
def baseStart_6009192 : Nat := 118140960795 + 6009192 * 2 ^ 59
def prefixEnd_6009192 : Nat := 4983230072969 + 3 ^ 40 * 6009192 * 2
def baseEnd_6009192 : Nat := 3085603841152758242364235

theorem tailTrace_6009192 : CollatzResearch.WordTrace tailWord_6009192 prefixEnd_6009192 3085603841152758242364235 := by
  unfold tailWord_6009192
  simp only [CollatzResearch.WordTrace]
  refine ⟨109586619022865573565862915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146115492030487431421150553 109586619022865573565862915)
  ·
    refine ⟨164379928534298360348794373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109586619022865573565862915 164379928534298360348794373)
    ·
      refine ⟨30821236600180942565398945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 164379928534298360348794373 30821236600180942565398945)
      ·
        refine ⟨23115927450135706924049209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30821236600180942565398945 23115927450135706924049209)
        ·
          refine ⟨17336945587601780193036907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23115927450135706924049209 17336945587601780193036907)
          ·
            refine ⟨26005418381402670289555361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17336945587601780193036907 26005418381402670289555361)
            ·
              refine ⟨19504063786052002717166521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26005418381402670289555361 19504063786052002717166521)
              ·
                refine ⟨14628047839539002037874891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19504063786052002717166521 14628047839539002037874891)
                ·
                  refine ⟨21942071759308503056812337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14628047839539002037874891 21942071759308503056812337)
                  ·
                    refine ⟨16456553819481377292609253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21942071759308503056812337 16456553819481377292609253)
                    ·
                      refine ⟨3085603841152758242364235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16456553819481377292609253 3085603841152758242364235)
                      ·
                        rfl

theorem cell23_6009192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_6009192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6009192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6009192 prefixEnd_6009192 := by exact prefixLift 6009192
  have htrace : WordTrace (prefixWord ++ tailWord_6009192) baseStart_6009192 baseEnd_6009192 := by
    simpa [prefixWord, tailWord_6009192, baseEnd_6009192] using wordTrace_append hprefix tailTrace_6009192
  have hstable : (prefixWord ++ tailWord_6009192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6009192).length < 2 ^ (prefixWord ++ tailWord_6009192).sum := by decide
  have hdescent : baseEnd_6009192 < baseStart_6009192 := by decide
  rcases family_descends (prefixWord ++ tailWord_6009192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6009196 : List Nat := [2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 4]
def baseStart_6009196 : Nat := 118140960795 + 6009196 * 2 ^ 59
def prefixEnd_6009196 : Nat := 4983230072969 + 3 ^ 40 * 6009196 * 2
def baseEnd_6009196 : Nat := 3085605895075376226714217

theorem tailTrace_6009196 : CollatzResearch.WordTrace tailWord_6009196 prefixEnd_6009196 3085605895075376226714217 := by
  unfold tailWord_6009196
  simp only [CollatzResearch.WordTrace]
  refine ⟨109586691968858327907435721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146115589291811103876580961 109586691968858327907435721)
  ·
    refine ⟨82190018976643745930576791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109586691968858327907435721 82190018976643745930576791)
    ·
      refine ⟨123285028464965618895865187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82190018976643745930576791 123285028464965618895865187)
      ·
        refine ⟨184927542697448428343797781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123285028464965618895865187 184927542697448428343797781)
        ·
          refine ⟨8668478563942895078615521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 184927542697448428343797781 8668478563942895078615521)
          ·
            refine ⟨6501358922957171308961641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8668478563942895078615521 6501358922957171308961641)
            ·
              refine ⟨4876019192217878481721231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6501358922957171308961641 4876019192217878481721231)
              ·
                refine ⟨7314028788326817722581847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4876019192217878481721231 7314028788326817722581847)
                ·
                  refine ⟨10971043182490226583872771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7314028788326817722581847 10971043182490226583872771)
                  ·
                    refine ⟨16456564773735339875809157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10971043182490226583872771 16456564773735339875809157)
                    ·
                      refine ⟨3085605895075376226714217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16456564773735339875809157 3085605895075376226714217)
                      ·
                        rfl

theorem cell23_6009196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 4].length) (baseStart_6009196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6009196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6009196 prefixEnd_6009196 := by exact prefixLift 6009196
  have htrace : WordTrace (prefixWord ++ tailWord_6009196) baseStart_6009196 baseEnd_6009196 := by
    simpa [prefixWord, tailWord_6009196, baseEnd_6009196] using wordTrace_append hprefix tailTrace_6009196
  have hstable : (prefixWord ++ tailWord_6009196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6009196).length < 2 ^ (prefixWord ++ tailWord_6009196).sum := by decide
  have hdescent : baseEnd_6009196 < baseStart_6009196 := by decide
  rcases family_descends (prefixWord ++ tailWord_6009196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6009206 : List Nat := [5, 1, 1, 4, 1, 1, 1, 1, 4, 4]
def baseStart_6009206 : Nat := 118140960795 + 6009206 * 2 ^ 59
def prefixEnd_6009206 : Nat := 4983230072969 + 3 ^ 40 * 6009206 * 2
def baseEnd_6009206 : Nat := 1028537009960640395863057

theorem tailTrace_6009206 : CollatzResearch.WordTrace tailWord_6009206 prefixEnd_6009206 1028537009960640395863057 := by
  unfold tailWord_6009206
  simp only [CollatzResearch.WordTrace]
  refine ⟨13698359291730026720170967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 146115832445120285015156981 13698359291730026720170967)
  ·
    refine ⟨20547538937595040080256451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13698359291730026720170967 20547538937595040080256451)
    ·
      refine ⟨30821308406392560120384677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20547538937595040080256451 30821308406392560120384677)
      ·
        refine ⟨5778995326198605022572127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30821308406392560120384677 5778995326198605022572127)
        ·
          refine ⟨8668492989297907533858191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5778995326198605022572127 8668492989297907533858191)
          ·
            refine ⟨13002739483946861300787287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8668492989297907533858191 13002739483946861300787287)
            ·
              refine ⟨19504109225920291951180931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13002739483946861300787287 19504109225920291951180931)
              ·
                refine ⟨29256163838880437926771397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19504109225920291951180931 29256163838880437926771397)
                ·
                  refine ⟨5485530719790082111269637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29256163838880437926771397 5485530719790082111269637)
                  ·
                    refine ⟨1028537009960640395863057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5485530719790082111269637 1028537009960640395863057)
                    ·
                      rfl

theorem cell23_6009206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 4, 4].length) (baseStart_6009206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6009206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6009206 prefixEnd_6009206 := by exact prefixLift 6009206
  have htrace : WordTrace (prefixWord ++ tailWord_6009206) baseStart_6009206 baseEnd_6009206 := by
    simpa [prefixWord, tailWord_6009206, baseEnd_6009206] using wordTrace_append hprefix tailTrace_6009206
  have hstable : (prefixWord ++ tailWord_6009206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6009206).length < 2 ^ (prefixWord ++ tailWord_6009206).sum := by decide
  have hdescent : baseEnd_6009206 < baseStart_6009206 := by decide
  rcases family_descends (prefixWord ++ tailWord_6009206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6009226 : List Nat := [3, 1, 2, 5, 1, 2, 1, 1, 1, 2, 4]
def baseStart_6009226 : Nat := 118140960795 + 6009226 * 2 ^ 59
def prefixEnd_6009226 : Nat := 4983230072969 + 3 ^ 40 * 6009226 * 2
def baseEnd_6009226 : Nat := 3085621299495011109339079

theorem tailTrace_6009226 : CollatzResearch.WordTrace tailWord_6009226 prefixEnd_6009226 3085621299495011109339079 := by
  unfold tailWord_6009226
  simp only [CollatzResearch.WordTrace]
  refine ⟨54793619531901992734615883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146116318751738647292309021 54793619531901992734615883)
  ·
    refine ⟨82190429297852989101923825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54793619531901992734615883 82190429297852989101923825)
    ·
      refine ⟨61642821973389741826442869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82190429297852989101923825 61642821973389741826442869)
      ·
        refine ⟨5779014560005288296229019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61642821973389741826442869 5779014560005288296229019)
        ·
          refine ⟨8668521840007932444343529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5779014560005288296229019 8668521840007932444343529)
          ·
            refine ⟨6501391380005949333257647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8668521840007932444343529 6501391380005949333257647)
            ·
              refine ⟨9752087070008923999886471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6501391380005949333257647 9752087070008923999886471)
              ·
                refine ⟨14628130605013385999829707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9752087070008923999886471 14628130605013385999829707)
                ·
                  refine ⟨21942195907520078999744561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14628130605013385999829707 21942195907520078999744561)
                  ·
                    refine ⟨16456646930640059249808421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21942195907520078999744561 16456646930640059249808421)
                    ·
                      refine ⟨3085621299495011109339079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16456646930640059249808421 3085621299495011109339079)
                      ·
                        rfl

theorem cell23_6009226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_6009226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6009226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6009226 prefixEnd_6009226 := by exact prefixLift 6009226
  have htrace : WordTrace (prefixWord ++ tailWord_6009226) baseStart_6009226 baseEnd_6009226 := by
    simpa [prefixWord, tailWord_6009226, baseEnd_6009226] using wordTrace_append hprefix tailTrace_6009226
  have hstable : (prefixWord ++ tailWord_6009226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6009226).length < 2 ^ (prefixWord ++ tailWord_6009226).sum := by decide
  have hdescent : baseEnd_6009226 < baseStart_6009226 := by decide
  rcases family_descends (prefixWord ++ tailWord_6009226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6009236 : List Nat := [2, 4, 2, 1, 4, 1, 2, 7]
def baseStart_6009236 : Nat := 118140960795 + 6009236 * 2 ^ 59
def prefixEnd_6009236 : Nat := 4983230072969 + 3 ^ 40 * 6009236 * 2
def baseEnd_6009236 : Nat := 114282460529687261859779

theorem tailTrace_6009236 : CollatzResearch.WordTrace tailWord_6009236 prefixEnd_6009236 114282460529687261859779 := by
  unfold tailWord_6009236
  simp only [CollatzResearch.WordTrace]
  refine ⟨109587421428785871323163781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146116561905047828430885041 109587421428785871323163781)
  ·
    refine ⟨20547641517897350873093209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109587421428785871323163781 20547641517897350873093209)
    ·
      refine ⟨15410731138423013154819907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20547641517897350873093209 15410731138423013154819907)
      ·
        refine ⟨23116096707634519732229861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15410731138423013154819907 23116096707634519732229861)
        ·
          refine ⟨4334268132681472449793099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23116096707634519732229861 4334268132681472449793099)
          ·
            refine ⟨6501402199022208674689649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4334268132681472449793099 6501402199022208674689649)
            ·
              refine ⟨4876051649266656506017237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6501402199022208674689649 4876051649266656506017237)
              ·
                refine ⟨114282460529687261859779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4876051649266656506017237 114282460529687261859779)
                ·
                  rfl

theorem cell23_6009236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 2, 7].length) (baseStart_6009236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6009236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6009236 prefixEnd_6009236 := by exact prefixLift 6009236
  have htrace : WordTrace (prefixWord ++ tailWord_6009236) baseStart_6009236 baseEnd_6009236 := by
    simpa [prefixWord, tailWord_6009236, baseEnd_6009236] using wordTrace_append hprefix tailTrace_6009236
  have hstable : (prefixWord ++ tailWord_6009236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6009236).length < 2 ^ (prefixWord ++ tailWord_6009236).sum := by decide
  have hdescent : baseEnd_6009236 < baseStart_6009236 := by decide
  rcases family_descends (prefixWord ++ tailWord_6009236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6009239 : List Nat := [1, 1, 3, 3, 1, 1, 3, 4, 1, 3, 2]
def baseStart_6009239 : Nat := 118140960795 + 6009239 * 2 ^ 59
def prefixEnd_6009239 : Nat := 4983230072969 + 3 ^ 40 * 6009239 * 2
def baseEnd_6009239 : Nat := 3085627974743519558476519

theorem tailTrace_6009239 : CollatzResearch.WordTrace tailWord_6009239 prefixEnd_6009239 3085627974743519558476519 := by
  unfold tailWord_6009239
  simp only [CollatzResearch.WordTrace]
  refine ⟨219174952276560874158686771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146116634851040582772457847 219174952276560874158686771)
  ·
    refine ⟨328762428414841311238030157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219174952276560874158686771 328762428414841311238030157)
    ·
      refine ⟨123285910655565491714261309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 328762428414841311238030157 123285910655565491714261309)
      ·
        refine ⟨46232216495837059392847991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123285910655565491714261309 46232216495837059392847991)
        ·
          refine ⟨69348324743755589089271987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46232216495837059392847991 69348324743755589089271987)
          ·
            refine ⟨104022487115633383633907981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69348324743755589089271987 104022487115633383633907981)
            ·
              refine ⟨39008432668362518862715493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104022487115633383633907981 39008432668362518862715493)
              ·
                refine ⟨7314081125317972286759155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39008432668362518862715493 7314081125317972286759155)
                ·
                  refine ⟨10971121687976958430138733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7314081125317972286759155 10971121687976958430138733)
                  ·
                    refine ⟨4114170632991359411302025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10971121687976958430138733 4114170632991359411302025)
                    ·
                      refine ⟨3085627974743519558476519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4114170632991359411302025 3085627974743519558476519)
                      ·
                        rfl

theorem cell23_6009239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 4, 1, 3, 2].length) (baseStart_6009239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6009239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6009239 prefixEnd_6009239 := by exact prefixLift 6009239
  have htrace : WordTrace (prefixWord ++ tailWord_6009239) baseStart_6009239 baseEnd_6009239 := by
    simpa [prefixWord, tailWord_6009239, baseEnd_6009239] using wordTrace_append hprefix tailTrace_6009239
  have hstable : (prefixWord ++ tailWord_6009239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6009239).length < 2 ^ (prefixWord ++ tailWord_6009239).sum := by decide
  have hdescent : baseEnd_6009239 < baseStart_6009239 := by decide
  rcases family_descends (prefixWord ++ tailWord_6009239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6009246 : List Nat := [4, 3, 1, 2, 1, 1, 1, 2, 4, 1, 3]
def baseStart_6009246 : Nat := 118140960795 + 6009246 * 2 ^ 59
def prefixEnd_6009246 : Nat := 4983230072969 + 3 ^ 40 * 6009246 * 2
def baseEnd_6009246 : Nat := 3085631569108101031088987

theorem tailTrace_6009246 : CollatzResearch.WordTrace tailWord_6009246 prefixEnd_6009246 3085631569108101031088987 := by
  unfold tailWord_6009246
  simp only [CollatzResearch.WordTrace]
  refine ⟨27396900948441939294273949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146116805058357009569461061 27396900948441939294273949)
  ·
    refine ⟨10273837855665727235352731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27396900948441939294273949 10273837855665727235352731)
    ·
      refine ⟨15410756783498590853029097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10273837855665727235352731 15410756783498590853029097)
      ·
        refine ⟨11558067587623943139771823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15410756783498590853029097 11558067587623943139771823)
        ·
          refine ⟨17337101381435914709657735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11558067587623943139771823 17337101381435914709657735)
          ·
            refine ⟨26005652072153872064486603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17337101381435914709657735 26005652072153872064486603)
            ·
              refine ⟨39008478108230808096729905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26005652072153872064486603 39008478108230808096729905)
              ·
                refine ⟨29256358581173106072547429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39008478108230808096729905 29256358581173106072547429)
                ·
                  refine ⟨5485567233969957388602643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29256358581173106072547429 5485567233969957388602643)
                  ·
                    refine ⟨8228350850954936082903965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5485567233969957388602643 8228350850954936082903965)
                    ·
                      refine ⟨3085631569108101031088987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8228350850954936082903965 3085631569108101031088987)
                      ·
                        rfl

theorem cell23_6009246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_6009246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6009246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6009246 prefixEnd_6009246 := by exact prefixLift 6009246
  have htrace : WordTrace (prefixWord ++ tailWord_6009246) baseStart_6009246 baseEnd_6009246 := by
    simpa [prefixWord, tailWord_6009246, baseEnd_6009246] using wordTrace_append hprefix tailTrace_6009246
  have hstable : (prefixWord ++ tailWord_6009246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6009246).length < 2 ^ (prefixWord ++ tailWord_6009246).sum := by decide
  have hdescent : baseEnd_6009246 < baseStart_6009246 := by decide
  rcases family_descends (prefixWord ++ tailWord_6009246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6009309 : List Nat := [1, 4, 3, 1, 1, 1, 2, 5, 5]
def baseStart_6009309 : Nat := 118140960795 + 6009309 * 2 ^ 59
def prefixEnd_6009309 : Nat := 4983230072969 + 3 ^ 40 * 6009309 * 2
def baseEnd_6009309 : Nat := 342851546487703809400133

theorem tailTrace_6009309 : CollatzResearch.WordTrace tailWord_6009309 prefixEnd_6009309 342851546487703809400133 := by
  unfold tailWord_6009309
  simp only [CollatzResearch.WordTrace]
  refine ⟨219177505386307276113734981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146118336924204850742489987 219177505386307276113734981)
  ·
    refine ⟨41095782259932614271325309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 219177505386307276113734981 41095782259932614271325309)
    ·
      refine ⟨15410918347474730351746991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41095782259932614271325309 15410918347474730351746991)
      ·
        refine ⟨23116377521212095527620487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15410918347474730351746991 23116377521212095527620487)
        ·
          refine ⟨34674566281818143291430731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23116377521212095527620487 34674566281818143291430731)
          ·
            refine ⟨52011849422727214937146097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34674566281818143291430731 52011849422727214937146097)
            ·
              refine ⟨39008887067045411202859573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52011849422727214937146097 39008887067045411202859573)
              ·
                refine ⟨3657083162535507300268085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39008887067045411202859573 3657083162535507300268085)
                ·
                  refine ⟨342851546487703809400133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3657083162535507300268085 342851546487703809400133)
                  ·
                    rfl

theorem cell23_6009309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 5, 5].length) (baseStart_6009309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6009309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6009309 prefixEnd_6009309 := by exact prefixLift 6009309
  have htrace : WordTrace (prefixWord ++ tailWord_6009309) baseStart_6009309 baseEnd_6009309 := by
    simpa [prefixWord, tailWord_6009309, baseEnd_6009309] using wordTrace_append hprefix tailTrace_6009309
  have hstable : (prefixWord ++ tailWord_6009309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6009309).length < 2 ^ (prefixWord ++ tailWord_6009309).sum := by decide
  have hdescent : baseEnd_6009309 < baseStart_6009309 := by decide
  rcases family_descends (prefixWord ++ tailWord_6009309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6009326 : List Nat := [4, 1, 2, 1, 2, 2, 4, 2, 5]
def baseStart_6009326 : Nat := 118140960795 + 6009326 * 2 ^ 59
def prefixEnd_6009326 : Nat := 4983230072969 + 3 ^ 40 * 6009326 * 2
def baseEnd_6009326 : Nat := 342852516395606746454291

theorem tailTrace_6009326 : CollatzResearch.WordTrace tailWord_6009326 prefixEnd_6009326 342852516395606746454291 := by
  unfold tailWord_6009326
  simp only [CollatzResearch.WordTrace]
  refine ⟨27397265678405711002137979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146118750284830458678069221 27397265678405711002137979)
  ·
    refine ⟨41095898517608566503206969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27397265678405711002137979 41095898517608566503206969)
    ·
      refine ⟨30821923888206424877405227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41095898517608566503206969 30821923888206424877405227)
      ·
        refine ⟨46232885832309637316107841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30821923888206424877405227 46232885832309637316107841)
        ·
          refine ⟨34674664374232227987080881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46232885832309637316107841 34674664374232227987080881)
          ·
            refine ⟨26005998280674170990310661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34674664374232227987080881 26005998280674170990310661)
            ·
              refine ⟨4876124677626407060683249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26005998280674170990310661 4876124677626407060683249)
              ·
                refine ⟨3657093508219805295512437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4876124677626407060683249 3657093508219805295512437)
                ·
                  refine ⟨342852516395606746454291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3657093508219805295512437 342852516395606746454291)
                  ·
                    rfl

theorem cell23_6009326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 4, 2, 5].length) (baseStart_6009326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6009326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6009326 prefixEnd_6009326 := by exact prefixLift 6009326
  have htrace : WordTrace (prefixWord ++ tailWord_6009326) baseStart_6009326 baseEnd_6009326 := by
    simpa [prefixWord, tailWord_6009326, baseEnd_6009326] using wordTrace_append hprefix tailTrace_6009326
  have hstable : (prefixWord ++ tailWord_6009326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6009326).length < 2 ^ (prefixWord ++ tailWord_6009326).sum := by decide
  have hdescent : baseEnd_6009326 < baseStart_6009326 := by decide
  rcases family_descends (prefixWord ++ tailWord_6009326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6009372 : List Nat := [2, 2, 3, 1, 2, 2, 1, 1, 2, 1, 6]
def baseStart_6009372 : Nat := 118140960795 + 6009372 * 2 ^ 59
def prefixEnd_6009372 : Nat := 4983230072969 + 3 ^ 40 * 6009372 * 2
def baseEnd_6009372 : Nat := 3085696267670567538113407

theorem tailTrace_6009372 : CollatzResearch.WordTrace tailWord_6009372 prefixEnd_6009372 3085696267670567538113407 := by
  unfold tailWord_6009372
  simp only [CollatzResearch.WordTrace]
  refine ⟨109589901592539518936639185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146119868790052691915518913 109589901592539518936639185)
  ·
    refine ⟨82192426194404639202479389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109589901592539518936639185 82192426194404639202479389)
    ·
      refine ⟨30822159822901739700929771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82192426194404639202479389 30822159822901739700929771)
      ·
        refine ⟨46233239734352609551394657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30822159822901739700929771 46233239734352609551394657)
        ·
          refine ⟨34674929800764457163545993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46233239734352609551394657 34674929800764457163545993)
          ·
            refine ⟨26006197350573342872659495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34674929800764457163545993 26006197350573342872659495)
            ·
              refine ⟨39009296025860014308989243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26006197350573342872659495 39009296025860014308989243)
              ·
                refine ⟨58513944038790021463483865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39009296025860014308989243 58513944038790021463483865)
                ·
                  refine ⟨43885458029092516097612899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58513944038790021463483865 43885458029092516097612899)
                  ·
                    refine ⟨65828187043638774146419349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43885458029092516097612899 65828187043638774146419349)
                    ·
                      refine ⟨3085696267670567538113407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65828187043638774146419349 3085696267670567538113407)
                      ·
                        rfl

theorem cell23_6009372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_6009372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6009372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6009372 prefixEnd_6009372 := by exact prefixLift 6009372
  have htrace : WordTrace (prefixWord ++ tailWord_6009372) baseStart_6009372 baseEnd_6009372 := by
    simpa [prefixWord, tailWord_6009372, baseEnd_6009372] using wordTrace_append hprefix tailTrace_6009372
  have hstable : (prefixWord ++ tailWord_6009372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6009372).length < 2 ^ (prefixWord ++ tailWord_6009372).sum := by decide
  have hdescent : baseEnd_6009372 < baseStart_6009372 := by decide
  rcases family_descends (prefixWord ++ tailWord_6009372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6009386 : List Nat := [3, 1, 4, 1, 1, 3, 2, 1, 3, 4]
def baseStart_6009386 : Nat := 118140960795 + 6009386 * 2 ^ 59
def prefixEnd_6009386 : Nat := 4983230072969 + 3 ^ 40 * 6009386 * 2
def baseEnd_6009386 : Nat := 1028567818799910161112781

theorem tailTrace_6009386 : CollatzResearch.WordTrace tailWord_6009386 prefixEnd_6009386 1028567818799910161112781 := by
  unfold tailWord_6009386
  simp only [CollatzResearch.WordTrace]
  refine ⟨54795078451757079566072003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146120209204685545509525341 54795078451757079566072003)
  ·
    refine ⟨82192617677635619349108005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54795078451757079566072003 82192617677635619349108005)
    ·
      refine ⟨15411115814556678627957751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82192617677635619349108005 15411115814556678627957751)
      ·
        refine ⟨23116673721835017941936627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15411115814556678627957751 23116673721835017941936627)
        ·
          refine ⟨34675010582752526912904941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23116673721835017941936627 34675010582752526912904941)
          ·
            refine ⟨13003128968532197592339353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34675010582752526912904941 13003128968532197592339353)
            ·
              refine ⟨9752346726399148194254515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13003128968532197592339353 9752346726399148194254515)
              ·
                refine ⟨14628520089598722291381773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9752346726399148194254515 14628520089598722291381773)
                ·
                  refine ⟨5485695033599520859268165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14628520089598722291381773 5485695033599520859268165)
                  ·
                    refine ⟨1028567818799910161112781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5485695033599520859268165 1028567818799910161112781)
                    ·
                      rfl

theorem cell23_6009386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_6009386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6009386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6009386 prefixEnd_6009386 := by exact prefixLift 6009386
  have htrace : WordTrace (prefixWord ++ tailWord_6009386) baseStart_6009386 baseEnd_6009386 := by
    simpa [prefixWord, tailWord_6009386, baseEnd_6009386] using wordTrace_append hprefix tailTrace_6009386
  have hstable : (prefixWord ++ tailWord_6009386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6009386).length < 2 ^ (prefixWord ++ tailWord_6009386).sum := by decide
  have hdescent : baseEnd_6009386 < baseStart_6009386 := by decide
  rcases family_descends (prefixWord ++ tailWord_6009386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6009399 : List Nat := [1, 1, 3, 1, 2, 3, 5, 1, 6]
def baseStart_6009399 : Nat := 118140960795 + 6009399 * 2 ^ 59
def prefixEnd_6009399 : Nat := 4983230072969 + 3 ^ 40 * 6009399 * 2
def baseEnd_6009399 : Nat := 342856681294248770275087

theorem tailTrace_6009399 : CollatzResearch.WordTrace tailWord_6009399 prefixEnd_6009399 342856681294248770275087 := by
  unfold tailWord_6009399
  simp only [CollatzResearch.WordTrace]
  refine ⟨219180787955981221484511251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146120525303987480989674167 219180787955981221484511251)
  ·
    refine ⟨328771181933971832226766877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219180787955981221484511251 328771181933971832226766877)
    ·
      refine ⟨123289193225239437085037579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 328771181933971832226766877 123289193225239437085037579)
      ·
        refine ⟨184933789837859155627556369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123289193225239437085037579 184933789837859155627556369)
        ·
          refine ⟨138700342378394366720667277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184933789837859155627556369 138700342378394366720667277)
          ·
            refine ⟨52012628391897887520250229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138700342378394366720667277 52012628391897887520250229)
            ·
              refine ⟨4876183911740426955023459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52012628391897887520250229 4876183911740426955023459)
              ·
                refine ⟨7314275867610640432535189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4876183911740426955023459 7314275867610640432535189)
                ·
                  refine ⟨342856681294248770275087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7314275867610640432535189 342856681294248770275087)
                  ·
                    rfl

theorem cell23_6009399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 5, 1, 6].length) (baseStart_6009399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6009399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6009399 prefixEnd_6009399 := by exact prefixLift 6009399
  have htrace : WordTrace (prefixWord ++ tailWord_6009399) baseStart_6009399 baseEnd_6009399 := by
    simpa [prefixWord, tailWord_6009399, baseEnd_6009399] using wordTrace_append hprefix tailTrace_6009399
  have hstable : (prefixWord ++ tailWord_6009399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6009399).length < 2 ^ (prefixWord ++ tailWord_6009399).sum := by decide
  have hdescent : baseEnd_6009399 < baseStart_6009399 := by decide
  rcases family_descends (prefixWord ++ tailWord_6009399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6009419 : List Nat := [1, 1, 1, 1, 3, 1, 6, 1, 1, 5, 2]
def baseStart_6009419 : Nat := 118140960795 + 6009419 * 2 ^ 59
def prefixEnd_6009419 : Nat := 4983230072969 + 3 ^ 40 * 6009419 * 2
def baseEnd_6009419 : Nat := 3085720401261328854225691

theorem tailTrace_6009419 : CollatzResearch.WordTrace tailWord_6009419 prefixEnd_6009419 3085720401261328854225691 := by
  unfold tailWord_6009419
  simp only [CollatzResearch.WordTrace]
  refine ⟨219181517415908764900239311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146121011610605843266826207 219181517415908764900239311)
  ·
    refine ⟨328772276123863147350358967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219181517415908764900239311 328772276123863147350358967)
    ·
      refine ⟨493158414185794721025538451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328772276123863147350358967 493158414185794721025538451)
      ·
        refine ⟨739737621278692081538307677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 493158414185794721025538451 739737621278692081538307677)
        ·
          refine ⟨277401607979509530576865379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 739737621278692081538307677 277401607979509530576865379)
          ·
            refine ⟨416102411969264295865298069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277401607979509530576865379 416102411969264295865298069)
            ·
              refine ⟨19504800561059263868685847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 416102411969264295865298069 19504800561059263868685847)
              ·
                refine ⟨29257200841588895803028771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19504800561059263868685847 29257200841588895803028771)
                ·
                  refine ⟨43885801262383343704543157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29257200841588895803028771 43885801262383343704543157)
                  ·
                    refine ⟨4114293868348438472300921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43885801262383343704543157 4114293868348438472300921)
                    ·
                      refine ⟨3085720401261328854225691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4114293868348438472300921 3085720401261328854225691)
                      ·
                        rfl

theorem cell23_6009419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 5, 2].length) (baseStart_6009419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6009419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6009419 prefixEnd_6009419 := by exact prefixLift 6009419
  have htrace : WordTrace (prefixWord ++ tailWord_6009419) baseStart_6009419 baseEnd_6009419 := by
    simpa [prefixWord, tailWord_6009419, baseEnd_6009419] using wordTrace_append hprefix tailTrace_6009419
  have hstable : (prefixWord ++ tailWord_6009419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6009419).length < 2 ^ (prefixWord ++ tailWord_6009419).sum := by decide
  have hdescent : baseEnd_6009419 < baseStart_6009419 := by decide
  rcases family_descends (prefixWord ++ tailWord_6009419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6009429 : List Nat := [1, 3, 2, 2, 1, 1, 4, 3, 1, 5]
def baseStart_6009429 : Nat := 118140960795 + 6009429 * 2 ^ 59
def prefixEnd_6009429 : Nat := 4983230072969 + 3 ^ 40 * 6009429 * 2
def baseEnd_6009429 : Nat := 1028575178689291271700215

theorem tailTrace_6009429 : CollatzResearch.WordTrace tailWord_6009429 prefixEnd_6009429 1028575178689291271700215 := by
  unfold tailWord_6009429
  simp only [CollatzResearch.WordTrace]
  refine ⟨219181882145872536608103341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146121254763915024405402227 219181882145872536608103341)
  ·
    refine ⟨82193205804702201228038753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219181882145872536608103341 82193205804702201228038753)
    ·
      refine ⟨61644904353526650921029065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82193205804702201228038753 61644904353526650921029065)
      ·
        refine ⟨46233678265144988190771799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61644904353526650921029065 46233678265144988190771799)
        ·
          refine ⟨69350517397717482286157699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46233678265144988190771799 69350517397717482286157699)
          ·
            refine ⟨104025776096576223429236549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69350517397717482286157699 104025776096576223429236549)
            ·
              refine ⟨19504833018108041892981853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104025776096576223429236549 19504833018108041892981853)
              ·
                refine ⟨7314312381790515709868195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19504833018108041892981853 7314312381790515709868195)
                ·
                  refine ⟨10971468572685773564802293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7314312381790515709868195 10971468572685773564802293)
                  ·
                    refine ⟨1028575178689291271700215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10971468572685773564802293 1028575178689291271700215)
                    ·
                      rfl

theorem cell23_6009429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 3, 1, 5].length) (baseStart_6009429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6009429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6009429 prefixEnd_6009429 := by exact prefixLift 6009429
  have htrace : WordTrace (prefixWord ++ tailWord_6009429) baseStart_6009429 baseEnd_6009429 := by
    simpa [prefixWord, tailWord_6009429, baseEnd_6009429] using wordTrace_append hprefix tailTrace_6009429
  have hstable : (prefixWord ++ tailWord_6009429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6009429).length < 2 ^ (prefixWord ++ tailWord_6009429).sum := by decide
  have hdescent : baseEnd_6009429 < baseStart_6009429 := by decide
  rcases family_descends (prefixWord ++ tailWord_6009429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6009472 : List Nat := [2, 1, 1, 2, 1, 5, 2, 9]
def baseStart_6009472 : Nat := 118140960795 + 6009472 * 2 ^ 59
def prefixEnd_6009472 : Nat := 4983230072969 + 3 ^ 40 * 6009472 * 2
def baseEnd_6009472 : Nat := 114286948730963598031961

theorem tailTrace_6009472 : CollatzResearch.WordTrace tailWord_6009472 prefixEnd_6009472 114286948730963598031961 := by
  unfold tailWord_6009472
  simp only [CollatzResearch.WordTrace]
  refine ⟨109591725242358377475959335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146122300323144503301279113 109591725242358377475959335)
  ·
    refine ⟨164387587863537566213939003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109591725242358377475959335 164387587863537566213939003)
    ·
      refine ⟨246581381795306349320908505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164387587863537566213939003 246581381795306349320908505)
      ·
        refine ⟨184936036346479761990681379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246581381795306349320908505 184936036346479761990681379)
        ·
          refine ⟨277404054519719642986022069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184936036346479761990681379 277404054519719642986022069)
          ·
            refine ⟨26006630111223716529939569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 277404054519719642986022069 26006630111223716529939569)
            ·
              refine ⟨19504972583417787397454677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26006630111223716529939569 19504972583417787397454677)
              ·
                refine ⟨114286948730963598031961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19504972583417787397454677 114286948730963598031961)
                ·
                  rfl

theorem cell23_6009472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 9].length) (baseStart_6009472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6009472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6009472 prefixEnd_6009472 := by exact prefixLift 6009472
  have htrace : WordTrace (prefixWord ++ tailWord_6009472) baseStart_6009472 baseEnd_6009472 := by
    simpa [prefixWord, tailWord_6009472, baseEnd_6009472] using wordTrace_append hprefix tailTrace_6009472
  have hstable : (prefixWord ++ tailWord_6009472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6009472).length < 2 ^ (prefixWord ++ tailWord_6009472).sum := by decide
  have hdescent : baseEnd_6009472 < baseStart_6009472 := by decide
  rcases family_descends (prefixWord ++ tailWord_6009472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6009479 : List Nat := [1, 1, 4, 2, 1, 2, 3, 2, 1, 2, 4]
def baseStart_6009479 : Nat := 118140960795 + 6009479 * 2 ^ 59
def prefixEnd_6009479 : Nat := 4983230072969 + 3 ^ 40 * 6009479 * 2
def baseEnd_6009479 : Nat := 3085751210100598619475415

theorem tailTrace_6009479 : CollatzResearch.WordTrace tailWord_6009479 prefixEnd_6009479 3085751210100598619475415 := by
  unfold tailWord_6009479
  simp only [CollatzResearch.WordTrace]
  refine ⟨219183705795691395147423491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146122470530460930098282327 219183705795691395147423491)
  ·
    refine ⟨328775558693537092721135237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219183705795691395147423491 328775558693537092721135237)
    ·
      refine ⟨61645417255038204885212857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 328775558693537092721135237 61645417255038204885212857)
      ·
        refine ⟨46234062941278653663909643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61645417255038204885212857 46234062941278653663909643)
        ·
          refine ⟨69351094411917980495864465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46234062941278653663909643 69351094411917980495864465)
          ·
            refine ⟨52013320808938485371898349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69351094411917980495864465 52013320808938485371898349)
            ·
              refine ⟨19504995303351932014461881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52013320808938485371898349 19504995303351932014461881)
              ·
                refine ⟨14628746477513949010846411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19504995303351932014461881 14628746477513949010846411)
                ·
                  refine ⟨21943119716270923516269617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14628746477513949010846411 21943119716270923516269617)
                  ·
                    refine ⟨16457339787203192637202213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21943119716270923516269617 16457339787203192637202213)
                    ·
                      refine ⟨3085751210100598619475415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16457339787203192637202213 3085751210100598619475415)
                      ·
                        rfl

theorem cell23_6009479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_6009479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6009479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6009479 prefixEnd_6009479 := by exact prefixLift 6009479
  have htrace : WordTrace (prefixWord ++ tailWord_6009479) baseStart_6009479 baseEnd_6009479 := by
    simpa [prefixWord, tailWord_6009479, baseEnd_6009479] using wordTrace_append hprefix tailTrace_6009479
  have hstable : (prefixWord ++ tailWord_6009479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6009479).length < 2 ^ (prefixWord ++ tailWord_6009479).sum := by decide
  have hdescent : baseEnd_6009479 < baseStart_6009479 := by decide
  rcases family_descends (prefixWord ++ tailWord_6009479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6009550 : List Nat := [4, 1, 1, 1, 3, 4, 1, 2, 2, 1, 3]
def baseStart_6009550 : Nat := 118140960795 + 6009550 * 2 ^ 59
def prefixEnd_6009550 : Nat := 4983230072969 + 3 ^ 40 * 6009550 * 2
def baseEnd_6009550 : Nat := 3085787667227067841687589

theorem tailTrace_6009550 : CollatzResearch.WordTrace tailWord_6009550 prefixEnd_6009550 3085787667227067841687589 := by
  unfold tailWord_6009550
  simp only [CollatzResearch.WordTrace]
  refine ⟨27398286922304271784157263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146124196918956116182172069 27398286922304271784157263)
  ·
    refine ⟨41097430383456407676235895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27398286922304271784157263 41097430383456407676235895)
    ·
      refine ⟨61646145575184611514353843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41097430383456407676235895 61646145575184611514353843)
      ·
        refine ⟨92469218362776917271530765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61646145575184611514353843 92469218362776917271530765)
        ·
          refine ⟨34675956886041343976824037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92469218362776917271530765 34675956886041343976824037)
          ·
            refine ⟨6501741916132751995654507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34675956886041343976824037 6501741916132751995654507)
            ·
              refine ⟨9752612874199127993481761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6501741916132751995654507 9752612874199127993481761)
              ·
                refine ⟨7314459655649345995111321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9752612874199127993481761 7314459655649345995111321)
                ·
                  refine ⟨5485844741737009496333491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7314459655649345995111321 5485844741737009496333491)
                  ·
                    refine ⟨8228767112605514244500237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5485844741737009496333491 8228767112605514244500237)
                    ·
                      refine ⟨3085787667227067841687589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8228767112605514244500237 3085787667227067841687589)
                      ·
                        rfl

theorem cell23_6009550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 2, 2, 1, 3].length) (baseStart_6009550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6009550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6009550 prefixEnd_6009550 := by exact prefixLift 6009550
  have htrace : WordTrace (prefixWord ++ tailWord_6009550) baseStart_6009550 baseEnd_6009550 := by
    simpa [prefixWord, tailWord_6009550, baseEnd_6009550] using wordTrace_append hprefix tailTrace_6009550
  have hstable : (prefixWord ++ tailWord_6009550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6009550).length < 2 ^ (prefixWord ++ tailWord_6009550).sum := by decide
  have hdescent : baseEnd_6009550 < baseStart_6009550 := by decide
  rcases family_descends (prefixWord ++ tailWord_6009550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6009573 : List Nat := [1, 3, 1, 4, 1, 2, 3, 1, 1, 4, 2]
def baseStart_6009573 : Nat := 118140960795 + 6009573 * 2 ^ 59
def prefixEnd_6009573 : Nat := 4983230072969 + 3 ^ 40 * 6009573 * 2
def baseEnd_6009573 : Nat := 3085799477282121251699983

theorem tailTrace_6009573 : CollatzResearch.WordTrace tailWord_6009573 prefixEnd_6009573 3085799477282121251699983 := by
  unfold tailWord_6009573
  simp only [CollatzResearch.WordTrace]
  refine ⟨219187134257350849201345373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146124756171567232800896915 219187134257350849201345373)
  ·
    refine ⟨82195175346506568450504515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219187134257350849201345373 82195175346506568450504515)
    ·
      refine ⟨123292763019759852675756773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82195175346506568450504515 123292763019759852675756773)
      ·
        refine ⟨23117393066204972376704395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123292763019759852675756773 23117393066204972376704395)
        ·
          refine ⟨34676089599307458565056593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23117393066204972376704395 34676089599307458565056593)
          ·
            refine ⟨26007067199480593923792445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34676089599307458565056593 26007067199480593923792445)
            ·
              refine ⟨9752650199805222721422167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26007067199480593923792445 9752650199805222721422167)
              ·
                refine ⟨14628975299707834082133251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9752650199805222721422167 14628975299707834082133251)
                ·
                  refine ⟨21943462949561751123199877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14628975299707834082133251 21943462949561751123199877)
                  ·
                    refine ⟨4114399303042828335599977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21943462949561751123199877 4114399303042828335599977)
                    ·
                      refine ⟨3085799477282121251699983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4114399303042828335599977 3085799477282121251699983)
                      ·
                        rfl

theorem cell23_6009573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 1, 1, 4, 2].length) (baseStart_6009573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6009573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6009573 prefixEnd_6009573 := by exact prefixLift 6009573
  have htrace : WordTrace (prefixWord ++ tailWord_6009573) baseStart_6009573 baseEnd_6009573 := by
    simpa [prefixWord, tailWord_6009573, baseEnd_6009573] using wordTrace_append hprefix tailTrace_6009573
  have hstable : (prefixWord ++ tailWord_6009573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6009573).length < 2 ^ (prefixWord ++ tailWord_6009573).sum := by decide
  have hdescent : baseEnd_6009573 < baseStart_6009573 := by decide
  rcases family_descends (prefixWord ++ tailWord_6009573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6009609 : List Nat := [1, 2, 1, 1, 3, 2, 3, 1, 4, 5]
def baseStart_6009609 : Nat := 118140960795 + 6009609 * 2 ^ 59
def prefixEnd_6009609 : Nat := 4983230072969 + 3 ^ 40 * 6009609 * 2
def baseEnd_6009609 : Nat := 1028605987528561036949939

theorem tailTrace_6009609 : CollatzResearch.WordTrace tailWord_6009609 prefixEnd_6009609 1028605987528561036949939 := by
  unfold tailWord_6009609
  simp only [CollatzResearch.WordTrace]
  refine ⟨219188447285220427349655881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146125631523480284899770587 219188447285220427349655881)
  ·
    refine ⟨164391335463915320512241911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219188447285220427349655881 164391335463915320512241911)
    ·
      refine ⟨246587003195872980768362867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164391335463915320512241911 246587003195872980768362867)
      ·
        refine ⟨369880504793809471152544301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246587003195872980768362867 369880504793809471152544301)
        ·
          refine ⟨138705189297678551682204113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 369880504793809471152544301 138705189297678551682204113)
          ·
            refine ⟨104028891973258913761653085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138705189297678551682204113 104028891973258913761653085)
            ·
              refine ⟨39010834489972092660619907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104028891973258913761653085 39010834489972092660619907)
              ·
                refine ⟨58516251734958138990929861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39010834489972092660619907 58516251734958138990929861)
                ·
                  refine ⟨10971797200304651060799349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58516251734958138990929861 10971797200304651060799349)
                  ·
                    refine ⟨1028605987528561036949939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10971797200304651060799349 1028605987528561036949939)
                    ·
                      rfl

theorem cell23_6009609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 4, 5].length) (baseStart_6009609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6009609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6009609 prefixEnd_6009609 := by exact prefixLift 6009609
  have htrace : WordTrace (prefixWord ++ tailWord_6009609) baseStart_6009609 baseEnd_6009609 := by
    simpa [prefixWord, tailWord_6009609, baseEnd_6009609] using wordTrace_append hprefix tailTrace_6009609
  have hstable : (prefixWord ++ tailWord_6009609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6009609).length < 2 ^ (prefixWord ++ tailWord_6009609).sum := by decide
  have hdescent : baseEnd_6009609 < baseStart_6009609 := by decide
  rcases family_descends (prefixWord ++ tailWord_6009609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6009619 : List Nat := [1, 1, 1, 2, 1, 3, 5, 1, 1, 2, 5]
def baseStart_6009619 : Nat := 118140960795 + 6009619 * 2 ^ 59
def prefixEnd_6009619 : Nat := 4983230072969 + 3 ^ 40 * 6009619 * 2
def baseEnd_6009619 : Nat := 3085823097392228071724771

theorem tailTrace_6009619 : CollatzResearch.WordTrace tailWord_6009619 prefixEnd_6009619 3085823097392228071724771 := by
  unfold tailWord_6009619
  simp only [CollatzResearch.WordTrace]
  refine ⟨219188812015184199057519911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146125874676789466038346607 219188812015184199057519911)
  ·
    refine ⟨328783218022776298586279867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219188812015184199057519911 328783218022776298586279867)
    ·
      refine ⟨493174827034164447879419801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328783218022776298586279867 493174827034164447879419801)
      ·
        refine ⟨369881120275623335909564851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 493174827034164447879419801 369881120275623335909564851)
        ·
          refine ⟨554821680413435003864347277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 369881120275623335909564851 554821680413435003864347277)
          ·
            refine ⟨208058130155038126449130229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 554821680413435003864347277 208058130155038126449130229)
            ·
              refine ⟨19505449702034824354605959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 208058130155038126449130229 19505449702034824354605959)
              ·
                refine ⟨29258174553052236531908939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19505449702034824354605959 29258174553052236531908939)
                ·
                  refine ⟨43887261829578354797863409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29258174553052236531908939 43887261829578354797863409)
                  ·
                    refine ⟨32915446372183766098397557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43887261829578354797863409 32915446372183766098397557)
                    ·
                      refine ⟨3085823097392228071724771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32915446372183766098397557 3085823097392228071724771)
                      ·
                        rfl

theorem cell23_6009619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 2, 5].length) (baseStart_6009619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6009619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6009619 prefixEnd_6009619 := by exact prefixLift 6009619
  have htrace : WordTrace (prefixWord ++ tailWord_6009619) baseStart_6009619 baseEnd_6009619 := by
    simpa [prefixWord, tailWord_6009619, baseEnd_6009619] using wordTrace_append hprefix tailTrace_6009619
  have hstable : (prefixWord ++ tailWord_6009619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6009619).length < 2 ^ (prefixWord ++ tailWord_6009619).sum := by decide
  have hdescent : baseEnd_6009619 < baseStart_6009619 := by decide
  rcases family_descends (prefixWord ++ tailWord_6009619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6009700 : List Nat := [2, 3, 1, 1, 4, 3, 1, 1, 2, 2, 3]
def baseStart_6009700 : Nat := 118140960795 + 6009700 * 2 ^ 59
def prefixEnd_6009700 : Nat := 4983230072969 + 3 ^ 40 * 6009700 * 2
def baseEnd_6009700 : Nat := 3085864689325242254811899

theorem tailTrace_6009700 : CollatzResearch.WordTrace tailWord_6009700 prefixEnd_6009700 3085864689325242254811899 := by
  unfold tailWord_6009700
  simp only [CollatzResearch.WordTrace]
  refine ⟨109595883163945374945609277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146127844218593833260812369 109595883163945374945609277)
  ·
    refine ⟨41098456186479515604603479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109595883163945374945609277 41098456186479515604603479)
    ·
      refine ⟨61647684279719273406905219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41098456186479515604603479 61647684279719273406905219)
      ·
        refine ⟨92471526419578910110357829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61647684279719273406905219 92471526419578910110357829)
        ·
          refine ⟨17338411203671045645692093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92471526419578910110357829 17338411203671045645692093)
          ·
            refine ⟨6501904201376642117134535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17338411203671045645692093 6501904201376642117134535)
            ·
              refine ⟨9752856302064963175701803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6501904201376642117134535 9752856302064963175701803)
              ·
                refine ⟨14629284453097444763552705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9752856302064963175701803 14629284453097444763552705)
                ·
                  refine ⟨10971963339823083572664529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14629284453097444763552705 10971963339823083572664529)
                  ·
                    refine ⟨8228972504867312679498397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10971963339823083572664529 8228972504867312679498397)
                    ·
                      refine ⟨3085864689325242254811899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8228972504867312679498397 3085864689325242254811899)
                      ·
                        rfl

theorem cell23_6009700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 1, 2, 2, 3].length) (baseStart_6009700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6009700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6009700 prefixEnd_6009700 := by exact prefixLift 6009700
  have htrace : WordTrace (prefixWord ++ tailWord_6009700) baseStart_6009700 baseEnd_6009700 := by
    simpa [prefixWord, tailWord_6009700, baseEnd_6009700] using wordTrace_append hprefix tailTrace_6009700
  have hstable : (prefixWord ++ tailWord_6009700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6009700).length < 2 ^ (prefixWord ++ tailWord_6009700).sum := by decide
  have hdescent : baseEnd_6009700 < baseStart_6009700 := by decide
  rcases family_descends (prefixWord ++ tailWord_6009700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6009723 : List Nat := [1, 1, 1, 1, 1, 5, 2, 4, 2, 3, 2]
def baseStart_6009723 : Nat := 118140960795 + 6009723 * 2 ^ 59
def prefixEnd_6009723 : Nat := 4983230072969 + 3 ^ 40 * 6009723 * 2
def baseEnd_6009723 : Nat := 3085876499380295664824293

theorem tailTrace_6009723 : CollatzResearch.WordTrace tailWord_6009723 prefixEnd_6009723 3085876499380295664824293 := by
  unfold tailWord_6009723
  simp only [CollatzResearch.WordTrace]
  refine ⟨219192605206807424819305823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146128403471204949879537215 219192605206807424819305823)
  ·
    refine ⟨328788907810211137228958735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219192605206807424819305823 328788907810211137228958735)
    ·
      refine ⟨493183361715316705843438103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328788907810211137228958735 493183361715316705843438103)
      ·
        refine ⟨739775042572975058765157155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 493183361715316705843438103 739775042572975058765157155)
        ·
          refine ⟨1109662563859462588147735733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 739775042572975058765157155 1109662563859462588147735733)
          ·
            refine ⟨104030865361824617638850225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1109662563859462588147735733 104030865361824617638850225)
            ·
              refine ⟨78023149021368463229137669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104030865361824617638850225 78023149021368463229137669)
              ·
                refine ⟨14629340441506586855463313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78023149021368463229137669 14629340441506586855463313)
                ·
                  refine ⟨10972005331129940141597485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14629340441506586855463313 10972005331129940141597485)
                  ·
                    refine ⟨4114501999173727553099057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10972005331129940141597485 4114501999173727553099057)
                    ·
                      refine ⟨3085876499380295664824293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4114501999173727553099057 3085876499380295664824293)
                      ·
                        rfl

theorem cell23_6009723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 4, 2, 3, 2].length) (baseStart_6009723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6009723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6009723 prefixEnd_6009723 := by exact prefixLift 6009723
  have htrace : WordTrace (prefixWord ++ tailWord_6009723) baseStart_6009723 baseEnd_6009723 := by
    simpa [prefixWord, tailWord_6009723, baseEnd_6009723] using wordTrace_append hprefix tailTrace_6009723
  have hstable : (prefixWord ++ tailWord_6009723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6009723).length < 2 ^ (prefixWord ++ tailWord_6009723).sum := by decide
  have hdescent : baseEnd_6009723 < baseStart_6009723 := by decide
  rcases family_descends (prefixWord ++ tailWord_6009723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6009838 : List Nat := [4, 1, 2, 1, 4, 2, 2, 2, 1, 2, 2]
def baseStart_6009838 : Nat := 118140960795 + 6009838 * 2 ^ 59
def prefixEnd_6009838 : Nat := 4983230072969 + 3 ^ 40 * 6009838 * 2
def baseEnd_6009838 : Nat := 3085935549655562714886265

theorem tailTrace_6009838 : CollatzResearch.WordTrace tailWord_6009838 prefixEnd_6009838 3085935549655562714886265 := by
  unfold tailWord_6009838
  simp only [CollatzResearch.WordTrace]
  refine ⟨27399599950173849932467771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146131199734260532973161445 27399599950173849932467771)
  ·
    refine ⟨41099399925260774898701657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27399599950173849932467771 41099399925260774898701657)
    ·
      refine ⟨30824549943945581174026243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41099399925260774898701657 30824549943945581174026243)
      ·
        refine ⟨46236824915918371761039365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30824549943945581174026243 46236824915918371761039365)
        ·
          refine ⟨8669404671734694705194881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46236824915918371761039365 8669404671734694705194881)
          ·
            refine ⟨6502053503801021028896161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8669404671734694705194881 6502053503801021028896161)
            ·
              refine ⟨4876540127850765771672121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6502053503801021028896161 4876540127850765771672121)
              ·
                refine ⟨3657405095888074328754091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4876540127850765771672121 3657405095888074328754091)
                ·
                  refine ⟨5486107643832111493131137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3657405095888074328754091 5486107643832111493131137)
                  ·
                    refine ⟨4114580732874083619848353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5486107643832111493131137 4114580732874083619848353)
                    ·
                      refine ⟨3085935549655562714886265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4114580732874083619848353 3085935549655562714886265)
                      ·
                        rfl

theorem cell23_6009838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 2, 2, 1, 2, 2].length) (baseStart_6009838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6009838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6009838 prefixEnd_6009838 := by exact prefixLift 6009838
  have htrace : WordTrace (prefixWord ++ tailWord_6009838) baseStart_6009838 baseEnd_6009838 := by
    simpa [prefixWord, tailWord_6009838, baseEnd_6009838] using wordTrace_append hprefix tailTrace_6009838
  have hstable : (prefixWord ++ tailWord_6009838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6009838).length < 2 ^ (prefixWord ++ tailWord_6009838).sum := by decide
  have hdescent : baseEnd_6009838 < baseStart_6009838 := by decide
  rcases family_descends (prefixWord ++ tailWord_6009838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6009863 : List Nat := [1, 1, 4, 3, 1, 1, 1, 2, 2, 4, 3]
def baseStart_6009863 : Nat := 118140960795 + 6009863 * 2 ^ 59
def prefixEnd_6009863 : Nat := 4983230072969 + 3 ^ 40 * 6009863 * 2
def baseEnd_6009863 : Nat := 3085948386671925117073649

theorem tailTrace_6009863 : CollatzResearch.WordTrace tailWord_6009863 prefixEnd_6009863 3085948386671925117073649 := by
  unfold tailWord_6009863
  simp only [CollatzResearch.WordTrace]
  refine ⟨219197711426300228729402243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146131807617533485819601495 219197711426300228729402243)
  ·
    refine ⟨328796567139450343094103365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219197711426300228729402243 328796567139450343094103365)
    ·
      refine ⟨61649356338646939330144381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 328796567139450343094103365 61649356338646939330144381)
      ·
        refine ⟨23118508626992602248804143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61649356338646939330144381 23118508626992602248804143)
        ·
          refine ⟨34677762940488903373206215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23118508626992602248804143 34677762940488903373206215)
          ·
            refine ⟨52016644410733355059809323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34677762940488903373206215 52016644410733355059809323)
            ·
              refine ⟨78024966616100032589713985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52016644410733355059809323 78024966616100032589713985)
              ·
                refine ⟨58518724962075024442285489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78024966616100032589713985 58518724962075024442285489)
                ·
                  refine ⟨43889043721556268331714117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58518724962075024442285489 43889043721556268331714117)
                  ·
                    refine ⟨8229195697791800312196397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43889043721556268331714117 8229195697791800312196397)
                    ·
                      refine ⟨3085948386671925117073649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8229195697791800312196397 3085948386671925117073649)
                      ·
                        rfl

theorem cell23_6009863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_6009863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6009863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6009863 prefixEnd_6009863 := by exact prefixLift 6009863
  have htrace : WordTrace (prefixWord ++ tailWord_6009863) baseStart_6009863 baseEnd_6009863 := by
    simpa [prefixWord, tailWord_6009863, baseEnd_6009863] using wordTrace_append hprefix tailTrace_6009863
  have hstable : (prefixWord ++ tailWord_6009863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6009863).length < 2 ^ (prefixWord ++ tailWord_6009863).sum := by decide
  have hdescent : baseEnd_6009863 < baseStart_6009863 := by decide
  rcases family_descends (prefixWord ++ tailWord_6009863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6009893 : List Nat := [1, 3, 1, 2, 2, 2, 1, 1, 4, 3, 3]
def baseStart_6009893 : Nat := 118140960795 + 6009893 * 2 ^ 59
def prefixEnd_6009893 : Nat := 4983230072969 + 3 ^ 40 * 6009893 * 2
def baseEnd_6009893 : Nat := 3085963791091559999698511

theorem tailTrace_6009893 : CollatzResearch.WordTrace tailWord_6009893 prefixEnd_6009893 3085963791091559999698511 := by
  unfold tailWord_6009893
  simp only [CollatzResearch.WordTrace]
  refine ⟨219198805616191543852994333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146132537077461029235329555 219198805616191543852994333)
  ·
    refine ⟨82199552106071828944872875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219198805616191543852994333 82199552106071828944872875)
    ·
      refine ⟨123299328159107743417309313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82199552106071828944872875 123299328159107743417309313)
      ·
        refine ⟨92474496119330807562981985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123299328159107743417309313 92474496119330807562981985)
        ·
          refine ⟨69355872089498105672236489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92474496119330807562981985 69355872089498105672236489)
          ·
            refine ⟨52016904067123579254177367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69355872089498105672236489 52016904067123579254177367)
            ·
              refine ⟨78025356100685368881266051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52016904067123579254177367 78025356100685368881266051)
              ·
                refine ⟨117038034151028053321899077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78025356100685368881266051 117038034151028053321899077)
                ·
                  refine ⟨21944631403317759997856077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 117038034151028053321899077 21944631403317759997856077)
                  ·
                    refine ⟨8229236776244159999196029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21944631403317759997856077 8229236776244159999196029)
                    ·
                      refine ⟨3085963791091559999698511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8229236776244159999196029 3085963791091559999698511)
                      ·
                        rfl

theorem cell23_6009893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 4, 3, 3].length) (baseStart_6009893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6009893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6009893 prefixEnd_6009893 := by exact prefixLift 6009893
  have htrace : WordTrace (prefixWord ++ tailWord_6009893) baseStart_6009893 baseEnd_6009893 := by
    simpa [prefixWord, tailWord_6009893, baseEnd_6009893] using wordTrace_append hprefix tailTrace_6009893
  have hstable : (prefixWord ++ tailWord_6009893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6009893).length < 2 ^ (prefixWord ++ tailWord_6009893).sum := by decide
  have hdescent : baseEnd_6009893 < baseStart_6009893 := by decide
  rcases family_descends (prefixWord ++ tailWord_6009893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6009913 : List Nat := [1, 2, 1, 5, 2, 1, 1, 2, 1, 7]
def baseStart_6009913 : Nat := 118140960795 + 6009913 * 2 ^ 59
def prefixEnd_6009913 : Nat := 4983230072969 + 3 ^ 40 * 6009913 * 2
def baseEnd_6009913 : Nat := 1028658020234883307149473

theorem tailTrace_6009913 : CollatzResearch.WordTrace tailWord_6009913 prefixEnd_6009913 1028658020234883307149473 := by
  unfold tailWord_6009913
  simp only [CollatzResearch.WordTrace]
  refine ⟨219199535076119087268722393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146133023384079391512481595 219199535076119087268722393)
  ·
    refine ⟨164399651307089315451541795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219199535076119087268722393 164399651307089315451541795)
    ·
      refine ⟨246599476960633973177312693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164399651307089315451541795 246599476960633973177312693)
      ·
        refine ⟨23118700965059434985373065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 246599476960633973177312693 23118700965059434985373065)
        ·
          refine ⟨17339025723794576239029799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23118700965059434985373065 17339025723794576239029799)
          ·
            refine ⟨26008538585691864358544699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17339025723794576239029799 26008538585691864358544699)
            ·
              refine ⟨39012807878537796537817049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26008538585691864358544699 39012807878537796537817049)
              ·
                refine ⟨29259605908903347403362787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39012807878537796537817049 29259605908903347403362787)
                ·
                  refine ⟨43889408863355021105044181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29259605908903347403362787 43889408863355021105044181)
                  ·
                    refine ⟨1028658020234883307149473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43889408863355021105044181 1028658020234883307149473)
                    ·
                      rfl

theorem cell23_6009913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 7].length) (baseStart_6009913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6009913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6009913 prefixEnd_6009913 := by exact prefixLift 6009913
  have htrace : WordTrace (prefixWord ++ tailWord_6009913) baseStart_6009913 baseEnd_6009913 := by
    simpa [prefixWord, tailWord_6009913, baseEnd_6009913] using wordTrace_append hprefix tailTrace_6009913
  have hstable : (prefixWord ++ tailWord_6009913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6009913).length < 2 ^ (prefixWord ++ tailWord_6009913).sum := by decide
  have hdescent : baseEnd_6009913 < baseStart_6009913 := by decide
  rcases family_descends (prefixWord ++ tailWord_6009913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6009970 : List Nat := [3, 2, 1, 2, 2, 1, 1, 2, 4, 2, 3]
def baseStart_6009970 : Nat := 118140960795 + 6009970 * 2 ^ 59
def prefixEnd_6009970 : Nat := 4983230072969 + 3 ^ 40 * 6009970 * 2
def baseEnd_6009970 : Nat := 3086003329101956198435657

theorem tailTrace_6009970 : CollatzResearch.WordTrace tailWord_6009970 prefixEnd_6009970 3086003329101956198435657 := by
  unfold tailWord_6009970
  simp only [CollatzResearch.WordTrace]
  refine ⟨54800403509228146500886841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146134409357941724002364909 54800403509228146500886841)
  ·
    refine ⟨41100302631921109875665131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54800403509228146500886841 41100302631921109875665131)
    ·
      refine ⟨61650453947881664813497697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41100302631921109875665131 61650453947881664813497697)
      ·
        refine ⟨46237840460911248610123273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61650453947881664813497697 46237840460911248610123273)
        ·
          refine ⟨34678380345683436457592455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46237840460911248610123273 34678380345683436457592455)
          ·
            refine ⟨52017570518525154686388683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34678380345683436457592455 52017570518525154686388683)
            ·
              refine ⟨78026355777787732029583025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52017570518525154686388683 78026355777787732029583025)
              ·
                refine ⟨58519766833340799022187269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78026355777787732029583025 58519766833340799022187269)
                ·
                  refine ⟨10972456281251399816660113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58519766833340799022187269 10972456281251399816660113)
                  ·
                    refine ⟨8229342210938549862495085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10972456281251399816660113 8229342210938549862495085)
                    ·
                      refine ⟨3086003329101956198435657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8229342210938549862495085 3086003329101956198435657)
                      ·
                        rfl

theorem cell23_6009970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 4, 2, 3].length) (baseStart_6009970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6009970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6009970 prefixEnd_6009970 := by exact prefixLift 6009970
  have htrace : WordTrace (prefixWord ++ tailWord_6009970) baseStart_6009970 baseEnd_6009970 := by
    simpa [prefixWord, tailWord_6009970, baseEnd_6009970] using wordTrace_append hprefix tailTrace_6009970
  have hstable : (prefixWord ++ tailWord_6009970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6009970).length < 2 ^ (prefixWord ++ tailWord_6009970).sum := by decide
  have hdescent : baseEnd_6009970 < baseStart_6009970 := by decide
  rcases family_descends (prefixWord ++ tailWord_6009970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6010000 : List Nat := [2, 1, 1, 1, 1, 1, 4, 1, 7, 1, 3]
def baseStart_6010000 : Nat := 118140960795 + 6010000 * 2 ^ 59
def prefixEnd_6010000 : Nat := 4983230072969 + 3 ^ 40 * 6010000 * 2
def baseEnd_6010000 : Nat := 3086018733521591081060519

theorem tailTrace_6010000 : CollatzResearch.WordTrace tailWord_6010000 prefixEnd_6010000 3086018733521591081060519 := by
  unfold tailWord_6010000
  simp only [CollatzResearch.WordTrace]
  refine ⟨109601354113401950563569727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146135138817869267418092969 109601354113401950563569727)
  ·
    refine ⟨164402031170102925845354591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109601354113401950563569727 164402031170102925845354591)
    ·
      refine ⟨246603046755154388768031887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164402031170102925845354591 246603046755154388768031887)
      ·
        refine ⟨369904570132731583152047831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246603046755154388768031887 369904570132731583152047831)
        ·
          refine ⟨554856855199097374728071747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 369904570132731583152047831 554856855199097374728071747)
          ·
            refine ⟨832285282798646062092107621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 554856855199097374728071747 832285282798646062092107621)
            ·
              refine ⟨156053490524746136642270179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 832285282798646062092107621 156053490524746136642270179)
              ·
                refine ⟨234080235787119204963405269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156053490524746136642270179 234080235787119204963405269)
                ·
                  refine ⟨5486255526260606366329811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 234080235787119204963405269 5486255526260606366329811)
                  ·
                    refine ⟨8229383289390909549494717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5486255526260606366329811 8229383289390909549494717)
                    ·
                      refine ⟨3086018733521591081060519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8229383289390909549494717 3086018733521591081060519)
                      ·
                        rfl

theorem cell23_6010000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 7, 1, 3].length) (baseStart_6010000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6010000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6010000 prefixEnd_6010000 := by exact prefixLift 6010000
  have htrace : WordTrace (prefixWord ++ tailWord_6010000) baseStart_6010000 baseEnd_6010000 := by
    simpa [prefixWord, tailWord_6010000, baseEnd_6010000] using wordTrace_append hprefix tailTrace_6010000
  have hstable : (prefixWord ++ tailWord_6010000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6010000).length < 2 ^ (prefixWord ++ tailWord_6010000).sum := by decide
  have hdescent : baseEnd_6010000 < baseStart_6010000 := by decide
  rcases family_descends (prefixWord ++ tailWord_6010000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6010017 : List Nat := [1, 2, 3, 3, 1, 1, 2, 3, 3, 1, 3]
def baseStart_6010017 : Nat := 118140960795 + 6010017 * 2 ^ 59
def prefixEnd_6010017 : Nat := 4983230072969 + 3 ^ 40 * 6010017 * 2
def baseEnd_6010017 : Nat := 3086027462692717514547941

theorem tailTrace_6010017 : CollatzResearch.WordTrace tailWord_6010017 prefixEnd_6010017 3086027462692717514547941 := by
  unfold tailWord_6010017
  simp only [CollatzResearch.WordTrace]
  refine ⟨219203328267742313030508305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146135552178494875353672203 219203328267742313030508305)
  ·
    refine ⟨164402496200806734772881229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219203328267742313030508305 164402496200806734772881229)
    ·
      refine ⟨61650936075302525539830461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164402496200806734772881229 61650936075302525539830461)
      ·
        refine ⟨23119101028238447077436423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61650936075302525539830461 23119101028238447077436423)
        ·
          refine ⟨34678651542357670616154635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23119101028238447077436423 34678651542357670616154635)
          ·
            refine ⟨52017977313536505924231953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34678651542357670616154635 52017977313536505924231953)
            ·
              refine ⟨39013482985152379443173965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52017977313536505924231953 39013482985152379443173965)
              ·
                refine ⟨14630056119432142291190237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39013482985152379443173965 14630056119432142291190237)
                ·
                  refine ⟨5486271044787053359196339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14630056119432142291190237 5486271044787053359196339)
                  ·
                    refine ⟨8229406567180580038794509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5486271044787053359196339 8229406567180580038794509)
                    ·
                      refine ⟨3086027462692717514547941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8229406567180580038794509 3086027462692717514547941)
                      ·
                        rfl

theorem cell23_6010017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_6010017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6010017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6010017 prefixEnd_6010017 := by exact prefixLift 6010017
  have htrace : WordTrace (prefixWord ++ tailWord_6010017) baseStart_6010017 baseEnd_6010017 := by
    simpa [prefixWord, tailWord_6010017, baseEnd_6010017] using wordTrace_append hprefix tailTrace_6010017
  have hstable : (prefixWord ++ tailWord_6010017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6010017).length < 2 ^ (prefixWord ++ tailWord_6010017).sum := by decide
  have hdescent : baseEnd_6010017 < baseStart_6010017 := by decide
  rcases family_descends (prefixWord ++ tailWord_6010017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6010020 : List Nat := [2, 3, 1, 2, 3, 1, 1, 2, 3, 5]
def baseStart_6010020 : Nat := 118140960795 + 6010020 * 2 ^ 59
def prefixEnd_6010020 : Nat := 4983230072969 + 3 ^ 40 * 6010020 * 2
def baseEnd_6010020 : Nat := 1028676334378227000936809

theorem tailTrace_6010020 : CollatzResearch.WordTrace tailWord_6010020 prefixEnd_6010020 1028676334378227000936809 := by
  unfold tailWord_6010020
  simp only [CollatzResearch.WordTrace]
  refine ⟨109601718843365722271433757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146135625124487629695245009 109601718843365722271433757)
  ·
    refine ⟨41100644566262145851787659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109601718843365722271433757 41100644566262145851787659)
    ·
      refine ⟨61650966849393218777681489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41100644566262145851787659 61650966849393218777681489)
      ·
        refine ⟨46238225137044914083261117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61650966849393218777681489 46238225137044914083261117)
        ·
          refine ⟨17339334426391842781222919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46238225137044914083261117 17339334426391842781222919)
          ·
            refine ⟨26009001639587764171834379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17339334426391842781222919 26009001639587764171834379)
            ·
              refine ⟨39013502459381646257751569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26009001639587764171834379 39013502459381646257751569)
              ·
                refine ⟨29260126844536234693313677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39013502459381646257751569 29260126844536234693313677)
                ·
                  refine ⟨10972547566701088009992629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29260126844536234693313677 10972547566701088009992629)
                  ·
                    refine ⟨1028676334378227000936809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10972547566701088009992629 1028676334378227000936809)
                    ·
                      rfl

theorem cell23_6010020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 3, 5].length) (baseStart_6010020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6010020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6010020 prefixEnd_6010020 := by exact prefixLift 6010020
  have htrace : WordTrace (prefixWord ++ tailWord_6010020) baseStart_6010020 baseEnd_6010020 := by
    simpa [prefixWord, tailWord_6010020, baseEnd_6010020] using wordTrace_append hprefix tailTrace_6010020
  have hstable : (prefixWord ++ tailWord_6010020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6010020).length < 2 ^ (prefixWord ++ tailWord_6010020).sum := by decide
  have hdescent : baseEnd_6010020 < baseStart_6010020 := by decide
  rcases family_descends (prefixWord ++ tailWord_6010020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6010038 : List Nat := [5, 1, 3, 2, 1, 2, 1, 1, 2, 2, 3]
def baseStart_6010038 : Nat := 118140960795 + 6010038 * 2 ^ 59
def prefixEnd_6010038 : Nat := 4983230072969 + 3 ^ 40 * 6010038 * 2
def baseEnd_6010038 : Nat := 3086038245786461932385345

theorem tailTrace_6010038 : CollatzResearch.WordTrace tailWord_6010038 prefixEnd_6010038 3086038245786461932385345 := by
  unfold tailWord_6010038
  simp only [CollatzResearch.WordTrace]
  refine ⟨13700255887541639601063923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 146136062800444155744681845 13700255887541639601063923)
  ·
    refine ⟨20550383831312459401595885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13700255887541639601063923 20550383831312459401595885)
    ·
      refine ⟨7706393936742172275598457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20550383831312459401595885 7706393936742172275598457)
      ·
        refine ⟨5779795452556629206698843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7706393936742172275598457 5779795452556629206698843)
        ·
          refine ⟨8669693178834943810048265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5779795452556629206698843 8669693178834943810048265)
          ·
            refine ⟨6502269884126207857536199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8669693178834943810048265 6502269884126207857536199)
            ·
              refine ⟨9753404826189311786304299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6502269884126207857536199 9753404826189311786304299)
              ·
                refine ⟨14630107239283967679456449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9753404826189311786304299 14630107239283967679456449)
                ·
                  refine ⟨10972580429462975759592337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14630107239283967679456449 10972580429462975759592337)
                  ·
                    refine ⟨8229435322097231819694253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10972580429462975759592337 8229435322097231819694253)
                    ·
                      refine ⟨3086038245786461932385345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8229435322097231819694253 3086038245786461932385345)
                      ·
                        rfl

theorem cell23_6010038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_6010038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6010038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6010038 prefixEnd_6010038 := by exact prefixLift 6010038
  have htrace : WordTrace (prefixWord ++ tailWord_6010038) baseStart_6010038 baseEnd_6010038 := by
    simpa [prefixWord, tailWord_6010038, baseEnd_6010038] using wordTrace_append hprefix tailTrace_6010038
  have hstable : (prefixWord ++ tailWord_6010038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6010038).length < 2 ^ (prefixWord ++ tailWord_6010038).sum := by decide
  have hdescent : baseEnd_6010038 < baseStart_6010038 := by decide
  rcases family_descends (prefixWord ++ tailWord_6010038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
