import V185TrunkScan23Chunk1332

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7895395 : List Nat := [1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 7]
def baseStart_7895395 : Nat := 118140960795 + 7895395 * 2 ^ 59
def prefixEnd_7895395 : Nat := 4983230072969 + 3 ^ 40 * 7895395 * 2
def baseEnd_7895395 : Nat := 4054132592105241964452245

theorem tailTrace_7895395 : CollatzResearch.WordTrace tailWord_7895395 prefixEnd_7895395 4054132592105241964452245 := by
  unfold tailWord_7895395
  simp only [CollatzResearch.WordTrace]
  refine ⟨287968713231339815957423639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191979142154226543971615759 287968713231339815957423639)
  ·
    refine ⟨431953069847009723936135459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287968713231339815957423639 431953069847009723936135459)
    ·
      refine ⟨647929604770514585904203189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431953069847009723936135459 647929604770514585904203189)
      ·
        refine ⟨60743400447235742428519049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 647929604770514585904203189 60743400447235742428519049)
        ·
          refine ⟨45557550335426806821389287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60743400447235742428519049 45557550335426806821389287)
          ·
            refine ⟨68336325503140210232083931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45557550335426806821389287 68336325503140210232083931)
            ·
              refine ⟨102504488254710315348125897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68336325503140210232083931 102504488254710315348125897)
              ·
                refine ⟨76878366191032736511094423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102504488254710315348125897 76878366191032736511094423)
                ·
                  refine ⟨115317549286549104766641635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76878366191032736511094423 115317549286549104766641635)
                  ·
                    refine ⟨172976323929823657149962453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 115317549286549104766641635 172976323929823657149962453)
                    ·
                      refine ⟨4054132592105241964452245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 172976323929823657149962453 4054132592105241964452245)
                      ·
                        rfl

theorem cell23_7895395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_7895395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7895395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7895395 prefixEnd_7895395 := by exact prefixLift 7895395
  have htrace : WordTrace (prefixWord ++ tailWord_7895395) baseStart_7895395 baseEnd_7895395 := by
    simpa [prefixWord, tailWord_7895395, baseEnd_7895395] using wordTrace_append hprefix tailTrace_7895395
  have hstable : (prefixWord ++ tailWord_7895395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7895395).length < 2 ^ (prefixWord ++ tailWord_7895395).sum := by decide
  have hdescent : baseEnd_7895395 < baseStart_7895395 := by decide
  rcases family_descends (prefixWord ++ tailWord_7895395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7895445 : List Nat := [1, 3, 2, 1, 1, 2, 1, 2, 10]
def baseStart_7895445 : Nat := 118140960795 + 7895445 * 2 ^ 59
def prefixEnd_7895445 : Nat := 4983230072969 + 3 ^ 40 * 7895445 * 2
def baseEnd_7895445 : Nat := 450462029570885196536335

theorem tailTrace_7895445 : CollatzResearch.WordTrace tailWord_7895445 prefixEnd_7895445 450462029570885196536335 := by
  unfold tailWord_7895445
  simp only [CollatzResearch.WordTrace]
  refine ⟨287970536881158674496743789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191980357920772449664495859 287970536881158674496743789)
  ·
    refine ⟨107988951330434502936278921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287970536881158674496743789 107988951330434502936278921)
    ·
      refine ⟨80991713497825877202209191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107988951330434502936278921 80991713497825877202209191)
      ·
        refine ⟨121487570246738815803313787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80991713497825877202209191 121487570246738815803313787)
        ·
          refine ⟨182231355370108223704970681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121487570246738815803313787 182231355370108223704970681)
          ·
            refine ⟨136673516527581167778728011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182231355370108223704970681 136673516527581167778728011)
            ·
              refine ⟨205010274791371751668092017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136673516527581167778728011 205010274791371751668092017)
              ·
                refine ⟨153757706093528813751069013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205010274791371751668092017 153757706093528813751069013)
                ·
                  refine ⟨450462029570885196536335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 153757706093528813751069013 450462029570885196536335)
                  ·
                    rfl

theorem cell23_7895445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 10].length) (baseStart_7895445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7895445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7895445 prefixEnd_7895445 := by exact prefixLift 7895445
  have htrace : WordTrace (prefixWord ++ tailWord_7895445) baseStart_7895445 baseEnd_7895445 := by
    simpa [prefixWord, tailWord_7895445, baseEnd_7895445] using wordTrace_append hprefix tailTrace_7895445
  have hstable : (prefixWord ++ tailWord_7895445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7895445).length < 2 ^ (prefixWord ++ tailWord_7895445).sum := by decide
  have hdescent : baseEnd_7895445 < baseStart_7895445 := by decide
  rcases family_descends (prefixWord ++ tailWord_7895445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7895459 : List Nat := [1, 1, 1, 4, 1, 4, 3, 1, 2, 2, 3]
def baseStart_7895459 : Nat := 118140960795 + 7895459 * 2 ^ 59
def prefixEnd_7895459 : Nat := 4983230072969 + 3 ^ 40 * 7895459 * 2
def baseEnd_7895459 : Nat := 4054165454867129714051951

theorem tailTrace_7895459 : CollatzResearch.WordTrace tailWord_7895459 prefixEnd_7895459 4054165454867129714051951 := by
  unfold tailWord_7895459
  simp only [CollatzResearch.WordTrace]
  refine ⟨287971047503107954887753431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191980698335405303258502287 287971047503107954887753431)
  ·
    refine ⟨431956571254661932331630147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287971047503107954887753431 431956571254661932331630147)
    ·
      refine ⟨647934856881992898497445221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431956571254661932331630147 647934856881992898497445221)
      ·
        refine ⟨121487785665373668468270979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 647934856881992898497445221 121487785665373668468270979)
        ·
          refine ⟨182231678498060502702406469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121487785665373668468270979 182231678498060502702406469)
          ·
            refine ⟨34168439718386344256701213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 182231678498060502702406469 34168439718386344256701213)
            ·
              refine ⟨12813164894394879096262955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34168439718386344256701213 12813164894394879096262955)
              ·
                refine ⟨19219747341592318644394433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12813164894394879096262955 19219747341592318644394433)
                ·
                  refine ⟨14414810506194238983295825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19219747341592318644394433 14414810506194238983295825)
                  ·
                    refine ⟨10811107879645679237471869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14414810506194238983295825 10811107879645679237471869)
                    ·
                      refine ⟨4054165454867129714051951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10811107879645679237471869 4054165454867129714051951)
                      ·
                        rfl

theorem cell23_7895459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 1, 2, 2, 3].length) (baseStart_7895459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7895459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7895459 prefixEnd_7895459 := by exact prefixLift 7895459
  have htrace : WordTrace (prefixWord ++ tailWord_7895459) baseStart_7895459 baseEnd_7895459 := by
    simpa [prefixWord, tailWord_7895459, baseEnd_7895459] using wordTrace_append hprefix tailTrace_7895459
  have hstable : (prefixWord ++ tailWord_7895459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7895459).length < 2 ^ (prefixWord ++ tailWord_7895459).sum := by decide
  have hdescent : baseEnd_7895459 < baseStart_7895459 := by decide
  rcases family_descends (prefixWord ++ tailWord_7895459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7895465 : List Nat := [1, 2, 1, 1, 1, 1, 3, 2, 3, 2, 6]
def baseStart_7895465 : Nat := 118140960795 + 7895465 * 2 ^ 59
def prefixEnd_7895465 : Nat := 4983230072969 + 3 ^ 40 * 7895465 * 2
def baseEnd_7895465 : Nat := 4054168535751056690576923

theorem tailTrace_7895465 : CollatzResearch.WordTrace tailWord_7895465 prefixEnd_7895465 4054168535751056690576923 := by
  unfold tailWord_7895465
  simp only [CollatzResearch.WordTrace]
  refine ⟨287971266341086217912471849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191980844227390811941647899 287971266341086217912471849)
  ·
    refine ⟨215978449755814663434353887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287971266341086217912471849 215978449755814663434353887)
    ·
      refine ⟨323967674633721995151530831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215978449755814663434353887 323967674633721995151530831)
      ·
        refine ⟨485951511950582992727296247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323967674633721995151530831 485951511950582992727296247)
        ·
          refine ⟨728927267925874489090944371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 485951511950582992727296247 728927267925874489090944371)
          ·
            refine ⟨1093390901888811733636416557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 728927267925874489090944371 1093390901888811733636416557)
            ·
              refine ⟨410021588208304400113656209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1093390901888811733636416557 410021588208304400113656209)
              ·
                refine ⟨307516191156228300085242157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 410021588208304400113656209 307516191156228300085242157)
                ·
                  refine ⟨115318571683585612531965809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 307516191156228300085242157 115318571683585612531965809)
                  ·
                    refine ⟨86488928762689209398974357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 115318571683585612531965809 86488928762689209398974357)
                    ·
                      refine ⟨4054168535751056690576923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86488928762689209398974357 4054168535751056690576923)
                      ·
                        rfl

theorem cell23_7895465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 2, 6].length) (baseStart_7895465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7895465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7895465 prefixEnd_7895465 := by exact prefixLift 7895465
  have htrace : WordTrace (prefixWord ++ tailWord_7895465) baseStart_7895465 baseEnd_7895465 := by
    simpa [prefixWord, tailWord_7895465, baseEnd_7895465] using wordTrace_append hprefix tailTrace_7895465
  have hstable : (prefixWord ++ tailWord_7895465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7895465).length < 2 ^ (prefixWord ++ tailWord_7895465).sum := by decide
  have hdescent : baseEnd_7895465 < baseStart_7895465 := by decide
  rcases family_descends (prefixWord ++ tailWord_7895465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7895479 : List Nat := [1, 1, 3, 1, 3, 5, 1, 2, 6]
def baseStart_7895479 : Nat := 118140960795 + 7895479 * 2 ^ 59
def prefixEnd_7895479 : Nat := 4983230072969 + 3 ^ 40 * 7895479 * 2
def baseEnd_7895479 : Nat := 450463969386691070644651

theorem tailTrace_7895479 : CollatzResearch.WordTrace tailWord_7895479 prefixEnd_7895479 450463969386691070644651 := by
  unfold tailWord_7895479
  simp only [CollatzResearch.WordTrace]
  refine ⟨287971776963035498303481491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191981184642023665535654327 287971776963035498303481491)
  ·
    refine ⟨431957665444553247455222237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287971776963035498303481491 431957665444553247455222237)
    ·
      refine ⟨161984124541707467795708339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 431957665444553247455222237 161984124541707467795708339)
      ·
        refine ⟨242976186812561201693562509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161984124541707467795708339 242976186812561201693562509)
        ·
          refine ⟨91116070054710450635085941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 242976186812561201693562509 91116070054710450635085941)
          ·
            refine ⟨8542131567629104747039307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91116070054710450635085941 8542131567629104747039307)
            ·
              refine ⟨12813197351443657120558961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8542131567629104747039307 12813197351443657120558961)
              ·
                refine ⟨9609898013582742840419221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12813197351443657120558961 9609898013582742840419221)
                ·
                  refine ⟨450463969386691070644651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9609898013582742840419221 450463969386691070644651)
                  ·
                    rfl

theorem cell23_7895479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 2, 6].length) (baseStart_7895479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7895479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7895479 prefixEnd_7895479 := by exact prefixLift 7895479
  have htrace : WordTrace (prefixWord ++ tailWord_7895479) baseStart_7895479 baseEnd_7895479 := by
    simpa [prefixWord, tailWord_7895479, baseEnd_7895479] using wordTrace_append hprefix tailTrace_7895479
  have hstable : (prefixWord ++ tailWord_7895479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7895479).length < 2 ^ (prefixWord ++ tailWord_7895479).sum := by decide
  have hdescent : baseEnd_7895479 < baseStart_7895479 := by decide
  rcases family_descends (prefixWord ++ tailWord_7895479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7895509 : List Nat := [1, 3, 2, 3, 1, 2, 1, 4, 1, 5]
def baseStart_7895509 : Nat := 118140960795 + 7895509 * 2 ^ 59
def prefixEnd_7895509 : Nat := 4983230072969 + 3 ^ 40 * 7895509 * 2
def baseEnd_7895509 : Nat := 1351397042966618172808907

theorem tailTrace_7895509 : CollatzResearch.WordTrace tailWord_7895509 prefixEnd_7895509 1351397042966618172808907 := by
  unfold tailWord_7895509
  simp only [CollatzResearch.WordTrace]
  refine ⟨287972871152926813427073581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191981914101951208951382387 287972871152926813427073581)
  ·
    refine ⟨107989826682347555035152593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287972871152926813427073581 107989826682347555035152593)
    ·
      refine ⟨80992370011760666276364445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107989826682347555035152593 80992370011760666276364445)
      ·
        refine ⟨30372138754410249853636667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80992370011760666276364445 30372138754410249853636667)
        ·
          refine ⟨45558208131615374780455001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30372138754410249853636667 45558208131615374780455001)
          ·
            refine ⟨34168656098711531085341251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45558208131615374780455001 34168656098711531085341251)
            ·
              refine ⟨51252984148067296628011877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34168656098711531085341251 51252984148067296628011877)
              ·
                refine ⟨9609934527762618117752227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51252984148067296628011877 9609934527762618117752227)
                ·
                  refine ⟨14414901791643927176628341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9609934527762618117752227 14414901791643927176628341)
                  ·
                    refine ⟨1351397042966618172808907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14414901791643927176628341 1351397042966618172808907)
                    ·
                      rfl

theorem cell23_7895509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 4, 1, 5].length) (baseStart_7895509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7895509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7895509 prefixEnd_7895509 := by exact prefixLift 7895509
  have htrace : WordTrace (prefixWord ++ tailWord_7895509) baseStart_7895509 baseEnd_7895509 := by
    simpa [prefixWord, tailWord_7895509, baseEnd_7895509] using wordTrace_append hprefix tailTrace_7895509
  have hstable : (prefixWord ++ tailWord_7895509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7895509).length < 2 ^ (prefixWord ++ tailWord_7895509).sum := by decide
  have hdescent : baseEnd_7895509 < baseStart_7895509 := by decide
  rcases family_descends (prefixWord ++ tailWord_7895509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7895533 : List Nat := [1, 5, 1, 3, 1, 2, 1, 2, 2, 3, 2]
def baseStart_7895533 : Nat := 118140960795 + 7895533 * 2 ^ 59
def prefixEnd_7895533 : Nat := 4983230072969 + 3 ^ 40 * 7895533 * 2
def baseEnd_7895533 : Nat := 4054203452435562424526611

theorem tailTrace_7895533 : CollatzResearch.WordTrace tailWord_7895533 prefixEnd_7895533 4054203452435562424526611 := by
  unfold tailWord_7895533
  simp only [CollatzResearch.WordTrace]
  refine ⟨287973746504839865525947253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191982497669893243683964835 287973746504839865525947253)
  ·
    refine ⟨26997538734828737393057555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 287973746504839865525947253 26997538734828737393057555)
    ·
      refine ⟨40496308102243106089586333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26997538734828737393057555 40496308102243106089586333)
      ·
        refine ⟨15186115538341164783594875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40496308102243106089586333 15186115538341164783594875)
        ·
          refine ⟨22779173307511747175392313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15186115538341164783594875 22779173307511747175392313)
          ·
            refine ⟨17084379980633810381544235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22779173307511747175392313 17084379980633810381544235)
            ·
              refine ⟨25626569970950715572316353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17084379980633810381544235 25626569970950715572316353)
              ·
                refine ⟨19219927478213036679237265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25626569970950715572316353 19219927478213036679237265)
                ·
                  refine ⟨14414945608659777509427949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19219927478213036679237265 14414945608659777509427949)
                  ·
                    refine ⟨5405604603247416566035481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14414945608659777509427949 5405604603247416566035481)
                    ·
                      refine ⟨4054203452435562424526611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5405604603247416566035481 4054203452435562424526611)
                      ·
                        rfl

theorem cell23_7895533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_7895533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7895533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7895533 prefixEnd_7895533 := by exact prefixLift 7895533
  have htrace : WordTrace (prefixWord ++ tailWord_7895533) baseStart_7895533 baseEnd_7895533 := by
    simpa [prefixWord, tailWord_7895533, baseEnd_7895533] using wordTrace_append hprefix tailTrace_7895533
  have hstable : (prefixWord ++ tailWord_7895533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7895533).length < 2 ^ (prefixWord ++ tailWord_7895533).sum := by decide
  have hdescent : baseEnd_7895533 < baseStart_7895533 := by decide
  rcases family_descends (prefixWord ++ tailWord_7895533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7895539 : List Nat := [1, 1, 1, 2, 2, 2, 4, 4, 2, 4]
def baseStart_7895539 : Nat := 118140960795 + 7895539 * 2 ^ 59
def prefixEnd_7895539 : Nat := 4983230072969 + 3 ^ 40 * 7895539 * 2
def baseEnd_7895539 : Nat := 1351402177773163133683861

theorem tailTrace_7895539 : CollatzResearch.WordTrace tailWord_7895539 prefixEnd_7895539 1351402177773163133683861 := by
  unfold tailWord_7895539
  simp only [CollatzResearch.WordTrace]
  refine ⟨287973965342818128550665671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191982643561878752367110447 287973965342818128550665671)
  ·
    refine ⟨431960948014227192825998507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287973965342818128550665671 431960948014227192825998507)
    ·
      refine ⟨647941422021340789238997761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431960948014227192825998507 647941422021340789238997761)
      ·
        refine ⟨485956066516005591929248321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 647941422021340789238997761 485956066516005591929248321)
        ·
          refine ⟨364467049887004193946936241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 485956066516005591929248321 364467049887004193946936241)
          ·
            refine ⟨273350287415253145460202181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 364467049887004193946936241 273350287415253145460202181)
            ·
              refine ⟨51253178890359964773787909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 273350287415253145460202181 51253178890359964773787909)
              ·
                refine ⟨9609971041942493395085233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51253178890359964773787909 9609971041942493395085233)
                ·
                  refine ⟨7207478281456870046313925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9609971041942493395085233 7207478281456870046313925)
                  ·
                    refine ⟨1351402177773163133683861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7207478281456870046313925 1351402177773163133683861)
                    ·
                      rfl

theorem cell23_7895539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 4, 2, 4].length) (baseStart_7895539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7895539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7895539 prefixEnd_7895539 := by exact prefixLift 7895539
  have htrace : WordTrace (prefixWord ++ tailWord_7895539) baseStart_7895539 baseEnd_7895539 := by
    simpa [prefixWord, tailWord_7895539, baseEnd_7895539] using wordTrace_append hprefix tailTrace_7895539
  have hstable : (prefixWord ++ tailWord_7895539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7895539).length < 2 ^ (prefixWord ++ tailWord_7895539).sum := by decide
  have hdescent : baseEnd_7895539 < baseStart_7895539 := by decide
  rcases family_descends (prefixWord ++ tailWord_7895539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7895546 : List Nat := [3, 1, 1, 1, 1, 2, 2, 5, 3, 2, 2]
def baseStart_7895546 : Nat := 118140960795 + 7895546 * 2 ^ 59
def prefixEnd_7895546 : Nat := 4983230072969 + 3 ^ 40 * 7895546 * 2
def baseEnd_7895546 : Nat := 4054210127684070873664051

theorem tailTrace_7895546 : CollatzResearch.WordTrace tailWord_7895546 prefixEnd_7895546 4054210127684070873664051 := by
  unfold tailWord_7895546
  simp only [CollatzResearch.WordTrace]
  refine ⟨71993555163448192186542623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191982813769195179164113661 71993555163448192186542623)
  ·
    refine ⟨107990332745172288279813935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71993555163448192186542623 107990332745172288279813935)
    ·
      refine ⟨161985499117758432419720903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107990332745172288279813935 161985499117758432419720903)
      ·
        refine ⟨242978248676637648629581355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161985499117758432419720903 242978248676637648629581355)
        ·
          refine ⟨364467373014956472944372033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242978248676637648629581355 364467373014956472944372033)
          ·
            refine ⟨273350529761217354708279025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 364467373014956472944372033 273350529761217354708279025)
            ·
              refine ⟨205012897320913016031209269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273350529761217354708279025 205012897320913016031209269)
              ·
                refine ⟨19219959123835595252925869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 205012897320913016031209269 19219959123835595252925869)
                ·
                  refine ⟨7207484671438348219847201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19219959123835595252925869 7207484671438348219847201)
                  ·
                    refine ⟨5405613503578761164885401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7207484671438348219847201 5405613503578761164885401)
                    ·
                      refine ⟨4054210127684070873664051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5405613503578761164885401 4054210127684070873664051)
                      ·
                        rfl

theorem cell23_7895546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 5, 3, 2, 2].length) (baseStart_7895546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7895546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7895546 prefixEnd_7895546 := by exact prefixLift 7895546
  have htrace : WordTrace (prefixWord ++ tailWord_7895546) baseStart_7895546 baseEnd_7895546 := by
    simpa [prefixWord, tailWord_7895546, baseEnd_7895546] using wordTrace_append hprefix tailTrace_7895546
  have hstable : (prefixWord ++ tailWord_7895546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7895546).length < 2 ^ (prefixWord ++ tailWord_7895546).sum := by decide
  have hdescent : baseEnd_7895546 < baseStart_7895546 := by decide
  rcases family_descends (prefixWord ++ tailWord_7895546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7895549 : List Nat := [1, 4, 1, 1, 1, 3, 2, 2, 3, 2, 3]
def baseStart_7895549 : Nat := 118140960795 + 7895549 * 2 ^ 59
def prefixEnd_7895549 : Nat := 4983230072969 + 3 ^ 40 * 7895549 * 2
def baseEnd_7895549 : Nat := 4054211668126034361926537

theorem tailTrace_7895549 : CollatzResearch.WordTrace tailWord_7895549 prefixEnd_7895549 4054211668126034361926537 := by
  unfold tailWord_7895549
  simp only [CollatzResearch.WordTrace]
  refine ⟨287974330072781900258529701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191982886715187933505686467 287974330072781900258529701)
  ·
    refine ⟨53995186888646606298474319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 287974330072781900258529701 53995186888646606298474319)
    ·
      refine ⟨80992780332969909447711479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53995186888646606298474319 80992780332969909447711479)
      ·
        refine ⟨121489170499454864171567219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80992780332969909447711479 121489170499454864171567219)
        ·
          refine ⟨182233755749182296257350829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121489170499454864171567219 182233755749182296257350829)
          ·
            refine ⟨68337658405943361096506561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182233755749182296257350829 68337658405943361096506561)
            ·
              refine ⟨51253243804457520822379921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68337658405943361096506561 51253243804457520822379921)
              ·
                refine ⟨38439932853343140616784941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51253243804457520822379921 38439932853343140616784941)
                ·
                  refine ⟨14414974820003677731294353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38439932853343140616784941 14414974820003677731294353)
                  ·
                    refine ⟨10811231115002758298470765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14414974820003677731294353 10811231115002758298470765)
                    ·
                      refine ⟨4054211668126034361926537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10811231115002758298470765 4054211668126034361926537)
                      ·
                        rfl

theorem cell23_7895549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 3, 2, 3].length) (baseStart_7895549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7895549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7895549 prefixEnd_7895549 := by exact prefixLift 7895549
  have htrace : WordTrace (prefixWord ++ tailWord_7895549) baseStart_7895549 baseEnd_7895549 := by
    simpa [prefixWord, tailWord_7895549, baseEnd_7895549] using wordTrace_append hprefix tailTrace_7895549
  have hstable : (prefixWord ++ tailWord_7895549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7895549).length < 2 ^ (prefixWord ++ tailWord_7895549).sum := by decide
  have hdescent : baseEnd_7895549 < baseStart_7895549 := by decide
  rcases family_descends (prefixWord ++ tailWord_7895549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7895566 : List Nat := [4, 1, 1, 2, 3, 2, 1, 1, 3, 2, 3]
def baseStart_7895566 : Nat := 118140960795 + 7895566 * 2 ^ 59
def prefixEnd_7895566 : Nat := 4983230072969 + 3 ^ 40 * 7895566 * 2
def baseEnd_7895566 : Nat := 4054220397297160795413959

theorem tailTrace_7895566 : CollatzResearch.WordTrace tailWord_7895566 prefixEnd_7895566 4054220397297160795413959 := by
  unfold tailWord_7895566
  simp only [CollatzResearch.WordTrace]
  refine ⟨35996868764215039020237319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191983300075813541441265701 35996868764215039020237319)
  ·
    refine ⟨53995303146322558530355979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35996868764215039020237319 53995303146322558530355979)
    ·
      refine ⟨80992954719483837795533969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53995303146322558530355979 80992954719483837795533969)
      ·
        refine ⟨60744716039612878346650477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80992954719483837795533969 60744716039612878346650477)
        ·
          refine ⟨22779268514854829379993929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60744716039612878346650477 22779268514854829379993929)
          ·
            refine ⟨17084451386141122034995447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22779268514854829379993929 17084451386141122034995447)
            ·
              refine ⟨25626677079211683052493171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17084451386141122034995447 25626677079211683052493171)
              ·
                refine ⟨38440015618817524578739757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25626677079211683052493171 38440015618817524578739757)
                ·
                  refine ⟨14415005857056571717027409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38440015618817524578739757 14415005857056571717027409)
                  ·
                    refine ⟨10811254392792428787770557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14415005857056571717027409 10811254392792428787770557)
                    ·
                      refine ⟨4054220397297160795413959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10811254392792428787770557 4054220397297160795413959)
                      ·
                        rfl

theorem cell23_7895566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 3, 2, 3].length) (baseStart_7895566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7895566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7895566 prefixEnd_7895566 := by exact prefixLift 7895566
  have htrace : WordTrace (prefixWord ++ tailWord_7895566) baseStart_7895566 baseEnd_7895566 := by
    simpa [prefixWord, tailWord_7895566, baseEnd_7895566] using wordTrace_append hprefix tailTrace_7895566
  have hstable : (prefixWord ++ tailWord_7895566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7895566).length < 2 ^ (prefixWord ++ tailWord_7895566).sum := by decide
  have hdescent : baseEnd_7895566 < baseStart_7895566 := by decide
  rcases family_descends (prefixWord ++ tailWord_7895566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7895591 : List Nat := [1, 1, 7, 2, 2, 1, 2, 2, 1, 1, 3]
def baseStart_7895591 : Nat := 118140960795 + 7895591 * 2 ^ 59
def prefixEnd_7895591 : Nat := 4983230072969 + 3 ^ 40 * 7895591 * 2
def baseEnd_7895591 : Nat := 4054233234313523197601345

theorem tailTrace_7895591 : CollatzResearch.WordTrace tailWord_7895591 prefixEnd_7895591 4054233234313523197601345 := by
  unfold tailWord_7895591
  simp only [CollatzResearch.WordTrace]
  refine ⟨287975861938629741431558627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191983907959086494287705751 287975861938629741431558627)
  ·
    refine ⟨431963792907944612147337941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287975861938629741431558627 431963792907944612147337941)
    ·
      refine ⟨10124151396279951847203233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 431963792907944612147337941 10124151396279951847203233)
      ·
        refine ⟨7593113547209963885402425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10124151396279951847203233 7593113547209963885402425)
        ·
          refine ⟨5694835160407472914051819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7593113547209963885402425 5694835160407472914051819)
          ·
            refine ⟨8542252740611209371077729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5694835160407472914051819 8542252740611209371077729)
            ·
              refine ⟨6406689555458407028308297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8542252740611209371077729 6406689555458407028308297)
              ·
                refine ⟨4805017166593805271231223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6406689555458407028308297 4805017166593805271231223)
                ·
                  refine ⟨7207525749890707906846835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4805017166593805271231223 7207525749890707906846835)
                  ·
                    refine ⟨10811288624836061860270253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7207525749890707906846835 10811288624836061860270253)
                    ·
                      refine ⟨4054233234313523197601345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10811288624836061860270253 4054233234313523197601345)
                      ·
                        rfl

theorem cell23_7895591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_7895591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7895591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7895591 prefixEnd_7895591 := by exact prefixLift 7895591
  have htrace : WordTrace (prefixWord ++ tailWord_7895591) baseStart_7895591 baseEnd_7895591 := by
    simpa [prefixWord, tailWord_7895591, baseEnd_7895591] using wordTrace_append hprefix tailTrace_7895591
  have hstable : (prefixWord ++ tailWord_7895591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7895591).length < 2 ^ (prefixWord ++ tailWord_7895591).sum := by decide
  have hdescent : baseEnd_7895591 < baseStart_7895591 := by decide
  rcases family_descends (prefixWord ++ tailWord_7895591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7895613 : List Nat := [1, 4, 1, 3, 2, 1, 2, 3, 2, 1, 3]
def baseStart_7895613 : Nat := 118140960795 + 7895613 * 2 ^ 59
def prefixEnd_7895613 : Nat := 4983230072969 + 3 ^ 40 * 7895613 * 2
def baseEnd_7895613 : Nat := 4054244530887922111526243

theorem tailTrace_7895613 : CollatzResearch.WordTrace tailWord_7895613 prefixEnd_7895613 4054244530887922111526243 := by
  unfold tailWord_7895613
  simp only [CollatzResearch.WordTrace]
  refine ⟨287976664344550039188859493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191984442896366692792572995 287976664344550039188859493)
  ·
    refine ⟨53995624564603132347911155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 287976664344550039188859493 53995624564603132347911155)
    ·
      refine ⟨80993436846904698521866733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53995624564603132347911155 80993436846904698521866733)
      ·
        refine ⟨30372538817589261945700025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80993436846904698521866733 30372538817589261945700025)
        ·
          refine ⟨22779404113191946459275019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30372538817589261945700025 22779404113191946459275019)
          ·
            refine ⟨34169106169787919688912529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22779404113191946459275019 34169106169787919688912529)
            ·
              refine ⟨25626829627340939766684397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34169106169787919688912529 25626829627340939766684397)
              ·
                refine ⟨9610061110252852412506649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25626829627340939766684397 9610061110252852412506649)
                ·
                  refine ⟨7207545832689639309379987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9610061110252852412506649 7207545832689639309379987)
                  ·
                    refine ⟨10811318749034458964069981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7207545832689639309379987 10811318749034458964069981)
                    ·
                      refine ⟨4054244530887922111526243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10811318749034458964069981 4054244530887922111526243)
                      ·
                        rfl

theorem cell23_7895613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_7895613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7895613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7895613 prefixEnd_7895613 := by exact prefixLift 7895613
  have htrace : WordTrace (prefixWord ++ tailWord_7895613) baseStart_7895613 baseEnd_7895613 := by
    simpa [prefixWord, tailWord_7895613, baseEnd_7895613] using wordTrace_append hprefix tailTrace_7895613
  have hstable : (prefixWord ++ tailWord_7895613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7895613).length < 2 ^ (prefixWord ++ tailWord_7895613).sum := by decide
  have hdescent : baseEnd_7895613 < baseStart_7895613 := by decide
  rcases family_descends (prefixWord ++ tailWord_7895613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7895620 : List Nat := [2, 3, 5, 1, 1, 1, 3, 7]
def baseStart_7895620 : Nat := 118140960795 + 7895620 * 2 ^ 59
def prefixEnd_7895620 : Nat := 4983230072969 + 3 ^ 40 * 7895620 * 2
def baseEnd_7895620 : Nat := 150157337972314947560693

theorem tailTrace_7895620 : CollatzResearch.WordTrace tailWord_7895620 prefixEnd_7895620 150157337972314947560693 := by
  unfold tailWord_7895620
  simp only [CollatzResearch.WordTrace]
  refine ⟨143988459827762339692182157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191984613103683119589576209 143988459827762339692182157)
  ·
    refine ⟨53995672435410877384568309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143988459827762339692182157 53995672435410877384568309)
    ·
      refine ⟨5062094290819769754803279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53995672435410877384568309 5062094290819769754803279)
      ·
        refine ⟨7593141436229654632204919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5062094290819769754803279 7593141436229654632204919)
        ·
          refine ⟨11389712154344481948307379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7593141436229654632204919 11389712154344481948307379)
          ·
            refine ⟨17084568231516722922461069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11389712154344481948307379 17084568231516722922461069)
            ·
              refine ⟨6406713086818771095922901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17084568231516722922461069 6406713086818771095922901)
              ·
                refine ⟨150157337972314947560693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6406713086818771095922901 150157337972314947560693)
                ·
                  rfl

theorem cell23_7895620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 3, 7].length) (baseStart_7895620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7895620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7895620 prefixEnd_7895620 := by exact prefixLift 7895620
  have htrace : WordTrace (prefixWord ++ tailWord_7895620) baseStart_7895620 baseEnd_7895620 := by
    simpa [prefixWord, tailWord_7895620, baseEnd_7895620] using wordTrace_append hprefix tailTrace_7895620
  have hstable : (prefixWord ++ tailWord_7895620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7895620).length < 2 ^ (prefixWord ++ tailWord_7895620).sum := by decide
  have hdescent : baseEnd_7895620 < baseStart_7895620 := by decide
  rcases family_descends (prefixWord ++ tailWord_7895620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7895649 : List Nat := [1, 2, 3, 1, 1, 4, 1, 2, 2, 2, 4]
def baseStart_7895649 : Nat := 118140960795 + 7895649 * 2 ^ 59
def prefixEnd_7895649 : Nat := 4983230072969 + 3 ^ 40 * 7895649 * 2
def baseEnd_7895649 : Nat := 4054263016191483970676077

theorem tailTrace_7895649 : CollatzResearch.WordTrace tailWord_7895649 prefixEnd_7895649 4054263016191483970676077 := by
  unfold tailWord_7895649
  simp only [CollatzResearch.WordTrace]
  refine ⟨287977977372419617337170001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191985318248279744891446667 287977977372419617337170001)
  ·
    refine ⟨215983483029314713002877501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287977977372419617337170001 215983483029314713002877501)
    ·
      refine ⟨80993806135993017376079063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215983483029314713002877501 80993806135993017376079063)
      ·
        refine ⟨121490709203989526064118595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80993806135993017376079063 121490709203989526064118595)
        ·
          refine ⟨182236063805984289096177893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121490709203989526064118595 182236063805984289096177893)
          ·
            refine ⟨34169261963622054205533355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 182236063805984289096177893 34169261963622054205533355)
            ·
              refine ⟨51253892945433081308300033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34169261963622054205533355 51253892945433081308300033)
              ·
                refine ⟨38440419709074810981225025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51253892945433081308300033 38440419709074810981225025)
                ·
                  refine ⟨28830314781806108235918769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38440419709074810981225025 28830314781806108235918769)
                  ·
                    refine ⟨21622736086354581176939077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28830314781806108235918769 21622736086354581176939077)
                    ·
                      refine ⟨4054263016191483970676077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21622736086354581176939077 4054263016191483970676077)
                      ·
                        rfl

theorem cell23_7895649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 2, 2, 4].length) (baseStart_7895649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7895649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7895649 prefixEnd_7895649 := by exact prefixLift 7895649
  have htrace : WordTrace (prefixWord ++ tailWord_7895649) baseStart_7895649 baseEnd_7895649 := by
    simpa [prefixWord, tailWord_7895649, baseEnd_7895649] using wordTrace_append hprefix tailTrace_7895649
  have hstable : (prefixWord ++ tailWord_7895649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7895649).length < 2 ^ (prefixWord ++ tailWord_7895649).sum := by decide
  have hdescent : baseEnd_7895649 < baseStart_7895649 := by decide
  rcases family_descends (prefixWord ++ tailWord_7895649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7895689 : List Nat := [1, 2, 1, 1, 4, 1, 1, 5, 2, 5]
def baseStart_7895689 : Nat := 118140960795 + 7895689 * 2 ^ 59
def prefixEnd_7895689 : Nat := 4983230072969 + 3 ^ 40 * 7895689 * 2
def baseEnd_7895689 : Nat := 1351427851805887938058631

theorem tailTrace_7895689 : CollatzResearch.WordTrace tailWord_7895689 prefixEnd_7895689 1351427851805887938058631 := by
  unfold tailWord_7895689
  simp only [CollatzResearch.WordTrace]
  refine ⟨287979436292274704168626121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191986290861516469445750747 287979436292274704168626121)
  ·
    refine ⟨215984577219206028126469591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287979436292274704168626121 215984577219206028126469591)
    ·
      refine ⟨323976865828809042189704387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215984577219206028126469591 323976865828809042189704387)
      ·
        refine ⟨485965298743213563284556581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323976865828809042189704387 485965298743213563284556581)
        ·
          refine ⟨91118493514352543115854359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 485965298743213563284556581 91118493514352543115854359)
          ·
            refine ⟨136677740271528814673781539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91118493514352543115854359 136677740271528814673781539)
            ·
              refine ⟨205016610407293222010672309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136677740271528814673781539 205016610407293222010672309)
              ·
                refine ⟨19220307225683739563500529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 205016610407293222010672309 19220307225683739563500529)
                ·
                  refine ⟨14415230419262804672625397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19220307225683739563500529 14415230419262804672625397)
                  ·
                    refine ⟨1351427851805887938058631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14415230419262804672625397 1351427851805887938058631)
                    ·
                      rfl

theorem cell23_7895689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 5, 2, 5].length) (baseStart_7895689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7895689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7895689 prefixEnd_7895689 := by exact prefixLift 7895689
  have htrace : WordTrace (prefixWord ++ tailWord_7895689) baseStart_7895689 baseEnd_7895689 := by
    simpa [prefixWord, tailWord_7895689, baseEnd_7895689] using wordTrace_append hprefix tailTrace_7895689
  have hstable : (prefixWord ++ tailWord_7895689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7895689).length < 2 ^ (prefixWord ++ tailWord_7895689).sum := by decide
  have hdescent : baseEnd_7895689 < baseStart_7895689 := by decide
  rcases family_descends (prefixWord ++ tailWord_7895689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7895710 : List Nat := [4, 3, 1, 1, 1, 1, 5, 2, 5]
def baseStart_7895710 : Nat := 118140960795 + 7895710 * 2 ^ 59
def prefixEnd_7895710 : Nat := 4983230072969 + 3 ^ 40 * 7895710 * 2
def baseEnd_7895710 : Nat := 450477148723489803557033

theorem tailTrace_7895710 : CollatzResearch.WordTrace tailWord_7895710 prefixEnd_7895710 450477148723489803557033 := by
  unfold tailWord_7895710
  simp only [CollatzResearch.WordTrace]
  refine ⟨35997525278149828094392573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191986801483465749836760389 35997525278149828094392573)
  ·
    refine ⟨13499071979306185535397215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35997525278149828094392573 13499071979306185535397215)
    ·
      refine ⟨20248607968959278303095823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13499071979306185535397215 20248607968959278303095823)
      ·
        refine ⟨30372911953438917454643735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20248607968959278303095823 30372911953438917454643735)
        ·
          refine ⟨45559367930158376181965603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30372911953438917454643735 45559367930158376181965603)
          ·
            refine ⟨68339051895237564272948405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45559367930158376181965603 68339051895237564272948405)
            ·
              refine ⟨6406786115178521650588913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68339051895237564272948405 6406786115178521650588913)
              ·
                refine ⟨4805089586383891237941685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6406786115178521650588913 4805089586383891237941685)
                ·
                  refine ⟨450477148723489803557033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4805089586383891237941685 450477148723489803557033)
                  ·
                    rfl

theorem cell23_7895710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_7895710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7895710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7895710 prefixEnd_7895710 := by exact prefixLift 7895710
  have htrace : WordTrace (prefixWord ++ tailWord_7895710) baseStart_7895710 baseEnd_7895710 := by
    simpa [prefixWord, tailWord_7895710, baseEnd_7895710] using wordTrace_append hprefix tailTrace_7895710
  have hstable : (prefixWord ++ tailWord_7895710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7895710).length < 2 ^ (prefixWord ++ tailWord_7895710).sum := by decide
  have hdescent : baseEnd_7895710 < baseStart_7895710 := by decide
  rcases family_descends (prefixWord ++ tailWord_7895710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7895769 : List Nat := [1, 2, 1, 2, 3, 2, 2, 1, 1, 2, 6]
def baseStart_7895769 : Nat := 118140960795 + 7895769 * 2 ^ 59
def prefixEnd_7895769 : Nat := 4983230072969 + 3 ^ 40 * 7895769 * 2
def baseEnd_7895769 : Nat := 4054324633870023501175525

theorem tailTrace_7895769 : CollatzResearch.WordTrace tailWord_7895769 prefixEnd_7895769 4054324633870023501175525 := by
  unfold tailWord_7895769
  simp only [CollatzResearch.WordTrace]
  refine ⟨287982354131984877831538361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191988236087989918554358907 287982354131984877831538361)
  ·
    refine ⟨215986765598988658373653771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287982354131984877831538361 215986765598988658373653771)
    ·
      refine ⟨323980148398482987560480657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215986765598988658373653771 323980148398482987560480657)
      ·
        refine ⟨242985111298862240670360493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323980148398482987560480657 242985111298862240670360493)
        ·
          refine ⟨91119416737073340251385185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 242985111298862240670360493 91119416737073340251385185)
          ·
            refine ⟨68339562552805005188538889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91119416737073340251385185 68339562552805005188538889)
            ·
              refine ⟨51254671914603753891404167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68339562552805005188538889 51254671914603753891404167)
              ·
                refine ⟨76882007871905630837106251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51254671914603753891404167 76882007871905630837106251)
                ·
                  refine ⟨115323011807858446255659377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76882007871905630837106251 115323011807858446255659377)
                  ·
                    refine ⟨86492258855893834691744533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 115323011807858446255659377 86492258855893834691744533)
                    ·
                      refine ⟨4054324633870023501175525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86492258855893834691744533 4054324633870023501175525)
                      ·
                        rfl

theorem cell23_7895769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 2, 6].length) (baseStart_7895769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7895769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7895769 prefixEnd_7895769 := by exact prefixLift 7895769
  have htrace : WordTrace (prefixWord ++ tailWord_7895769) baseStart_7895769 baseEnd_7895769 := by
    simpa [prefixWord, tailWord_7895769, baseEnd_7895769] using wordTrace_append hprefix tailTrace_7895769
  have hstable : (prefixWord ++ tailWord_7895769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7895769).length < 2 ^ (prefixWord ++ tailWord_7895769).sum := by decide
  have hdescent : baseEnd_7895769 < baseStart_7895769 := by decide
  rcases family_descends (prefixWord ++ tailWord_7895769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7895793 : List Nat := [1, 2, 2, 2, 2, 2, 3, 2, 3, 1, 3]
def baseStart_7895793 : Nat := 118140960795 + 7895793 * 2 ^ 59
def prefixEnd_7895793 : Nat := 4983230072969 + 3 ^ 40 * 7895793 * 2
def baseEnd_7895793 : Nat := 4054336957405731407275415

theorem tailTrace_7895793 : CollatzResearch.WordTrace tailWord_7895793 prefixEnd_7895793 4054336957405731407275415 := by
  unfold tailWord_7895793
  simp only [CollatzResearch.WordTrace]
  refine ⟨287983229483897929930412033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191988819655931953286941355 287983229483897929930412033)
  ·
    refine ⟨215987422112923447447809025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287983229483897929930412033 215987422112923447447809025)
    ·
      refine ⟨161990566584692585585856769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215987422112923447447809025 161990566584692585585856769)
      ·
        refine ⟨121492924938519439189392577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161990566584692585585856769 121492924938519439189392577)
        ·
          refine ⟨91119693703889579392044433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121492924938519439189392577 91119693703889579392044433)
          ·
            refine ⟨68339770277917184544033325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91119693703889579392044433 68339770277917184544033325)
            ·
              refine ⟨25627413854218944204012497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68339770277917184544033325 25627413854218944204012497)
              ·
                refine ⟨19220560390664208153009373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25627413854218944204012497 19220560390664208153009373)
                ·
                  refine ⟨7207710146499078057378515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19220560390664208153009373 7207710146499078057378515)
                  ·
                    refine ⟨10811565219748617086067773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7207710146499078057378515 10811565219748617086067773)
                    ·
                      refine ⟨4054336957405731407275415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10811565219748617086067773 4054336957405731407275415)
                      ·
                        rfl

theorem cell23_7895793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 2, 3, 1, 3].length) (baseStart_7895793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7895793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7895793 prefixEnd_7895793 := by exact prefixLift 7895793
  have htrace : WordTrace (prefixWord ++ tailWord_7895793) baseStart_7895793 baseEnd_7895793 := by
    simpa [prefixWord, tailWord_7895793, baseEnd_7895793] using wordTrace_append hprefix tailTrace_7895793
  have hstable : (prefixWord ++ tailWord_7895793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7895793).length < 2 ^ (prefixWord ++ tailWord_7895793).sum := by decide
  have hdescent : baseEnd_7895793 < baseStart_7895793 := by decide
  rcases family_descends (prefixWord ++ tailWord_7895793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7895797 : List Nat := [1, 3, 6, 1, 1, 1, 1, 1, 1, 4, 3]
def baseStart_7895797 : Nat := 118140960795 + 7895797 * 2 ^ 59
def prefixEnd_7895797 : Nat := 4983230072969 + 3 ^ 40 * 7895797 * 2
def baseEnd_7895797 : Nat := 4054339011328349391625397

theorem tailTrace_7895797 : CollatzResearch.WordTrace tailWord_7895797 prefixEnd_7895797 4054339011328349391625397 := by
  unfold tailWord_7895797
  simp only [CollatzResearch.WordTrace]
  refine ⟨287983375375883438613557645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191988916917255625742371763 287983375375883438613557645)
  ·
    refine ⟨107993765765956289480084117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287983375375883438613557645 107993765765956289480084117)
    ·
      refine ⟨5062207770279201069378943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 107993765765956289480084117 5062207770279201069378943)
      ·
        refine ⟨7593311655418801604068415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5062207770279201069378943 7593311655418801604068415)
        ·
          refine ⟨11389967483128202406102623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7593311655418801604068415 11389967483128202406102623)
          ·
            refine ⟨17084951224692303609153935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11389967483128202406102623 17084951224692303609153935)
            ·
              refine ⟨25627426837038455413730903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17084951224692303609153935 25627426837038455413730903)
              ·
                refine ⟨38441140255557683120596355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25627426837038455413730903 38441140255557683120596355)
                ·
                  refine ⟨57661710383336524680894533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38441140255557683120596355 57661710383336524680894533)
                  ·
                    refine ⟨10811570696875598377667725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57661710383336524680894533 10811570696875598377667725)
                    ·
                      refine ⟨4054339011328349391625397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10811570696875598377667725 4054339011328349391625397)
                      ·
                        rfl

theorem cell23_7895797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_7895797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7895797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7895797 prefixEnd_7895797 := by exact prefixLift 7895797
  have htrace : WordTrace (prefixWord ++ tailWord_7895797) baseStart_7895797 baseEnd_7895797 := by
    simpa [prefixWord, tailWord_7895797, baseEnd_7895797] using wordTrace_append hprefix tailTrace_7895797
  have hstable : (prefixWord ++ tailWord_7895797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7895797).length < 2 ^ (prefixWord ++ tailWord_7895797).sum := by decide
  have hdescent : baseEnd_7895797 < baseStart_7895797 := by decide
  rcases family_descends (prefixWord ++ tailWord_7895797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7895836 : List Nat := [2, 2, 3, 1, 1, 3, 1, 1, 3, 1, 5]
def baseStart_7895836 : Nat := 118140960795 + 7895836 * 2 ^ 59
def prefixEnd_7895836 : Nat := 4983230072969 + 3 ^ 40 * 7895836 * 2
def baseEnd_7895836 : Nat := 4054359037073874739037717

theorem tailTrace_7895836 : CollatzResearch.WordTrace tailWord_7895836 prefixEnd_7895836 4054359037073874739037717 := by
  unfold tailWord_7895836
  simp only [CollatzResearch.WordTrace]
  refine ⟨143992398911371074137113681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191989865215161432182818241 143992398911371074137113681)
  ·
    refine ⟨107994299183528305602835261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143992398911371074137113681 107994299183528305602835261)
    ·
      refine ⟨40497862193823114601063223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107994299183528305602835261 40497862193823114601063223)
      ·
        refine ⟨60746793290734671901594835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40497862193823114601063223 60746793290734671901594835)
        ·
          refine ⟨91120189936102007852392253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60746793290734671901594835 91120189936102007852392253)
          ·
            refine ⟨34170071226038252944647095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91120189936102007852392253 34170071226038252944647095)
            ·
              refine ⟨51255106839057379416970643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34170071226038252944647095 51255106839057379416970643)
              ·
                refine ⟨76882660258586069125455965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51255106839057379416970643 76882660258586069125455965)
                ·
                  refine ⟨28830997596969775922045987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76882660258586069125455965 28830997596969775922045987)
                  ·
                    refine ⟨43246496395454663883068981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28830997596969775922045987 43246496395454663883068981)
                    ·
                      refine ⟨4054359037073874739037717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43246496395454663883068981 4054359037073874739037717)
                      ·
                        rfl

theorem cell23_7895836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_7895836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7895836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7895836 prefixEnd_7895836 := by exact prefixLift 7895836
  have htrace : WordTrace (prefixWord ++ tailWord_7895836) baseStart_7895836 baseEnd_7895836 := by
    simpa [prefixWord, tailWord_7895836, baseEnd_7895836] using wordTrace_append hprefix tailTrace_7895836
  have hstable : (prefixWord ++ tailWord_7895836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7895836).length < 2 ^ (prefixWord ++ tailWord_7895836).sum := by decide
  have hdescent : baseEnd_7895836 < baseStart_7895836 := by decide
  rcases family_descends (prefixWord ++ tailWord_7895836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7895849 : List Nat := [1, 2, 1, 1, 1, 1, 1, 4, 2, 2, 7]
def baseStart_7895849 : Nat := 118140960795 + 7895849 * 2 ^ 59
def prefixEnd_7895849 : Nat := 4983230072969 + 3 ^ 40 * 7895849 * 2
def baseEnd_7895849 : Nat := 4054365712322383188175157

theorem tailTrace_7895849 : CollatzResearch.WordTrace tailWord_7895849 prefixEnd_7895849 4054365712322383188175157 := by
  unfold tailWord_7895849
  simp only [CollatzResearch.WordTrace]
  refine ⟨287985271971695051494450601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191990181314463367662967067 287985271971695051494450601)
  ·
    refine ⟨215988953978771288620837951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287985271971695051494450601 215988953978771288620837951)
    ·
      refine ⟨323983430968156932931256927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215988953978771288620837951 323983430968156932931256927)
      ·
        refine ⟨485975146452235399396885391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323983430968156932931256927 485975146452235399396885391)
        ·
          refine ⟨728962719678353099095328087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 485975146452235399396885391 728962719678353099095328087)
          ·
            refine ⟨1093444079517529648642992131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 728962719678353099095328087 1093444079517529648642992131)
            ·
              refine ⟨1640166119276294472964488197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1093444079517529648642992131 1640166119276294472964488197)
              ·
                refine ⟨307531147364305213680841537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1640166119276294472964488197 307531147364305213680841537)
                ·
                  refine ⟨230648360523228910260631153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 307531147364305213680841537 230648360523228910260631153)
                  ·
                    refine ⟨172986270392421682695473365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 230648360523228910260631153 172986270392421682695473365)
                    ·
                      refine ⟨4054365712322383188175157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 172986270392421682695473365 4054365712322383188175157)
                      ·
                        rfl

theorem cell23_7895849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 2, 7].length) (baseStart_7895849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7895849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7895849 prefixEnd_7895849 := by exact prefixLift 7895849
  have htrace : WordTrace (prefixWord ++ tailWord_7895849) baseStart_7895849 baseEnd_7895849 := by
    simpa [prefixWord, tailWord_7895849, baseEnd_7895849] using wordTrace_append hprefix tailTrace_7895849
  have hstable : (prefixWord ++ tailWord_7895849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7895849).length < 2 ^ (prefixWord ++ tailWord_7895849).sum := by decide
  have hdescent : baseEnd_7895849 < baseStart_7895849 := by decide
  rcases family_descends (prefixWord ++ tailWord_7895849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7895870 : List Nat := [4, 2, 1, 2, 3, 1, 2, 1, 1, 1, 5]
def baseStart_7895870 : Nat := 118140960795 + 7895870 * 2 ^ 59
def prefixEnd_7895870 : Nat := 4983230072969 + 3 ^ 40 * 7895870 * 2
def baseEnd_7895870 : Nat := 4054376495416127606012561

theorem tailTrace_7895870 : CollatzResearch.WordTrace tailWord_7895870 prefixEnd_7895870 4054376495416127606012561 := by
  unfold tailWord_7895870
  simp only [CollatzResearch.WordTrace]
  refine ⟨35998254738077371510120633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191990691936412648053976709 35998254738077371510120633)
  ·
    refine ⟨26998691053558028632590475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35998254738077371510120633 26998691053558028632590475)
    ·
      refine ⟨40498036580337042948885713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26998691053558028632590475 40498036580337042948885713)
      ·
        refine ⟨30373527435252782211664285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40498036580337042948885713 30373527435252782211664285)
        ·
          refine ⟨11390072788219793329374107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30373527435252782211664285 11390072788219793329374107)
          ·
            refine ⟨17085109182329689994061161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11390072788219793329374107 17085109182329689994061161)
            ·
              refine ⟨12813831886747267495545871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17085109182329689994061161 12813831886747267495545871)
              ·
                refine ⟨19220747830120901243318807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12813831886747267495545871 19220747830120901243318807)
                ·
                  refine ⟨28831121745181351864978211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19220747830120901243318807 28831121745181351864978211)
                  ·
                    refine ⟨43246682617772027797467317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28831121745181351864978211 43246682617772027797467317)
                    ·
                      refine ⟨4054376495416127606012561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43246682617772027797467317 4054376495416127606012561)
                      ·
                        rfl

theorem cell23_7895870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_7895870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7895870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7895870 prefixEnd_7895870 := by exact prefixLift 7895870
  have htrace : WordTrace (prefixWord ++ tailWord_7895870) baseStart_7895870 baseEnd_7895870 := by
    simpa [prefixWord, tailWord_7895870, baseEnd_7895870] using wordTrace_append hprefix tailTrace_7895870
  have hstable : (prefixWord ++ tailWord_7895870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7895870).length < 2 ^ (prefixWord ++ tailWord_7895870).sum := by decide
  have hdescent : baseEnd_7895870 < baseStart_7895870 := by decide
  rcases family_descends (prefixWord ++ tailWord_7895870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7895878 : List Nat := [6, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3]
def baseStart_7895878 : Nat := 118140960795 + 7895878 * 2 ^ 59
def prefixEnd_7895878 : Nat := 4983230072969 + 3 ^ 40 * 7895878 * 2
def baseEnd_7895878 : Nat := 4054380603261363574712525

theorem tailTrace_7895878 : CollatzResearch.WordTrace tailWord_7895878 prefixEnd_7895878 4054380603261363574712525 := by
  unfold tailWord_7895878
  simp only [CollatzResearch.WordTrace]
  refine ⟨8999572802768437170226759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 191990886459059992964837525 8999572802768437170226759)
  ·
    refine ⟨13499359204152655755340139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8999572802768437170226759 13499359204152655755340139)
    ·
      refine ⟨20249038806228983633010209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13499359204152655755340139 20249038806228983633010209)
      ·
        refine ⟨15186779104671737724757657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20249038806228983633010209 15186779104671737724757657)
        ·
          refine ⟨11390084328503803293568243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15186779104671737724757657 11390084328503803293568243)
          ·
            refine ⟨17085126492755704940352365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11390084328503803293568243 17085126492755704940352365)
            ·
              refine ⟨6406922434783389352632137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17085126492755704940352365 6406922434783389352632137)
              ·
                refine ⟨4805191826087542014474103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6406922434783389352632137 4805191826087542014474103)
                ·
                  refine ⟨7207787739131313021711155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4805191826087542014474103 7207787739131313021711155)
                  ·
                    refine ⟨10811681608696969532566733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7207787739131313021711155 10811681608696969532566733)
                    ·
                      refine ⟨4054380603261363574712525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10811681608696969532566733 4054380603261363574712525)
                      ·
                        rfl

theorem cell23_7895878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_7895878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7895878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7895878 prefixEnd_7895878 := by exact prefixLift 7895878
  have htrace : WordTrace (prefixWord ++ tailWord_7895878) baseStart_7895878 baseEnd_7895878 := by
    simpa [prefixWord, tailWord_7895878, baseEnd_7895878] using wordTrace_append hprefix tailTrace_7895878
  have hstable : (prefixWord ++ tailWord_7895878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7895878).length < 2 ^ (prefixWord ++ tailWord_7895878).sum := by decide
  have hdescent : baseEnd_7895878 < baseStart_7895878 := by decide
  rcases family_descends (prefixWord ++ tailWord_7895878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7895923 : List Nat := [1, 1, 1, 2, 2, 1, 5, 1, 3, 4, 2]
def baseStart_7895923 : Nat := 118140960795 + 7895923 * 2 ^ 59
def prefixEnd_7895923 : Nat := 4983230072969 + 3 ^ 40 * 7895923 * 2
def baseEnd_7895923 : Nat := 4054403709890815898649817

theorem tailTrace_7895923 : CollatzResearch.WordTrace tailWord_7895923 prefixEnd_7895923 4054403709890815898649817 := by
  unfold tailWord_7895923
  simp only [CollatzResearch.WordTrace]
  refine ⟨287987970973426962132644423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191991980648951308088429615 287987970973426962132644423)
  ·
    refine ⟨431981956460140443198966635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287987970973426962132644423 431981956460140443198966635)
    ·
      refine ⟨647972934690210664798449953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431981956460140443198966635 647972934690210664798449953)
      ·
        refine ⟨485979701017657998598837465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 647972934690210664798449953 485979701017657998598837465)
        ·
          refine ⟨364484775763243498949128099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 485979701017657998598837465 364484775763243498949128099)
          ·
            refine ⟨546727163644865248423692149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364484775763243498949128099 546727163644865248423692149)
            ·
              refine ⟨51255671591706117039721139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 546727163644865248423692149 51255671591706117039721139)
              ·
                refine ⟨76883507387559175559581709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51255671591706117039721139 76883507387559175559581709)
                ·
                  refine ⟨28831315270334690834843141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76883507387559175559581709 28831315270334690834843141)
                  ·
                    refine ⟨5405871613187754531533089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28831315270334690834843141 5405871613187754531533089)
                    ·
                      refine ⟨4054403709890815898649817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5405871613187754531533089 4054403709890815898649817)
                      ·
                        rfl

theorem cell23_7895923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 3, 4, 2].length) (baseStart_7895923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7895923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7895923 prefixEnd_7895923 := by exact prefixLift 7895923
  have htrace : WordTrace (prefixWord ++ tailWord_7895923) baseStart_7895923 baseEnd_7895923 := by
    simpa [prefixWord, tailWord_7895923, baseEnd_7895923] using wordTrace_append hprefix tailTrace_7895923
  have hstable : (prefixWord ++ tailWord_7895923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7895923).length < 2 ^ (prefixWord ++ tailWord_7895923).sum := by decide
  have hdescent : baseEnd_7895923 < baseStart_7895923 := by decide
  rcases family_descends (prefixWord ++ tailWord_7895923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7895943 : List Nat := [1, 1, 4, 2, 3, 1, 1, 1, 2, 4, 3]
def baseStart_7895943 : Nat := 118140960795 + 7895943 * 2 ^ 59
def prefixEnd_7895943 : Nat := 4983230072969 + 3 ^ 40 * 7895943 * 2
def baseEnd_7895943 : Nat := 4054413979503905820399725

theorem tailTrace_7895943 : CollatzResearch.WordTrace tailWord_7895943 prefixEnd_7895943 4054413979503905820399725 := by
  unfold tailWord_7895943
  simp only [CollatzResearch.WordTrace]
  refine ⟨287988700433354505548372483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191992466955569670365581655 287988700433354505548372483)
  ·
    refine ⟨431983050650031758322558725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287988700433354505548372483 431983050650031758322558725)
    ·
      refine ⟨80996821996880954685479761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 431983050650031758322558725 80996821996880954685479761)
      ·
        refine ⟨60747616497660716014109821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80996821996880954685479761 60747616497660716014109821)
        ·
          refine ⟨22780356186622768505291183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60747616497660716014109821 22780356186622768505291183)
          ·
            refine ⟨34170534279934152757936775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22780356186622768505291183 34170534279934152757936775)
            ·
              refine ⟨51255801419901229136905163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34170534279934152757936775 51255801419901229136905163)
              ·
                refine ⟨76883702129851843705357745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51255801419901229136905163 76883702129851843705357745)
                ·
                  refine ⟨57662776597388882779018309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76883702129851843705357745 57662776597388882779018309)
                  ·
                    refine ⟨10811770612010415521065933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57662776597388882779018309 10811770612010415521065933)
                    ·
                      refine ⟨4054413979503905820399725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10811770612010415521065933 4054413979503905820399725)
                      ·
                        rfl

theorem cell23_7895943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 4, 3].length) (baseStart_7895943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7895943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7895943 prefixEnd_7895943 := by exact prefixLift 7895943
  have htrace : WordTrace (prefixWord ++ tailWord_7895943) baseStart_7895943 baseEnd_7895943 := by
    simpa [prefixWord, tailWord_7895943, baseEnd_7895943] using wordTrace_append hprefix tailTrace_7895943
  have hstable : (prefixWord ++ tailWord_7895943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7895943).length < 2 ^ (prefixWord ++ tailWord_7895943).sum := by decide
  have hdescent : baseEnd_7895943 < baseStart_7895943 := by decide
  rcases family_descends (prefixWord ++ tailWord_7895943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7895957 : List Nat := [1, 3, 2, 1, 1, 4, 2, 3, 2, 2, 2]
def baseStart_7895957 : Nat := 118140960795 + 7895957 * 2 ^ 59
def prefixEnd_7895957 : Nat := 4983230072969 + 3 ^ 40 * 7895957 * 2
def baseEnd_7895957 : Nat := 4054421168233068765624661

theorem tailTrace_7895957 : CollatzResearch.WordTrace tailWord_7895957 prefixEnd_7895957 4054421168233068765624661 := by
  unfold tailWord_7895957
  simp only [CollatzResearch.WordTrace]
  refine ⟨287989211055303785939382125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191992807370202523959588083 287989211055303785939382125)
  ·
    refine ⟨107995954145738919727268297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287989211055303785939382125 107995954145738919727268297)
    ·
      refine ⟨80996965609304189795451223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107995954145738919727268297 80996965609304189795451223)
      ·
        refine ⟨121495448413956284693176835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80996965609304189795451223 121495448413956284693176835)
        ·
          refine ⟨182243172620934427039765253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121495448413956284693176835 182243172620934427039765253)
          ·
            refine ⟨34170594866425205069955985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 182243172620934427039765253 34170594866425205069955985)
            ·
              refine ⟨25627946149818903802466989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34170594866425205069955985 25627946149818903802466989)
              ·
                refine ⟨9610479806182088925925121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25627946149818903802466989 9610479806182088925925121)
                ·
                  refine ⟨7207859854636566694443841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9610479806182088925925121 7207859854636566694443841)
                  ·
                    refine ⟨5405894890977425020832881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7207859854636566694443841 5405894890977425020832881)
                    ·
                      refine ⟨4054421168233068765624661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5405894890977425020832881 4054421168233068765624661)
                      ·
                        rfl

theorem cell23_7895957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 3, 2, 2, 2].length) (baseStart_7895957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7895957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7895957 prefixEnd_7895957 := by exact prefixLift 7895957
  have htrace : WordTrace (prefixWord ++ tailWord_7895957) baseStart_7895957 baseEnd_7895957 := by
    simpa [prefixWord, tailWord_7895957, baseEnd_7895957] using wordTrace_append hprefix tailTrace_7895957
  have hstable : (prefixWord ++ tailWord_7895957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7895957).length < 2 ^ (prefixWord ++ tailWord_7895957).sum := by decide
  have hdescent : baseEnd_7895957 < baseStart_7895957 := by decide
  rcases family_descends (prefixWord ++ tailWord_7895957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7895983 : List Nat := [1, 1, 2, 1, 2, 2, 2, 2, 1, 7, 2]
def baseStart_7895983 : Nat := 118140960795 + 7895983 * 2 ^ 59
def prefixEnd_7895983 : Nat := 4983230072969 + 3 ^ 40 * 7895983 * 2
def baseEnd_7895983 : Nat := 4054434518730085663899541

theorem tailTrace_7895983 : CollatzResearch.WordTrace tailWord_7895983 prefixEnd_7895983 4054434518730085663899541 := by
  unfold tailWord_7895983
  simp only [CollatzResearch.WordTrace]
  refine ⟨287990159353209592379828603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191993439568806394919885735 287990159353209592379828603)
  ·
    refine ⟨431985239029814388569742905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287990159353209592379828603 431985239029814388569742905)
    ·
      refine ⟨323988929272360791427307179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 431985239029814388569742905 323988929272360791427307179)
      ·
        refine ⟨485983393908541187140960769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323988929272360791427307179 485983393908541187140960769)
        ·
          refine ⟨364487545431405890355720577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 485983393908541187140960769 364487545431405890355720577)
          ·
            refine ⟨273365659073554417766790433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 364487545431405890355720577 273365659073554417766790433)
            ·
              refine ⟨205024244305165813325092825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273365659073554417766790433 205024244305165813325092825)
              ·
                refine ⟨153768183228874359993819619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205024244305165813325092825 153768183228874359993819619)
                ·
                  refine ⟨230652274843311539990729429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153768183228874359993819619 230652274843311539990729429)
                  ·
                    refine ⟨5405912691640114218532721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 230652274843311539990729429 5405912691640114218532721)
                    ·
                      refine ⟨4054434518730085663899541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5405912691640114218532721 4054434518730085663899541)
                      ·
                        rfl

theorem cell23_7895983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 7, 2].length) (baseStart_7895983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7895983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7895983 prefixEnd_7895983 := by exact prefixLift 7895983
  have htrace : WordTrace (prefixWord ++ tailWord_7895983) baseStart_7895983 baseEnd_7895983 := by
    simpa [prefixWord, tailWord_7895983, baseEnd_7895983] using wordTrace_append hprefix tailTrace_7895983
  have hstable : (prefixWord ++ tailWord_7895983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7895983).length < 2 ^ (prefixWord ++ tailWord_7895983).sum := by decide
  have hdescent : baseEnd_7895983 < baseStart_7895983 := by decide
  rcases family_descends (prefixWord ++ tailWord_7895983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7896023 : List Nat := [1, 1, 3, 2, 1, 1, 2, 3, 5, 4]
def baseStart_7896023 : Nat := 118140960795 + 7896023 * 2 ^ 59
def prefixEnd_7896023 : Nat := 4983230072969 + 3 ^ 40 * 7896023 * 2
def baseEnd_7896023 : Nat := 1351485019318755169133119

theorem tailTrace_7896023 : CollatzResearch.WordTrace tailWord_7896023 prefixEnd_7896023 1351485019318755169133119 := by
  unfold tailWord_7896023
  simp only [CollatzResearch.WordTrace]
  refine ⟨287991618273064679211284723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191994412182043119474189815 287991618273064679211284723)
  ·
    refine ⟨431987427409597018816927085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287991618273064679211284723 431987427409597018816927085)
    ·
      refine ⟨161995285278598882056347657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 431987427409597018816927085 161995285278598882056347657)
      ·
        refine ⟨121496463958949161542260743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161995285278598882056347657 121496463958949161542260743)
        ·
          refine ⟨182244695938423742313391115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121496463958949161542260743 182244695938423742313391115)
          ·
            refine ⟨273367043907635613470086673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182244695938423742313391115 273367043907635613470086673)
            ·
              refine ⟨205025282930726710102565005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273367043907635613470086673 205025282930726710102565005)
              ·
                refine ⟨76884481099022516288461877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 205025282930726710102565005 76884481099022516288461877)
                ·
                  refine ⟨7207920103033360902043301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76884481099022516288461877 7207920103033360902043301)
                  ·
                    refine ⟨1351485019318755169133119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7207920103033360902043301 1351485019318755169133119)
                    ·
                      rfl

theorem cell23_7896023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 5, 4].length) (baseStart_7896023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7896023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7896023 prefixEnd_7896023 := by exact prefixLift 7896023
  have htrace : WordTrace (prefixWord ++ tailWord_7896023) baseStart_7896023 baseEnd_7896023 := by
    simpa [prefixWord, tailWord_7896023, baseEnd_7896023] using wordTrace_append hprefix tailTrace_7896023
  have hstable : (prefixWord ++ tailWord_7896023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7896023).length < 2 ^ (prefixWord ++ tailWord_7896023).sum := by decide
  have hdescent : baseEnd_7896023 < baseStart_7896023 := by decide
  rcases family_descends (prefixWord ++ tailWord_7896023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7896113 : List Nat := [1, 2, 2, 3, 1, 2, 1, 2, 3, 6]
def baseStart_7896113 : Nat := 118140960795 + 7896113 * 2 ^ 59
def prefixEnd_7896113 : Nat := 4983230072969 + 3 ^ 40 * 7896113 * 2
def baseEnd_7896113 : Nat := 1351500423738390051757981

theorem tailTrace_7896113 : CollatzResearch.WordTrace tailWord_7896113 prefixEnd_7896113 1351500423738390051757981 := by
  unfold tailWord_7896113
  simp only [CollatzResearch.WordTrace]
  refine ⟨287994900842738624582060993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191996600561825749721373995 287994900842738624582060993)
  ·
    refine ⟨215996175632053968436545745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287994900842738624582060993 215996175632053968436545745)
    ·
      refine ⟨161997131724040476327409309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215996175632053968436545745 161997131724040476327409309)
      ·
        refine ⟨60748924396515178622778491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161997131724040476327409309 60748924396515178622778491)
        ·
          refine ⟨91123386594772767934167737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60748924396515178622778491 91123386594772767934167737)
          ·
            refine ⟨68342539946079575950625803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91123386594772767934167737 68342539946079575950625803)
            ·
              refine ⟨102513809919119363925938705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68342539946079575950625803 102513809919119363925938705)
              ·
                refine ⟨76885357439339522944454029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102513809919119363925938705 76885357439339522944454029)
                ·
                  refine ⟨28832009039752321104170261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76885357439339522944454029 28832009039752321104170261)
                  ·
                    refine ⟨1351500423738390051757981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28832009039752321104170261 1351500423738390051757981)
                    ·
                      rfl

theorem cell23_7896113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 3, 6].length) (baseStart_7896113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7896113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7896113 prefixEnd_7896113 := by exact prefixLift 7896113
  have htrace : WordTrace (prefixWord ++ tailWord_7896113) baseStart_7896113 baseEnd_7896113 := by
    simpa [prefixWord, tailWord_7896113, baseEnd_7896113] using wordTrace_append hprefix tailTrace_7896113
  have hstable : (prefixWord ++ tailWord_7896113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7896113).length < 2 ^ (prefixWord ++ tailWord_7896113).sum := by decide
  have hdescent : baseEnd_7896113 < baseStart_7896113 := by decide
  rcases family_descends (prefixWord ++ tailWord_7896113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7896114 : List Nat := [3, 2, 1, 1, 2, 2, 3, 4, 1, 1, 3]
def baseStart_7896114 : Nat := 118140960795 + 7896114 * 2 ^ 59
def prefixEnd_7896114 : Nat := 4983230072969 + 3 ^ 40 * 7896114 * 2
def baseEnd_7896114 : Nat := 4054501784695824651361439

theorem tailTrace_7896114 : CollatzResearch.WordTrace tailWord_7896114 prefixEnd_7896114 4054501784695824651361439 := by
  unfold tailWord_7896114
  simp only [CollatzResearch.WordTrace]
  refine ⟨71998734328933750438211849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191996624877156667835231597 71998734328933750438211849)
  ·
    refine ⟨53999050746700312828658887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71998734328933750438211849 53999050746700312828658887)
    ·
      refine ⟨80998576120050469242988331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53999050746700312828658887 80998576120050469242988331)
      ·
        refine ⟨121497864180075703864482497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80998576120050469242988331 121497864180075703864482497)
        ·
          refine ⟨91123398135056777898361873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121497864180075703864482497 91123398135056777898361873)
          ·
            refine ⟨68342548601292583423771405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91123398135056777898361873 68342548601292583423771405)
            ·
              refine ⟨25628455725484718783914277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68342548601292583423771405 25628455725484718783914277)
              ·
                refine ⟨4805335448528384771983927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25628455725484718783914277 4805335448528384771983927)
                ·
                  refine ⟨7208003172792577157975891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4805335448528384771983927 7208003172792577157975891)
                  ·
                    refine ⟨10812004759188865736963837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7208003172792577157975891 10812004759188865736963837)
                    ·
                      refine ⟨4054501784695824651361439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10812004759188865736963837 4054501784695824651361439)
                      ·
                        rfl

theorem cell23_7896114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 4, 1, 1, 3].length) (baseStart_7896114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7896114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7896114 prefixEnd_7896114 := by exact prefixLift 7896114
  have htrace : WordTrace (prefixWord ++ tailWord_7896114) baseStart_7896114 baseEnd_7896114 := by
    simpa [prefixWord, tailWord_7896114, baseEnd_7896114] using wordTrace_append hprefix tailTrace_7896114
  have hstable : (prefixWord ++ tailWord_7896114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7896114).length < 2 ^ (prefixWord ++ tailWord_7896114).sum := by decide
  have hdescent : baseEnd_7896114 < baseStart_7896114 := by decide
  rcases family_descends (prefixWord ++ tailWord_7896114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7896120 : List Nat := [2, 1, 2, 1, 5, 1, 1, 2, 3, 1, 4]
def baseStart_7896120 : Nat := 118140960795 + 7896120 * 2 ^ 59
def prefixEnd_7896120 : Nat := 4983230072969 + 3 ^ 40 * 7896120 * 2
def baseEnd_7896120 : Nat := 4054504865579751627886411

theorem tailTrace_7896120 : CollatzResearch.WordTrace tailWord_7896120 prefixEnd_7896120 4054504865579751627886411 := by
  unfold tailWord_7896120
  simp only [CollatzResearch.WordTrace]
  refine ⟨143997578076856632388782907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191996770769142176518377209 143997578076856632388782907)
  ·
    refine ⟨215996367115284948583174361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143997578076856632388782907 215996367115284948583174361)
    ·
      refine ⟨161997275336463711437380771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215996367115284948583174361 161997275336463711437380771)
      ·
        refine ⟨242995913004695567156071157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161997275336463711437380771 242995913004695567156071157)
        ·
          refine ⟨22780866844190209420881671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 242995913004695567156071157 22780866844190209420881671)
          ·
            refine ⟨34171300266285314131322507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22780866844190209420881671 34171300266285314131322507)
            ·
              refine ⟨51256950399427971196983761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34171300266285314131322507 51256950399427971196983761)
              ·
                refine ⟨38442712799570978397737821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51256950399427971196983761 38442712799570978397737821)
                ·
                  refine ⟨14416017299839116899151683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38442712799570978397737821 14416017299839116899151683)
                  ·
                    refine ⟨21624025949758675348727525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14416017299839116899151683 21624025949758675348727525)
                    ·
                      refine ⟨4054504865579751627886411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21624025949758675348727525 4054504865579751627886411)
                      ·
                        rfl

theorem cell23_7896120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 3, 1, 4].length) (baseStart_7896120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7896120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7896120 prefixEnd_7896120 := by exact prefixLift 7896120
  have htrace : WordTrace (prefixWord ++ tailWord_7896120) baseStart_7896120 baseEnd_7896120 := by
    simpa [prefixWord, tailWord_7896120, baseEnd_7896120] using wordTrace_append hprefix tailTrace_7896120
  have hstable : (prefixWord ++ tailWord_7896120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7896120).length < 2 ^ (prefixWord ++ tailWord_7896120).sum := by decide
  have hdescent : baseEnd_7896120 < baseStart_7896120 := by decide
  rcases family_descends (prefixWord ++ tailWord_7896120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7896123 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 1, 8, 3]
def baseStart_7896123 : Nat := 118140960795 + 7896123 * 2 ^ 59
def prefixEnd_7896123 : Nat := 4983230072969 + 3 ^ 40 * 7896123 * 2
def baseEnd_7896123 : Nat := 4054506406021715116148897

theorem tailTrace_7896123 : CollatzResearch.WordTrace tailWord_7896123 prefixEnd_7896123 4054506406021715116148897 := by
  unfold tailWord_7896123
  simp only [CollatzResearch.WordTrace]
  refine ⟨287995265572702396289925023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191996843715134930859950015 287995265572702396289925023)
  ·
    refine ⟨431992898359053594434887535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287995265572702396289925023 431992898359053594434887535)
    ·
      refine ⟨647989347538580391652331303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431992898359053594434887535 647989347538580391652331303)
      ·
        refine ⟨971984021307870587478496955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 647989347538580391652331303 971984021307870587478496955)
        ·
          refine ⟨1457976031961805881217745433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 971984021307870587478496955 1457976031961805881217745433)
          ·
            refine ⟨1093482023971354410913309075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1457976031961805881217745433 1093482023971354410913309075)
            ·
              refine ⟨1640223035957031616369963613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1093482023971354410913309075 1640223035957031616369963613)
              ·
                refine ⟨615083638483886856138736355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1640223035957031616369963613 615083638483886856138736355)
                ·
                  refine ⟨922625457725830284208104533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 615083638483886856138736355 922625457725830284208104533)
                  ·
                    refine ⟨10812017082724573643063725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 922625457725830284208104533 10812017082724573643063725)
                    ·
                      refine ⟨4054506406021715116148897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10812017082724573643063725 4054506406021715116148897)
                      ·
                        rfl

theorem cell23_7896123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 8, 3].length) (baseStart_7896123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7896123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7896123 prefixEnd_7896123 := by exact prefixLift 7896123
  have htrace : WordTrace (prefixWord ++ tailWord_7896123) baseStart_7896123 baseEnd_7896123 := by
    simpa [prefixWord, tailWord_7896123, baseEnd_7896123] using wordTrace_append hprefix tailTrace_7896123
  have hstable : (prefixWord ++ tailWord_7896123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7896123).length < 2 ^ (prefixWord ++ tailWord_7896123).sum := by decide
  have hdescent : baseEnd_7896123 < baseStart_7896123 := by decide
  rcases family_descends (prefixWord ++ tailWord_7896123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7896133 : List Nat := [1, 3, 1, 1, 1, 3, 2, 3, 1, 1, 6]
def baseStart_7896133 : Nat := 118140960795 + 7896133 * 2 ^ 59
def prefixEnd_7896133 : Nat := 4983230072969 + 3 ^ 40 * 7896133 * 2
def baseEnd_7896133 : Nat := 4054511540828260077023851

theorem tailTrace_7896133 : CollatzResearch.WordTrace tailWord_7896133 prefixEnd_7896133 4054511540828260077023851 := by
  unfold tailWord_7896133
  simp only [CollatzResearch.WordTrace]
  refine ⟨287995630302666167997789053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191997086868444111998526035 287995630302666167997789053)
  ·
    refine ⟨107998361363499812999170895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287995630302666167997789053 107998361363499812999170895)
    ·
      refine ⟨161997542045249719498756343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107998361363499812999170895 161997542045249719498756343)
      ·
        refine ⟨242996313067874579248134515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161997542045249719498756343 242996313067874579248134515)
        ·
          refine ⟨364494469601811868872201773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242996313067874579248134515 364494469601811868872201773)
          ·
            refine ⟨136685426100679450827075665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 364494469601811868872201773 136685426100679450827075665)
            ·
              refine ⟨102514069575509588120306749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136685426100679450827075665 102514069575509588120306749)
              ·
                refine ⟨38442776090816095545115031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102514069575509588120306749 38442776090816095545115031)
                ·
                  refine ⟨57664164136224143317672547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38442776090816095545115031 57664164136224143317672547)
                  ·
                    refine ⟨86496246204336214976508821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57664164136224143317672547 86496246204336214976508821)
                    ·
                      refine ⟨4054511540828260077023851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86496246204336214976508821 4054511540828260077023851)
                      ·
                        rfl

theorem cell23_7896133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 1, 6].length) (baseStart_7896133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7896133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7896133 prefixEnd_7896133 := by exact prefixLift 7896133
  have htrace : WordTrace (prefixWord ++ tailWord_7896133) baseStart_7896133 baseEnd_7896133 := by
    simpa [prefixWord, tailWord_7896133, baseEnd_7896133] using wordTrace_append hprefix tailTrace_7896133
  have hstable : (prefixWord ++ tailWord_7896133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7896133).length < 2 ^ (prefixWord ++ tailWord_7896133).sum := by decide
  have hdescent : baseEnd_7896133 < baseStart_7896133 := by decide
  rcases family_descends (prefixWord ++ tailWord_7896133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7896141 : List Nat := [1, 6, 1, 1, 1, 4, 1, 1, 2, 3, 2]
def baseStart_7896141 : Nat := 118140960795 + 7896141 * 2 ^ 59
def prefixEnd_7896141 : Nat := 4983230072969 + 3 ^ 40 * 7896141 * 2
def baseEnd_7896141 : Nat := 4054515648673496045723815

theorem tailTrace_7896141 : CollatzResearch.WordTrace tailWord_7896141 prefixEnd_7896141 4054515648673496045723815 := by
  unfold tailWord_7896141
  simp only [CollatzResearch.WordTrace]
  refine ⟨287995922086637185364080277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191997281391091456909386851 287995922086637185364080277)
  ·
    refine ⟨13499808847811118063941263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 287995922086637185364080277 13499808847811118063941263)
    ·
      refine ⟨20249713271716677095911895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13499808847811118063941263 20249713271716677095911895)
      ·
        refine ⟨30374569907575015643867843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20249713271716677095911895 30374569907575015643867843)
        ·
          refine ⟨45561854861362523465801765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30374569907575015643867843 45561854861362523465801765)
          ·
            refine ⟨8542847786505473149837831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45561854861362523465801765 8542847786505473149837831)
            ·
              refine ⟨12814271679758209724756747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8542847786505473149837831 12814271679758209724756747)
              ·
                refine ⟨19221407519637314587135121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12814271679758209724756747 19221407519637314587135121)
                ·
                  refine ⟨14416055639727985940351341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19221407519637314587135121 14416055639727985940351341)
                  ·
                    refine ⟨5406020864897994727631753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14416055639727985940351341 5406020864897994727631753)
                    ·
                      refine ⟨4054515648673496045723815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5406020864897994727631753 4054515648673496045723815)
                      ·
                        rfl

theorem cell23_7896141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 1, 2, 3, 2].length) (baseStart_7896141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7896141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7896141 prefixEnd_7896141 := by exact prefixLift 7896141
  have htrace : WordTrace (prefixWord ++ tailWord_7896141) baseStart_7896141 baseEnd_7896141 := by
    simpa [prefixWord, tailWord_7896141, baseEnd_7896141] using wordTrace_append hprefix tailTrace_7896141
  have hstable : (prefixWord ++ tailWord_7896141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7896141).length < 2 ^ (prefixWord ++ tailWord_7896141).sum := by decide
  have hdescent : baseEnd_7896141 < baseStart_7896141 := by decide
  rcases family_descends (prefixWord ++ tailWord_7896141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7896163 : List Nat := [1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 6]
def baseStart_7896163 : Nat := 118140960795 + 7896163 * 2 ^ 59
def prefixEnd_7896163 : Nat := 4983230072969 + 3 ^ 40 * 7896163 * 2
def baseEnd_7896163 : Nat := 4054526945247894959648713

theorem tailTrace_7896163 : CollatzResearch.WordTrace tailWord_7896163 prefixEnd_7896163 4054526945247894959648713 := by
  unfold tailWord_7896163
  simp only [CollatzResearch.WordTrace]
  refine ⟨287996724492557483121381143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191997816328371655414254095 287996724492557483121381143)
  ·
    refine ⟨431995086738836224682071715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287996724492557483121381143 431995086738836224682071715)
    ·
      refine ⟨647992630108254337023107573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431995086738836224682071715 647992630108254337023107573)
      ·
        refine ⟨60749309072648844095916335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 647992630108254337023107573 60749309072648844095916335)
        ·
          refine ⟨91123963608973266143874503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60749309072648844095916335 91123963608973266143874503)
          ·
            refine ⟨136685945413459899215811755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91123963608973266143874503 136685945413459899215811755)
            ·
              refine ⟨205028918120189848823717633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136685945413459899215811755 205028918120189848823717633)
              ·
                refine ⟨153771688590142386617788225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205028918120189848823717633 153771688590142386617788225)
                ·
                  refine ⟨115328766442606789963341169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153771688590142386617788225 115328766442606789963341169)
                  ·
                    refine ⟨86496574831955092472505877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 115328766442606789963341169 86496574831955092472505877)
                    ·
                      refine ⟨4054526945247894959648713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86496574831955092472505877 4054526945247894959648713)
                      ·
                        rfl

theorem cell23_7896163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_7896163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7896163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7896163 prefixEnd_7896163 := by exact prefixLift 7896163
  have htrace : WordTrace (prefixWord ++ tailWord_7896163) baseStart_7896163 baseEnd_7896163 := by
    simpa [prefixWord, tailWord_7896163, baseEnd_7896163] using wordTrace_append hprefix tailTrace_7896163
  have hstable : (prefixWord ++ tailWord_7896163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7896163).length < 2 ^ (prefixWord ++ tailWord_7896163).sum := by decide
  have hdescent : baseEnd_7896163 < baseStart_7896163 := by decide
  rcases family_descends (prefixWord ++ tailWord_7896163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7896181 : List Nat := [1, 3, 4, 3, 2, 1, 1, 1, 1, 6]
def baseStart_7896181 : Nat := 118140960795 + 7896181 * 2 ^ 59
def prefixEnd_7896181 : Nat := 4983230072969 + 3 ^ 40 * 7896181 * 2
def baseEnd_7896181 : Nat := 1351512062633225296407877

theorem tailTrace_7896181 : CollatzResearch.WordTrace tailWord_7896181 prefixEnd_7896181 1351512062633225296407877 := by
  unfold tailWord_7896181
  simp only [CollatzResearch.WordTrace]
  refine ⟨287997381006492272195536397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191998254004328181463690931 287997381006492272195536397)
  ·
    refine ⟨107999017877434602073326149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287997381006492272195536397 107999017877434602073326149)
    ·
      refine ⟨20249815852018987888748653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107999017877434602073326149 20249815852018987888748653)
      ·
        refine ⟨7593680944507120458280745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20249815852018987888748653 7593680944507120458280745)
        ·
          refine ⟨5695260708380340343710559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7593680944507120458280745 5695260708380340343710559)
          ·
            refine ⟨8542891062570510515565839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5695260708380340343710559 8542891062570510515565839)
            ·
              refine ⟨12814336593855765773348759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8542891062570510515565839 12814336593855765773348759)
              ·
                refine ⟨19221504890783648660023139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12814336593855765773348759 19221504890783648660023139)
                ·
                  refine ⟨28832257336175472990034709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19221504890783648660023139 28832257336175472990034709)
                  ·
                    refine ⟨1351512062633225296407877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28832257336175472990034709 1351512062633225296407877)
                    ·
                      rfl

theorem cell23_7896181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_7896181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7896181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7896181 prefixEnd_7896181 := by exact prefixLift 7896181
  have htrace : WordTrace (prefixWord ++ tailWord_7896181) baseStart_7896181 baseEnd_7896181 := by
    simpa [prefixWord, tailWord_7896181, baseEnd_7896181] using wordTrace_append hprefix tailTrace_7896181
  have hstable : (prefixWord ++ tailWord_7896181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7896181).length < 2 ^ (prefixWord ++ tailWord_7896181).sum := by decide
  have hdescent : baseEnd_7896181 < baseStart_7896181 := by decide
  rcases family_descends (prefixWord ++ tailWord_7896181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7896187 : List Nat := [1, 1, 1, 1, 1, 4, 1, 7, 2, 1, 3]
def baseStart_7896187 : Nat := 118140960795 + 7896187 * 2 ^ 59
def prefixEnd_7896187 : Nat := 4983230072969 + 3 ^ 40 * 7896187 * 2
def baseEnd_7896187 : Nat := 4054539268783602865748603

theorem tailTrace_7896187 : CollatzResearch.WordTrace tailWord_7896187 prefixEnd_7896187 4054539268783602865748603 := by
  unfold tailWord_7896187
  simp only [CollatzResearch.WordTrace]
  refine ⟨287997599844470535220254815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191998399896313690146836543 287997599844470535220254815)
  ·
    refine ⟨431996399766705802830382223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287997599844470535220254815 431996399766705802830382223)
    ·
      refine ⟨647994599650058704245573335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431996399766705802830382223 647994599650058704245573335)
      ·
        refine ⟨971991899475088056368360003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 647994599650058704245573335 971991899475088056368360003)
        ·
          refine ⟨1457987849212632084552540005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 971991899475088056368360003 1457987849212632084552540005)
          ·
            refine ⟨273372721727368515853601251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1457987849212632084552540005 273372721727368515853601251)
            ·
              refine ⟨410059082591052773780401877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273372721727368515853601251 410059082591052773780401877)
              ·
                refine ⟨9610759748227799385478169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 410059082591052773780401877 9610759748227799385478169)
                ·
                  refine ⟨7208069811170849539108627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9610759748227799385478169 7208069811170849539108627)
                  ·
                    refine ⟨10812104716756274308662941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7208069811170849539108627 10812104716756274308662941)
                    ·
                      refine ⟨4054539268783602865748603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10812104716756274308662941 4054539268783602865748603)
                      ·
                        rfl

theorem cell23_7896187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 7, 2, 1, 3].length) (baseStart_7896187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7896187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7896187 prefixEnd_7896187 := by exact prefixLift 7896187
  have htrace : WordTrace (prefixWord ++ tailWord_7896187) baseStart_7896187 baseEnd_7896187 := by
    simpa [prefixWord, tailWord_7896187, baseEnd_7896187] using wordTrace_append hprefix tailTrace_7896187
  have hstable : (prefixWord ++ tailWord_7896187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7896187).length < 2 ^ (prefixWord ++ tailWord_7896187).sum := by decide
  have hdescent : baseEnd_7896187 < baseStart_7896187 := by decide
  rcases family_descends (prefixWord ++ tailWord_7896187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7896203 : List Nat := [1, 1, 1, 1, 4, 1, 1, 4, 1, 8]
def baseStart_7896203 : Nat := 118140960795 + 7896203 * 2 ^ 59
def prefixEnd_7896203 : Nat := 4983230072969 + 3 ^ 40 * 7896203 * 2
def baseEnd_7896203 : Nat := 1351515828158024934382843

theorem tailTrace_7896203 : CollatzResearch.WordTrace tailWord_7896203 prefixEnd_7896203 1351515828158024934382843 := by
  unfold tailWord_7896203
  simp only [CollatzResearch.WordTrace]
  refine ⟨287998183412412569952837263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191998788941608379968558175 287998183412412569952837263)
  ·
    refine ⟨431997275118618854929255895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287998183412412569952837263 431997275118618854929255895)
    ·
      refine ⟨647995912677928282393883843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431997275118618854929255895 647995912677928282393883843)
      ·
        refine ⟨971993869016892423590825765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 647995912677928282393883843 971993869016892423590825765)
        ·
          refine ⟨182248850440667329423279831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 971993869016892423590825765 182248850440667329423279831)
          ·
            refine ⟨273373275661000994134919747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182248850440667329423279831 273373275661000994134919747)
            ·
              refine ⟨410059913491501491202379621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273373275661000994134919747 410059913491501491202379621)
              ·
                refine ⟨76886233779656529600446179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 410059913491501491202379621 76886233779656529600446179)
                ·
                  refine ⟨115329350669484794400669269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76886233779656529600446179 115329350669484794400669269)
                  ·
                    refine ⟨1351515828158024934382843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 115329350669484794400669269 1351515828158024934382843)
                    ·
                      rfl

theorem cell23_7896203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 8].length) (baseStart_7896203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7896203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7896203 prefixEnd_7896203 := by exact prefixLift 7896203
  have htrace : WordTrace (prefixWord ++ tailWord_7896203) baseStart_7896203 baseEnd_7896203 := by
    simpa [prefixWord, tailWord_7896203, baseEnd_7896203] using wordTrace_append hprefix tailTrace_7896203
  have hstable : (prefixWord ++ tailWord_7896203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7896203).length < 2 ^ (prefixWord ++ tailWord_7896203).sum := by decide
  have hdescent : baseEnd_7896203 < baseStart_7896203 := by decide
  rcases family_descends (prefixWord ++ tailWord_7896203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7896233 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 13]
def baseStart_7896233 : Nat := 118140960795 + 7896233 * 2 ^ 59
def prefixEnd_7896233 : Nat := 4983230072969 + 3 ^ 40 * 7896233 * 2
def baseEnd_7896233 : Nat := 450506987654856631752599

theorem tailTrace_7896233 : CollatzResearch.WordTrace tailWord_7896233 prefixEnd_7896233 450506987654856631752599 := by
  unfold tailWord_7896233
  simp only [CollatzResearch.WordTrace]
  refine ⟨287999277602303885076429353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191999518401535923384286235 287999277602303885076429353)
  ·
    refine ⟨215999458201727913807322015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287999277602303885076429353 215999458201727913807322015)
    ·
      refine ⟨323999187302591870710983023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215999458201727913807322015 323999187302591870710983023)
      ·
        refine ⟨485998780953887806066474535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323999187302591870710983023 485998780953887806066474535)
        ·
          refine ⟨728998171430831709099711803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 485998780953887806066474535 728998171430831709099711803)
          ·
            refine ⟨1093497257146247563649567705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 728998171430831709099711803 1093497257146247563649567705)
            ·
              refine ⟨820122942859685672737175779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1093497257146247563649567705 820122942859685672737175779)
              ·
                refine ⟨1230184414289528509105763669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 820122942859685672737175779 1230184414289528509105763669)
                ·
                  refine ⟨450506987654856631752599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 13 1230184414289528509105763669 450506987654856631752599)
                  ·
                    rfl

theorem cell23_7896233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 13].length) (baseStart_7896233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7896233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7896233 prefixEnd_7896233 := by exact prefixLift 7896233
  have htrace : WordTrace (prefixWord ++ tailWord_7896233) baseStart_7896233 baseEnd_7896233 := by
    simpa [prefixWord, tailWord_7896233, baseEnd_7896233] using wordTrace_append hprefix tailTrace_7896233
  have hstable : (prefixWord ++ tailWord_7896233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7896233).length < 2 ^ (prefixWord ++ tailWord_7896233).sum := by decide
  have hdescent : baseEnd_7896233 < baseStart_7896233 := by decide
  rcases family_descends (prefixWord ++ tailWord_7896233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7896287 : List Nat := [1, 1, 2, 3, 2, 1, 3, 1, 2, 5, 2]
def baseStart_7896287 : Nat := 118140960795 + 7896287 * 2 ^ 59
def prefixEnd_7896287 : Nat := 4983230072969 + 3 ^ 40 * 7896287 * 2
def baseEnd_7896287 : Nat := 4054590616849052474498143

theorem tailTrace_7896287 : CollatzResearch.WordTrace tailWord_7896287 prefixEnd_7896287 4054590616849052474498143 := by
  unfold tailWord_7896287
  simp only [CollatzResearch.WordTrace]
  refine ⟨288001247144108252298895115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192000831429405501532596743 288001247144108252298895115)
  ·
    refine ⟨432001870716162378448342673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288001247144108252298895115 432001870716162378448342673)
    ·
      refine ⟨324001403037121783836257005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432001870716162378448342673 324001403037121783836257005)
      ·
        refine ⟨121500526138920668938596377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 324001403037121783836257005 121500526138920668938596377)
        ·
          refine ⟨91125394604190501703947283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121500526138920668938596377 91125394604190501703947283)
          ·
            refine ⟨136688091906285752555920925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91125394604190501703947283 136688091906285752555920925)
            ·
              refine ⟨51258034464857157208470347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136688091906285752555920925 51258034464857157208470347)
              ·
                refine ⟨76887051697285735812705521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51258034464857157208470347 76887051697285735812705521)
                ·
                  refine ⟨57665288772964301859529141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76887051697285735812705521 57665288772964301859529141)
                  ·
                    refine ⟨5406120822465403299330857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57665288772964301859529141 5406120822465403299330857)
                    ·
                      refine ⟨4054590616849052474498143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5406120822465403299330857 4054590616849052474498143)
                      ·
                        rfl

theorem cell23_7896287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 5, 2].length) (baseStart_7896287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7896287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7896287 prefixEnd_7896287 := by exact prefixLift 7896287
  have htrace : WordTrace (prefixWord ++ tailWord_7896287) baseStart_7896287 baseEnd_7896287 := by
    simpa [prefixWord, tailWord_7896287, baseEnd_7896287] using wordTrace_append hprefix tailTrace_7896287
  have hstable : (prefixWord ++ tailWord_7896287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7896287).length < 2 ^ (prefixWord ++ tailWord_7896287).sum := by decide
  have hdescent : baseEnd_7896287 < baseStart_7896287 := by decide
  rcases family_descends (prefixWord ++ tailWord_7896287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7896334 : List Nat := [4, 1, 1, 2, 1, 3, 1, 2, 2, 4, 2]
def baseStart_7896334 : Nat := 118140960795 + 7896334 * 2 ^ 59
def prefixEnd_7896334 : Nat := 4983230072969 + 3 ^ 40 * 7896334 * 2
def baseEnd_7896334 : Nat := 4054614750439813790610427

theorem tailTrace_7896334 : CollatzResearch.WordTrace tailWord_7896334 prefixEnd_7896334 4054614750439813790610427 := by
  unfold tailWord_7896334
  simp only [CollatzResearch.WordTrace]
  refine ⟨36000370171867247415732007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192001974249958652883904037 36000370171867247415732007)
  ·
    refine ⟨54000555257800871123598011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36000370171867247415732007 54000555257800871123598011)
    ·
      refine ⟨81000832886701306685397017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54000555257800871123598011 81000832886701306685397017)
      ·
        refine ⟨60750624665025980014047763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81000832886701306685397017 60750624665025980014047763)
        ·
          refine ⟨91125936997538970021071645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60750624665025980014047763 91125936997538970021071645)
          ·
            refine ⟨34172226374077113757901867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91125936997538970021071645 34172226374077113757901867)
            ·
              refine ⟨51258339561115670636852801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34172226374077113757901867 51258339561115670636852801)
              ·
                refine ⟨38443754670836752977639601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51258339561115670636852801 38443754670836752977639601)
                ·
                  refine ⟨28832816003127564733229701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38443754670836752977639601 28832816003127564733229701)
                  ·
                    refine ⟨5406153000586418387480569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28832816003127564733229701 5406153000586418387480569)
                    ·
                      refine ⟨4054614750439813790610427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5406153000586418387480569 4054614750439813790610427)
                      ·
                        rfl

theorem cell23_7896334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 2, 4, 2].length) (baseStart_7896334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7896334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7896334 prefixEnd_7896334 := by exact prefixLift 7896334
  have htrace : WordTrace (prefixWord ++ tailWord_7896334) baseStart_7896334 baseEnd_7896334 := by
    simpa [prefixWord, tailWord_7896334, baseEnd_7896334] using wordTrace_append hprefix tailTrace_7896334
  have hstable : (prefixWord ++ tailWord_7896334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7896334).length < 2 ^ (prefixWord ++ tailWord_7896334).sum := by decide
  have hdescent : baseEnd_7896334 < baseStart_7896334 := by decide
  rcases family_descends (prefixWord ++ tailWord_7896334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7896337 : List Nat := [1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 3]
def baseStart_7896337 : Nat := 118140960795 + 7896337 * 2 ^ 59
def prefixEnd_7896337 : Nat := 4983230072969 + 3 ^ 40 * 7896337 * 2
def baseEnd_7896337 : Nat := 4054616290881777278872913

theorem tailTrace_7896337 : CollatzResearch.WordTrace tailWord_7896337 prefixEnd_7896337 4054616290881777278872913 := by
  unfold tailWord_7896337
  simp only [CollatzResearch.WordTrace]
  refine ⟨288003070793927110838215265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192002047195951407225476843 288003070793927110838215265)
  ·
    refine ⟨216002303095445333128661449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288003070793927110838215265 216002303095445333128661449)
    ·
      refine ⟨162001727321583999846496087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216002303095445333128661449 162001727321583999846496087)
      ·
        refine ⟨243002590982375999769744131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162001727321583999846496087 243002590982375999769744131)
        ·
          refine ⟨364503886473563999654616197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243002590982375999769744131 364503886473563999654616197)
          ·
            refine ⟨68344478713793249935240537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 364503886473563999654616197 68344478713793249935240537)
            ·
              refine ⟨51258359035344937451430403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68344478713793249935240537 51258359035344937451430403)
              ·
                refine ⟨76887538553017406177145605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51258359035344937451430403 76887538553017406177145605)
                ·
                  refine ⟨14416413478690763658214801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76887538553017406177145605 14416413478690763658214801)
                  ·
                    refine ⟨10812310109018072743661101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14416413478690763658214801 10812310109018072743661101)
                    ·
                      refine ⟨4054616290881777278872913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10812310109018072743661101 4054616290881777278872913)
                      ·
                        rfl

theorem cell23_7896337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 3].length) (baseStart_7896337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7896337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7896337 prefixEnd_7896337 := by exact prefixLift 7896337
  have htrace : WordTrace (prefixWord ++ tailWord_7896337) baseStart_7896337 baseEnd_7896337 := by
    simpa [prefixWord, tailWord_7896337, baseEnd_7896337] using wordTrace_append hprefix tailTrace_7896337
  have hstable : (prefixWord ++ tailWord_7896337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7896337).length < 2 ^ (prefixWord ++ tailWord_7896337).sum := by decide
  have hdescent : baseEnd_7896337 < baseStart_7896337 := by decide
  rcases family_descends (prefixWord ++ tailWord_7896337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7896344 : List Nat := [2, 1, 2, 3, 1, 4, 2, 1, 3, 4]
def baseStart_7896344 : Nat := 118140960795 + 7896344 * 2 ^ 59
def prefixEnd_7896344 : Nat := 4983230072969 + 3 ^ 40 * 7896344 * 2
def baseEnd_7896344 : Nat := 1351539961748786250495127

theorem tailTrace_7896344 : CollatzResearch.WordTrace tailWord_7896344 prefixEnd_7896344 1351539961748786250495127 := by
  unfold tailWord_7896344
  simp only [CollatzResearch.WordTrace]
  refine ⟨144001663052450875516860043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192002217403267834022480057 144001663052450875516860043)
  ·
    refine ⟨216002494578676313275290065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144001663052450875516860043 216002494578676313275290065)
    ·
      refine ⟨162001870934007234956467549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216002494578676313275290065 162001870934007234956467549)
      ·
        refine ⟨60750701600252713108675331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162001870934007234956467549 60750701600252713108675331)
        ·
          refine ⟨91126052400379069663012997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60750701600252713108675331 91126052400379069663012997)
          ·
            refine ⟨17086134825071075561814937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91126052400379069663012997 17086134825071075561814937)
            ·
              refine ⟨12814601118803306671361203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17086134825071075561814937 12814601118803306671361203)
              ·
                refine ⟨19221901678204960007041805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12814601118803306671361203 19221901678204960007041805)
                ·
                  refine ⟨7208213129326860002640677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19221901678204960007041805 7208213129326860002640677)
                  ·
                    refine ⟨1351539961748786250495127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7208213129326860002640677 1351539961748786250495127)
                    ·
                      rfl

theorem cell23_7896344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 1, 3, 4].length) (baseStart_7896344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7896344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7896344 prefixEnd_7896344 := by exact prefixLift 7896344
  have htrace : WordTrace (prefixWord ++ tailWord_7896344) baseStart_7896344 baseEnd_7896344 := by
    simpa [prefixWord, tailWord_7896344, baseEnd_7896344] using wordTrace_append hprefix tailTrace_7896344
  have hstable : (prefixWord ++ tailWord_7896344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7896344).length < 2 ^ (prefixWord ++ tailWord_7896344).sum := by decide
  have hdescent : baseEnd_7896344 < baseStart_7896344 := by decide
  rcases family_descends (prefixWord ++ tailWord_7896344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7896451 : List Nat := [1, 1, 1, 3, 5, 2, 2, 2, 2, 4]
def baseStart_7896451 : Nat := 118140960795 + 7896451 * 2 ^ 59
def prefixEnd_7896451 : Nat := 4983230072969 + 3 ^ 40 * 7896451 * 2
def baseEnd_7896451 : Nat := 1351558275892129944282463

theorem tailTrace_7896451 : CollatzResearch.WordTrace tailWord_7896451 prefixEnd_7896451 1351558275892129944282463 := by
  unfold tailWord_7896451
  simp only [CollatzResearch.WordTrace]
  refine ⟨288007228715514108307865207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192004819143676072205243471 288007228715514108307865207)
  ·
    refine ⟨432010843073271162461797811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288007228715514108307865207 432010843073271162461797811)
    ·
      refine ⟨648016264609906743692696717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432010843073271162461797811 648016264609906743692696717)
      ·
        refine ⟨243006099228715028884761269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 648016264609906743692696717 243006099228715028884761269)
        ·
          refine ⟨22781821802692033957946369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 243006099228715028884761269 22781821802692033957946369)
          ·
            refine ⟨17086366352019025468459777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22781821802692033957946369 17086366352019025468459777)
            ·
              refine ⟨12814774764014269101344833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17086366352019025468459777 12814774764014269101344833)
              ·
                refine ⟨9611081073010701826008625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12814774764014269101344833 9611081073010701826008625)
                ·
                  refine ⟨7208310804758026369506469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9611081073010701826008625 7208310804758026369506469)
                  ·
                    refine ⟨1351558275892129944282463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7208310804758026369506469 1351558275892129944282463)
                    ·
                      rfl

theorem cell23_7896451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 2, 2, 4].length) (baseStart_7896451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7896451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7896451 prefixEnd_7896451 := by exact prefixLift 7896451
  have htrace : WordTrace (prefixWord ++ tailWord_7896451) baseStart_7896451 baseEnd_7896451 := by
    simpa [prefixWord, tailWord_7896451, baseEnd_7896451] using wordTrace_append hprefix tailTrace_7896451
  have hstable : (prefixWord ++ tailWord_7896451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7896451).length < 2 ^ (prefixWord ++ tailWord_7896451).sum := by decide
  have hdescent : baseEnd_7896451 < baseStart_7896451 := by decide
  rcases family_descends (prefixWord ++ tailWord_7896451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7896508 : List Nat := [2, 2, 2, 4, 2, 1, 1, 1, 4, 1, 3]
def baseStart_7896508 : Nat := 118140960795 + 7896508 * 2 ^ 59
def prefixEnd_7896508 : Nat := 4983230072969 + 3 ^ 40 * 7896508 * 2
def baseEnd_7896508 : Nat := 4054704096073696109834627

theorem tailTrace_7896508 : CollatzResearch.WordTrace tailWord_7896508 prefixEnd_7896508 4054704096073696109834627 := by
  unfold tailWord_7896508
  simp only [CollatzResearch.WordTrace]
  refine ⟨144004653838153803521345089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192006205117538404695126785 144004653838153803521345089)
  ·
    refine ⟨108003490378615352641008817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144004653838153803521345089 108003490378615352641008817)
    ·
      refine ⟨81002617783961514480756613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108003490378615352641008817 81002617783961514480756613)
      ·
        refine ⟨15187990834492783965141865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81002617783961514480756613 15187990834492783965141865)
        ·
          refine ⟨11390993125869587973856399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15187990834492783965141865 11390993125869587973856399)
          ·
            refine ⟨17086489688804381960784599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11390993125869587973856399 17086489688804381960784599)
            ·
              refine ⟨25629734533206572941176899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17086489688804381960784599 25629734533206572941176899)
              ·
                refine ⟨38444601799809859411765349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25629734533206572941176899 38444601799809859411765349)
                ·
                  refine ⟨7208362837464348639706003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38444601799809859411765349 7208362837464348639706003)
                  ·
                    refine ⟨10812544256196522959559005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7208362837464348639706003 10812544256196522959559005)
                    ·
                      refine ⟨4054704096073696109834627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10812544256196522959559005 4054704096073696109834627)
                      ·
                        rfl

theorem cell23_7896508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_7896508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7896508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7896508 prefixEnd_7896508 := by exact prefixLift 7896508
  have htrace : WordTrace (prefixWord ++ tailWord_7896508) baseStart_7896508 baseEnd_7896508 := by
    simpa [prefixWord, tailWord_7896508, baseEnd_7896508] using wordTrace_append hprefix tailTrace_7896508
  have hstable : (prefixWord ++ tailWord_7896508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7896508).length < 2 ^ (prefixWord ++ tailWord_7896508).sum := by decide
  have hdescent : baseEnd_7896508 < baseStart_7896508 := by decide
  rcases family_descends (prefixWord ++ tailWord_7896508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7896524 : List Nat := [2, 2, 1, 4, 2, 1, 2, 1, 2, 6]
def baseStart_7896524 : Nat := 118140960795 + 7896524 * 2 ^ 59
def prefixEnd_7896524 : Nat := 4983230072969 + 3 ^ 40 * 7896524 * 2
def baseEnd_7896524 : Nat := 1351570770588056015744851

theorem tailTrace_7896524 : CollatzResearch.WordTrace tailWord_7896524 prefixEnd_7896524 1351570770588056015744851 := by
  unfold tailWord_7896524
  simp only [CollatzResearch.WordTrace]
  refine ⟨144004945622124820887636313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192006594162833094516848417 144004945622124820887636313)
  ·
    refine ⟨108003709216593615665727235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144004945622124820887636313 108003709216593615665727235)
    ·
      refine ⟨162005563824890423498590853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108003709216593615665727235 162005563824890423498590853)
      ·
        refine ⟨30376043217166954405985785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162005563824890423498590853 30376043217166954405985785)
        ·
          refine ⟨22782032412875215804489339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30376043217166954405985785 22782032412875215804489339)
          ·
            refine ⟨34173048619312823706734009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22782032412875215804489339 34173048619312823706734009)
            ·
              refine ⟨25629786464484617780050507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34173048619312823706734009 25629786464484617780050507)
              ·
                refine ⟨38444679696726926670075761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25629786464484617780050507 38444679696726926670075761)
                ·
                  refine ⟨28833509772545195002556821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38444679696726926670075761 28833509772545195002556821)
                  ·
                    refine ⟨1351570770588056015744851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28833509772545195002556821 1351570770588056015744851)
                    ·
                      rfl

theorem cell23_7896524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 2, 6].length) (baseStart_7896524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7896524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7896524 prefixEnd_7896524 := by exact prefixLift 7896524
  have htrace : WordTrace (prefixWord ++ tailWord_7896524) baseStart_7896524 baseEnd_7896524 := by
    simpa [prefixWord, tailWord_7896524, baseEnd_7896524] using wordTrace_append hprefix tailTrace_7896524
  have hstable : (prefixWord ++ tailWord_7896524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7896524).length < 2 ^ (prefixWord ++ tailWord_7896524).sum := by decide
  have hdescent : baseEnd_7896524 < baseStart_7896524 := by decide
  rcases family_descends (prefixWord ++ tailWord_7896524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7896565 : List Nat := [1, 3, 5, 1, 1, 1, 2, 1, 4, 2, 2]
def baseStart_7896565 : Nat := 118140960795 + 7896565 * 2 ^ 59
def prefixEnd_7896565 : Nat := 4983230072969 + 3 ^ 40 * 7896565 * 2
def baseEnd_7896565 : Nat := 4054733364471002386821865

theorem tailTrace_7896565 : CollatzResearch.WordTrace tailWord_7896565 prefixEnd_7896565 4054733364471002386821865 := by
  unfold tailWord_7896565
  simp only [CollatzResearch.WordTrace]
  refine ⟨288011386637101105777515149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192007591091400737185010099 288011386637101105777515149)
  ·
    refine ⟨108004269988912914666568181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288011386637101105777515149 108004269988912914666568181)
    ·
      refine ⟨10125400311460585749990767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108004269988912914666568181 10125400311460585749990767)
      ·
        refine ⟨15188100467190878624986151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10125400311460585749990767 15188100467190878624986151)
        ·
          refine ⟨22782150700786317937479227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15188100467190878624986151 22782150700786317937479227)
          ·
            refine ⟨34173226051179476906218841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22782150700786317937479227 34173226051179476906218841)
            ·
              refine ⟨25629919538384607679664131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34173226051179476906218841 25629919538384607679664131)
              ·
                refine ⟨38444879307576911519496197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25629919538384607679664131 38444879307576911519496197)
                ·
                  refine ⟨7208414870170670909905537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38444879307576911519496197 7208414870170670909905537)
                  ·
                    refine ⟨5406311152628003182429153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7208414870170670909905537 5406311152628003182429153)
                    ·
                      refine ⟨4054733364471002386821865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5406311152628003182429153 4054733364471002386821865)
                      ·
                        rfl

theorem cell23_7896565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_7896565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7896565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7896565 prefixEnd_7896565 := by exact prefixLift 7896565
  have htrace : WordTrace (prefixWord ++ tailWord_7896565) baseStart_7896565 baseEnd_7896565 := by
    simpa [prefixWord, tailWord_7896565, baseEnd_7896565] using wordTrace_append hprefix tailTrace_7896565
  have hstable : (prefixWord ++ tailWord_7896565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7896565).length < 2 ^ (prefixWord ++ tailWord_7896565).sum := by decide
  have hdescent : baseEnd_7896565 < baseStart_7896565 := by decide
  rcases family_descends (prefixWord ++ tailWord_7896565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7896567 : List Nat := [1, 1, 3, 1, 1, 1, 1, 4, 3, 7]
def baseStart_7896567 : Nat := 118140960795 + 7896567 * 2 ^ 59
def prefixEnd_7896567 : Nat := 4983230072969 + 3 ^ 40 * 7896567 * 2
def baseEnd_7896567 : Nat := 1351578130477437126332285

theorem tailTrace_7896567 : CollatzResearch.WordTrace tailWord_7896567 prefixEnd_7896567 1351578130477437126332285 := by
  unfold tailWord_7896567
  simp only [CollatzResearch.WordTrace]
  refine ⟨288011459583093860119087955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192007639722062573412725303 288011459583093860119087955)
  ·
    refine ⟨432017189374640790178631933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288011459583093860119087955 432017189374640790178631933)
    ·
      refine ⟨162006446015490296316986975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 432017189374640790178631933 162006446015490296316986975)
      ·
        refine ⟨243009669023235444475480463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162006446015490296316986975 243009669023235444475480463)
        ·
          refine ⟨364514503534853166713220695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243009669023235444475480463 364514503534853166713220695)
          ·
            refine ⟨546771755302279750069831043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364514503534853166713220695 546771755302279750069831043)
            ·
              refine ⟨820157632953419625104746565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 546771755302279750069831043 820157632953419625104746565)
              ·
                refine ⟨153779556178766179707139981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 820157632953419625104746565 153779556178766179707139981)
                ·
                  refine ⟨57667333567037317390177493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 153779556178766179707139981 57667333567037317390177493)
                  ·
                    refine ⟨1351578130477437126332285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57667333567037317390177493 1351578130477437126332285)
                    ·
                      rfl

theorem cell23_7896567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 7].length) (baseStart_7896567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7896567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7896567 prefixEnd_7896567 := by exact prefixLift 7896567
  have htrace : WordTrace (prefixWord ++ tailWord_7896567) baseStart_7896567 baseEnd_7896567 := by
    simpa [prefixWord, tailWord_7896567, baseEnd_7896567] using wordTrace_append hprefix tailTrace_7896567
  have hstable : (prefixWord ++ tailWord_7896567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7896567).length < 2 ^ (prefixWord ++ tailWord_7896567).sum := by decide
  have hdescent : baseEnd_7896567 < baseStart_7896567 := by decide
  rcases family_descends (prefixWord ++ tailWord_7896567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7896624 : List Nat := [2, 1, 1, 1, 2, 3, 1, 2, 3, 4, 3]
def baseStart_7896624 : Nat := 118140960795 + 7896624 * 2 ^ 59
def prefixEnd_7896624 : Nat := 4983230072969 + 3 ^ 40 * 7896624 * 2
def baseEnd_7896624 : Nat := 4054763659829617655984093

theorem tailTrace_7896624 : CollatzResearch.WordTrace tailWord_7896624 prefixEnd_7896624 4054763659829617655984093 := by
  unfold tailWord_7896624
  simp only [CollatzResearch.WordTrace]
  refine ⟨144006769271943679426956463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192009025695924905902608617 144006769271943679426956463)
  ·
    refine ⟨216010153907915519140434695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144006769271943679426956463 216010153907915519140434695)
    ·
      refine ⟨324015230861873278710652043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216010153907915519140434695 324015230861873278710652043)
      ·
        refine ⟨486022846292809918065978065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324015230861873278710652043 486022846292809918065978065)
        ·
          refine ⟨364517134719607438549483549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 486022846292809918065978065 364517134719607438549483549)
          ·
            refine ⟨136693925519852789456056331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 364517134719607438549483549 136693925519852789456056331)
            ·
              refine ⟨205040888279779184184084497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136693925519852789456056331 205040888279779184184084497)
              ·
                refine ⟨153780666209834388138063373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205040888279779184184084497 153780666209834388138063373)
                ·
                  refine ⟨57667749828687895551773765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 153780666209834388138063373 57667749828687895551773765)
                  ·
                    refine ⟨10812703092878980415957581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57667749828687895551773765 10812703092878980415957581)
                    ·
                      refine ⟨4054763659829617655984093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10812703092878980415957581 4054763659829617655984093)
                      ·
                        rfl

theorem cell23_7896624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 3, 4, 3].length) (baseStart_7896624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7896624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7896624 prefixEnd_7896624 := by exact prefixLift 7896624
  have htrace : WordTrace (prefixWord ++ tailWord_7896624) baseStart_7896624 baseEnd_7896624 := by
    simpa [prefixWord, tailWord_7896624, baseEnd_7896624] using wordTrace_append hprefix tailTrace_7896624
  have hstable : (prefixWord ++ tailWord_7896624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7896624).length < 2 ^ (prefixWord ++ tailWord_7896624).sum := by decide
  have hdescent : baseEnd_7896624 < baseStart_7896624 := by decide
  rcases family_descends (prefixWord ++ tailWord_7896624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7896641 : List Nat := [1, 2, 5, 1, 1, 1, 2, 2, 1, 4, 3]
def baseStart_7896641 : Nat := 118140960795 + 7896641 * 2 ^ 59
def prefixEnd_7896641 : Nat := 4983230072969 + 3 ^ 40 * 7896641 * 2
def baseEnd_7896641 : Nat := 4054772389000744089471515

theorem tailTrace_7896641 : CollatzResearch.WordTrace tailWord_7896641 prefixEnd_7896641 4054772389000744089471515 := by
  unfold tailWord_7896641
  simp only [CollatzResearch.WordTrace]
  refine ⟨288014158584825770757281777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192009439056550513838187851 288014158584825770757281777)
  ·
    refine ⟨216010618938619328067961333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288014158584825770757281777 216010618938619328067961333)
    ·
      refine ⟨20250995525495562006371375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 216010618938619328067961333 20250995525495562006371375)
      ·
        refine ⟨30376493288243343009557063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20250995525495562006371375 30376493288243343009557063)
        ·
          refine ⟨45564739932365014514335595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30376493288243343009557063 45564739932365014514335595)
          ·
            refine ⟨68347109898547521771503393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45564739932365014514335595 68347109898547521771503393)
            ·
              refine ⟨51260332423910641328627545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68347109898547521771503393 51260332423910641328627545)
              ·
                refine ⟨38445249317932980996470659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51260332423910641328627545 38445249317932980996470659)
                ·
                  refine ⟨57667873976899471494705989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38445249317932980996470659 57667873976899471494705989)
                  ·
                    refine ⟨10812726370668650905257373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57667873976899471494705989 10812726370668650905257373)
                    ·
                      refine ⟨4054772389000744089471515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10812726370668650905257373 4054772389000744089471515)
                      ·
                        rfl

theorem cell23_7896641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_7896641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7896641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7896641 prefixEnd_7896641 := by exact prefixLift 7896641
  have htrace : WordTrace (prefixWord ++ tailWord_7896641) baseStart_7896641 baseEnd_7896641 := by
    simpa [prefixWord, tailWord_7896641, baseEnd_7896641] using wordTrace_append hprefix tailTrace_7896641
  have hstable : (prefixWord ++ tailWord_7896641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7896641).length < 2 ^ (prefixWord ++ tailWord_7896641).sum := by decide
  have hdescent : baseEnd_7896641 < baseStart_7896641 := by decide
  rcases family_descends (prefixWord ++ tailWord_7896641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7896658 : List Nat := [3, 2, 2, 1, 2, 2, 3, 1, 2, 2, 3]
def baseStart_7896658 : Nat := 118140960795 + 7896658 * 2 ^ 59
def prefixEnd_7896658 : Nat := 4983230072969 + 3 ^ 40 * 7896658 * 2
def baseEnd_7896658 : Nat := 4054781118171870522958937

theorem tailTrace_7896658 : CollatzResearch.WordTrace tailWord_7896658 prefixEnd_7896658 4054781118171870522958937 := by
  unfold tailWord_7896658
  simp only [CollatzResearch.WordTrace]
  refine ⟨72003694656441045665162657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192009852417176121773767085 72003694656441045665162657)
  ·
    refine ⟨54002770992330784248871993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72003694656441045665162657 54002770992330784248871993)
    ·
      refine ⟨40502078244248088186653995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54002770992330784248871993 40502078244248088186653995)
      ·
        refine ⟨60753117366372132279980993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40502078244248088186653995 60753117366372132279980993)
        ·
          refine ⟨45564838024779099209985745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60753117366372132279980993 45564838024779099209985745)
          ·
            refine ⟨34173628518584324407489309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45564838024779099209985745 34173628518584324407489309)
            ·
              refine ⟨12815110694469121652808491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34173628518584324407489309 12815110694469121652808491)
              ·
                refine ⟨19222666041703682479212737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12815110694469121652808491 19222666041703682479212737)
                ·
                  refine ⟨14416999531277761859409553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19222666041703682479212737 14416999531277761859409553)
                  ·
                    refine ⟨10812749648458321394557165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14416999531277761859409553 10812749648458321394557165)
                    ·
                      refine ⟨4054781118171870522958937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10812749648458321394557165 4054781118171870522958937)
                      ·
                        rfl

theorem cell23_7896658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 1, 2, 2, 3].length) (baseStart_7896658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7896658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7896658 prefixEnd_7896658 := by exact prefixLift 7896658
  have htrace : WordTrace (prefixWord ++ tailWord_7896658) baseStart_7896658 baseEnd_7896658 := by
    simpa [prefixWord, tailWord_7896658, baseEnd_7896658] using wordTrace_append hprefix tailTrace_7896658
  have hstable : (prefixWord ++ tailWord_7896658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7896658).length < 2 ^ (prefixWord ++ tailWord_7896658).sum := by decide
  have hdescent : baseEnd_7896658 < baseStart_7896658 := by decide
  rcases family_descends (prefixWord ++ tailWord_7896658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7896688 : List Nat := [2, 1, 1, 1, 6, 1, 1, 3, 3, 1, 3]
def baseStart_7896688 : Nat := 118140960795 + 7896688 * 2 ^ 59
def prefixEnd_7896688 : Nat := 4983230072969 + 3 ^ 40 * 7896688 * 2
def baseEnd_7896688 : Nat := 4054796522591505405583799

theorem tailTrace_7896688 : CollatzResearch.WordTrace tailWord_7896688 prefixEnd_7896688 4054796522591505405583799 := by
  unfold tailWord_7896688
  simp only [CollatzResearch.WordTrace]
  refine ⟨144007936407827748892121359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192010581877103665189495145 144007936407827748892121359)
  ·
    refine ⟨216011904611741623338182039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144007936407827748892121359 216011904611741623338182039)
    ·
      refine ⟨324017856917612435007273059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216011904611741623338182039 324017856917612435007273059)
      ·
        refine ⟨486026785376418652510909589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324017856917612435007273059 486026785376418652510909589)
        ·
          refine ⟨22782505564519624336448887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 486026785376418652510909589 22782505564519624336448887)
          ·
            refine ⟨34173758346779436504673331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22782505564519624336448887 34173758346779436504673331)
            ·
              refine ⟨51260637520169154757009997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34173758346779436504673331 51260637520169154757009997)
              ·
                refine ⟨19222739070063433033878749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51260637520169154757009997 19222739070063433033878749)
                ·
                  refine ⟨7208527151273787387704531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19222739070063433033878749 7208527151273787387704531)
                  ·
                    refine ⟨10812790726910681081556797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7208527151273787387704531 10812790726910681081556797)
                    ·
                      refine ⟨4054796522591505405583799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10812790726910681081556797 4054796522591505405583799)
                      ·
                        rfl

theorem cell23_7896688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 3, 3, 1, 3].length) (baseStart_7896688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7896688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7896688 prefixEnd_7896688 := by exact prefixLift 7896688
  have htrace : WordTrace (prefixWord ++ tailWord_7896688) baseStart_7896688 baseEnd_7896688 := by
    simpa [prefixWord, tailWord_7896688, baseEnd_7896688] using wordTrace_append hprefix tailTrace_7896688
  have hstable : (prefixWord ++ tailWord_7896688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7896688).length < 2 ^ (prefixWord ++ tailWord_7896688).sum := by decide
  have hdescent : baseEnd_7896688 < baseStart_7896688 := by decide
  rcases family_descends (prefixWord ++ tailWord_7896688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7896728 : List Nat := [2, 1, 2, 4, 1, 2, 2, 3, 1, 1, 4]
def baseStart_7896728 : Nat := 118140960795 + 7896728 * 2 ^ 59
def prefixEnd_7896728 : Nat := 4983230072969 + 3 ^ 40 * 7896728 * 2
def baseEnd_7896728 : Nat := 4054817061817685249083615

theorem tailTrace_7896728 : CollatzResearch.WordTrace tailWord_7896728 prefixEnd_7896728 4054817061817685249083615 := by
  unfold tailWord_7896728
  simp only [CollatzResearch.WordTrace]
  refine ⟨144008665867755292307849419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192011554490340389743799225 144008665867755292307849419)
  ·
    refine ⟨216012998801632938461774129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144008665867755292307849419 216012998801632938461774129)
    ·
      refine ⟨162009749101224703846330597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216012998801632938461774129 162009749101224703846330597)
      ·
        refine ⟨30376827956479631971186987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162009749101224703846330597 30376827956479631971186987)
        ·
          refine ⟨45565241934719447956780481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30376827956479631971186987 45565241934719447956780481)
          ·
            refine ⟨34173931451039585967585361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45565241934719447956780481 34173931451039585967585361)
            ·
              refine ⟨25630448588279689475689021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34173931451039585967585361 25630448588279689475689021)
              ·
                refine ⟨9611418220604883553383383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25630448588279689475689021 9611418220604883553383383)
                ·
                  refine ⟨14417127330907325330075075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9611418220604883553383383 14417127330907325330075075)
                  ·
                    refine ⟨21625690996360987995112613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14417127330907325330075075 21625690996360987995112613)
                    ·
                      refine ⟨4054817061817685249083615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21625690996360987995112613 4054817061817685249083615)
                      ·
                        rfl

theorem cell23_7896728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_7896728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7896728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7896728 prefixEnd_7896728 := by exact prefixLift 7896728
  have htrace : WordTrace (prefixWord ++ tailWord_7896728) baseStart_7896728 baseEnd_7896728 := by
    simpa [prefixWord, tailWord_7896728, baseEnd_7896728] using wordTrace_append hprefix tailTrace_7896728
  have hstable : (prefixWord ++ tailWord_7896728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7896728).length < 2 ^ (prefixWord ++ tailWord_7896728).sum := by decide
  have hdescent : baseEnd_7896728 < baseStart_7896728 := by decide
  rcases family_descends (prefixWord ++ tailWord_7896728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7896790 : List Nat := [5, 2, 1, 3, 2, 1, 2, 2, 1, 1, 3]
def baseStart_7896790 : Nat := 118140960795 + 7896790 * 2 ^ 59
def prefixEnd_7896790 : Nat := 4983230072969 + 3 ^ 40 * 7896790 * 2
def baseEnd_7896790 : Nat := 4054848897618264006508331

theorem tailTrace_7896790 : CollatzResearch.WordTrace tailWord_7896790 prefixEnd_7896790 4054848897618264006508331 := by
  unfold tailWord_7896790
  simp only [CollatzResearch.WordTrace]
  refine ⟨18001224566330373075278489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 192013062040857312802970549 18001224566330373075278489)
  ·
    refine ⟨13500918424747779806458867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18001224566330373075278489 13500918424747779806458867)
    ·
      refine ⟨20251377637121669709688301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13500918424747779806458867 20251377637121669709688301)
      ·
        refine ⟨7594266613920626141133113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20251377637121669709688301 7594266613920626141133113)
        ·
          refine ⟨5695699960440469605849835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7594266613920626141133113 5695699960440469605849835)
          ·
            refine ⟨8543549940660704408774753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5695699960440469605849835 8543549940660704408774753)
            ·
              refine ⟨6407662455495528306581065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8543549940660704408774753 6407662455495528306581065)
              ·
                refine ⟨4805746841621646229935799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6407662455495528306581065 4805746841621646229935799)
                ·
                  refine ⟨7208620262432469344903699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4805746841621646229935799 7208620262432469344903699)
                  ·
                    refine ⟨10812930393648704017355549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7208620262432469344903699 10812930393648704017355549)
                    ·
                      refine ⟨4054848897618264006508331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10812930393648704017355549 4054848897618264006508331)
                      ·
                        rfl

theorem cell23_7896790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_7896790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7896790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7896790 prefixEnd_7896790 := by exact prefixLift 7896790
  have htrace : WordTrace (prefixWord ++ tailWord_7896790) baseStart_7896790 baseEnd_7896790 := by
    simpa [prefixWord, tailWord_7896790, baseEnd_7896790] using wordTrace_append hprefix tailTrace_7896790
  have hstable : (prefixWord ++ tailWord_7896790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7896790).length < 2 ^ (prefixWord ++ tailWord_7896790).sum := by decide
  have hdescent : baseEnd_7896790 < baseStart_7896790 := by decide
  rcases family_descends (prefixWord ++ tailWord_7896790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7896796 : List Nat := [2, 2, 5, 1, 2, 1, 1, 4, 1, 2, 2]
def baseStart_7896796 : Nat := 118140960795 + 7896796 * 2 ^ 59
def prefixEnd_7896796 : Nat := 4983230072969 + 3 ^ 40 * 7896796 * 2
def baseEnd_7896796 : Nat := 4054851978502190983033303

theorem tailTrace_7896796 : CollatzResearch.WordTrace tailWord_7896796 prefixEnd_7896796 4054851978502190983033303 := by
  unfold tailWord_7896796
  simp only [CollatzResearch.WordTrace]
  refine ⟨144009905949632116114587121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192013207932842821486116161 144009905949632116114587121)
  ·
    refine ⟨108007429462224087085940341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144009905949632116114587121 108007429462224087085940341)
    ·
      refine ⟨10125696512083508164306907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108007429462224087085940341 10125696512083508164306907)
      ·
        refine ⟨15188544768125262246460361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10125696512083508164306907 15188544768125262246460361)
        ·
          refine ⟨11391408576093946684845271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15188544768125262246460361 11391408576093946684845271)
          ·
            refine ⟨17087112864140920027267907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11391408576093946684845271 17087112864140920027267907)
            ·
              refine ⟨25630669296211380040901861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17087112864140920027267907 25630669296211380040901861)
              ·
                refine ⟨4805750493039633757669099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25630669296211380040901861 4805750493039633757669099)
                ·
                  refine ⟨7208625739559450636503649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4805750493039633757669099 7208625739559450636503649)
                  ·
                    refine ⟨5406469304669587977377737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7208625739559450636503649 5406469304669587977377737)
                    ·
                      refine ⟨4054851978502190983033303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5406469304669587977377737 4054851978502190983033303)
                      ·
                        rfl

theorem cell23_7896796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_7896796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7896796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7896796 prefixEnd_7896796 := by exact prefixLift 7896796
  have htrace : WordTrace (prefixWord ++ tailWord_7896796) baseStart_7896796 baseEnd_7896796 := by
    simpa [prefixWord, tailWord_7896796, baseEnd_7896796] using wordTrace_append hprefix tailTrace_7896796
  have hstable : (prefixWord ++ tailWord_7896796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7896796).length < 2 ^ (prefixWord ++ tailWord_7896796).sum := by decide
  have hdescent : baseEnd_7896796 < baseStart_7896796 := by decide
  rcases family_descends (prefixWord ++ tailWord_7896796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7896858 : List Nat := [3, 1, 1, 3, 2, 3, 2, 1, 7]
def baseStart_7896858 : Nat := 118140960795 + 7896858 * 2 ^ 59
def prefixEnd_7896858 : Nat := 4983230072969 + 3 ^ 40 * 7896858 * 2
def baseEnd_7896858 : Nat := 450542646033641082273113

theorem tailTrace_7896858 : CollatzResearch.WordTrace tailWord_7896858 prefixEnd_7896858 450542646033641082273113 := by
  unfold tailWord_7896858
  simp only [CollatzResearch.WordTrace]
  refine ⟨72005518306259904204482807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192014715483359744545287485 72005518306259904204482807)
  ·
    refine ⟨108008277459389856306724211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72005518306259904204482807 108008277459389856306724211)
    ·
      refine ⟨162012416189084784460086317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108008277459389856306724211 162012416189084784460086317)
      ·
        refine ⟨60754656070906794172532369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162012416189084784460086317 60754656070906794172532369)
        ·
          refine ⟨45565992053180095629399277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60754656070906794172532369 45565992053180095629399277)
          ·
            refine ⟨17087247019942535861024729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45565992053180095629399277 17087247019942535861024729)
            ·
              refine ⟨12815435264956901895768547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17087247019942535861024729 12815435264956901895768547)
              ·
                refine ⟨19223152897435352843652821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12815435264956901895768547 19223152897435352843652821)
                ·
                  refine ⟨450542646033641082273113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19223152897435352843652821 450542646033641082273113)
                  ·
                    rfl

theorem cell23_7896858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 1, 7].length) (baseStart_7896858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7896858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7896858 prefixEnd_7896858 := by exact prefixLift 7896858
  have htrace : WordTrace (prefixWord ++ tailWord_7896858) baseStart_7896858 baseEnd_7896858 := by
    simpa [prefixWord, tailWord_7896858, baseEnd_7896858] using wordTrace_append hprefix tailTrace_7896858
  have hstable : (prefixWord ++ tailWord_7896858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7896858).length < 2 ^ (prefixWord ++ tailWord_7896858).sum := by decide
  have hdescent : baseEnd_7896858 < baseStart_7896858 := by decide
  rcases family_descends (prefixWord ++ tailWord_7896858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7896869 : List Nat := [1, 3, 1, 2, 3, 3, 3, 1, 2, 2, 2]
def baseStart_7896869 : Nat := 118140960795 + 7896869 * 2 ^ 59
def prefixEnd_7896869 : Nat := 4983230072969 + 3 ^ 40 * 7896869 * 2
def baseEnd_7896869 : Nat := 4054889462589969197420467

theorem tailTrace_7896869 : CollatzResearch.WordTrace tailWord_7896869 prefixEnd_7896869 4054889462589969197420467 := by
  unfold tailWord_7896869
  simp only [CollatzResearch.WordTrace]
  refine ⟨288022474427999765696581661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192014982951999843797721107 288022474427999765696581661)
  ·
    refine ⟨108008427910499912136218123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288022474427999765696581661 108008427910499912136218123)
    ·
      refine ⟨162012641865749868204327185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108008427910499912136218123 162012641865749868204327185)
      ·
        refine ⟨121509481399312401153245389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162012641865749868204327185 121509481399312401153245389)
        ·
          refine ⟨45566055524742150432467021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121509481399312401153245389 45566055524742150432467021)
          ·
            refine ⟨17087270821778306412175133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45566055524742150432467021 17087270821778306412175133)
            ·
              refine ⟨6407726558166864904565675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17087270821778306412175133 6407726558166864904565675)
              ·
                refine ⟨9611589837250297356848513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6407726558166864904565675 9611589837250297356848513)
                ·
                  refine ⟨7208692377937723017636385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9611589837250297356848513 7208692377937723017636385)
                  ·
                    refine ⟨5406519283453292263227289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7208692377937723017636385 5406519283453292263227289)
                    ·
                      refine ⟨4054889462589969197420467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5406519283453292263227289 4054889462589969197420467)
                      ·
                        rfl

theorem cell23_7896869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 3, 1, 2, 2, 2].length) (baseStart_7896869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7896869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7896869 prefixEnd_7896869 := by exact prefixLift 7896869
  have htrace : WordTrace (prefixWord ++ tailWord_7896869) baseStart_7896869 baseEnd_7896869 := by
    simpa [prefixWord, tailWord_7896869, baseEnd_7896869] using wordTrace_append hprefix tailTrace_7896869
  have hstable : (prefixWord ++ tailWord_7896869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7896869).length < 2 ^ (prefixWord ++ tailWord_7896869).sum := by decide
  have hdescent : baseEnd_7896869 < baseStart_7896869 := by decide
  rcases family_descends (prefixWord ++ tailWord_7896869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7896909 : List Nat := [1, 6, 1, 2, 1, 2, 3, 2, 5]
def baseStart_7896909 : Nat := 118140960795 + 7896909 * 2 ^ 59
def prefixEnd_7896909 : Nat := 4983230072969 + 3 ^ 40 * 7896909 * 2
def baseEnd_7896909 : Nat := 450545555757349893435587

theorem tailTrace_7896909 : CollatzResearch.WordTrace tailWord_7896909 prefixEnd_7896909 450545555757349893435587 := by
  unfold tailWord_7896909
  simp only [CollatzResearch.WordTrace]
  refine ⟨288023933347854852528037781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192015955565236568352025187 288023933347854852528037781)
  ·
    refine ⟨13501121875680696212251771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 288023933347854852528037781 13501121875680696212251771)
    ·
      refine ⟨20251682813521044318377657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13501121875680696212251771 20251682813521044318377657)
      ·
        refine ⟨15188762110140783238783243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20251682813521044318377657 15188762110140783238783243)
        ·
          refine ⟨22783143165211174858174865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15188762110140783238783243 22783143165211174858174865)
          ·
            refine ⟨17087357373908381143631149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22783143165211174858174865 17087357373908381143631149)
            ·
              refine ⟨6407759015215642928861681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17087357373908381143631149 6407759015215642928861681)
              ·
                refine ⟨4805819261411732196646261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6407759015215642928861681 4805819261411732196646261)
                ·
                  refine ⟨450545555757349893435587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4805819261411732196646261 450545555757349893435587)
                  ·
                    rfl

theorem cell23_7896909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_7896909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7896909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7896909 prefixEnd_7896909 := by exact prefixLift 7896909
  have htrace : WordTrace (prefixWord ++ tailWord_7896909) baseStart_7896909 baseEnd_7896909 := by
    simpa [prefixWord, tailWord_7896909, baseEnd_7896909] using wordTrace_append hprefix tailTrace_7896909
  have hstable : (prefixWord ++ tailWord_7896909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7896909).length < 2 ^ (prefixWord ++ tailWord_7896909).sum := by decide
  have hdescent : baseEnd_7896909 < baseStart_7896909 := by decide
  rcases family_descends (prefixWord ++ tailWord_7896909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7896942 : List Nat := [4, 1, 2, 3, 1, 2, 2, 1, 2, 1, 4]
def baseStart_7896942 : Nat := 118140960795 + 7896942 * 2 ^ 59
def prefixEnd_7896942 : Nat := 4983230072969 + 3 ^ 40 * 7896942 * 2
def baseEnd_7896942 : Nat := 4054926946677747411807631

theorem tailTrace_7896942 : CollatzResearch.WordTrace tailWord_7896942 prefixEnd_7896942 4054926946677747411807631 := by
  unfold tailWord_7896942
  simp only [CollatzResearch.WordTrace]
  refine ⟨36003142119591912395498635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192016757971156866109326053 36003142119591912395498635)
  ·
    refine ⟨54004713179387868593247953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36003142119591912395498635 54004713179387868593247953)
    ·
      refine ⟨40503534884540901444935965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54004713179387868593247953 40503534884540901444935965)
      ·
        refine ⟨15188825581702838041850987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40503534884540901444935965 15188825581702838041850987)
        ·
          refine ⟨22783238372554257062776481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15188825581702838041850987 22783238372554257062776481)
          ·
            refine ⟨17087428779415692797082361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22783238372554257062776481 17087428779415692797082361)
            ·
              refine ⟨12815571584561769597811771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17087428779415692797082361 12815571584561769597811771)
              ·
                refine ⟨19223357376842654396717657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12815571584561769597811771 19223357376842654396717657)
                ·
                  refine ⟨14417518032631990797538243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19223357376842654396717657 14417518032631990797538243)
                  ·
                    refine ⟨21626277048947986196307365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14417518032631990797538243 21626277048947986196307365)
                    ·
                      refine ⟨4054926946677747411807631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21626277048947986196307365 4054926946677747411807631)
                      ·
                        rfl

theorem cell23_7896942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_7896942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7896942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7896942 prefixEnd_7896942 := by exact prefixLift 7896942
  have htrace : WordTrace (prefixWord ++ tailWord_7896942) baseStart_7896942 baseEnd_7896942 := by
    simpa [prefixWord, tailWord_7896942, baseEnd_7896942] using wordTrace_append hprefix tailTrace_7896942
  have hstable : (prefixWord ++ tailWord_7896942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7896942).length < 2 ^ (prefixWord ++ tailWord_7896942).sum := by decide
  have hdescent : baseEnd_7896942 < baseStart_7896942 := by decide
  rcases family_descends (prefixWord ++ tailWord_7896942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7896945 : List Nat := [1, 2, 2, 2, 1, 3, 4, 1, 2, 2, 3]
def baseStart_7896945 : Nat := 118140960795 + 7896945 * 2 ^ 59
def prefixEnd_7896945 : Nat := 4983230072969 + 3 ^ 40 * 7896945 * 2
def baseEnd_7896945 : Nat := 4054928487119710900070117

theorem tailTrace_7896945 : CollatzResearch.WordTrace tailWord_7896945 prefixEnd_7896945 4054928487119710900070117 := by
  unfold tailWord_7896945
  simp only [CollatzResearch.WordTrace]
  refine ⟨288025246375724430676348289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192016830917149620450898859 288025246375724430676348289)
  ·
    refine ⟨216018934781793323007261217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288025246375724430676348289 216018934781793323007261217)
    ·
      refine ⟨162014201086344992255445913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216018934781793323007261217 162014201086344992255445913)
      ·
        refine ⟨121510650814758744191584435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162014201086344992255445913 121510650814758744191584435)
        ·
          refine ⟨182265976222138116287376653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121510650814758744191584435 182265976222138116287376653)
          ·
            refine ⟨68349741083301793607766245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182265976222138116287376653 68349741083301793607766245)
            ·
              refine ⟨12815576453119086301456171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68349741083301793607766245 12815576453119086301456171)
              ·
                refine ⟨19223364679678629452184257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12815576453119086301456171 19223364679678629452184257)
                ·
                  refine ⟨14417523509758972089138193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19223364679678629452184257 14417523509758972089138193)
                  ·
                    refine ⟨10813142632319229066853645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14417523509758972089138193 10813142632319229066853645)
                    ·
                      refine ⟨4054928487119710900070117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10813142632319229066853645 4054928487119710900070117)
                      ·
                        rfl

theorem cell23_7896945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 1, 2, 2, 3].length) (baseStart_7896945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7896945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7896945 prefixEnd_7896945 := by exact prefixLift 7896945
  have htrace : WordTrace (prefixWord ++ tailWord_7896945) baseStart_7896945 baseEnd_7896945 := by
    simpa [prefixWord, tailWord_7896945, baseEnd_7896945] using wordTrace_append hprefix tailTrace_7896945
  have hstable : (prefixWord ++ tailWord_7896945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7896945).length < 2 ^ (prefixWord ++ tailWord_7896945).sum := by decide
  have hdescent : baseEnd_7896945 < baseStart_7896945 := by decide
  rcases family_descends (prefixWord ++ tailWord_7896945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7896951 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 8]
def baseStart_7896951 : Nat := 118140960795 + 7896951 * 2 ^ 59
def prefixEnd_7896951 : Nat := 4983230072969 + 3 ^ 40 * 7896951 * 2
def baseEnd_7896951 : Nat := 4054931568003637876595089

theorem tailTrace_7896951 : CollatzResearch.WordTrace tailWord_7896951 prefixEnd_7896951 4054931568003637876595089 := by
  unfold tailWord_7896951
  simp only [CollatzResearch.WordTrace]
  refine ⟨288025465213702693701066707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192016976809135129134044471 288025465213702693701066707)
  ·
    refine ⟨432038197820554040551600061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288025465213702693701066707 432038197820554040551600061)
    ·
      refine ⟨162014324182707765206850023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 432038197820554040551600061 162014324182707765206850023)
      ·
        refine ⟨243021486274061647810275035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162014324182707765206850023 243021486274061647810275035)
        ·
          refine ⟨364532229411092471715412553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243021486274061647810275035 364532229411092471715412553)
          ·
            refine ⟨273399172058319353786559415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 364532229411092471715412553 273399172058319353786559415)
            ·
              refine ⟨410098758087479030679839123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273399172058319353786559415 410098758087479030679839123)
              ·
                refine ⟨615148137131218546019758685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 410098758087479030679839123 615148137131218546019758685)
                ·
                  refine ⟨230680551424206954757409507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 615148137131218546019758685 230680551424206954757409507)
                  ·
                    refine ⟨346020827136310432136114261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 230680551424206954757409507 346020827136310432136114261)
                    ·
                      refine ⟨4054931568003637876595089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 346020827136310432136114261 4054931568003637876595089)
                      ·
                        rfl

theorem cell23_7896951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 8].length) (baseStart_7896951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7896951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7896951 prefixEnd_7896951 := by exact prefixLift 7896951
  have htrace : WordTrace (prefixWord ++ tailWord_7896951) baseStart_7896951 baseEnd_7896951 := by
    simpa [prefixWord, tailWord_7896951, baseEnd_7896951] using wordTrace_append hprefix tailTrace_7896951
  have hstable : (prefixWord ++ tailWord_7896951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7896951).length < 2 ^ (prefixWord ++ tailWord_7896951).sum := by decide
  have hdescent : baseEnd_7896951 < baseStart_7896951 := by decide
  rcases family_descends (prefixWord ++ tailWord_7896951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7896985 : List Nat := [1, 2, 1, 2, 1, 3, 2, 2, 4, 3, 2]
def baseStart_7896985 : Nat := 118140960795 + 7896985 * 2 ^ 59
def prefixEnd_7896985 : Nat := 4983230072969 + 3 ^ 40 * 7896985 * 2
def baseEnd_7896985 : Nat := 4054949026345890743569933

theorem tailTrace_7896985 : CollatzResearch.WordTrace tailWord_7896985 prefixEnd_7896985 4054949026345890743569933 := by
  unfold tailWord_7896985
  simp only [CollatzResearch.WordTrace]
  refine ⟨288026705295579517507804409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192017803530386345005202939 288026705295579517507804409)
  ·
    refine ⟨216020028971684638130853307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288026705295579517507804409 216020028971684638130853307)
    ·
      refine ⟨324030043457526957196279961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216020028971684638130853307 324030043457526957196279961)
      ·
        refine ⟨243022532593145217897209971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324030043457526957196279961 243022532593145217897209971)
        ·
          refine ⟨364533798889717826845814957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243022532593145217897209971 364533798889717826845814957)
          ·
            refine ⟨136700174583644185067180609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 364533798889717826845814957 136700174583644185067180609)
            ·
              refine ⟨102525130937733138800385457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136700174583644185067180609 102525130937733138800385457)
              ·
                refine ⟨76893848203299854100289093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102525130937733138800385457 76893848203299854100289093)
                ·
                  refine ⟨14417596538118722643804205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76893848203299854100289093 14417596538118722643804205)
                  ·
                    refine ⟨5406598701794520991426577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14417596538118722643804205 5406598701794520991426577)
                    ·
                      refine ⟨4054949026345890743569933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5406598701794520991426577 4054949026345890743569933)
                      ·
                        rfl

theorem cell23_7896985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 4, 3, 2].length) (baseStart_7896985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7896985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7896985 prefixEnd_7896985 := by exact prefixLift 7896985
  have htrace : WordTrace (prefixWord ++ tailWord_7896985) baseStart_7896985 baseEnd_7896985 := by
    simpa [prefixWord, tailWord_7896985, baseEnd_7896985] using wordTrace_append hprefix tailTrace_7896985
  have hstable : (prefixWord ++ tailWord_7896985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7896985).length < 2 ^ (prefixWord ++ tailWord_7896985).sum := by decide
  have hdescent : baseEnd_7896985 < baseStart_7896985 := by decide
  rcases family_descends (prefixWord ++ tailWord_7896985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7897009 : List Nat := [1, 2, 2, 4, 2, 1, 1, 5, 1, 1, 3]
def baseStart_7897009 : Nat := 118140960795 + 7897009 * 2 ^ 59
def prefixEnd_7897009 : Nat := 4983230072969 + 3 ^ 40 * 7897009 * 2
def baseEnd_7897009 : Nat := 4054961349881598649669823

theorem tailTrace_7897009 : CollatzResearch.WordTrace tailWord_7897009 prefixEnd_7897009 4054961349881598649669823 := by
  unfold tailWord_7897009
  simp only [CollatzResearch.WordTrace]
  refine ⟨288027580647492569606678081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192018387098328379737785387 288027580647492569606678081)
  ·
    refine ⟨216020685485619427205008561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288027580647492569606678081 216020685485619427205008561)
    ·
      refine ⟨162015514114214570403756421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216020685485619427205008561 162015514114214570403756421)
      ·
        refine ⟨30377908896415231950704329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162015514114214570403756421 30377908896415231950704329)
        ·
          refine ⟨22783431672311423963028247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30377908896415231950704329 22783431672311423963028247)
          ·
            refine ⟨34175147508467135944542371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22783431672311423963028247 34175147508467135944542371)
            ·
              refine ⟨51262721262700703916813557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34175147508467135944542371 51262721262700703916813557)
              ·
                refine ⟨4805880118378190992201271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51262721262700703916813557 4805880118378190992201271)
                ·
                  refine ⟨7208820177567286488301907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4805880118378190992201271 7208820177567286488301907)
                  ·
                    refine ⟨10813230266350929732452861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7208820177567286488301907 10813230266350929732452861)
                    ·
                      refine ⟨4054961349881598649669823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10813230266350929732452861 4054961349881598649669823)
                      ·
                        rfl

theorem cell23_7897009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 5, 1, 1, 3].length) (baseStart_7897009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7897009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7897009 prefixEnd_7897009 := by exact prefixLift 7897009
  have htrace : WordTrace (prefixWord ++ tailWord_7897009) baseStart_7897009 baseEnd_7897009 := by
    simpa [prefixWord, tailWord_7897009, baseEnd_7897009] using wordTrace_append hprefix tailTrace_7897009
  have hstable : (prefixWord ++ tailWord_7897009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7897009).length < 2 ^ (prefixWord ++ tailWord_7897009).sum := by decide
  have hdescent : baseEnd_7897009 < baseStart_7897009 := by decide
  rcases family_descends (prefixWord ++ tailWord_7897009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7897038 : List Nat := [4, 1, 1, 1, 2, 2, 2, 10]
def baseStart_7897038 : Nat := 118140960795 + 7897038 * 2 ^ 59
def prefixEnd_7897038 : Nat := 4983230072969 + 3 ^ 40 * 7897038 * 2
def baseEnd_7897038 : Nat := 150184305215577001341007

theorem tailTrace_7897038 : CollatzResearch.WordTrace tailWord_7897038 prefixEnd_7897038 150184305215577001341007 := by
  unfold tailWord_7897038
  simp only [CollatzResearch.WordTrace]
  refine ⟨36003579795548438444935471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192019092242925005039655845 36003579795548438444935471)
  ·
    refine ⟨54005369693322657667403207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36003579795548438444935471 54005369693322657667403207)
    ·
      refine ⟨81008054539983986501104811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54005369693322657667403207 81008054539983986501104811)
      ·
        refine ⟨121512081809975979751657217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81008054539983986501104811 121512081809975979751657217)
        ·
          refine ⟨91134061357481984813742913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121512081809975979751657217 91134061357481984813742913)
          ·
            refine ⟨68350546018111488610307185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91134061357481984813742913 68350546018111488610307185)
            ·
              refine ⟨51262909513583616457730389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68350546018111488610307185 51262909513583616457730389)
              ·
                refine ⟨150184305215577001341007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 51262909513583616457730389 150184305215577001341007)
                ·
                  rfl

theorem cell23_7897038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 10].length) (baseStart_7897038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7897038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7897038 prefixEnd_7897038 := by exact prefixLift 7897038
  have htrace : WordTrace (prefixWord ++ tailWord_7897038) baseStart_7897038 baseEnd_7897038 := by
    simpa [prefixWord, tailWord_7897038, baseEnd_7897038] using wordTrace_append hprefix tailTrace_7897038
  have hstable : (prefixWord ++ tailWord_7897038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7897038).length < 2 ^ (prefixWord ++ tailWord_7897038).sum := by decide
  have hdescent : baseEnd_7897038 < baseStart_7897038 := by decide
  rcases family_descends (prefixWord ++ tailWord_7897038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7897045 : List Nat := [1, 3, 2, 3, 2, 2, 1, 1, 1, 1, 6]
def baseStart_7897045 : Nat := 118140960795 + 7897045 * 2 ^ 59
def prefixEnd_7897045 : Nat := 4983230072969 + 3 ^ 40 * 7897045 * 2
def baseEnd_7897045 : Nat := 4054979835185160508819657

theorem tailTrace_7897045 : CollatzResearch.WordTrace tailWord_7897045 prefixEnd_7897045 4054979835185160508819657 := by
  unfold tailWord_7897045
  simp only [CollatzResearch.WordTrace]
  refine ⟨288028893675362147754988589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192019262450241431836659059 288028893675362147754988589)
  ·
    refine ⟨108010835128260805408120721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288028893675362147754988589 108010835128260805408120721)
    ·
      refine ⟨81008126346195604056090541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108010835128260805408120721 81008126346195604056090541)
      ·
        refine ⟨30378047379823351521033953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81008126346195604056090541 30378047379823351521033953)
        ·
          refine ⟨22783535534867513640775465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30378047379823351521033953 22783535534867513640775465)
          ·
            refine ⟨17087651651150635230581599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22783535534867513640775465 17087651651150635230581599)
            ·
              refine ⟨25631477476725952845872399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17087651651150635230581599 25631477476725952845872399)
              ·
                refine ⟨38447216215088929268808599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25631477476725952845872399 38447216215088929268808599)
                ·
                  refine ⟨57670824322633393903212899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38447216215088929268808599 57670824322633393903212899)
                  ·
                    refine ⟨86506236483950090854819349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57670824322633393903212899 86506236483950090854819349)
                    ·
                      refine ⟨4054979835185160508819657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86506236483950090854819349 4054979835185160508819657)
                      ·
                        rfl

theorem cell23_7897045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_7897045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7897045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7897045 prefixEnd_7897045 := by exact prefixLift 7897045
  have htrace : WordTrace (prefixWord ++ tailWord_7897045) baseStart_7897045 baseEnd_7897045 := by
    simpa [prefixWord, tailWord_7897045, baseEnd_7897045] using wordTrace_append hprefix tailTrace_7897045
  have hstable : (prefixWord ++ tailWord_7897045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7897045).length < 2 ^ (prefixWord ++ tailWord_7897045).sum := by decide
  have hdescent : baseEnd_7897045 < baseStart_7897045 := by decide
  rcases family_descends (prefixWord ++ tailWord_7897045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7897055 : List Nat := [1, 1, 2, 3, 4, 1, 4, 7]
def baseStart_7897055 : Nat := 118140960795 + 7897055 * 2 ^ 59
def prefixEnd_7897055 : Nat := 4983230072969 + 3 ^ 40 * 7897055 * 2
def baseEnd_7897055 : Nat := 150184628518211313692393

theorem tailTrace_7897055 : CollatzResearch.WordTrace tailWord_7897055 prefixEnd_7897055 150184628518211313692393 := by
  unfold tailWord_7897055
  simp only [CollatzResearch.WordTrace]
  refine ⟨288029258405325919462852619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192019505603550612975235079 288029258405325919462852619)
  ·
    refine ⟨432043887607988879194278929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288029258405325919462852619 432043887607988879194278929)
    ·
      refine ⟨324032915705991659395709197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432043887607988879194278929 324032915705991659395709197)
      ·
        refine ⟨121512343389746872273390949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 324032915705991659395709197 121512343389746872273390949)
        ·
          refine ⟨22783564385577538551260803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121512343389746872273390949 22783564385577538551260803)
          ·
            refine ⟨34175346578366307826891205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22783564385577538551260803 34175346578366307826891205)
            ·
              refine ⟨6407877483443682717542101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34175346578366307826891205 6407877483443682717542101)
              ·
                refine ⟨150184628518211313692393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6407877483443682717542101 150184628518211313692393)
                ·
                  rfl

theorem cell23_7897055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 4, 7].length) (baseStart_7897055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7897055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7897055 prefixEnd_7897055 := by exact prefixLift 7897055
  have htrace : WordTrace (prefixWord ++ tailWord_7897055) baseStart_7897055 baseEnd_7897055 := by
    simpa [prefixWord, tailWord_7897055, baseEnd_7897055] using wordTrace_append hprefix tailTrace_7897055
  have hstable : (prefixWord ++ tailWord_7897055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7897055).length < 2 ^ (prefixWord ++ tailWord_7897055).sum := by decide
  have hdescent : baseEnd_7897055 < baseStart_7897055 := by decide
  rcases family_descends (prefixWord ++ tailWord_7897055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7897069 : List Nat := [1, 5, 1, 4, 1, 1, 2, 1, 1, 1, 5]
def baseStart_7897069 : Nat := 118140960795 + 7897069 * 2 ^ 59
def prefixEnd_7897069 : Nat := 4983230072969 + 3 ^ 40 * 7897069 * 2
def baseEnd_7897069 : Nat := 4054992158720868414919547

theorem tailTrace_7897069 : CollatzResearch.WordTrace tailWord_7897069 prefixEnd_7897069 4054992158720868414919547 := by
  unfold tailWord_7897069
  simp only [CollatzResearch.WordTrace]
  refine ⟨288029769027275199853862261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192019846018183466569241507 288029769027275199853862261)
  ·
    refine ⟨27002790846307049986299587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 288029769027275199853862261 27002790846307049986299587)
    ·
      refine ⟨40504186269460574979449381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27002790846307049986299587 40504186269460574979449381)
      ·
        refine ⟨7594534925523857808646759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40504186269460574979449381 7594534925523857808646759)
        ·
          refine ⟨11391802388285786712970139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7594534925523857808646759 11391802388285786712970139)
          ·
            refine ⟨17087703582428680069455209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11391802388285786712970139 17087703582428680069455209)
            ·
              refine ⟨12815777686821510052091407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17087703582428680069455209 12815777686821510052091407)
              ·
                refine ⟨19223666530232265078137111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12815777686821510052091407 19223666530232265078137111)
                ·
                  refine ⟨28835499795348397617205667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19223666530232265078137111 28835499795348397617205667)
                  ·
                    refine ⟨43253249693022596425808501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28835499795348397617205667 43253249693022596425808501)
                    ·
                      refine ⟨4054992158720868414919547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43253249693022596425808501 4054992158720868414919547)
                      ·
                        rfl

theorem cell23_7897069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_7897069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7897069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7897069 prefixEnd_7897069 := by exact prefixLift 7897069
  have htrace : WordTrace (prefixWord ++ tailWord_7897069) baseStart_7897069 baseEnd_7897069 := by
    simpa [prefixWord, tailWord_7897069, baseEnd_7897069] using wordTrace_append hprefix tailTrace_7897069
  have hstable : (prefixWord ++ tailWord_7897069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7897069).length < 2 ^ (prefixWord ++ tailWord_7897069).sum := by decide
  have hdescent : baseEnd_7897069 < baseStart_7897069 := by decide
  rcases family_descends (prefixWord ++ tailWord_7897069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7897109 : List Nat := [1, 3, 2, 1, 5, 1, 1, 1, 3, 3, 2]
def baseStart_7897109 : Nat := 118140960795 + 7897109 * 2 ^ 59
def prefixEnd_7897109 : Nat := 4983230072969 + 3 ^ 40 * 7897109 * 2
def baseEnd_7897109 : Nat := 4055012697947048258419363

theorem tailTrace_7897109 : CollatzResearch.WordTrace tailWord_7897109 prefixEnd_7897109 4055012697947048258419363 := by
  unfold tailWord_7897109
  simp only [CollatzResearch.WordTrace]
  refine ⟨288031227947130286685318381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192020818631420191123545587 288031227947130286685318381)
  ·
    refine ⟨108011710480173857506994393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288031227947130286685318381 108011710480173857506994393)
    ·
      refine ⟨81008782860130393130245795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108011710480173857506994393 81008782860130393130245795)
      ·
        refine ⟨121513174290195589695368693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81008782860130393130245795 121513174290195589695368693)
        ·
          refine ⟨11391860089705836533940815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 121513174290195589695368693 11391860089705836533940815)
          ·
            refine ⟨17087790134558754800911223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11391860089705836533940815 17087790134558754800911223)
            ·
              refine ⟨25631685201838132201366835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17087790134558754800911223 25631685201838132201366835)
              ·
                refine ⟨38447527802757198302050253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25631685201838132201366835 38447527802757198302050253)
                ·
                  refine ⟨14417822926033949363268845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38447527802757198302050253 14417822926033949363268845)
                  ·
                    refine ⟨5406683597262731011225817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14417822926033949363268845 5406683597262731011225817)
                    ·
                      refine ⟨4055012697947048258419363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5406683597262731011225817 4055012697947048258419363)
                      ·
                        rfl

theorem cell23_7897109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 3, 3, 2].length) (baseStart_7897109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7897109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7897109 prefixEnd_7897109 := by exact prefixLift 7897109
  have htrace : WordTrace (prefixWord ++ tailWord_7897109) baseStart_7897109 baseEnd_7897109 := by
    simpa [prefixWord, tailWord_7897109, baseEnd_7897109] using wordTrace_append hprefix tailTrace_7897109
  have hstable : (prefixWord ++ tailWord_7897109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7897109).length < 2 ^ (prefixWord ++ tailWord_7897109).sum := by decide
  have hdescent : baseEnd_7897109 < baseStart_7897109 := by decide
  rcases family_descends (prefixWord ++ tailWord_7897109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7897125 : List Nat := [1, 3, 1, 2, 2, 3, 2, 1, 2, 1, 5]
def baseStart_7897125 : Nat := 118140960795 + 7897125 * 2 ^ 59
def prefixEnd_7897125 : Nat := 4983230072969 + 3 ^ 40 * 7897125 * 2
def baseEnd_7897125 : Nat := 4055020913637520195819289

theorem tailTrace_7897125 : CollatzResearch.WordTrace tailWord_7897125 prefixEnd_7897125 4055020913637520195819289 := by
  unfold tailWord_7897125
  simp only [CollatzResearch.WordTrace]
  refine ⟨288031811515072321417900829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192021207676714880945267219 288031811515072321417900829)
  ·
    refine ⟨108011929318152120531712811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288031811515072321417900829 108011929318152120531712811)
    ·
      refine ⟨162017893977228180797569217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108011929318152120531712811 162017893977228180797569217)
      ·
        refine ⟨121513420482921135598176913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162017893977228180797569217 121513420482921135598176913)
        ·
          refine ⟨91135065362190851698632685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121513420482921135598176913 91135065362190851698632685)
          ·
            refine ⟨34175649510821569386987257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91135065362190851698632685 34175649510821569386987257)
            ·
              refine ⟨25631737133116177040240443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34175649510821569386987257 25631737133116177040240443)
              ·
                refine ⟨38447605699674265560360665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25631737133116177040240443 38447605699674265560360665)
                ·
                  refine ⟨28835704274755699170270499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38447605699674265560360665 28835704274755699170270499)
                  ·
                    refine ⟨43253556412133548755405749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28835704274755699170270499 43253556412133548755405749)
                    ·
                      refine ⟨4055020913637520195819289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43253556412133548755405749 4055020913637520195819289)
                      ·
                        rfl

theorem cell23_7897125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 2, 1, 5].length) (baseStart_7897125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7897125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7897125 prefixEnd_7897125 := by exact prefixLift 7897125
  have htrace : WordTrace (prefixWord ++ tailWord_7897125) baseStart_7897125 baseEnd_7897125 := by
    simpa [prefixWord, tailWord_7897125, baseEnd_7897125] using wordTrace_append hprefix tailTrace_7897125
  have hstable : (prefixWord ++ tailWord_7897125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7897125).length < 2 ^ (prefixWord ++ tailWord_7897125).sum := by decide
  have hdescent : baseEnd_7897125 < baseStart_7897125 := by decide
  rcases family_descends (prefixWord ++ tailWord_7897125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7897139 : List Nat := [1, 1, 1, 2, 4, 1, 3, 4, 2, 2, 2]
def baseStart_7897139 : Nat := 118140960795 + 7897139 * 2 ^ 59
def prefixEnd_7897139 : Nat := 4983230072969 + 3 ^ 40 * 7897139 * 2
def baseEnd_7897139 : Nat := 4055028102366683141044225

theorem tailTrace_7897139 : CollatzResearch.WordTrace tailWord_7897139 prefixEnd_7897139 4055028102366683141044225 := by
  unfold tailWord_7897139
  simp only [CollatzResearch.WordTrace]
  refine ⟨288032322137021601808910471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192021548091347734539273647 288032322137021601808910471)
  ·
    refine ⟨432048483205532402713365707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288032322137021601808910471 432048483205532402713365707)
    ·
      refine ⟨648072724808298604070048561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432048483205532402713365707 648072724808298604070048561)
      ·
        refine ⟨486054543606223953052536421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 648072724808298604070048561 486054543606223953052536421)
        ·
          refine ⟨91135226926166991197350579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 486054543606223953052536421 91135226926166991197350579)
          ·
            refine ⟨136702840389250486796025869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91135226926166991197350579 136702840389250486796025869)
            ·
              refine ⟨51263565145968932548509701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136702840389250486796025869 51263565145968932548509701)
              ·
                refine ⟨9611918464869174852845569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51263565145968932548509701 9611918464869174852845569)
                ·
                  refine ⟨7208938848651881139634177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9611918464869174852845569 7208938848651881139634177)
                  ·
                    refine ⟨5406704136488910854725633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7208938848651881139634177 5406704136488910854725633)
                    ·
                      refine ⟨4055028102366683141044225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5406704136488910854725633 4055028102366683141044225)
                      ·
                        rfl

theorem cell23_7897139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 4, 2, 2, 2].length) (baseStart_7897139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7897139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7897139 prefixEnd_7897139 := by exact prefixLift 7897139
  have htrace : WordTrace (prefixWord ++ tailWord_7897139) baseStart_7897139 baseEnd_7897139 := by
    simpa [prefixWord, tailWord_7897139, baseEnd_7897139] using wordTrace_append hprefix tailTrace_7897139
  have hstable : (prefixWord ++ tailWord_7897139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7897139).length < 2 ^ (prefixWord ++ tailWord_7897139).sum := by decide
  have hdescent : baseEnd_7897139 < baseStart_7897139 := by decide
  rcases family_descends (prefixWord ++ tailWord_7897139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7897142 : List Nat := [5, 1, 2, 1, 1, 1, 1, 1, 1, 6, 3]
def baseStart_7897142 : Nat := 118140960795 + 7897142 * 2 ^ 59
def prefixEnd_7897142 : Nat := 4983230072969 + 3 ^ 40 * 7897142 * 2
def baseEnd_7897142 : Nat := 4055029642808646629306711

theorem tailTrace_7897142 : CollatzResearch.WordTrace tailWord_7897142 prefixEnd_7897142 4055029642808646629306711 := by
  unfold tailWord_7897142
  simp only [CollatzResearch.WordTrace]
  refine ⟨18002026972250670832579355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 192021621037340488880846453 18002026972250670832579355)
  ·
    refine ⟨27003040458376006248869033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18002026972250670832579355 27003040458376006248869033)
    ·
      refine ⟨20252280343782004686651775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27003040458376006248869033 20252280343782004686651775)
      ·
        refine ⟨30378420515673007029977663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20252280343782004686651775 30378420515673007029977663)
        ·
          refine ⟨45567630773509510544966495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30378420515673007029977663 45567630773509510544966495)
          ·
            refine ⟨68351446160264265817449743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45567630773509510544966495 68351446160264265817449743)
            ·
              refine ⟨102527169240396398726174615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68351446160264265817449743 102527169240396398726174615)
              ·
                refine ⟨153790753860594598089261923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102527169240396398726174615 153790753860594598089261923)
                ·
                  refine ⟨230686130790891897133892885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153790753860594598089261923 230686130790891897133892885)
                  ·
                    refine ⟨10813412380823057678151229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 230686130790891897133892885 10813412380823057678151229)
                    ·
                      refine ⟨4055029642808646629306711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10813412380823057678151229 4055029642808646629306711)
                      ·
                        rfl

theorem cell23_7897142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_7897142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7897142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7897142 prefixEnd_7897142 := by exact prefixLift 7897142
  have htrace : WordTrace (prefixWord ++ tailWord_7897142) baseStart_7897142 baseEnd_7897142 := by
    simpa [prefixWord, tailWord_7897142, baseEnd_7897142] using wordTrace_append hprefix tailTrace_7897142
  have hstable : (prefixWord ++ tailWord_7897142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7897142).length < 2 ^ (prefixWord ++ tailWord_7897142).sum := by decide
  have hdescent : baseEnd_7897142 < baseStart_7897142 := by decide
  rcases family_descends (prefixWord ++ tailWord_7897142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7897225 : List Nat := [1, 2, 1, 1, 4, 2, 1, 1, 2, 4, 4]
def baseStart_7897225 : Nat := 118140960795 + 7897225 * 2 ^ 59
def prefixEnd_7897225 : Nat := 4983230072969 + 3 ^ 40 * 7897225 * 2
def baseEnd_7897225 : Nat := 4055072261702969804568829

theorem tailTrace_7897225 : CollatzResearch.WordTrace tailWord_7897225 prefixEnd_7897225 4055072261702969804568829 := by
  unfold tailWord_7897225
  simp only [CollatzResearch.WordTrace]
  refine ⟨288035458814710038496541129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192023639209806692331027419 288035458814710038496541129)
  ·
    refine ⟨216026594111032528872405847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288035458814710038496541129 216026594111032528872405847)
    ·
      refine ⟨324039891166548793308608771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216026594111032528872405847 324039891166548793308608771)
      ·
        refine ⟨486059836749823189962913157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324039891166548793308608771 486059836749823189962913157)
        ·
          refine ⟨91136219390591848118046217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 486059836749823189962913157 91136219390591848118046217)
          ·
            refine ⟨68352164542943886088534663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91136219390591848118046217 68352164542943886088534663)
            ·
              refine ⟨102528246814415829132801995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68352164542943886088534663 102528246814415829132801995)
              ·
                refine ⟨153792370221623743699202993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102528246814415829132801995 153792370221623743699202993)
                ·
                  refine ⟨115344277666217807774402245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153792370221623743699202993 115344277666217807774402245)
                  ·
                    refine ⟨21627052062415838957700421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 115344277666217807774402245 21627052062415838957700421)
                    ·
                      refine ⟨4055072261702969804568829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21627052062415838957700421 4055072261702969804568829)
                      ·
                        rfl

theorem cell23_7897225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 4, 4].length) (baseStart_7897225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7897225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7897225 prefixEnd_7897225 := by exact prefixLift 7897225
  have htrace : WordTrace (prefixWord ++ tailWord_7897225) baseStart_7897225 baseEnd_7897225 := by
    simpa [prefixWord, tailWord_7897225, baseEnd_7897225] using wordTrace_append hprefix tailTrace_7897225
  have hstable : (prefixWord ++ tailWord_7897225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7897225).length < 2 ^ (prefixWord ++ tailWord_7897225).sum := by decide
  have hdescent : baseEnd_7897225 < baseStart_7897225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7897225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7897232 : List Nat := [2, 1, 1, 1, 1, 1, 6, 3, 2, 2, 3]
def baseStart_7897232 : Nat := 118140960795 + 7897232 * 2 ^ 59
def prefixEnd_7897232 : Nat := 4983230072969 + 3 ^ 40 * 7897232 * 2
def baseEnd_7897232 : Nat := 4055075856067551277181297

theorem tailTrace_7897232 : CollatzResearch.WordTrace tailWord_7897232 prefixEnd_7897232 4055075856067551277181297 := by
  unfold tailWord_7897232
  simp only [CollatzResearch.WordTrace]
  refine ⟨144017857062842339346022975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192023809417123119128030633 144017857062842339346022975)
  ·
    refine ⟨216026785594263509019034463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144017857062842339346022975 216026785594263509019034463)
    ·
      refine ⟨324040178391395263528551695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216026785594263509019034463 324040178391395263528551695)
      ·
        refine ⟨486060267587092895292827543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324040178391395263528551695 486060267587092895292827543)
        ·
          refine ⟨729090401380639342939241315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486060267587092895292827543 729090401380639342939241315)
          ·
            refine ⟨1093635602070959014408861973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 729090401380639342939241315 1093635602070959014408861973)
            ·
              refine ⟨51264168847076203800415405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1093635602070959014408861973 51264168847076203800415405)
              ·
                refine ⟨19224063317653576425155777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51264168847076203800415405 19224063317653576425155777)
                ·
                  refine ⟨14418047488240182318866833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19224063317653576425155777 14418047488240182318866833)
                  ·
                    refine ⟨10813535616180136739150125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14418047488240182318866833 10813535616180136739150125)
                    ·
                      refine ⟨4055075856067551277181297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10813535616180136739150125 4055075856067551277181297)
                      ·
                        rfl

theorem cell23_7897232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 3, 2, 2, 3].length) (baseStart_7897232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7897232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7897232 prefixEnd_7897232 := by exact prefixLift 7897232
  have htrace : WordTrace (prefixWord ++ tailWord_7897232) baseStart_7897232 baseEnd_7897232 := by
    simpa [prefixWord, tailWord_7897232, baseEnd_7897232] using wordTrace_append hprefix tailTrace_7897232
  have hstable : (prefixWord ++ tailWord_7897232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7897232).length < 2 ^ (prefixWord ++ tailWord_7897232).sum := by decide
  have hdescent : baseEnd_7897232 < baseStart_7897232 := by decide
  rcases family_descends (prefixWord ++ tailWord_7897232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7897246 : List Nat := [4, 3, 1, 1, 3, 1, 1, 2, 2, 1, 4]
def baseStart_7897246 : Nat := 118140960795 + 7897246 * 2 ^ 59
def prefixEnd_7897246 : Nat := 4983230072969 + 3 ^ 40 * 7897246 * 2
def baseEnd_7897246 : Nat := 4055083044796714222406233

theorem tailTrace_7897246 : CollatzResearch.WordTrace tailWord_7897246 prefixEnd_7897246 4055083044796714222406233 := by
  unfold tailWord_7897246
  simp only [CollatzResearch.WordTrace]
  refine ⟨36004528093454244885381949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192024149831755972722037061 36004528093454244885381949)
  ·
    refine ⟨13501698035045341832018231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36004528093454244885381949 13501698035045341832018231)
    ·
      refine ⟨20252547052568012748027347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13501698035045341832018231 20252547052568012748027347)
      ·
        refine ⟨30378820578852019122041021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20252547052568012748027347 30378820578852019122041021)
        ·
          refine ⟨11392057717069507170765383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30378820578852019122041021 11392057717069507170765383)
          ·
            refine ⟨17088086575604260756148075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11392057717069507170765383 17088086575604260756148075)
            ·
              refine ⟨25632129863406391134222113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17088086575604260756148075 25632129863406391134222113)
              ·
                refine ⟨19224097397554793350666585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25632129863406391134222113 19224097397554793350666585)
                ·
                  refine ⟨14418073048166095012999939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19224097397554793350666585 14418073048166095012999939)
                  ·
                    refine ⟨21627109572249142519499909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14418073048166095012999939 21627109572249142519499909)
                    ·
                      refine ⟨4055083044796714222406233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21627109572249142519499909 4055083044796714222406233)
                      ·
                        rfl

theorem cell23_7897246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_7897246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7897246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7897246 prefixEnd_7897246 := by exact prefixLift 7897246
  have htrace : WordTrace (prefixWord ++ tailWord_7897246) baseStart_7897246 baseEnd_7897246 := by
    simpa [prefixWord, tailWord_7897246, baseEnd_7897246] using wordTrace_append hprefix tailTrace_7897246
  have hstable : (prefixWord ++ tailWord_7897246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7897246).length < 2 ^ (prefixWord ++ tailWord_7897246).sum := by decide
  have hdescent : baseEnd_7897246 < baseStart_7897246 := by decide
  rcases family_descends (prefixWord ++ tailWord_7897246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7897249 : List Nat := [1, 2, 3, 3, 1, 3, 1, 2, 2, 2, 3]
def baseStart_7897249 : Nat := 118140960795 + 7897249 * 2 ^ 59
def prefixEnd_7897249 : Nat := 4983230072969 + 3 ^ 40 * 7897249 * 2
def baseEnd_7897249 : Nat := 4055084585238677710668719

theorem tailTrace_7897249 : CollatzResearch.WordTrace tailWord_7897249 prefixEnd_7897249 4055084585238677710668719 := by
  unfold tailWord_7897249
  simp only [CollatzResearch.WordTrace]
  refine ⟨288036334166623090595414801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192024222777748727063609867 288036334166623090595414801)
  ·
    refine ⟨216027250624967317946561101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288036334166623090595414801 216027250624967317946561101)
    ·
      refine ⟨81010218984362744229960413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216027250624967317946561101 81010218984362744229960413)
      ·
        refine ⟨30378832119136029086235155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81010218984362744229960413 30378832119136029086235155)
        ·
          refine ⟨45568248178704043629352733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30378832119136029086235155 45568248178704043629352733)
          ·
            refine ⟨17088093067014016361007275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45568248178704043629352733 17088093067014016361007275)
            ·
              refine ⟨25632139600521024541510913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17088093067014016361007275 25632139600521024541510913)
              ·
                refine ⟨19224104700390768406133185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25632139600521024541510913 19224104700390768406133185)
                ·
                  refine ⟨14418078525293076304599889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19224104700390768406133185 14418078525293076304599889)
                  ·
                    refine ⟨10813558893969807228449917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14418078525293076304599889 10813558893969807228449917)
                    ·
                      refine ⟨4055084585238677710668719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10813558893969807228449917 4055084585238677710668719)
                      ·
                        rfl

theorem cell23_7897249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_7897249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7897249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7897249 prefixEnd_7897249 := by exact prefixLift 7897249
  have htrace : WordTrace (prefixWord ++ tailWord_7897249) baseStart_7897249 baseEnd_7897249 := by
    simpa [prefixWord, tailWord_7897249, baseEnd_7897249] using wordTrace_append hprefix tailTrace_7897249
  have hstable : (prefixWord ++ tailWord_7897249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7897249).length < 2 ^ (prefixWord ++ tailWord_7897249).sum := by decide
  have hdescent : baseEnd_7897249 < baseStart_7897249 := by decide
  rcases family_descends (prefixWord ++ tailWord_7897249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7897319 : List Nat := [1, 1, 5, 3, 1, 1, 1, 2, 3, 1, 4]
def baseStart_7897319 : Nat := 118140960795 + 7897319 * 2 ^ 59
def prefixEnd_7897319 : Nat := 4983230072969 + 3 ^ 40 * 7897319 * 2
def baseEnd_7897319 : Nat := 4055120528884492436793397

theorem tailTrace_7897319 : CollatzResearch.WordTrace tailWord_7897319 prefixEnd_7897319 4055120528884492436793397 := by
  unfold tailWord_7897319
  simp only [CollatzResearch.WordTrace]
  refine ⟨288038887276369492550463011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192025924850912995033642007 288038887276369492550463011)
  ·
    refine ⟨432058330914554238825694517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288038887276369492550463011 432058330914554238825694517)
    ·
      refine ⟨40505468523239459889908861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 432058330914554238825694517 40505468523239459889908861)
      ·
        refine ⟨15189550696214797458715823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40505468523239459889908861 15189550696214797458715823)
        ·
          refine ⟨22784326044322196188073735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15189550696214797458715823 22784326044322196188073735)
          ·
            refine ⟨34176489066483294282110603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22784326044322196188073735 34176489066483294282110603)
            ·
              refine ⟨51264733599724941423165905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34176489066483294282110603 51264733599724941423165905)
              ·
                refine ⟨38448550199793706067374429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51264733599724941423165905 38448550199793706067374429)
                ·
                  refine ⟨14418206324922639775265411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38448550199793706067374429 14418206324922639775265411)
                  ·
                    refine ⟨21627309487383959662898117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14418206324922639775265411 21627309487383959662898117)
                    ·
                      refine ⟨4055120528884492436793397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21627309487383959662898117 4055120528884492436793397)
                      ·
                        rfl

theorem cell23_7897319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_7897319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7897319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7897319 prefixEnd_7897319 := by exact prefixLift 7897319
  have htrace : WordTrace (prefixWord ++ tailWord_7897319) baseStart_7897319 baseEnd_7897319 := by
    simpa [prefixWord, tailWord_7897319, baseEnd_7897319] using wordTrace_append hprefix tailTrace_7897319
  have hstable : (prefixWord ++ tailWord_7897319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7897319).length < 2 ^ (prefixWord ++ tailWord_7897319).sum := by decide
  have hdescent : baseEnd_7897319 < baseStart_7897319 := by decide
  rcases family_descends (prefixWord ++ tailWord_7897319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7897322 : List Nat := [3, 1, 3, 1, 1, 2, 2, 1, 3, 1, 5]
def baseStart_7897322 : Nat := 118140960795 + 7897322 * 2 ^ 59
def prefixEnd_7897322 : Nat := 4983230072969 + 3 ^ 40 * 7897322 * 2
def baseEnd_7897322 : Nat := 4055122069326455925055883

theorem tailTrace_7897322 : CollatzResearch.WordTrace tailWord_7897322 prefixEnd_7897322 4055122069326455925055883 := by
  unfold tailWord_7897322
  simp only [CollatzResearch.WordTrace]
  refine ⟨72009749173839656015705555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192025997796905749375214813 72009749173839656015705555)
  ·
    refine ⟨108014623760759484023558333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72009749173839656015705555 108014623760759484023558333)
    ·
      refine ⟨40505483910284806508834375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108014623760759484023558333 40505483910284806508834375)
      ·
        refine ⟨60758225865427209763251563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40505483910284806508834375 60758225865427209763251563)
        ·
          refine ⟨91137338798140814644877345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60758225865427209763251563 91137338798140814644877345)
          ·
            refine ⟨68353004098605610983658009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91137338798140814644877345 68353004098605610983658009)
            ·
              refine ⟨51264753073954208237743507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68353004098605610983658009 51264753073954208237743507)
              ·
                refine ⟨76897129610931312356615261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51264753073954208237743507 76897129610931312356615261)
                ·
                  refine ⟨28836423604099242133730723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76897129610931312356615261 28836423604099242133730723)
                  ·
                    refine ⟨43254635406148863200596085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28836423604099242133730723 43254635406148863200596085)
                    ·
                      refine ⟨4055122069326455925055883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43254635406148863200596085 4055122069326455925055883)
                      ·
                        rfl

theorem cell23_7897322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_7897322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7897322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7897322 prefixEnd_7897322 := by exact prefixLift 7897322
  have htrace : WordTrace (prefixWord ++ tailWord_7897322) baseStart_7897322 baseEnd_7897322 := by
    simpa [prefixWord, tailWord_7897322, baseEnd_7897322] using wordTrace_append hprefix tailTrace_7897322
  have hstable : (prefixWord ++ tailWord_7897322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7897322).length < 2 ^ (prefixWord ++ tailWord_7897322).sum := by decide
  have hdescent : baseEnd_7897322 < baseStart_7897322 := by decide
  rcases family_descends (prefixWord ++ tailWord_7897322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7897329 : List Nat := [1, 2, 2, 2, 2, 1, 4, 3, 2, 4]
def baseStart_7897329 : Nat := 118140960795 + 7897329 * 2 ^ 59
def prefixEnd_7897329 : Nat := 4983230072969 + 3 ^ 40 * 7897329 * 2
def baseEnd_7897329 : Nat := 1351708554563679132556117

theorem tailTrace_7897329 : CollatzResearch.WordTrace tailWord_7897329 prefixEnd_7897329 1351708554563679132556117 := by
  unfold tailWord_7897329
  simp only [CollatzResearch.WordTrace]
  refine ⟨288039252006333264258327041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192026168004222176172218027 288039252006333264258327041)
  ·
    refine ⟨216029439004749948193745281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288039252006333264258327041 216029439004749948193745281)
    ·
      refine ⟨162022079253562461145308961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216029439004749948193745281 162022079253562461145308961)
      ·
        refine ⟨121516559440171845858981721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162022079253562461145308961 121516559440171845858981721)
        ·
          refine ⟨91137419580128884394236291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121516559440171845858981721 91137419580128884394236291)
          ·
            refine ⟨136706129370193326591354437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91137419580128884394236291 136706129370193326591354437)
            ·
              refine ⟨25632399256911248735878957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 136706129370193326591354437 25632399256911248735878957)
              ·
                refine ⟨9612149721341718275954609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25632399256911248735878957 9612149721341718275954609)
                ·
                  refine ⟨7209112291006288706965957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9612149721341718275954609 7209112291006288706965957)
                  ·
                    refine ⟨1351708554563679132556117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7209112291006288706965957 1351708554563679132556117)
                    ·
                      rfl

theorem cell23_7897329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 3, 2, 4].length) (baseStart_7897329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7897329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7897329 prefixEnd_7897329 := by exact prefixLift 7897329
  have htrace : WordTrace (prefixWord ++ tailWord_7897329) baseStart_7897329 baseEnd_7897329 := by
    simpa [prefixWord, tailWord_7897329, baseEnd_7897329] using wordTrace_append hprefix tailTrace_7897329
  have hstable : (prefixWord ++ tailWord_7897329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7897329).length < 2 ^ (prefixWord ++ tailWord_7897329).sum := by decide
  have hdescent : baseEnd_7897329 < baseStart_7897329 := by decide
  rcases family_descends (prefixWord ++ tailWord_7897329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7897353 : List Nat := [1, 2, 1, 1, 3, 4, 1, 5, 1, 2, 2]
def baseStart_7897353 : Nat := 118140960795 + 7897353 * 2 ^ 59
def prefixEnd_7897353 : Nat := 4983230072969 + 3 ^ 40 * 7897353 * 2
def baseEnd_7897353 : Nat := 4055137987226745303768241

theorem tailTrace_7897353 : CollatzResearch.WordTrace tailWord_7897353 prefixEnd_7897353 4055137987226745303768241 := by
  unfold tailWord_7897353
  simp only [CollatzResearch.WordTrace]
  refine ⟨288040127358246316357200713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192026751572164210904800475 288040127358246316357200713)
  ·
    refine ⟨216030095518684737267900535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288040127358246316357200713 216030095518684737267900535)
    ·
      refine ⟨324045143278027105901850803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216030095518684737267900535 324045143278027105901850803)
      ·
        refine ⟨486067714917040658852776205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324045143278027105901850803 486067714917040658852776205)
        ·
          refine ⟨182275393093890247069791077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 486067714917040658852776205 182275393093890247069791077)
          ·
            refine ⟨34176636205104421325585827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 182275393093890247069791077 34176636205104421325585827)
            ·
              refine ⟨51264954307656631988378741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34176636205104421325585827 51264954307656631988378741)
              ·
                refine ⟨4806089466342809248910507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51264954307656631988378741 4806089466342809248910507)
                ·
                  refine ⟨7209134199514213873365761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4806089466342809248910507 7209134199514213873365761)
                  ·
                    refine ⟨5406850649635660405024321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7209134199514213873365761 5406850649635660405024321)
                    ·
                      refine ⟨4055137987226745303768241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5406850649635660405024321 4055137987226745303768241)
                      ·
                        rfl

theorem cell23_7897353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 5, 1, 2, 2].length) (baseStart_7897353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7897353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7897353 prefixEnd_7897353 := by exact prefixLift 7897353
  have htrace : WordTrace (prefixWord ++ tailWord_7897353) baseStart_7897353 baseEnd_7897353 := by
    simpa [prefixWord, tailWord_7897353, baseEnd_7897353] using wordTrace_append hprefix tailTrace_7897353
  have hstable : (prefixWord ++ tailWord_7897353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7897353).length < 2 ^ (prefixWord ++ tailWord_7897353).sum := by decide
  have hdescent : baseEnd_7897353 < baseStart_7897353 := by decide
  rcases family_descends (prefixWord ++ tailWord_7897353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7897383 : List Nat := [1, 1, 8, 1, 1, 1, 1, 1, 1, 1, 6]
def baseStart_7897383 : Nat := 118140960795 + 7897383 * 2 ^ 59
def prefixEnd_7897383 : Nat := 4983230072969 + 3 ^ 40 * 7897383 * 2
def baseEnd_7897383 : Nat := 4055153391646380186393103

theorem tailTrace_7897383 : CollatzResearch.WordTrace tailWord_7897383 prefixEnd_7897383 4055153391646380186393103 := by
  unfold tailWord_7897383
  simp only [CollatzResearch.WordTrace]
  refine ⟨288041221548137631480792803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192027481032091754320528535 288041221548137631480792803)
  ·
    refine ⟨432061832322206447221189205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288041221548137631480792803 432061832322206447221189205)
    ·
      refine ⟨5063224597525856803373311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 432061832322206447221189205 5063224597525856803373311)
      ·
        refine ⟨7594836896288785205059967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5063224597525856803373311 7594836896288785205059967)
        ·
          refine ⟨11392255344433177807589951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7594836896288785205059967 11392255344433177807589951)
          ·
            refine ⟨17088383016649766711384927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11392255344433177807589951 17088383016649766711384927)
            ·
              refine ⟨25632574524974650067077391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17088383016649766711384927 25632574524974650067077391)
              ·
                refine ⟨38448861787461975100616087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25632574524974650067077391 38448861787461975100616087)
                ·
                  refine ⟨57673292681192962650924131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38448861787461975100616087 57673292681192962650924131)
                  ·
                    refine ⟨86509939021789443976386197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57673292681192962650924131 86509939021789443976386197)
                    ·
                      refine ⟨4055153391646380186393103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86509939021789443976386197 4055153391646380186393103)
                      ·
                        rfl

theorem cell23_7897383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_7897383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7897383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7897383 prefixEnd_7897383 := by exact prefixLift 7897383
  have htrace : WordTrace (prefixWord ++ tailWord_7897383) baseStart_7897383 baseEnd_7897383 := by
    simpa [prefixWord, tailWord_7897383, baseEnd_7897383] using wordTrace_append hprefix tailTrace_7897383
  have hstable : (prefixWord ++ tailWord_7897383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7897383).length < 2 ^ (prefixWord ++ tailWord_7897383).sum := by decide
  have hdescent : baseEnd_7897383 < baseStart_7897383 := by decide
  rcases family_descends (prefixWord ++ tailWord_7897383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7897390 : List Nat := [4, 1, 3, 3, 1, 1, 2, 2, 1, 2, 3]
def baseStart_7897390 : Nat := 118140960795 + 7897390 * 2 ^ 59
def prefixEnd_7897390 : Nat := 4983230072969 + 3 ^ 40 * 7897390 * 2
def baseEnd_7897390 : Nat := 4055156986010961659005571

theorem tailTrace_7897390 : CollatzResearch.WordTrace tailWord_7897390 prefixEnd_7897390 4055156986010961659005571 := by
  unfold tailWord_7897390
  simp only [CollatzResearch.WordTrace]
  refine ⟨36005184607389033959537203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192027651239408181117531749 36005184607389033959537203)
  ·
    refine ⟨54007776911083550939305805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36005184607389033959537203 54007776911083550939305805)
    ·
      refine ⟨20252916341656331602239677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54007776911083550939305805 20252916341656331602239677)
      ·
        refine ⟨7594843628121124350839879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20252916341656331602239677 7594843628121124350839879)
        ·
          refine ⟨11392265442181686526259819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7594843628121124350839879 11392265442181686526259819)
          ·
            refine ⟨17088398163272529789389729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11392265442181686526259819 17088398163272529789389729)
            ·
              refine ⟨12816298622454397342042297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17088398163272529789389729 12816298622454397342042297)
              ·
                refine ⟨9612223966840798006531723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12816298622454397342042297 9612223966840798006531723)
                ·
                  refine ⟨14418335950261197009797585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9612223966840798006531723 14418335950261197009797585)
                  ·
                    refine ⟨10813751962695897757348189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14418335950261197009797585 10813751962695897757348189)
                    ·
                      refine ⟨4055156986010961659005571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10813751962695897757348189 4055156986010961659005571)
                      ·
                        rfl

theorem cell23_7897390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_7897390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7897390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7897390 prefixEnd_7897390 := by exact prefixLift 7897390
  have htrace : WordTrace (prefixWord ++ tailWord_7897390) baseStart_7897390 baseEnd_7897390 := by
    simpa [prefixWord, tailWord_7897390, baseEnd_7897390] using wordTrace_append hprefix tailTrace_7897390
  have hstable : (prefixWord ++ tailWord_7897390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7897390).length < 2 ^ (prefixWord ++ tailWord_7897390).sum := by decide
  have hdescent : baseEnd_7897390 < baseStart_7897390 := by decide
  rcases family_descends (prefixWord ++ tailWord_7897390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7897422 : List Nat := [4, 1, 1, 1, 1, 1, 2, 1, 2, 3, 6]
def baseStart_7897422 : Nat := 118140960795 + 7897422 * 2 ^ 59
def prefixEnd_7897422 : Nat := 4983230072969 + 3 ^ 40 * 7897422 * 2
def baseEnd_7897422 : Nat := 4055173417391905533805423

theorem tailTrace_7897422 : CollatzResearch.WordTrace tailWord_7897422 prefixEnd_7897422 4055173417391905533805423 := by
  unfold tailWord_7897422
  simp only [CollatzResearch.WordTrace]
  refine ⟨36005330499374542642682815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192028429329997560760975013 36005330499374542642682815)
  ·
    refine ⟨54007995749061813964024223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36005330499374542642682815 54007995749061813964024223)
    ·
      refine ⟨81011993623592720946036335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54007995749061813964024223 81011993623592720946036335)
      ·
        refine ⟨121517990435389081419054503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81011993623592720946036335 121517990435389081419054503)
        ·
          refine ⟨182276985653083622128581755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121517990435389081419054503 182276985653083622128581755)
          ·
            refine ⟨273415478479625433192872633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182276985653083622128581755 273415478479625433192872633)
            ·
              refine ⟨205061608859719074894654475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273415478479625433192872633 205061608859719074894654475)
              ·
                refine ⟨307592413289578612341981713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205061608859719074894654475 307592413289578612341981713)
                ·
                  refine ⟨230694309967183959256486285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 307592413289578612341981713 230694309967183959256486285)
                  ·
                    refine ⟨86510366237693984721182357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 230694309967183959256486285 86510366237693984721182357)
                    ·
                      refine ⟨4055173417391905533805423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86510366237693984721182357 4055173417391905533805423)
                      ·
                        rfl

theorem cell23_7897422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_7897422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7897422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7897422 prefixEnd_7897422 := by exact prefixLift 7897422
  have htrace : WordTrace (prefixWord ++ tailWord_7897422) baseStart_7897422 baseEnd_7897422 := by
    simpa [prefixWord, tailWord_7897422, baseEnd_7897422] using wordTrace_append hprefix tailTrace_7897422
  have hstable : (prefixWord ++ tailWord_7897422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7897422).length < 2 ^ (prefixWord ++ tailWord_7897422).sum := by decide
  have hdescent : baseEnd_7897422 < baseStart_7897422 := by decide
  rcases family_descends (prefixWord ++ tailWord_7897422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7897432 : List Nat := [2, 1, 2, 2, 1, 1, 2, 5, 7]
def baseStart_7897432 : Nat := 118140960795 + 7897432 * 2 ^ 59
def prefixEnd_7897432 : Nat := 4983230072969 + 3 ^ 40 * 7897432 * 2
def baseEnd_7897432 : Nat := 450575394688716721631153

theorem tailTrace_7897432 : CollatzResearch.WordTrace tailWord_7897432 prefixEnd_7897432 450575394688716721631153 := by
  unfold tailWord_7897432
  simp only [CollatzResearch.WordTrace]
  refine ⟨144021504362480056424663275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192028672483306741899551033 144021504362480056424663275)
  ·
    refine ⟨216032256543720084636994913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144021504362480056424663275 216032256543720084636994913)
    ·
      refine ⟨162024192407790063477746185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216032256543720084636994913 162024192407790063477746185)
      ·
        refine ⟨121518144305842547608309639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162024192407790063477746185 121518144305842547608309639)
        ·
          refine ⟨182277216458763821412464459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121518144305842547608309639 182277216458763821412464459)
          ·
            refine ⟨273415824688145732118696689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182277216458763821412464459 273415824688145732118696689)
            ·
              refine ⟨205061868516109299089022517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273415824688145732118696689 205061868516109299089022517)
              ·
                refine ⟨19224550173385246789595861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 205061868516109299089022517 19224550173385246789595861)
                ·
                  refine ⟨450575394688716721631153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19224550173385246789595861 450575394688716721631153)
                  ·
                    rfl

theorem cell23_7897432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 5, 7].length) (baseStart_7897432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7897432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7897432 prefixEnd_7897432 := by exact prefixLift 7897432
  have htrace : WordTrace (prefixWord ++ tailWord_7897432) baseStart_7897432 baseEnd_7897432 := by
    simpa [prefixWord, tailWord_7897432, baseEnd_7897432] using wordTrace_append hprefix tailTrace_7897432
  have hstable : (prefixWord ++ tailWord_7897432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7897432).length < 2 ^ (prefixWord ++ tailWord_7897432).sum := by decide
  have hdescent : baseEnd_7897432 < baseStart_7897432 := by decide
  rcases family_descends (prefixWord ++ tailWord_7897432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7897443 : List Nat := [1, 1, 1, 5, 2, 1, 3, 3, 2, 2, 2]
def baseStart_7897443 : Nat := 118140960795 + 7897443 * 2 ^ 59
def prefixEnd_7897443 : Nat := 4983230072969 + 3 ^ 40 * 7897443 * 2
def baseEnd_7897443 : Nat := 4055184200485649951642827

theorem tailTrace_7897443 : CollatzResearch.WordTrace tailWord_7897443 prefixEnd_7897443 4055184200485649951642827 := by
  unfold tailWord_7897443
  simp only [CollatzResearch.WordTrace]
  refine ⟨288043409927920261727976983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192028939951946841151984655 288043409927920261727976983)
  ·
    refine ⟨432065114891880392591965475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288043409927920261727976983 432065114891880392591965475)
    ·
      refine ⟨648097672337820588887948213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432065114891880392591965475 648097672337820588887948213)
      ·
        refine ⟨60759156781670680208245145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 648097672337820588887948213 60759156781670680208245145)
        ·
          refine ⟨45569367586253010156183859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60759156781670680208245145 45569367586253010156183859)
          ·
            refine ⟨68354051379379515234275789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45569367586253010156183859 68354051379379515234275789)
            ·
              refine ⟨25632769267267318212853421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68354051379379515234275789 25632769267267318212853421)
              ·
                refine ⟨9612288475225244329820033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25632769267267318212853421 9612288475225244329820033)
                ·
                  refine ⟨7209216356418933247365025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9612288475225244329820033 7209216356418933247365025)
                  ·
                    refine ⟨5406912267314199935523769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7209216356418933247365025 5406912267314199935523769)
                    ·
                      refine ⟨4055184200485649951642827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5406912267314199935523769 4055184200485649951642827)
                      ·
                        rfl

theorem cell23_7897443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 3, 2, 2, 2].length) (baseStart_7897443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7897443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7897443 prefixEnd_7897443 := by exact prefixLift 7897443
  have htrace : WordTrace (prefixWord ++ tailWord_7897443) baseStart_7897443 baseEnd_7897443 := by
    simpa [prefixWord, tailWord_7897443, baseEnd_7897443] using wordTrace_append hprefix tailTrace_7897443
  have hstable : (prefixWord ++ tailWord_7897443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7897443).length < 2 ^ (prefixWord ++ tailWord_7897443).sum := by decide
  have hdescent : baseEnd_7897443 < baseStart_7897443 := by decide
  rcases family_descends (prefixWord ++ tailWord_7897443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7897479 : List Nat := [1, 1, 4, 2, 2, 1, 1, 4, 2, 5]
def baseStart_7897479 : Nat := 118140960795 + 7897479 * 2 ^ 59
def prefixEnd_7897479 : Nat := 4983230072969 + 3 ^ 40 * 7897479 * 2
def baseEnd_7897479 : Nat := 1351734228596403936930887

theorem tailTrace_7897479 : CollatzResearch.WordTrace tailWord_7897479 prefixEnd_7897479 1351734228596403936930887 := by
  unfold tailWord_7897479
  simp only [CollatzResearch.WordTrace]
  refine ⟨288044722955789839876287491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192029815303859893250858327 288044722955789839876287491)
  ·
    refine ⟨432067084433684759814431237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288044722955789839876287491 432067084433684759814431237)
    ·
      refine ⟨81012578331315892465205857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 432067084433684759814431237 81012578331315892465205857)
      ·
        refine ⟨60759433748486919348904393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81012578331315892465205857 60759433748486919348904393)
        ·
          refine ⟨45569575311365189511678295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60759433748486919348904393 45569575311365189511678295)
          ·
            refine ⟨68354362967047784267517443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45569575311365189511678295 68354362967047784267517443)
            ·
              refine ⟨102531544450571676401276165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68354362967047784267517443 102531544450571676401276165)
              ·
                refine ⟨19224664584482189325239281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102531544450571676401276165 19224664584482189325239281)
                ·
                  refine ⟨14418498438361641993929461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19224664584482189325239281 14418498438361641993929461)
                  ·
                    refine ⟨1351734228596403936930887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14418498438361641993929461 1351734228596403936930887)
                    ·
                      rfl

theorem cell23_7897479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 4, 2, 5].length) (baseStart_7897479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7897479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7897479 prefixEnd_7897479 := by exact prefixLift 7897479
  have htrace : WordTrace (prefixWord ++ tailWord_7897479) baseStart_7897479 baseEnd_7897479 := by
    simpa [prefixWord, tailWord_7897479, baseEnd_7897479] using wordTrace_append hprefix tailTrace_7897479
  have hstable : (prefixWord ++ tailWord_7897479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7897479).length < 2 ^ (prefixWord ++ tailWord_7897479).sum := by decide
  have hdescent : baseEnd_7897479 < baseStart_7897479 := by decide
  rcases family_descends (prefixWord ++ tailWord_7897479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7897483 : List Nat := [1, 1, 1, 1, 4, 6, 2, 2, 5]
def baseStart_7897483 : Nat := 118140960795 + 7897483 * 2 ^ 59
def prefixEnd_7897483 : Nat := 4983230072969 + 3 ^ 40 * 7897483 * 2
def baseEnd_7897483 : Nat := 450578304412425532793627

theorem tailTrace_7897483 : CollatzResearch.WordTrace tailWord_7897483 prefixEnd_7897483 450578304412425532793627 := by
  unfold tailWord_7897483
  simp only [CollatzResearch.WordTrace]
  refine ⟨288044868847775348559433103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192029912565183565706288735 288044868847775348559433103)
  ·
    refine ⟨432067303271663022839149655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288044868847775348559433103 432067303271663022839149655)
    ·
      refine ⟨648100954907494534258724483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432067303271663022839149655 648100954907494534258724483)
      ·
        refine ⟨972151432361241801388086725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 648100954907494534258724483 972151432361241801388086725)
        ·
          refine ⟨182278393567732837760266261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 972151432361241801388086725 182278393567732837760266261)
          ·
            refine ⟨8544299698487476770012481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 182278393567732837760266261 8544299698487476770012481)
            ·
              refine ⟨6408224773865607577509361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8544299698487476770012481 6408224773865607577509361)
              ·
                refine ⟨4806168580399205683132021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6408224773865607577509361 4806168580399205683132021)
                ·
                  refine ⟨450578304412425532793627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4806168580399205683132021 450578304412425532793627)
                  ·
                    rfl

theorem cell23_7897483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 2, 2, 5].length) (baseStart_7897483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7897483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7897483 prefixEnd_7897483 := by exact prefixLift 7897483
  have htrace : WordTrace (prefixWord ++ tailWord_7897483) baseStart_7897483 baseEnd_7897483 := by
    simpa [prefixWord, tailWord_7897483, baseEnd_7897483] using wordTrace_append hprefix tailTrace_7897483
  have hstable : (prefixWord ++ tailWord_7897483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7897483).length < 2 ^ (prefixWord ++ tailWord_7897483).sum := by decide
  have hdescent : baseEnd_7897483 < baseStart_7897483 := by decide
  rcases family_descends (prefixWord ++ tailWord_7897483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7897494 : List Nat := [5, 3, 1, 2, 1, 1, 2, 1, 1, 4, 2]
def baseStart_7897494 : Nat := 118140960795 + 7897494 * 2 ^ 59
def prefixEnd_7897494 : Nat := 4983230072969 + 3 ^ 40 * 7897494 * 2
def baseEnd_7897494 : Nat := 4055210387999029252105093

theorem tailTrace_7897494 : CollatzResearch.WordTrace tailWord_7897494 prefixEnd_7897494 4055210387999029252105093 := by
  unfold tailWord_7897494
  simp only [CollatzResearch.WordTrace]
  refine ⟨18002829378170968589880221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 192030180033823664958722357 18002829378170968589880221)
  ·
    refine ⟨6751061016814113221205083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18002829378170968589880221 6751061016814113221205083)
    ·
      refine ⟨10126591525221169831807625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6751061016814113221205083 10126591525221169831807625)
      ·
        refine ⟨7594943643915877373855719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10126591525221169831807625 7594943643915877373855719)
        ·
          refine ⟨11392415465873816060783579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7594943643915877373855719 11392415465873816060783579)
          ·
            refine ⟨17088623198810724091175369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11392415465873816060783579 17088623198810724091175369)
            ·
              refine ⟨12816467399108043068381527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17088623198810724091175369 12816467399108043068381527)
              ·
                refine ⟨19224701098662064602572291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12816467399108043068381527 19224701098662064602572291)
                ·
                  refine ⟨28837051647993096903858437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19224701098662064602572291 28837051647993096903858437)
                  ·
                    refine ⟨5406947183998705669473457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28837051647993096903858437 5406947183998705669473457)
                    ·
                      refine ⟨4055210387999029252105093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5406947183998705669473457 4055210387999029252105093)
                      ·
                        rfl

theorem cell23_7897494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_7897494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7897494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7897494 prefixEnd_7897494 := by exact prefixLift 7897494
  have htrace : WordTrace (prefixWord ++ tailWord_7897494) baseStart_7897494 baseEnd_7897494 := by
    simpa [prefixWord, tailWord_7897494, baseEnd_7897494] using wordTrace_append hprefix tailTrace_7897494
  have hstable : (prefixWord ++ tailWord_7897494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7897494).length < 2 ^ (prefixWord ++ tailWord_7897494).sum := by decide
  have hdescent : baseEnd_7897494 < baseStart_7897494 := by decide
  rcases family_descends (prefixWord ++ tailWord_7897494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7897529 : List Nat := [1, 2, 1, 4, 3, 1, 1, 1, 2, 1, 6]
def baseStart_7897529 : Nat := 118140960795 + 7897529 * 2 ^ 59
def prefixEnd_7897529 : Nat := 4983230072969 + 3 ^ 40 * 7897529 * 2
def baseEnd_7897529 : Nat := 4055228359821936615167431

theorem tailTrace_7897529 : CollatzResearch.WordTrace tailWord_7897529 prefixEnd_7897529 4055228359821936615167431 := by
  unfold tailWord_7897529
  simp only [CollatzResearch.WordTrace]
  refine ⟨288046546605608698415607641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192031031070405798943738427 288046546605608698415607641)
  ·
    refine ⟨216034909954206523811705731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288046546605608698415607641 216034909954206523811705731)
    ·
      refine ⟨324052364931309785717558597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216034909954206523811705731 324052364931309785717558597)
      ·
        refine ⟨60759818424620584822042237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 324052364931309785717558597 60759818424620584822042237)
        ·
          refine ⟨22784931909232719308265839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60759818424620584822042237 22784931909232719308265839)
          ·
            refine ⟨34177397863849078962398759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22784931909232719308265839 34177397863849078962398759)
            ·
              refine ⟨51266096795773618443598139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34177397863849078962398759 51266096795773618443598139)
              ·
                refine ⟨76899145193660427665397209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51266096795773618443598139 76899145193660427665397209)
                ·
                  refine ⟨57674358895245320749047907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76899145193660427665397209 57674358895245320749047907)
                  ·
                    refine ⟨86511538342867981123571861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57674358895245320749047907 86511538342867981123571861)
                    ·
                      refine ⟨4055228359821936615167431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86511538342867981123571861 4055228359821936615167431)
                      ·
                        rfl

theorem cell23_7897529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_7897529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7897529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7897529 prefixEnd_7897529 := by exact prefixLift 7897529
  have htrace : WordTrace (prefixWord ++ tailWord_7897529) baseStart_7897529 baseEnd_7897529 := by
    simpa [prefixWord, tailWord_7897529, baseEnd_7897529] using wordTrace_append hprefix tailTrace_7897529
  have hstable : (prefixWord ++ tailWord_7897529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7897529).length < 2 ^ (prefixWord ++ tailWord_7897529).sum := by decide
  have hdescent : baseEnd_7897529 < baseStart_7897529 := by decide
  rcases family_descends (prefixWord ++ tailWord_7897529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7897543 : List Nat := [1, 1, 4, 1, 1, 4, 2, 4, 1, 4]
def baseStart_7897543 : Nat := 118140960795 + 7897543 * 2 ^ 59
def prefixEnd_7897543 : Nat := 4983230072969 + 3 ^ 40 * 7897543 * 2
def baseEnd_7897543 : Nat := 1351745182850366520130789

theorem tailTrace_7897543 : CollatzResearch.WordTrace tailWord_7897543 prefixEnd_7897543 1351745182850366520130789 := by
  unfold tailWord_7897543
  simp only [CollatzResearch.WordTrace]
  refine ⟨288047057227557978806617283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192031371485038652537744855 288047057227557978806617283)
  ·
    refine ⟨432070585841336968209925925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288047057227557978806617283 432070585841336968209925925)
    ·
      refine ⟨81013234845250681539361111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 432070585841336968209925925 81013234845250681539361111)
      ·
        refine ⟨121519852267876022309041667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81013234845250681539361111 121519852267876022309041667)
        ·
          refine ⟨182279778401814033463562501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121519852267876022309041667 182279778401814033463562501)
          ·
            refine ⟨34177458450340131274417969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 182279778401814033463562501 34177458450340131274417969)
            ·
              refine ⟨25633093837755098455813477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34177458450340131274417969 25633093837755098455813477)
              ·
                refine ⟨4806205094579080960465027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25633093837755098455813477 4806205094579080960465027)
                ·
                  refine ⟨7209307641868621440697541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4806205094579080960465027 7209307641868621440697541)
                  ·
                    refine ⟨1351745182850366520130789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7209307641868621440697541 1351745182850366520130789)
                    ·
                      rfl

theorem cell23_7897543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 4, 1, 4].length) (baseStart_7897543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7897543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7897543 prefixEnd_7897543 := by exact prefixLift 7897543
  have htrace : WordTrace (prefixWord ++ tailWord_7897543) baseStart_7897543 baseEnd_7897543 := by
    simpa [prefixWord, tailWord_7897543, baseEnd_7897543] using wordTrace_append hprefix tailTrace_7897543
  have hstable : (prefixWord ++ tailWord_7897543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7897543).length < 2 ^ (prefixWord ++ tailWord_7897543).sum := by decide
  have hdescent : baseEnd_7897543 < baseStart_7897543 := by decide
  rcases family_descends (prefixWord ++ tailWord_7897543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7897609 : List Nat := [1, 2, 1, 1, 3, 1, 2, 3, 3, 1, 5]
def baseStart_7897609 : Nat := 118140960795 + 7897609 * 2 ^ 59
def prefixEnd_7897609 : Nat := 4983230072969 + 3 ^ 40 * 7897609 * 2
def baseEnd_7897609 : Nat := 4055269438274296302167063

theorem tailTrace_7897609 : CollatzResearch.WordTrace tailWord_7897609 prefixEnd_7897609 4055269438274296302167063 := by
  unfold tailWord_7897609
  simp only [CollatzResearch.WordTrace]
  refine ⟨288049464445318872078519881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192032976296879248052346587 288049464445318872078519881)
  ·
    refine ⟨216037098333989154058889911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288049464445318872078519881 216037098333989154058889911)
    ·
      refine ⟨324055647500983731088334867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216037098333989154058889911 324055647500983731088334867)
      ·
        refine ⟨486083471251475596632502301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324055647500983731088334867 486083471251475596632502301)
        ·
          refine ⟨182281301719303348737188363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 486083471251475596632502301 182281301719303348737188363)
          ·
            refine ⟨273421952578955023105782545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182281301719303348737188363 273421952578955023105782545)
            ·
              refine ⟨205066464434216267329336909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273421952578955023105782545 205066464434216267329336909)
              ·
                refine ⟨76899924162831100248501341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 205066464434216267329336909 76899924162831100248501341)
                ·
                  refine ⟨28837471561061662593188003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76899924162831100248501341 28837471561061662593188003)
                  ·
                    refine ⟨43256207341592493889782005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28837471561061662593188003 43256207341592493889782005)
                    ·
                      refine ⟨4055269438274296302167063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43256207341592493889782005 4055269438274296302167063)
                      ·
                        rfl

theorem cell23_7897609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 3, 1, 5].length) (baseStart_7897609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7897609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7897609 prefixEnd_7897609 := by exact prefixLift 7897609
  have htrace : WordTrace (prefixWord ++ tailWord_7897609) baseStart_7897609 baseEnd_7897609 := by
    simpa [prefixWord, tailWord_7897609, baseEnd_7897609] using wordTrace_append hprefix tailTrace_7897609
  have hstable : (prefixWord ++ tailWord_7897609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7897609).length < 2 ^ (prefixWord ++ tailWord_7897609).sum := by decide
  have hdescent : baseEnd_7897609 < baseStart_7897609 := by decide
  rcases family_descends (prefixWord ++ tailWord_7897609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7897619 : List Nat := [1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 6]
def baseStart_7897619 : Nat := 118140960795 + 7897619 * 2 ^ 59
def prefixEnd_7897619 : Nat := 4983230072969 + 3 ^ 40 * 7897619 * 2
def baseEnd_7897619 : Nat := 4055274573080841263042017

theorem tailTrace_7897619 : CollatzResearch.WordTrace tailWord_7897619 prefixEnd_7897619 4055274573080841263042017 := by
  unfold tailWord_7897619
  simp only [CollatzResearch.WordTrace]
  refine ⟨288049829175282643786383911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192033219450188429190922607 288049829175282643786383911)
  ·
    refine ⟨432074743762923965679575867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288049829175282643786383911 432074743762923965679575867)
    ·
      refine ⟨648112115644385948519363801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432074743762923965679575867 648112115644385948519363801)
      ·
        refine ⟨486084086733289461389522851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 648112115644385948519363801 486084086733289461389522851)
        ·
          refine ⟨729126130099934192084284277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486084086733289461389522851 729126130099934192084284277)
          ·
            refine ⟨68355574696868830507901651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 729126130099934192084284277 68355574696868830507901651)
            ·
              refine ⟨102533362045303245761852477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68355574696868830507901651 102533362045303245761852477)
              ·
                refine ⟨38450010766988717160694679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102533362045303245761852477 38450010766988717160694679)
                ·
                  refine ⟨57675016150483075741042019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38450010766988717160694679 57675016150483075741042019)
                  ·
                    refine ⟨86512524225724613611563029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57675016150483075741042019 86512524225724613611563029)
                    ·
                      refine ⟨4055274573080841263042017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86512524225724613611563029 4055274573080841263042017)
                      ·
                        rfl

theorem cell23_7897619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 6].length) (baseStart_7897619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7897619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7897619 prefixEnd_7897619 := by exact prefixLift 7897619
  have htrace : WordTrace (prefixWord ++ tailWord_7897619) baseStart_7897619 baseEnd_7897619 := by
    simpa [prefixWord, tailWord_7897619, baseEnd_7897619] using wordTrace_append hprefix tailTrace_7897619
  have hstable : (prefixWord ++ tailWord_7897619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7897619).length < 2 ^ (prefixWord ++ tailWord_7897619).sum := by decide
  have hdescent : baseEnd_7897619 < baseStart_7897619 := by decide
  rcases family_descends (prefixWord ++ tailWord_7897619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7897620 : List Nat := [2, 4, 3, 1, 1, 1, 3, 2, 1, 5]
def baseStart_7897620 : Nat := 118140960795 + 7897620 * 2 ^ 59
def prefixEnd_7897620 : Nat := 4983230072969 + 3 ^ 40 * 7897620 * 2
def baseEnd_7897620 : Nat := 1351758362187165253043171

theorem tailTrace_7897620 : CollatzResearch.WordTrace tailWord_7897620 prefixEnd_7897620 1351758362187165253043171 := by
  unfold tailWord_7897620
  simp only [CollatzResearch.WordTrace]
  refine ⟨144024932824139510478585157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192033243765519347304780209 144024932824139510478585157)
  ·
    refine ⟨27004674904526158214734717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144024932824139510478585157 27004674904526158214734717)
    ·
      refine ⟨10126753089197309330525519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27004674904526158214734717 10126753089197309330525519)
      ·
        refine ⟨15190129633795963995788279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10126753089197309330525519 15190129633795963995788279)
        ·
          refine ⟨22785194450693945993682419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15190129633795963995788279 22785194450693945993682419)
          ·
            refine ⟨34177791676040918990523629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22785194450693945993682419 34177791676040918990523629)
            ·
              refine ⟨12816671878515344621446361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34177791676040918990523629 12816671878515344621446361)
              ·
                refine ⟨9612503908886508466084771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12816671878515344621446361 9612503908886508466084771)
                ·
                  refine ⟨14418755863329762699127157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9612503908886508466084771 14418755863329762699127157)
                  ·
                    refine ⟨1351758362187165253043171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14418755863329762699127157 1351758362187165253043171)
                    ·
                      rfl

theorem cell23_7897620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_7897620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7897620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7897620 prefixEnd_7897620 := by exact prefixLift 7897620
  have htrace : WordTrace (prefixWord ++ tailWord_7897620) baseStart_7897620 baseEnd_7897620 := by
    simpa [prefixWord, tailWord_7897620, baseEnd_7897620] using wordTrace_append hprefix tailTrace_7897620
  have hstable : (prefixWord ++ tailWord_7897620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7897620).length < 2 ^ (prefixWord ++ tailWord_7897620).sum := by decide
  have hdescent : baseEnd_7897620 < baseStart_7897620 := by decide
  rcases family_descends (prefixWord ++ tailWord_7897620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7897646 : List Nat := [4, 1, 3, 1, 3, 11]
def baseStart_7897646 : Nat := 118140960795 + 7897646 * 2 ^ 59
def prefixEnd_7897646 : Nat := 4983230072969 + 3 ^ 40 * 7897646 * 2
def baseEnd_7897646 : Nat := 16688429782133796944051

theorem tailTrace_7897646 : CollatzResearch.WordTrace tailWord_7897646 prefixEnd_7897646 16688429782133796944051 := by
  unfold tailWord_7897646
  simp only [CollatzResearch.WordTrace]
  refine ⟨36006351743273103424702099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192033875964123218265077861 36006351743273103424702099)
  ·
    refine ⟨54009527614909655137053149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36006351743273103424702099 54009527614909655137053149)
    ·
      refine ⟨20253572855591120676394931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54009527614909655137053149 20253572855591120676394931)
      ·
        refine ⟨30380359283386681014592397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20253572855591120676394931 30380359283386681014592397)
        ·
          refine ⟨11392634731270005380472149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30380359283386681014592397 11392634731270005380472149)
          ·
            refine ⟨16688429782133796944051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 11392634731270005380472149 16688429782133796944051)
            ·
              rfl

theorem cell23_7897646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 11].length) (baseStart_7897646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7897646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7897646 prefixEnd_7897646 := by exact prefixLift 7897646
  have htrace : WordTrace (prefixWord ++ tailWord_7897646) baseStart_7897646 baseEnd_7897646 := by
    simpa [prefixWord, tailWord_7897646, baseEnd_7897646] using wordTrace_append hprefix tailTrace_7897646
  have hstable : (prefixWord ++ tailWord_7897646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7897646).length < 2 ^ (prefixWord ++ tailWord_7897646).sum := by decide
  have hdescent : baseEnd_7897646 < baseStart_7897646 := by decide
  rcases family_descends (prefixWord ++ tailWord_7897646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7897656 : List Nat := [2, 1, 2, 1, 4, 1, 1, 2, 3, 3, 3]
def baseStart_7897656 : Nat := 118140960795 + 7897656 * 2 ^ 59
def prefixEnd_7897656 : Nat := 4983230072969 + 3 ^ 40 * 7897656 * 2
def baseEnd_7897656 : Nat := 4055293571865057618279347

theorem tailTrace_7897656 : CollatzResearch.WordTrace tailWord_7897656 prefixEnd_7897656 4055293571865057618279347 := by
  unfold tailWord_7897656
  simp only [CollatzResearch.WordTrace]
  refine ⟨144025589338074299552740411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192034119117432399403653881 144025589338074299552740411)
  ·
    refine ⟨216038384007111449329110617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144025589338074299552740411 216038384007111449329110617)
    ·
      refine ⟨162028788005333586996832963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216038384007111449329110617 162028788005333586996832963)
      ·
        refine ⟨243043182008000380495249445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162028788005333586996832963 243043182008000380495249445)
        ·
          refine ⟨45570596626500071342859271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 243043182008000380495249445 45570596626500071342859271)
          ·
            refine ⟨68355894939750107014288907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45570596626500071342859271 68355894939750107014288907)
            ·
              refine ⟨102533842409625160521433361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68355894939750107014288907 102533842409625160521433361)
              ·
                refine ⟨76900381807218870391075021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102533842409625160521433361 76900381807218870391075021)
                ·
                  refine ⟨28837643177707076396653133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76900381807218870391075021 28837643177707076396653133)
                  ·
                    refine ⟨10814116191640153648744925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28837643177707076396653133 10814116191640153648744925)
                    ·
                      refine ⟨4055293571865057618279347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10814116191640153648744925 4055293571865057618279347)
                      ·
                        rfl

theorem cell23_7897656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 3, 3, 3].length) (baseStart_7897656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7897656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7897656 prefixEnd_7897656 := by exact prefixLift 7897656
  have htrace : WordTrace (prefixWord ++ tailWord_7897656) baseStart_7897656 baseEnd_7897656 := by
    simpa [prefixWord, tailWord_7897656, baseEnd_7897656] using wordTrace_append hprefix tailTrace_7897656
  have hstable : (prefixWord ++ tailWord_7897656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7897656).length < 2 ^ (prefixWord ++ tailWord_7897656).sum := by decide
  have hdescent : baseEnd_7897656 < baseStart_7897656 := by decide
  rcases family_descends (prefixWord ++ tailWord_7897656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7897657 : List Nat := [1, 2, 1, 5, 1, 1, 3, 4, 1, 2, 2]
def baseStart_7897657 : Nat := 118140960795 + 7897657 * 2 ^ 59
def prefixEnd_7897657 : Nat := 4983230072969 + 3 ^ 40 * 7897657 * 2
def baseEnd_7897657 : Nat := 4055294085345712114366843

theorem tailTrace_7897657 : CollatzResearch.WordTrace tailWord_7897657 prefixEnd_7897657 4055294085345712114366843 := by
  unfold tailWord_7897657
  simp only [CollatzResearch.WordTrace]
  refine ⟨288051215149144976276267225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192034143432763317517511483 288051215149144976276267225)
  ·
    refine ⟨216038411361858732207200419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288051215149144976276267225 216038411361858732207200419)
    ·
      refine ⟨324057617042788098310800629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216038411361858732207200419 324057617042788098310800629)
      ·
        refine ⟨30380401597761384216637559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 324057617042788098310800629 30380401597761384216637559)
        ·
          refine ⟨45570602396642076324956339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30380401597761384216637559 45570602396642076324956339)
          ·
            refine ⟨68355903594963114487434509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45570602396642076324956339 68355903594963114487434509)
            ·
              refine ⟨25633463848111167932787941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68355903594963114487434509 25633463848111167932787941)
              ·
                refine ⟨4806274471520843987397739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25633463848111167932787941 4806274471520843987397739)
                ·
                  refine ⟨7209411707281265981096609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4806274471520843987397739 7209411707281265981096609)
                  ·
                    refine ⟨5407058780460949485822457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7209411707281265981096609 5407058780460949485822457)
                    ·
                      refine ⟨4055294085345712114366843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5407058780460949485822457 4055294085345712114366843)
                      ·
                        rfl

theorem cell23_7897657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 4, 1, 2, 2].length) (baseStart_7897657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7897657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7897657 prefixEnd_7897657 := by exact prefixLift 7897657
  have htrace : WordTrace (prefixWord ++ tailWord_7897657) baseStart_7897657 baseEnd_7897657 := by
    simpa [prefixWord, tailWord_7897657, baseEnd_7897657] using wordTrace_append hprefix tailTrace_7897657
  have hstable : (prefixWord ++ tailWord_7897657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7897657).length < 2 ^ (prefixWord ++ tailWord_7897657).sum := by decide
  have hdescent : baseEnd_7897657 < baseStart_7897657 := by decide
  rcases family_descends (prefixWord ++ tailWord_7897657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7897670 : List Nat := [6, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4]
def baseStart_7897670 : Nat := 118140960795 + 7897670 * 2 ^ 59
def prefixEnd_7897670 : Nat := 4983230072969 + 3 ^ 40 * 7897670 * 2
def baseEnd_7897670 : Nat := 4055300760594220563504283

theorem tailTrace_7897670 : CollatzResearch.WordTrace tailWord_7897670 prefixEnd_7897670 4055300760594220563504283 := by
  unfold tailWord_7897670
  simp only [CollatzResearch.WordTrace]
  refine ⟨9001615290565558734265327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 192034459532065252997660309 9001615290565558734265327)
  ·
    refine ⟨13502422935848338101397991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9001615290565558734265327 13502422935848338101397991)
    ·
      refine ⟨20253634403772507152096987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13502422935848338101397991 20253634403772507152096987)
      ·
        refine ⟨30380451605658760728145481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20253634403772507152096987 30380451605658760728145481)
        ·
          refine ⟨22785338704244070546109111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30380451605658760728145481 22785338704244070546109111)
          ·
            refine ⟨34178008056366105819163667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22785338704244070546109111 34178008056366105819163667)
            ·
              refine ⟨51267012084549158728745501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34178008056366105819163667 51267012084549158728745501)
              ·
                refine ⟨19225129531705934523279563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51267012084549158728745501 19225129531705934523279563)
                ·
                  refine ⟨28837694297558901784919345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19225129531705934523279563 28837694297558901784919345)
                  ·
                    refine ⟨21628270723169176338689509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28837694297558901784919345 21628270723169176338689509)
                    ·
                      refine ⟨4055300760594220563504283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21628270723169176338689509 4055300760594220563504283)
                      ·
                        rfl

theorem cell23_7897670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_7897670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7897670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7897670 prefixEnd_7897670 := by exact prefixLift 7897670
  have htrace : WordTrace (prefixWord ++ tailWord_7897670) baseStart_7897670 baseEnd_7897670 := by
    simpa [prefixWord, tailWord_7897670, baseEnd_7897670] using wordTrace_append hprefix tailTrace_7897670
  have hstable : (prefixWord ++ tailWord_7897670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7897670).length < 2 ^ (prefixWord ++ tailWord_7897670).sum := by decide
  have hdescent : baseEnd_7897670 < baseStart_7897670 := by decide
  rcases family_descends (prefixWord ++ tailWord_7897670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7897700 : List Nat := [2, 3, 1, 1, 2, 2, 3, 3, 1, 3, 2]
def baseStart_7897700 : Nat := 118140960795 + 7897700 * 2 ^ 59
def prefixEnd_7897700 : Nat := 4983230072969 + 3 ^ 40 * 7897700 * 2
def baseEnd_7897700 : Nat := 4055316165013855446129145

theorem tailTrace_7897700 : CollatzResearch.WordTrace tailWord_7897700 prefixEnd_7897700 4055316165013855446129145 := by
  unfold tailWord_7897700
  simp only [CollatzResearch.WordTrace]
  refine ⟨144026391743994597310041277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192035188991992796413388369 144026391743994597310041277)
  ·
    refine ⟨54009896903997973991265479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144026391743994597310041277 54009896903997973991265479)
    ·
      refine ⟨81014845355996960986898219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54009896903997973991265479 81014845355996960986898219)
      ·
        refine ⟨121522268033995441480347329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81014845355996960986898219 121522268033995441480347329)
        ·
          refine ⟨91141701025496581110260497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121522268033995441480347329 91141701025496581110260497)
          ·
            refine ⟨68356275769122435832695373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91141701025496581110260497 68356275769122435832695373)
            ·
              refine ⟨25633603413420913437260765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68356275769122435832695373 25633603413420913437260765)
              ·
                refine ⟨9612601280032842538972787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25633603413420913437260765 9612601280032842538972787)
                ·
                  refine ⟨14418901920049263808459181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9612601280032842538972787 14418901920049263808459181)
                  ·
                    refine ⟨5407088220018473928172193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14418901920049263808459181 5407088220018473928172193)
                    ·
                      refine ⟨4055316165013855446129145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5407088220018473928172193 4055316165013855446129145)
                      ·
                        rfl

theorem cell23_7897700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 3, 1, 3, 2].length) (baseStart_7897700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7897700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7897700 prefixEnd_7897700 := by exact prefixLift 7897700
  have htrace : WordTrace (prefixWord ++ tailWord_7897700) baseStart_7897700 baseEnd_7897700 := by
    simpa [prefixWord, tailWord_7897700, baseEnd_7897700] using wordTrace_append hprefix tailTrace_7897700
  have hstable : (prefixWord ++ tailWord_7897700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7897700).length < 2 ^ (prefixWord ++ tailWord_7897700).sum := by decide
  have hdescent : baseEnd_7897700 < baseStart_7897700 := by decide
  rcases family_descends (prefixWord ++ tailWord_7897700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7897706 : List Nat := [3, 1, 3, 2, 1, 1, 1, 1, 4, 6]
def baseStart_7897706 : Nat := 118140960795 + 7897706 * 2 ^ 59
def prefixEnd_7897706 : Nat := 4983230072969 + 3 ^ 40 * 7897706 * 2
def baseEnd_7897706 : Nat := 1351773081965927474218039

theorem tailTrace_7897706 : CollatzResearch.WordTrace tailWord_7897706 prefixEnd_7897706 1351773081965927474218039 := by
  unfold tailWord_7897706
  simp only [CollatzResearch.WordTrace]
  refine ⟨72013250581491864411200243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192035334883978305096533981 72013250581491864411200243)
  ·
    refine ⟨108019875872237796616800365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72013250581491864411200243 108019875872237796616800365)
    ·
      refine ⟨40507453452089173731300137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108019875872237796616800365 40507453452089173731300137)
      ·
        refine ⟨30380590089066880298475103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40507453452089173731300137 30380590089066880298475103)
        ·
          refine ⟨45570885133600320447712655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30380590089066880298475103 45570885133600320447712655)
          ·
            refine ⟨68356327700400480671568983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45570885133600320447712655 68356327700400480671568983)
            ·
              refine ⟨102534491550600721007353475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68356327700400480671568983 102534491550600721007353475)
              ·
                refine ⟨153801737325901081511030213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102534491550600721007353475 153801737325901081511030213)
                ·
                  refine ⟨28837825748606452783318165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 153801737325901081511030213 28837825748606452783318165)
                  ·
                    refine ⟨1351773081965927474218039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28837825748606452783318165 1351773081965927474218039)
                    ·
                      rfl

theorem cell23_7897706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_7897706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7897706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7897706 prefixEnd_7897706 := by exact prefixLift 7897706
  have htrace : WordTrace (prefixWord ++ tailWord_7897706) baseStart_7897706 baseEnd_7897706 := by
    simpa [prefixWord, tailWord_7897706, baseEnd_7897706] using wordTrace_append hprefix tailTrace_7897706
  have hstable : (prefixWord ++ tailWord_7897706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7897706).length < 2 ^ (prefixWord ++ tailWord_7897706).sum := by decide
  have hdescent : baseEnd_7897706 < baseStart_7897706 := by decide
  rcases family_descends (prefixWord ++ tailWord_7897706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7897781 : List Nat := [1, 3, 3, 3, 1, 3, 2, 1, 2, 2, 2]
def baseStart_7897781 : Nat := 118140960795 + 7897781 * 2 ^ 59
def prefixEnd_7897781 : Nat := 4983230072969 + 3 ^ 40 * 7897781 * 2
def baseEnd_7897781 : Nat := 4055357756946869629216273

theorem tailTrace_7897781 : CollatzResearch.WordTrace tailWord_7897781 prefixEnd_7897781 4055357756946869629216273 := by
  unfold tailWord_7897781
  simp only [CollatzResearch.WordTrace]
  refine ⟨288055737800695745453781197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192037158533797163635854131 288055737800695745453781197)
  ·
    refine ⟨108020901675260904545167949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288055737800695745453781197 108020901675260904545167949)
    ·
      refine ⟨40507838128222839204437981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108020901675260904545167949 40507838128222839204437981)
      ·
        refine ⟨15190439298083564701664243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40507838128222839204437981 15190439298083564701664243)
        ·
          refine ⟨22785658947125347052496365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15190439298083564701664243 22785658947125347052496365)
          ·
            refine ⟨8544622105172005144686137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22785658947125347052496365 8544622105172005144686137)
            ·
              refine ⟨6408466578879003858514603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8544622105172005144686137 6408466578879003858514603)
              ·
                refine ⟨9612699868318505787771905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6408466578879003858514603 9612699868318505787771905)
                ·
                  refine ⟨7209524901238879340828929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9612699868318505787771905 7209524901238879340828929)
                  ·
                    refine ⟨5407143675929159505621697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7209524901238879340828929 5407143675929159505621697)
                    ·
                      refine ⟨4055357756946869629216273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5407143675929159505621697 4055357756946869629216273)
                      ·
                        rfl

theorem cell23_7897781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_7897781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7897781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7897781 prefixEnd_7897781 := by exact prefixLift 7897781
  have htrace : WordTrace (prefixWord ++ tailWord_7897781) baseStart_7897781 baseEnd_7897781 := by
    simpa [prefixWord, tailWord_7897781, baseEnd_7897781] using wordTrace_append hprefix tailTrace_7897781
  have hstable : (prefixWord ++ tailWord_7897781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7897781).length < 2 ^ (prefixWord ++ tailWord_7897781).sum := by decide
  have hdescent : baseEnd_7897781 < baseStart_7897781 := by decide
  rcases family_descends (prefixWord ++ tailWord_7897781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7897803 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 6, 4, 2]
def baseStart_7897803 : Nat := 118140960795 + 7897803 * 2 ^ 59
def prefixEnd_7897803 : Nat := 4983230072969 + 3 ^ 40 * 7897803 * 2
def baseEnd_7897803 : Nat := 4055369053521268543141171

theorem tailTrace_7897803 : CollatzResearch.WordTrace tailWord_7897803 prefixEnd_7897803 4055369053521268543141171 := by
  unfold tailWord_7897803
  simp only [CollatzResearch.WordTrace]
  refine ⟨288056540206616043211082063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192037693471077362140721375 288056540206616043211082063)
  ·
    refine ⟨432084810309924064816623095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288056540206616043211082063 432084810309924064816623095)
    ·
      refine ⟨648127215464886097224934643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432084810309924064816623095 648127215464886097224934643)
      ·
        refine ⟨972190823197329145837401965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 648127215464886097224934643 972190823197329145837401965)
        ·
          refine ⟨364571558698998429689025737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 972190823197329145837401965 364571558698998429689025737)
          ·
            refine ⟨273428669024248822266769303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 364571558698998429689025737 273428669024248822266769303)
            ·
              refine ⟨410143003536373233400153955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273428669024248822266769303 410143003536373233400153955)
              ·
                refine ⟨615214505304559850100230933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 410143003536373233400153955 615214505304559850100230933)
                ·
                  refine ⟨28838179936151242973448325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 615214505304559850100230933 28838179936151242973448325)
                  ·
                    refine ⟨5407158738028358057521561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28838179936151242973448325 5407158738028358057521561)
                    ·
                      refine ⟨4055369053521268543141171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5407158738028358057521561 4055369053521268543141171)
                      ·
                        rfl

theorem cell23_7897803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 6, 4, 2].length) (baseStart_7897803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7897803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7897803 prefixEnd_7897803 := by exact prefixLift 7897803
  have htrace : WordTrace (prefixWord ++ tailWord_7897803) baseStart_7897803 baseEnd_7897803 := by
    simpa [prefixWord, tailWord_7897803, baseEnd_7897803] using wordTrace_append hprefix tailTrace_7897803
  have hstable : (prefixWord ++ tailWord_7897803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7897803).length < 2 ^ (prefixWord ++ tailWord_7897803).sum := by decide
  have hdescent : baseEnd_7897803 < baseStart_7897803 := by decide
  rcases family_descends (prefixWord ++ tailWord_7897803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7897870 : List Nat := [4, 1, 1, 2, 1, 1, 1, 1, 7, 1, 3]
def baseStart_7897870 : Nat := 118140960795 + 7897870 * 2 ^ 59
def prefixEnd_7897870 : Nat := 4983230072969 + 3 ^ 40 * 7897870 * 2
def baseEnd_7897870 : Nat := 4055403456725119781003363

theorem tailTrace_7897870 : CollatzResearch.WordTrace tailWord_7897870 prefixEnd_7897870 4055403456725119781003363 := by
  unfold tailWord_7897870
  simp only [CollatzResearch.WordTrace]
  refine ⟨36007372987171664206721383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192039322598248875769180709 36007372987171664206721383)
  ·
    refine ⟨54011059480757496310082075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36007372987171664206721383 54011059480757496310082075)
    ·
      refine ⟨81016589221136244465123113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54011059480757496310082075 81016589221136244465123113)
      ·
        refine ⟨60762441915852183348842335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81016589221136244465123113 60762441915852183348842335)
        ·
          refine ⟨91143662873778275023263503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60762441915852183348842335 91143662873778275023263503)
          ·
            refine ⟨136715494310667412534895255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91143662873778275023263503 136715494310667412534895255)
            ·
              refine ⟨205073241466001118802342883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136715494310667412534895255 205073241466001118802342883)
              ·
                refine ⟨307609862199001678203514325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205073241466001118802342883 307609862199001678203514325)
                ·
                  refine ⟨7209606145289101832894867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 307609862199001678203514325 7209606145289101832894867)
                  ·
                    refine ⟨10814409217933652749342301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7209606145289101832894867 10814409217933652749342301)
                    ·
                      refine ⟨4055403456725119781003363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10814409217933652749342301 4055403456725119781003363)
                      ·
                        rfl

theorem cell23_7897870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 7, 1, 3].length) (baseStart_7897870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7897870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7897870 prefixEnd_7897870 := by exact prefixLift 7897870
  have htrace : WordTrace (prefixWord ++ tailWord_7897870) baseStart_7897870 baseEnd_7897870 := by
    simpa [prefixWord, tailWord_7897870, baseEnd_7897870] using wordTrace_append hprefix tailTrace_7897870
  have hstable : (prefixWord ++ tailWord_7897870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7897870).length < 2 ^ (prefixWord ++ tailWord_7897870).sum := by decide
  have hdescent : baseEnd_7897870 < baseStart_7897870 := by decide
  rcases family_descends (prefixWord ++ tailWord_7897870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7897880 : List Nat := [2, 1, 2, 3, 1, 1, 1, 3, 4, 3, 2]
def baseStart_7897880 : Nat := 118140960795 + 7897880 * 2 ^ 59
def prefixEnd_7897880 : Nat := 4983230072969 + 3 ^ 40 * 7897880 * 2
def baseEnd_7897880 : Nat := 4055408591531664741878317

theorem tailTrace_7897880 : CollatzResearch.WordTrace tailWord_7897880 prefixEnd_7897880 4055408591531664741878317 := by
  unfold tailWord_7897880
  simp only [CollatzResearch.WordTrace]
  refine ⟨144029674313668542680817547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192039565751558056907756729 144029674313668542680817547)
  ·
    refine ⟨216044511470502814021226321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144029674313668542680817547 216044511470502814021226321)
    ·
      refine ⟨162033383602877110515919741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216044511470502814021226321 162033383602877110515919741)
      ·
        refine ⟨60762518851078916443469903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162033383602877110515919741 60762518851078916443469903)
        ·
          refine ⟨91143778276618374665204855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60762518851078916443469903 91143778276618374665204855)
          ·
            refine ⟨136715667414927561997807283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91143778276618374665204855 136715667414927561997807283)
            ·
              refine ⟨205073501122391342996710925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136715667414927561997807283 205073501122391342996710925)
              ·
                refine ⟨76902562920896753623766597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 205073501122391342996710925 76902562920896753623766597)
                ·
                  refine ⟨14419230547668141304456237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76902562920896753623766597 14419230547668141304456237)
                  ·
                    refine ⟨5407211455375552989171089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14419230547668141304456237 5407211455375552989171089)
                    ·
                      refine ⟨4055408591531664741878317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5407211455375552989171089 4055408591531664741878317)
                      ·
                        rfl

theorem cell23_7897880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 4, 3, 2].length) (baseStart_7897880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7897880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7897880 prefixEnd_7897880 := by exact prefixLift 7897880
  have htrace : WordTrace (prefixWord ++ tailWord_7897880) baseStart_7897880 baseEnd_7897880 := by
    simpa [prefixWord, tailWord_7897880, baseEnd_7897880] using wordTrace_append hprefix tailTrace_7897880
  have hstable : (prefixWord ++ tailWord_7897880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7897880).length < 2 ^ (prefixWord ++ tailWord_7897880).sum := by decide
  have hdescent : baseEnd_7897880 < baseStart_7897880 := by decide
  rcases family_descends (prefixWord ++ tailWord_7897880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7897887 : List Nat := [1, 1, 2, 4, 2, 3, 2, 1, 3, 1, 3]
def baseStart_7897887 : Nat := 118140960795 + 7897887 * 2 ^ 59
def prefixEnd_7897887 : Nat := 4983230072969 + 3 ^ 40 * 7897887 * 2
def baseEnd_7897887 : Nat := 4055412185896246214490785

theorem tailTrace_7897887 : CollatzResearch.WordTrace tailWord_7897887 prefixEnd_7897887 4055412185896246214490785 := by
  unfold tailWord_7897887
  simp only [CollatzResearch.WordTrace]
  refine ⟨288059603938311725557139915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192039735958874483704759943 288059603938311725557139915)
  ·
    refine ⟨432089405907467588335709873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288059603938311725557139915 432089405907467588335709873)
    ·
      refine ⟨324067054430600691251782405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432089405907467588335709873 324067054430600691251782405)
      ·
        refine ⟨60762572705737629609709201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 324067054430600691251782405 60762572705737629609709201)
        ·
          refine ⟨45571929529303222207281901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60762572705737629609709201 45571929529303222207281901)
          ·
            refine ⟨17089473573488708327730713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45571929529303222207281901 17089473573488708327730713)
            ·
              refine ⟨12817105180116531245798035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17089473573488708327730713 12817105180116531245798035)
              ·
                refine ⟨19225657770174796868697053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12817105180116531245798035 19225657770174796868697053)
                ·
                  refine ⟨7209621663815548825761395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19225657770174796868697053 7209621663815548825761395)
                  ·
                    refine ⟨10814432495723323238642093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7209621663815548825761395 10814432495723323238642093)
                    ·
                      refine ⟨4055412185896246214490785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10814432495723323238642093 4055412185896246214490785)
                      ·
                        rfl

theorem cell23_7897887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 1, 3, 1, 3].length) (baseStart_7897887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7897887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7897887 prefixEnd_7897887 := by exact prefixLift 7897887
  have htrace : WordTrace (prefixWord ++ tailWord_7897887) baseStart_7897887 baseEnd_7897887 := by
    simpa [prefixWord, tailWord_7897887, baseEnd_7897887] using wordTrace_append hprefix tailTrace_7897887
  have hstable : (prefixWord ++ tailWord_7897887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7897887).length < 2 ^ (prefixWord ++ tailWord_7897887).sum := by decide
  have hdescent : baseEnd_7897887 < baseStart_7897887 := by decide
  rcases family_descends (prefixWord ++ tailWord_7897887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7897903 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 8, 4]
def baseStart_7897903 : Nat := 118140960795 + 7897903 * 2 ^ 59
def prefixEnd_7897903 : Nat := 4983230072969 + 3 ^ 40 * 7897903 * 2
def baseEnd_7897903 : Nat := 1351806800528906050630237

theorem tailTrace_7897903 : CollatzResearch.WordTrace tailWord_7897903 prefixEnd_7897903 1351806800528906050630237 := by
  unfold tailWord_7897903
  simp only [CollatzResearch.WordTrace]
  refine ⟨288060187506253760289722363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192040125004169173526481575 288060187506253760289722363)
  ·
    refine ⟨432090281259380640434583545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288060187506253760289722363 432090281259380640434583545)
    ·
      refine ⟨324067710944535480325937659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432090281259380640434583545 324067710944535480325937659)
      ·
        refine ⟨486101566416803220488906489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324067710944535480325937659 486101566416803220488906489)
        ·
          refine ⟨364576174812602415366679867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 486101566416803220488906489 364576174812602415366679867)
          ·
            refine ⟨546864262218903623050019801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364576174812602415366679867 546864262218903623050019801)
            ·
              refine ⟨410148196664177717287514851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 546864262218903623050019801 410148196664177717287514851)
              ·
                refine ⟨615222294996266575931272277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 410148196664177717287514851 615222294996266575931272277)
                ·
                  refine ⟨7209636269487498936694597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 615222294996266575931272277 7209636269487498936694597)
                  ·
                    refine ⟨1351806800528906050630237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7209636269487498936694597 1351806800528906050630237)
                    ·
                      rfl

theorem cell23_7897903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 8, 4].length) (baseStart_7897903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7897903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7897903 prefixEnd_7897903 := by exact prefixLift 7897903
  have htrace : WordTrace (prefixWord ++ tailWord_7897903) baseStart_7897903 baseEnd_7897903 := by
    simpa [prefixWord, tailWord_7897903, baseEnd_7897903] using wordTrace_append hprefix tailTrace_7897903
  have hstable : (prefixWord ++ tailWord_7897903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7897903).length < 2 ^ (prefixWord ++ tailWord_7897903).sum := by decide
  have hdescent : baseEnd_7897903 < baseStart_7897903 := by decide
  rcases family_descends (prefixWord ++ tailWord_7897903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7897923 : List Nat := [1, 1, 1, 3, 1, 4, 2, 1, 3, 2, 4]
def baseStart_7897923 : Nat := 118140960795 + 7897923 * 2 ^ 59
def prefixEnd_7897923 : Nat := 4983230072969 + 3 ^ 40 * 7897923 * 2
def baseEnd_7897923 : Nat := 4055430671199808073640619

theorem tailTrace_7897923 : CollatzResearch.WordTrace tailWord_7897923 prefixEnd_7897923 4055430671199808073640619 := by
  unfold tailWord_7897923
  simp only [CollatzResearch.WordTrace]
  refine ⟨288060916966181303705450423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192040611310787535803633615 288060916966181303705450423)
  ·
    refine ⟨432091375449271955558175635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288060916966181303705450423 432091375449271955558175635)
    ·
      refine ⟨648137063173907933337263453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432091375449271955558175635 648137063173907933337263453)
      ·
        refine ⟨243051398690215475001473795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 648137063173907933337263453 243051398690215475001473795)
        ·
          refine ⟨364577098035323212502210693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243051398690215475001473795 364577098035323212502210693)
          ·
            refine ⟨68358205881623102344164505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 364577098035323212502210693 68358205881623102344164505)
            ·
              refine ⟨51268654411217326758123379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68358205881623102344164505 51268654411217326758123379)
              ·
                refine ⟨76902981616825990137185069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51268654411217326758123379 76902981616825990137185069)
                ·
                  refine ⟨28838618106309746301444401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76902981616825990137185069 28838618106309746301444401)
                  ·
                    refine ⟨21628963579732309726083301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28838618106309746301444401 21628963579732309726083301)
                    ·
                      refine ⟨4055430671199808073640619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21628963579732309726083301 4055430671199808073640619)
                      ·
                        rfl

theorem cell23_7897923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 3, 2, 4].length) (baseStart_7897923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7897923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7897923 prefixEnd_7897923 := by exact prefixLift 7897923
  have htrace : WordTrace (prefixWord ++ tailWord_7897923) baseStart_7897923 baseEnd_7897923 := by
    simpa [prefixWord, tailWord_7897923, baseEnd_7897923] using wordTrace_append hprefix tailTrace_7897923
  have hstable : (prefixWord ++ tailWord_7897923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7897923).length < 2 ^ (prefixWord ++ tailWord_7897923).sum := by decide
  have hdescent : baseEnd_7897923 < baseStart_7897923 := by decide
  rcases family_descends (prefixWord ++ tailWord_7897923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7897944 : List Nat := [2, 1, 2, 2, 1, 1, 1, 8, 1, 2, 2]
def baseStart_7897944 : Nat := 118140960795 + 7897944 * 2 ^ 59
def prefixEnd_7897944 : Nat := 4983230072969 + 3 ^ 40 * 7897944 * 2
def baseEnd_7897944 : Nat := 4055441454293552491478023

theorem tailTrace_7897944 : CollatzResearch.WordTrace tailWord_7897944 prefixEnd_7897944 4055441454293552491478023 := by
  unfold tailWord_7897944
  simp only [CollatzResearch.WordTrace]
  refine ⟨144030841449552612145982443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192041121932736816194643257 144030841449552612145982443)
  ·
    refine ⟨216046262174328918218973665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144030841449552612145982443 216046262174328918218973665)
    ·
      refine ⟨162034696630746688664230249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216046262174328918218973665 162034696630746688664230249)
      ·
        refine ⟨121526022473060016498172687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162034696630746688664230249 121526022473060016498172687)
        ·
          refine ⟨182289033709590024747259031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121526022473060016498172687 182289033709590024747259031)
          ·
            refine ⟨273433550564385037120888547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182289033709590024747259031 273433550564385037120888547)
            ·
              refine ⟨410150325846577555681332821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273433550564385037120888547 410150325846577555681332821)
              ·
                refine ⟨4806449131014580730640619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 410150325846577555681332821 4806449131014580730640619)
                ·
                  refine ⟨7209673696521871095960929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4806449131014580730640619 7209673696521871095960929)
                  ·
                    refine ⟨5407255272391403321970697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7209673696521871095960929 5407255272391403321970697)
                    ·
                      refine ⟨4055441454293552491478023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5407255272391403321970697 4055441454293552491478023)
                      ·
                        rfl

theorem cell23_7897944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 8, 1, 2, 2].length) (baseStart_7897944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7897944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7897944 prefixEnd_7897944 := by exact prefixLift 7897944
  have htrace : WordTrace (prefixWord ++ tailWord_7897944) baseStart_7897944 baseEnd_7897944 := by
    simpa [prefixWord, tailWord_7897944, baseEnd_7897944] using wordTrace_append hprefix tailTrace_7897944
  have hstable : (prefixWord ++ tailWord_7897944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7897944).length < 2 ^ (prefixWord ++ tailWord_7897944).sum := by decide
  have hdescent : baseEnd_7897944 < baseStart_7897944 := by decide
  rcases family_descends (prefixWord ++ tailWord_7897944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7897954 : List Nat := [3, 3, 2, 1, 3, 1, 1, 3, 2, 4]
def baseStart_7897954 : Nat := 118140960795 + 7897954 * 2 ^ 59
def prefixEnd_7897954 : Nat := 4983230072969 + 3 ^ 40 * 7897954 * 2
def baseEnd_7897954 : Nat := 1351815529700032484117659

theorem tailTrace_7897954 : CollatzResearch.WordTrace tailWord_7897954 prefixEnd_7897954 1351815529700032484117659 := by
  unfold tailWord_7897954
  simp only [CollatzResearch.WordTrace]
  refine ⟨72015511907267248999957229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192041365086045997333219277 72015511907267248999957229)
  ·
    refine ⟨27005816965225218374983961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72015511907267248999957229 27005816965225218374983961)
    ·
      refine ⟨20254362723918913781237971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27005816965225218374983961 20254362723918913781237971)
      ·
        refine ⟨30381544085878370671856957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20254362723918913781237971 30381544085878370671856957)
        ·
          refine ⟨11393079032204389001946359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30381544085878370671856957 11393079032204389001946359)
          ·
            refine ⟨17089618548306583502919539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11393079032204389001946359 17089618548306583502919539)
            ·
              refine ⟨25634427822459875254379309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17089618548306583502919539 25634427822459875254379309)
              ·
                refine ⟨9612910433422453220392241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25634427822459875254379309 9612910433422453220392241)
                ·
                  refine ⟨7209682825066839915294181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9612910433422453220392241 7209682825066839915294181)
                  ·
                    refine ⟨1351815529700032484117659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7209682825066839915294181 1351815529700032484117659)
                    ·
                      rfl

theorem cell23_7897954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_7897954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7897954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7897954 prefixEnd_7897954 := by exact prefixLift 7897954
  have htrace : WordTrace (prefixWord ++ tailWord_7897954) baseStart_7897954 baseEnd_7897954 := by
    simpa [prefixWord, tailWord_7897954, baseEnd_7897954] using wordTrace_append hprefix tailTrace_7897954
  have hstable : (prefixWord ++ tailWord_7897954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7897954).length < 2 ^ (prefixWord ++ tailWord_7897954).sum := by decide
  have hdescent : baseEnd_7897954 < baseStart_7897954 := by decide
  rcases family_descends (prefixWord ++ tailWord_7897954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7897994 : List Nat := [3, 1, 2, 4, 1, 1, 1, 4, 2, 1, 3]
def baseStart_7897994 : Nat := 118140960795 + 7897994 * 2 ^ 59
def prefixEnd_7897994 : Nat := 4983230072969 + 3 ^ 40 * 7897994 * 2
def baseEnd_7897994 : Nat := 4055467128326277295852793

theorem tailTrace_7897994 : CollatzResearch.WordTrace tailWord_7897994 prefixEnd_7897994 4055467128326277295852793 := by
  unfold tailWord_7897994
  simp only [CollatzResearch.WordTrace]
  refine ⟨72015876637231020707821259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192042337699282721887523357 72015876637231020707821259)
  ·
    refine ⟨108023814955846531061731889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72015876637231020707821259 108023814955846531061731889)
    ·
      refine ⟨81017861216884898296298917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108023814955846531061731889 81017861216884898296298917)
      ·
        refine ⟨15190848978165918430556047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81017861216884898296298917 15190848978165918430556047)
        ·
          refine ⟨22786273467248877645834071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15190848978165918430556047 22786273467248877645834071)
          ·
            refine ⟨34179410200873316468751107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22786273467248877645834071 34179410200873316468751107)
            ·
              refine ⟨51269115301309974703126661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34179410200873316468751107 51269115301309974703126661)
              ·
                refine ⟨9612959118995620256836249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51269115301309974703126661 9612959118995620256836249)
                ·
                  refine ⟨7209719339246715192627187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9612959118995620256836249 7209719339246715192627187)
                  ·
                    refine ⟨10814579008870072788940781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7209719339246715192627187 10814579008870072788940781)
                    ·
                      refine ⟨4055467128326277295852793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10814579008870072788940781 4055467128326277295852793)
                      ·
                        rfl

theorem cell23_7897994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_7897994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7897994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7897994 prefixEnd_7897994 := by exact prefixLift 7897994
  have htrace : WordTrace (prefixWord ++ tailWord_7897994) baseStart_7897994 baseEnd_7897994 := by
    simpa [prefixWord, tailWord_7897994, baseEnd_7897994] using wordTrace_append hprefix tailTrace_7897994
  have hstable : (prefixWord ++ tailWord_7897994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7897994).length < 2 ^ (prefixWord ++ tailWord_7897994).sum := by decide
  have hdescent : baseEnd_7897994 < baseStart_7897994 := by decide
  rcases family_descends (prefixWord ++ tailWord_7897994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7898003 : List Nat := [1, 1, 1, 2, 1, 2, 1, 4, 4, 1, 5]
def baseStart_7898003 : Nat := 118140960795 + 7898003 * 2 ^ 59
def prefixEnd_7898003 : Nat := 4983230072969 + 3 ^ 40 * 7898003 * 2
def baseEnd_7898003 : Nat := 4055471749652167760640251

theorem tailTrace_7898003 : CollatzResearch.WordTrace tailWord_7898003 prefixEnd_7898003 4055471749652167760640251 := by
  unfold tailWord_7898003
  simp only [CollatzResearch.WordTrace]
  refine ⟨288063834805891477368362663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192042556537260984912241775 288063834805891477368362663)
  ·
    refine ⟨432095752208837216052543995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288063834805891477368362663 432095752208837216052543995)
    ·
      refine ⟨648143628313255824078815993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432095752208837216052543995 648143628313255824078815993)
      ·
        refine ⟨486107721234941868059111995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 648143628313255824078815993 486107721234941868059111995)
        ·
          refine ⟨729161581852412802088667993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486107721234941868059111995 729161581852412802088667993)
          ·
            refine ⟨546871186389309601566500995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 729161581852412802088667993 546871186389309601566500995)
            ·
              refine ⟨820306779583964402349751493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 546871186389309601566500995 820306779583964402349751493)
              ·
                refine ⟨153807521171993325440578405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 820306779583964402349751493 153807521171993325440578405)
                ·
                  refine ⟨28838910219748748520108451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 153807521171993325440578405 28838910219748748520108451)
                  ·
                    refine ⟨43258365329623122780162677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28838910219748748520108451 43258365329623122780162677)
                    ·
                      refine ⟨4055471749652167760640251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43258365329623122780162677 4055471749652167760640251)
                      ·
                        rfl

theorem cell23_7898003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 4, 1, 5].length) (baseStart_7898003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7898003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7898003 prefixEnd_7898003 := by exact prefixLift 7898003
  have htrace : WordTrace (prefixWord ++ tailWord_7898003) baseStart_7898003 baseEnd_7898003 := by
    simpa [prefixWord, tailWord_7898003, baseEnd_7898003] using wordTrace_append hprefix tailTrace_7898003
  have hstable : (prefixWord ++ tailWord_7898003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7898003).length < 2 ^ (prefixWord ++ tailWord_7898003).sum := by decide
  have hdescent : baseEnd_7898003 < baseStart_7898003 := by decide
  rcases family_descends (prefixWord ++ tailWord_7898003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7898020 : List Nat := [2, 3, 1, 2, 1, 2, 1, 2, 2, 4, 3]
def baseStart_7898020 : Nat := 118140960795 + 7898020 * 2 ^ 59
def prefixEnd_7898020 : Nat := 4983230072969 + 3 ^ 40 * 7898020 * 2
def baseEnd_7898020 : Nat := 4055480478823294194127673

theorem tailTrace_7898020 : CollatzResearch.WordTrace tailWord_7898020 prefixEnd_7898020 4055480478823294194127673 := by
  unfold tailWord_7898020
  simp only [CollatzResearch.WordTrace]
  refine ⟨144032227423414944635865757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192042969897886592847821009 144032227423414944635865757)
  ·
    refine ⟨54012085283780604238449659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144032227423414944635865757 54012085283780604238449659)
    ·
      refine ⟨81018127925670906357674489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54012085283780604238449659 81018127925670906357674489)
      ·
        refine ⟨60763595944253179768255867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81018127925670906357674489 60763595944253179768255867)
        ·
          refine ⟨91145393916379769652383801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60763595944253179768255867 91145393916379769652383801)
          ·
            refine ⟨68359045437284827239287851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91145393916379769652383801 68359045437284827239287851)
            ·
              refine ⟨102538568155927240858931777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68359045437284827239287851 102538568155927240858931777)
              ·
                refine ⟨76903926116945430644198833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102538568155927240858931777 76903926116945430644198833)
                ·
                  refine ⟨57677944587709072983149125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76903926116945430644198833 57677944587709072983149125)
                  ·
                    refine ⟨10814614610195451184340461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57677944587709072983149125 10814614610195451184340461)
                    ·
                      refine ⟨4055480478823294194127673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10814614610195451184340461 4055480478823294194127673)
                      ·
                        rfl

theorem cell23_7898020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 2, 4, 3].length) (baseStart_7898020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7898020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7898020 prefixEnd_7898020 := by exact prefixLift 7898020
  have htrace : WordTrace (prefixWord ++ tailWord_7898020) baseStart_7898020 baseEnd_7898020 := by
    simpa [prefixWord, tailWord_7898020, baseEnd_7898020] using wordTrace_append hprefix tailTrace_7898020
  have hstable : (prefixWord ++ tailWord_7898020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7898020).length < 2 ^ (prefixWord ++ tailWord_7898020).sum := by decide
  have hdescent : baseEnd_7898020 < baseStart_7898020 := by decide
  rcases family_descends (prefixWord ++ tailWord_7898020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7898068 : List Nat := [2, 4, 1, 2, 1, 3, 3, 1, 2, 2, 2]
def baseStart_7898068 : Nat := 118140960795 + 7898068 * 2 ^ 59
def prefixEnd_7898068 : Nat := 4983230072969 + 3 ^ 40 * 7898068 * 2
def baseEnd_7898068 : Nat := 4055505125894710006327453

theorem tailTrace_7898068 : CollatzResearch.WordTrace tailWord_7898068 prefixEnd_7898068 4055505125894710006327453 := by
  unfold tailWord_7898068
  simp only [CollatzResearch.WordTrace]
  refine ⟨144033102775327996734739429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192044137033770662312985905 144033102775327996734739429)
  ·
    refine ⟨27006206770373999387763643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144033102775327996734739429 27006206770373999387763643)
    ·
      refine ⟨40509310155560999081645465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27006206770373999387763643 40509310155560999081645465)
      ·
        refine ⟨30381982616670749311234099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40509310155560999081645465 30381982616670749311234099)
        ·
          refine ⟨45572973925006123966851149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30381982616670749311234099 45572973925006123966851149)
          ·
            refine ⟨17089865221877296487569181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45572973925006123966851149 17089865221877296487569181)
            ·
              refine ⟨6408699458203986182838443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17089865221877296487569181 6408699458203986182838443)
              ·
                refine ⟨9613049187305979274257665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6408699458203986182838443 9613049187305979274257665)
                ·
                  refine ⟨7209786890479484455693249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9613049187305979274257665 7209786890479484455693249)
                  ·
                    refine ⟨5407340167859613341769937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7209786890479484455693249 5407340167859613341769937)
                    ·
                      refine ⟨4055505125894710006327453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5407340167859613341769937 4055505125894710006327453)
                      ·
                        rfl

theorem cell23_7898068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 3, 1, 2, 2, 2].length) (baseStart_7898068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7898068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7898068 prefixEnd_7898068 := by exact prefixLift 7898068
  have htrace : WordTrace (prefixWord ++ tailWord_7898068) baseStart_7898068 baseEnd_7898068 := by
    simpa [prefixWord, tailWord_7898068, baseEnd_7898068] using wordTrace_append hprefix tailTrace_7898068
  have hstable : (prefixWord ++ tailWord_7898068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7898068).length < 2 ^ (prefixWord ++ tailWord_7898068).sum := by decide
  have hdescent : baseEnd_7898068 < baseStart_7898068 := by decide
  rcases family_descends (prefixWord ++ tailWord_7898068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7898164 : List Nat := [2, 5, 1, 2, 1, 1, 1, 4, 6]
def baseStart_7898164 : Nat := 118140960795 + 7898164 * 2 ^ 59
def prefixEnd_7898164 : Nat := 4983230072969 + 3 ^ 40 * 7898164 * 2
def baseEnd_7898164 : Nat := 450617157781949070080779

theorem tailTrace_7898164 : CollatzResearch.WordTrace tailWord_7898164 prefixEnd_7898164 450617157781949070080779 := by
  unfold tailWord_7898164
  simp only [CollatzResearch.WordTrace]
  refine ⟨144034853479154100932486773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192046471305538801243315697 144034853479154100932486773)
  ·
    refine ⟨13503267513670696962420635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 144034853479154100932486773 13503267513670696962420635)
    ·
      refine ⟨20254901270506045443630953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13503267513670696962420635 20254901270506045443630953)
      ·
        refine ⟨15191175952879534082723215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20254901270506045443630953 15191175952879534082723215)
        ·
          refine ⟨22786763929319301124084823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15191175952879534082723215 22786763929319301124084823)
          ·
            refine ⟨34180145893978951686127235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22786763929319301124084823 34180145893978951686127235)
            ·
              refine ⟨51270218840968427529190853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34180145893978951686127235 51270218840968427529190853)
              ·
                refine ⟨9613166032681580161723285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51270218840968427529190853 9613166032681580161723285)
                ·
                  refine ⟨450617157781949070080779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9613166032681580161723285 450617157781949070080779)
                  ·
                    rfl

theorem cell23_7898164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_7898164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7898164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7898164 prefixEnd_7898164 := by exact prefixLift 7898164
  have htrace : WordTrace (prefixWord ++ tailWord_7898164) baseStart_7898164 baseEnd_7898164 := by
    simpa [prefixWord, tailWord_7898164, baseEnd_7898164] using wordTrace_append hprefix tailTrace_7898164
  have hstable : (prefixWord ++ tailWord_7898164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7898164).length < 2 ^ (prefixWord ++ tailWord_7898164).sum := by decide
  have hdescent : baseEnd_7898164 < baseStart_7898164 := by decide
  rcases family_descends (prefixWord ++ tailWord_7898164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7898167 : List Nat := [1, 1, 3, 1, 2, 2, 1, 2, 3, 5, 2]
def baseStart_7898167 : Nat := 118140960795 + 7898167 * 2 ^ 59
def prefixEnd_7898167 : Nat := 4983230072969 + 3 ^ 40 * 7898167 * 2
def baseEnd_7898167 : Nat := 4055555960479505118989497

theorem tailTrace_7898167 : CollatzResearch.WordTrace tailWord_7898167 prefixEnd_7898167 4055555960479505118989497 := by
  unfold tailWord_7898167
  simp only [CollatzResearch.WordTrace]
  refine ⟨288069816377297333377332755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192046544251531555584888503 288069816377297333377332755)
  ·
    refine ⟨432104724565946000065999133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288069816377297333377332755 432104724565946000065999133)
    ·
      refine ⟨162039271712229750024749675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 432104724565946000065999133 162039271712229750024749675)
      ·
        refine ⟨243058907568344625037124513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162039271712229750024749675 243058907568344625037124513)
        ·
          refine ⟨182294180676258468777843385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243058907568344625037124513 182294180676258468777843385)
          ·
            refine ⟨136720635507193851583382539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182294180676258468777843385 136720635507193851583382539)
            ·
              refine ⟨205080953260790777375073809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136720635507193851583382539 205080953260790777375073809)
              ·
                refine ⟨153810714945593083031305357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205080953260790777375073809 153810714945593083031305357)
                ·
                  refine ⟨57679018104597406136739509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 153810714945593083031305357 57679018104597406136739509)
                  ·
                    refine ⟨5407407947306006825319329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57679018104597406136739509 5407407947306006825319329)
                    ·
                      refine ⟨4055555960479505118989497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5407407947306006825319329 4055555960479505118989497)
                      ·
                        rfl

theorem cell23_7898167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 5, 2].length) (baseStart_7898167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7898167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7898167 prefixEnd_7898167 := by exact prefixLift 7898167
  have htrace : WordTrace (prefixWord ++ tailWord_7898167) baseStart_7898167 baseEnd_7898167 := by
    simpa [prefixWord, tailWord_7898167, baseEnd_7898167] using wordTrace_append hprefix tailTrace_7898167
  have hstable : (prefixWord ++ tailWord_7898167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7898167).length < 2 ^ (prefixWord ++ tailWord_7898167).sum := by decide
  have hdescent : baseEnd_7898167 < baseStart_7898167 := by decide
  rcases family_descends (prefixWord ++ tailWord_7898167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7898168 : List Nat := [2, 1, 2, 1, 5, 3, 2, 2, 1, 4]
def baseStart_7898168 : Nat := 118140960795 + 7898168 * 2 ^ 59
def prefixEnd_7898168 : Nat := 4983230072969 + 3 ^ 40 * 7898168 * 2
def baseEnd_7898168 : Nat := 1351852157986719871692331

theorem tailTrace_7898168 : CollatzResearch.WordTrace tailWord_7898168 prefixEnd_7898168 1351852157986719871692331 := by
  unfold tailWord_7898168
  simp only [CollatzResearch.WordTrace]
  refine ⟨144034926425146855274059579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192046568566862473698746105 144034926425146855274059579)
  ·
    refine ⟨216052389637720282911089369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144034926425146855274059579 216052389637720282911089369)
    ·
      refine ⟨162039292228290212183317027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216052389637720282911089369 162039292228290212183317027)
      ·
        refine ⟨243058938342435318274975541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162039292228290212183317027 243058938342435318274975541)
        ·
          refine ⟨22786775469603311088278957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 243058938342435318274975541 22786775469603311088278957)
          ·
            refine ⟨8545040801101241658104609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22786775469603311088278957 8545040801101241658104609)
            ·
              refine ⟨6408780600825931243578457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8545040801101241658104609 6408780600825931243578457)
              ·
                refine ⟨4806585450619448432683843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6408780600825931243578457 4806585450619448432683843)
                ·
                  refine ⟨7209878175929172649025765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4806585450619448432683843 7209878175929172649025765)
                  ·
                    refine ⟨1351852157986719871692331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7209878175929172649025765 1351852157986719871692331)
                    ·
                      rfl

theorem cell23_7898168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 2, 2, 1, 4].length) (baseStart_7898168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7898168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7898168 prefixEnd_7898168 := by exact prefixLift 7898168
  have htrace : WordTrace (prefixWord ++ tailWord_7898168) baseStart_7898168 baseEnd_7898168 := by
    simpa [prefixWord, tailWord_7898168, baseEnd_7898168] using wordTrace_append hprefix tailTrace_7898168
  have hstable : (prefixWord ++ tailWord_7898168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7898168).length < 2 ^ (prefixWord ++ tailWord_7898168).sum := by decide
  have hdescent : baseEnd_7898168 < baseStart_7898168 := by decide
  rcases family_descends (prefixWord ++ tailWord_7898168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7898197 : List Nat := [1, 3, 2, 2, 1, 2, 1, 3, 3, 1, 4]
def baseStart_7898197 : Nat := 118140960795 + 7898197 * 2 ^ 59
def prefixEnd_7898197 : Nat := 4983230072969 + 3 ^ 40 * 7898197 * 2
def baseEnd_7898197 : Nat := 4055571364899140001614359

theorem tailTrace_7898197 : CollatzResearch.WordTrace tailWord_7898197 prefixEnd_7898197 4055571364899140001614359 := by
  unfold tailWord_7898197
  simp only [CollatzResearch.WordTrace]
  refine ⟨288070910567188648500924845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192047273711459099000616563 288070910567188648500924845)
  ·
    refine ⟨108026591462695743187846817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288070910567188648500924845 108026591462695743187846817)
    ·
      refine ⟨81019943597021807390885113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108026591462695743187846817 81019943597021807390885113)
      ·
        refine ⟨60764957697766355543163835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81019943597021807390885113 60764957697766355543163835)
        ·
          refine ⟨91147436546649533314745753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60764957697766355543163835 91147436546649533314745753)
          ·
            refine ⟨68360577409987149986059315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91147436546649533314745753 68360577409987149986059315)
            ·
              refine ⟨102540866114980724979088973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68360577409987149986059315 102540866114980724979088973)
              ·
                refine ⟨38452824793117771867158365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102540866114980724979088973 38452824793117771867158365)
                ·
                  refine ⟨14419809297419164450184387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38452824793117771867158365 14419809297419164450184387)
                  ·
                    refine ⟨21629713946128746675276581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14419809297419164450184387 21629713946128746675276581)
                    ·
                      refine ⟨4055571364899140001614359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21629713946128746675276581 4055571364899140001614359)
                      ·
                        rfl

theorem cell23_7898197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_7898197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7898197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7898197 prefixEnd_7898197 := by exact prefixLift 7898197
  have htrace : WordTrace (prefixWord ++ tailWord_7898197) baseStart_7898197 baseEnd_7898197 := by
    simpa [prefixWord, tailWord_7898197, baseEnd_7898197] using wordTrace_append hprefix tailTrace_7898197
  have hstable : (prefixWord ++ tailWord_7898197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7898197).length < 2 ^ (prefixWord ++ tailWord_7898197).sum := by decide
  have hdescent : baseEnd_7898197 < baseStart_7898197 := by decide
  rcases family_descends (prefixWord ++ tailWord_7898197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7898207 : List Nat := [1, 1, 2, 3, 1, 1, 4, 2, 4, 4]
def baseStart_7898207 : Nat := 118140960795 + 7898207 * 2 ^ 59
def prefixEnd_7898207 : Nat := 4983230072969 + 3 ^ 40 * 7898207 * 2
def baseEnd_7898207 : Nat := 1351858833235228320829771

theorem tailTrace_7898207 : CollatzResearch.WordTrace tailWord_7898207 prefixEnd_7898207 1351858833235228320829771 := by
  unfold tailWord_7898207
  simp only [CollatzResearch.WordTrace]
  refine ⟨288071275297152420208788875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192047516864768280139192583 288071275297152420208788875)
  ·
    refine ⟨432106912945728630313183313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288071275297152420208788875 432106912945728630313183313)
    ·
      refine ⟨324080184709296472734887485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432106912945728630313183313 324080184709296472734887485)
      ·
        refine ⟨121530069265986177275582807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 324080184709296472734887485 121530069265986177275582807)
        ·
          refine ⟨182295103898979265913374211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121530069265986177275582807 182295103898979265913374211)
          ·
            refine ⟨273442655848468898870061317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182295103898979265913374211 273442655848468898870061317)
            ·
              refine ⟨51270497971587918538136497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 273442655848468898870061317 51270497971587918538136497)
              ·
                refine ⟨38452873478690938903602373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51270497971587918538136497 38452873478690938903602373)
                ·
                  refine ⟨7209913777254551044425445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38452873478690938903602373 7209913777254551044425445)
                  ·
                    refine ⟨1351858833235228320829771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7209913777254551044425445 1351858833235228320829771)
                    ·
                      rfl

theorem cell23_7898207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 4, 4].length) (baseStart_7898207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7898207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7898207 prefixEnd_7898207 := by exact prefixLift 7898207
  have htrace : WordTrace (prefixWord ++ tailWord_7898207) baseStart_7898207 baseEnd_7898207 := by
    simpa [prefixWord, tailWord_7898207, baseEnd_7898207] using wordTrace_append hprefix tailTrace_7898207
  have hstable : (prefixWord ++ tailWord_7898207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7898207).length < 2 ^ (prefixWord ++ tailWord_7898207).sum := by decide
  have hdescent : baseEnd_7898207 < baseStart_7898207 := by decide
  rcases family_descends (prefixWord ++ tailWord_7898207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7898220 : List Nat := [2, 2, 1, 1, 3, 2, 12]
def baseStart_7898220 : Nat := 118140960795 + 7898220 * 2 ^ 59
def prefixEnd_7898220 : Nat := 4983230072969 + 3 ^ 40 * 7898220 * 2
def baseEnd_7898220 : Nat := 50068928085854239649713

theorem tailTrace_7898220 : CollatzResearch.WordTrace tailWord_7898220 prefixEnd_7898220 50068928085854239649713 := by
  unfold tailWord_7898220
  simp only [CollatzResearch.WordTrace]
  refine ⟨144035874723052661714506057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192047832964070215619341409 144035874723052661714506057)
  ·
    refine ⟨108026906042289496285879543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144035874723052661714506057 108026906042289496285879543)
    ·
      refine ⟨162040359063434244428819315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108026906042289496285879543 162040359063434244428819315)
      ·
        refine ⟨243060538595151366643228973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162040359063434244428819315 243060538595151366643228973)
        ·
          refine ⟨91147701973181762491210865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 243060538595151366643228973 91147701973181762491210865)
          ·
            refine ⟨68360776479886321868408149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91147701973181762491210865 68360776479886321868408149)
            ·
              refine ⟨50068928085854239649713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 68360776479886321868408149 50068928085854239649713)
              ·
                rfl

theorem cell23_7898220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 12].length) (baseStart_7898220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7898220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7898220 prefixEnd_7898220 := by exact prefixLift 7898220
  have htrace : WordTrace (prefixWord ++ tailWord_7898220) baseStart_7898220 baseEnd_7898220 := by
    simpa [prefixWord, tailWord_7898220, baseEnd_7898220] using wordTrace_append hprefix tailTrace_7898220
  have hstable : (prefixWord ++ tailWord_7898220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7898220).length < 2 ^ (prefixWord ++ tailWord_7898220).sum := by decide
  have hdescent : baseEnd_7898220 < baseStart_7898220 := by decide
  rcases family_descends (prefixWord ++ tailWord_7898220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7898231 : List Nat := [1, 1, 3, 1, 1, 4, 4, 1, 3, 2, 2]
def baseStart_7898231 : Nat := 118140960795 + 7898231 * 2 ^ 59
def prefixEnd_7898231 : Nat := 4983230072969 + 3 ^ 40 * 7898231 * 2
def baseEnd_7898231 : Nat := 4055588823241392868589203

theorem tailTrace_7898231 : CollatzResearch.WordTrace tailWord_7898231 prefixEnd_7898231 4055588823241392868589203 := by
  unfold tailWord_7898231
  simp only [CollatzResearch.WordTrace]
  refine ⟨288072150649065472307662547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192048100432710314871775031 288072150649065472307662547)
  ·
    refine ⟨432108225973598208461493821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288072150649065472307662547 432108225973598208461493821)
    ·
      refine ⟨162040584740099328173060183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 432108225973598208461493821 162040584740099328173060183)
      ·
        refine ⟨243060877110148992259590275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162040584740099328173060183 243060877110148992259590275)
        ·
          refine ⟨364591315665223488389385413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243060877110148992259590275 364591315665223488389385413)
          ·
            refine ⟨68360871687229404073009765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 364591315665223488389385413 68360871687229404073009765)
            ·
              refine ⟨12817663441355513263689331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68360871687229404073009765 12817663441355513263689331)
              ·
                refine ⟨19226495162033269895533997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12817663441355513263689331 19226495162033269895533997)
                ·
                  refine ⟨7209935685762476210825249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19226495162033269895533997 7209935685762476210825249)
                  ·
                    refine ⟨5407451764321857158118937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7209935685762476210825249 5407451764321857158118937)
                    ·
                      refine ⟨4055588823241392868589203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5407451764321857158118937 4055588823241392868589203)
                      ·
                        rfl

theorem cell23_7898231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 1, 3, 2, 2].length) (baseStart_7898231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7898231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7898231 prefixEnd_7898231 := by exact prefixLift 7898231
  have htrace : WordTrace (prefixWord ++ tailWord_7898231) baseStart_7898231 baseEnd_7898231 := by
    simpa [prefixWord, tailWord_7898231, baseEnd_7898231] using wordTrace_append hprefix tailTrace_7898231
  have hstable : (prefixWord ++ tailWord_7898231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7898231).length < 2 ^ (prefixWord ++ tailWord_7898231).sum := by decide
  have hdescent : baseEnd_7898231 < baseStart_7898231 := by decide
  rcases family_descends (prefixWord ++ tailWord_7898231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7898244 : List Nat := [2, 3, 2, 1, 2, 2, 3, 1, 1, 2, 4]
def baseStart_7898244 : Nat := 118140960795 + 7898244 * 2 ^ 59
def prefixEnd_7898244 : Nat := 4983230072969 + 3 ^ 40 * 7898244 * 2
def baseEnd_7898244 : Nat := 4055595498489901317726643

theorem tailTrace_7898244 : CollatzResearch.WordTrace tailWord_7898244 prefixEnd_7898244 4055595498489901317726643 := by
  unfold tailWord_7898244
  simp only [CollatzResearch.WordTrace]
  refine ⟨144036312399009187763942893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192048416532012250351923857 144036312399009187763942893)
  ·
    refine ⟨54013617149628445411478585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144036312399009187763942893 54013617149628445411478585)
    ·
      refine ⟨40510212862221334058608939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54013617149628445411478585 40510212862221334058608939)
      ·
        refine ⟨60765319293332001087913409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40510212862221334058608939 60765319293332001087913409)
        ·
          refine ⟨45573989469999000815935057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60765319293332001087913409 45573989469999000815935057)
          ·
            refine ⟨34180492102499250611951293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45573989469999000815935057 34180492102499250611951293)
            ·
              refine ⟨12817684538437218979481735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34180492102499250611951293 12817684538437218979481735)
              ·
                refine ⟨19226526807655828469222603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12817684538437218979481735 19226526807655828469222603)
                ·
                  refine ⟨28839790211483742703833905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19226526807655828469222603 28839790211483742703833905)
                  ·
                    refine ⟨21629842658612807027875429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28839790211483742703833905 21629842658612807027875429)
                    ·
                      refine ⟨4055595498489901317726643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21629842658612807027875429 4055595498489901317726643)
                      ·
                        rfl

theorem cell23_7898244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 1, 1, 2, 4].length) (baseStart_7898244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7898244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7898244 prefixEnd_7898244 := by exact prefixLift 7898244
  have htrace : WordTrace (prefixWord ++ tailWord_7898244) baseStart_7898244 baseEnd_7898244 := by
    simpa [prefixWord, tailWord_7898244, baseEnd_7898244] using wordTrace_append hprefix tailTrace_7898244
  have hstable : (prefixWord ++ tailWord_7898244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7898244).length < 2 ^ (prefixWord ++ tailWord_7898244).sum := by decide
  have hdescent : baseEnd_7898244 < baseStart_7898244 := by decide
  rcases family_descends (prefixWord ++ tailWord_7898244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7898254 : List Nat := [4, 1, 1, 3, 2, 1, 4, 7]
def baseStart_7898254 : Nat := 118140960795 + 7898254 * 2 ^ 59
def prefixEnd_7898254 : Nat := 4983230072969 + 3 ^ 40 * 7898254 * 2
def baseEnd_7898254 : Nat := 150207430862831343651911

theorem tailTrace_7898254 : CollatzResearch.WordTrace tailWord_7898254 prefixEnd_7898254 150207430862831343651911 := by
  unfold tailWord_7898254
  simp only [CollatzResearch.WordTrace]
  refine ⟨36009123690997768404468727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192048659685321431490499877 36009123690997768404468727)
  ·
    refine ⟨54013685536496652606703091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36009123690997768404468727 54013685536496652606703091)
    ·
      refine ⟨81020528304744978910054637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54013685536496652606703091 81020528304744978910054637)
      ·
        refine ⟨30382698114279367091270489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81020528304744978910054637 30382698114279367091270489)
        ·
          refine ⟨22787023585709525318452867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30382698114279367091270489 22787023585709525318452867)
          ·
            refine ⟨34180535378564287977679301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22787023585709525318452867 34180535378564287977679301)
            ·
              refine ⟨6408850383480803995814869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34180535378564287977679301 6408850383480803995814869)
              ·
                refine ⟨150207430862831343651911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6408850383480803995814869 150207430862831343651911)
                ·
                  rfl

theorem cell23_7898254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 4, 7].length) (baseStart_7898254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7898254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7898254 prefixEnd_7898254 := by exact prefixLift 7898254
  have htrace : WordTrace (prefixWord ++ tailWord_7898254) baseStart_7898254 baseEnd_7898254 := by
    simpa [prefixWord, tailWord_7898254, baseEnd_7898254] using wordTrace_append hprefix tailTrace_7898254
  have hstable : (prefixWord ++ tailWord_7898254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7898254).length < 2 ^ (prefixWord ++ tailWord_7898254).sum := by decide
  have hdescent : baseEnd_7898254 < baseStart_7898254 := by decide
  rcases family_descends (prefixWord ++ tailWord_7898254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7898307 : List Nat := [1, 1, 1, 3, 1, 1, 1, 3, 4, 4, 3]
def baseStart_7898307 : Nat := 118140960795 + 7898307 * 2 ^ 59
def prefixEnd_7898307 : Nat := 4983230072969 + 3 ^ 40 * 7898307 * 2
def baseEnd_7898307 : Nat := 4055627847771134571238853

theorem tailTrace_7898307 : CollatzResearch.WordTrace tailWord_7898307 prefixEnd_7898307 4055627847771134571238853 := by
  unfold tailWord_7898307
  simp only [CollatzResearch.WordTrace]
  refine ⟨288074922596790137287429175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192049948397860091524952783 288074922596790137287429175)
  ·
    refine ⟨432112383895185205931143763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288074922596790137287429175 432112383895185205931143763)
    ·
      refine ⟨648168575842777808896715645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432112383895185205931143763 648168575842777808896715645)
      ·
        refine ⟨243063215941041678336268367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 648168575842777808896715645 243063215941041678336268367)
        ·
          refine ⟨364594823911562517504402551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243063215941041678336268367 364594823911562517504402551)
          ·
            refine ⟨546892235867343776256603827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364594823911562517504402551 546892235867343776256603827)
            ·
              refine ⟨820338353801015664384905741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 546892235867343776256603827 820338353801015664384905741)
              ·
                refine ⟨307626882675380874144339653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 820338353801015664384905741 307626882675380874144339653)
                ·
                  refine ⟨57680040501633913902063685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 307626882675380874144339653 57680040501633913902063685)
                  ·
                    refine ⟨10815007594056358856636941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57680040501633913902063685 10815007594056358856636941)
                    ·
                      refine ⟨4055627847771134571238853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10815007594056358856636941 4055627847771134571238853)
                      ·
                        rfl

theorem cell23_7898307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 4, 3].length) (baseStart_7898307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7898307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7898307 prefixEnd_7898307 := by exact prefixLift 7898307
  have htrace : WordTrace (prefixWord ++ tailWord_7898307) baseStart_7898307 baseEnd_7898307 := by
    simpa [prefixWord, tailWord_7898307, baseEnd_7898307] using wordTrace_append hprefix tailTrace_7898307
  have hstable : (prefixWord ++ tailWord_7898307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7898307).length < 2 ^ (prefixWord ++ tailWord_7898307).sum := by decide
  have hdescent : baseEnd_7898307 < baseStart_7898307 := by decide
  rcases family_descends (prefixWord ++ tailWord_7898307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7898308 : List Nat := [2, 3, 3, 1, 3, 1, 1, 1, 3, 3, 2]
def baseStart_7898308 : Nat := 118140960795 + 7898308 * 2 ^ 59
def prefixEnd_7898308 : Nat := 4983230072969 + 3 ^ 40 * 7898308 * 2
def baseEnd_7898308 : Nat := 4055628361251789067326349

theorem tailTrace_7898308 : CollatzResearch.WordTrace tailWord_7898308 prefixEnd_7898308 4055628361251789067326349 := by
  unfold tailWord_7898308
  simp only [CollatzResearch.WordTrace]
  refine ⟨144037479534893257229107789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192049972713191009638810385 144037479534893257229107789)
  ·
    refine ⟨54014054825584971460915421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144037479534893257229107789 54014054825584971460915421)
    ·
      refine ⟨20255270559594364297843283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54014054825584971460915421 20255270559594364297843283)
      ·
        refine ⟨30382905839391546446764925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20255270559594364297843283 30382905839391546446764925)
        ·
          refine ⟨11393589689771829917536847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30382905839391546446764925 11393589689771829917536847)
          ·
            refine ⟨17090384534657744876305271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11393589689771829917536847 17090384534657744876305271)
            ·
              refine ⟨25635576801986617314457907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17090384534657744876305271 25635576801986617314457907)
              ·
                refine ⟨38453365202979925971686861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25635576801986617314457907 38453365202979925971686861)
                ·
                  refine ⟨14420011951117472239382573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38453365202979925971686861 14420011951117472239382573)
                  ·
                    refine ⟨5407504481669052089768465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14420011951117472239382573 5407504481669052089768465)
                    ·
                      refine ⟨4055628361251789067326349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5407504481669052089768465 4055628361251789067326349)
                      ·
                        rfl

theorem cell23_7898308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 3, 3, 2].length) (baseStart_7898308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7898308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7898308 prefixEnd_7898308 := by exact prefixLift 7898308
  have htrace : WordTrace (prefixWord ++ tailWord_7898308) baseStart_7898308 baseEnd_7898308 := by
    simpa [prefixWord, tailWord_7898308, baseEnd_7898308] using wordTrace_append hprefix tailTrace_7898308
  have hstable : (prefixWord ++ tailWord_7898308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7898308).length < 2 ^ (prefixWord ++ tailWord_7898308).sum := by decide
  have hdescent : baseEnd_7898308 < baseStart_7898308 := by decide
  rcases family_descends (prefixWord ++ tailWord_7898308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7898325 : List Nat := [1, 3, 2, 4, 1, 2, 3, 1, 1, 3, 2]
def baseStart_7898325 : Nat := 118140960795 + 7898325 * 2 ^ 59
def prefixEnd_7898325 : Nat := 4983230072969 + 3 ^ 40 * 7898325 * 2
def baseEnd_7898325 : Nat := 4055637090422915500813771

theorem tailTrace_7898325 : CollatzResearch.WordTrace tailWord_7898325 prefixEnd_7898325 4055637090422915500813771 := by
  unfold tailWord_7898325
  simp only [CollatzResearch.WordTrace]
  refine ⟨288075579110724926361584429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192050386073816617574389619 288075579110724926361584429)
  ·
    refine ⟨108028342166521847385594161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288075579110724926361584429 108028342166521847385594161)
    ·
      refine ⟨81021256624891385539195621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108028342166521847385594161 81021256624891385539195621)
      ·
        refine ⟨15191485617167134788599179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81021256624891385539195621 15191485617167134788599179)
        ·
          refine ⟨22787228425750702182898769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15191485617167134788599179 22787228425750702182898769)
          ·
            refine ⟨17090421319313026637174077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22787228425750702182898769 17090421319313026637174077)
            ·
              refine ⟨6408907994742384988940279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17090421319313026637174077 6408907994742384988940279)
              ·
                refine ⟨9613361992113577483410419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6408907994742384988940279 9613361992113577483410419)
                ·
                  refine ⟨14420042988170366225115629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9613361992113577483410419 14420042988170366225115629)
                  ·
                    refine ⟨5407516120563887334418361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14420042988170366225115629 5407516120563887334418361)
                    ·
                      refine ⟨4055637090422915500813771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5407516120563887334418361 4055637090422915500813771)
                      ·
                        rfl

theorem cell23_7898325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_7898325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7898325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7898325 prefixEnd_7898325 := by exact prefixLift 7898325
  have htrace : WordTrace (prefixWord ++ tailWord_7898325) baseStart_7898325 baseEnd_7898325 := by
    simpa [prefixWord, tailWord_7898325, baseEnd_7898325] using wordTrace_append hprefix tailTrace_7898325
  have hstable : (prefixWord ++ tailWord_7898325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7898325).length < 2 ^ (prefixWord ++ tailWord_7898325).sum := by decide
  have hdescent : baseEnd_7898325 < baseStart_7898325 := by decide
  rcases family_descends (prefixWord ++ tailWord_7898325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7898421 : List Nat := [1, 3, 3, 1, 2, 2, 2, 2, 3, 4]
def baseStart_7898421 : Nat := 118140960795 + 7898421 * 2 ^ 59
def prefixEnd_7898421 : Nat := 4983230072969 + 3 ^ 40 * 7898421 * 2
def baseEnd_7898421 : Nat := 1351895461521915708404443

theorem tailTrace_7898421 : CollatzResearch.WordTrace tailWord_7898421 prefixEnd_7898421 1351895461521915708404443 := by
  unfold tailWord_7898421
  simp only [CollatzResearch.WordTrace]
  refine ⟨288079080518377134757079117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192052720345584756504719411 288079080518377134757079117)
  ·
    refine ⟨108029655194391425533904669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288079080518377134757079117 108029655194391425533904669)
    ·
      refine ⟨40511120697896784575214251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108029655194391425533904669 40511120697896784575214251)
      ·
        refine ⟨60766681046845176862821377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40511120697896784575214251 60766681046845176862821377)
        ·
          refine ⟨45575010785133882647116033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60766681046845176862821377 45575010785133882647116033)
          ·
            refine ⟨34181258088850411985337025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45575010785133882647116033 34181258088850411985337025)
            ·
              refine ⟨25635943566637808989002769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34181258088850411985337025 25635943566637808989002769)
              ·
                refine ⟨19226957674978356741752077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25635943566637808989002769 19226957674978356741752077)
                ·
                  refine ⟨7210109128116883778157029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19226957674978356741752077 7210109128116883778157029)
                  ·
                    refine ⟨1351895461521915708404443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7210109128116883778157029 1351895461521915708404443)
                    ·
                      rfl

theorem cell23_7898421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 2, 3, 4].length) (baseStart_7898421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7898421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7898421 prefixEnd_7898421 := by exact prefixLift 7898421
  have htrace : WordTrace (prefixWord ++ tailWord_7898421) baseStart_7898421 baseEnd_7898421 := by
    simpa [prefixWord, tailWord_7898421, baseEnd_7898421] using wordTrace_append hprefix tailTrace_7898421
  have hstable : (prefixWord ++ tailWord_7898421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7898421).length < 2 ^ (prefixWord ++ tailWord_7898421).sum := by decide
  have hdescent : baseEnd_7898421 < baseStart_7898421 := by decide
  rcases family_descends (prefixWord ++ tailWord_7898421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7898445 : List Nat := [1, 6, 1, 3, 1, 1, 1, 2, 2, 1, 4]
def baseStart_7898445 : Nat := 118140960795 + 7898445 * 2 ^ 59
def prefixEnd_7898445 : Nat := 4983230072969 + 3 ^ 40 * 7898445 * 2
def baseEnd_7898445 : Nat := 4055698708101455031313219

theorem tailTrace_7898445 : CollatzResearch.WordTrace tailWord_7898445 prefixEnd_7898445 4055698708101455031313219 := by
  unfold tailWord_7898445
  simp only [CollatzResearch.WordTrace]
  refine ⟨288079955870290186855952789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192053303913526791237301859 288079955870290186855952789)
  ·
    refine ⟨13503747931419852508872787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 288079955870290186855952789 13503747931419852508872787)
    ·
      refine ⟨20255621897129778763309181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13503747931419852508872787 20255621897129778763309181)
      ·
        refine ⟨7595858211423667036240943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20255621897129778763309181 7595858211423667036240943)
        ·
          refine ⟨11393787317135500554361415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7595858211423667036240943 11393787317135500554361415)
          ·
            refine ⟨17090680975703250831542123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11393787317135500554361415 17090680975703250831542123)
            ·
              refine ⟨25636021463554876247313185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17090680975703250831542123 25636021463554876247313185)
              ·
                refine ⟨19227016097666157185484889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25636021463554876247313185 19227016097666157185484889)
                ·
                  refine ⟨14420262073249617889113667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19227016097666157185484889 14420262073249617889113667)
                  ·
                    refine ⟨21630393109874426833670501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14420262073249617889113667 21630393109874426833670501)
                    ·
                      refine ⟨4055698708101455031313219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21630393109874426833670501 4055698708101455031313219)
                      ·
                        rfl

theorem cell23_7898445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_7898445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7898445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7898445 prefixEnd_7898445 := by exact prefixLift 7898445
  have htrace : WordTrace (prefixWord ++ tailWord_7898445) baseStart_7898445 baseEnd_7898445 := by
    simpa [prefixWord, tailWord_7898445, baseEnd_7898445] using wordTrace_append hprefix tailTrace_7898445
  have hstable : (prefixWord ++ tailWord_7898445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7898445).length < 2 ^ (prefixWord ++ tailWord_7898445).sum := by decide
  have hdescent : baseEnd_7898445 < baseStart_7898445 := by decide
  rcases family_descends (prefixWord ++ tailWord_7898445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7898447 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 1, 11]
def baseStart_7898447 : Nat := 118140960795 + 7898447 * 2 ^ 59
def prefixEnd_7898447 : Nat := 4983230072969 + 3 ^ 40 * 7898447 * 2
def baseEnd_7898447 : Nat := 1351899911687588007829403

theorem tailTrace_7898447 : CollatzResearch.WordTrace tailWord_7898447 prefixEnd_7898447 1351899911687588007829403 := by
  unfold tailWord_7898447
  simp only [CollatzResearch.WordTrace]
  refine ⟨288080028816282941197525595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192053352544188627465017063 288080028816282941197525595)
  ·
    refine ⟨432120043224424411796288393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288080028816282941197525595 432120043224424411796288393)
    ·
      refine ⟨324090032418318308847216295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432120043224424411796288393 324090032418318308847216295)
      ·
        refine ⟨486135048627477463270824443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324090032418318308847216295 486135048627477463270824443)
        ·
          refine ⟨729202572941216194906236665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486135048627477463270824443 729202572941216194906236665)
          ·
            refine ⟨546901929705912146179677499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 729202572941216194906236665 546901929705912146179677499)
            ·
              refine ⟨820352894558868219269516249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 546901929705912146179677499 820352894558868219269516249)
              ·
                refine ⟨615264670919151164452137187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 820352894558868219269516249 615264670919151164452137187)
                ·
                  refine ⟨922897006378726746678205781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 615264670919151164452137187 922897006378726746678205781)
                  ·
                    refine ⟨1351899911687588007829403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 922897006378726746678205781 1351899911687588007829403)
                    ·
                      rfl

theorem cell23_7898447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 11].length) (baseStart_7898447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7898447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7898447 prefixEnd_7898447 := by exact prefixLift 7898447
  have htrace : WordTrace (prefixWord ++ tailWord_7898447) baseStart_7898447 baseEnd_7898447 := by
    simpa [prefixWord, tailWord_7898447, baseEnd_7898447] using wordTrace_append hprefix tailTrace_7898447
  have hstable : (prefixWord ++ tailWord_7898447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7898447).length < 2 ^ (prefixWord ++ tailWord_7898447).sum := by decide
  have hdescent : baseEnd_7898447 < baseStart_7898447 := by decide
  rcases family_descends (prefixWord ++ tailWord_7898447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7898455 : List Nat := [1, 1, 3, 2, 3, 3, 3, 2, 1, 4]
def baseStart_7898455 : Nat := 118140960795 + 7898455 * 2 ^ 59
def prefixEnd_7898455 : Nat := 4983230072969 + 3 ^ 40 * 7898455 * 2
def baseEnd_7898455 : Nat := 1351901280969333330729391

theorem tailTrace_7898455 : CollatzResearch.WordTrace tailWord_7898455 prefixEnd_7898455 1351901280969333330729391 := by
  unfold tailWord_7898455
  simp only [CollatzResearch.WordTrace]
  refine ⟨288080320600253958563816819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192053547066835972375877879 288080320600253958563816819)
  ·
    refine ⟨432120480900380937845725229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288080320600253958563816819 432120480900380937845725229)
    ·
      refine ⟨162045180337642851692146961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 432120480900380937845725229 162045180337642851692146961)
      ·
        refine ⟨121533885253232138769110221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162045180337642851692146961 121533885253232138769110221)
        ·
          refine ⟨45575206969962052038416333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121533885253232138769110221 45575206969962052038416333)
          ·
            refine ⟨17090702613735769514406125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45575206969962052038416333 17090702613735769514406125)
            ·
              refine ⟨6409013480150913567902297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17090702613735769514406125 6409013480150913567902297)
              ·
                refine ⟨4806760110113185175926723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6409013480150913567902297 4806760110113185175926723)
                ·
                  refine ⟨7210140165169777763890085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4806760110113185175926723 7210140165169777763890085)
                  ·
                    refine ⟨1351901280969333330729391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7210140165169777763890085 1351901280969333330729391)
                    ·
                      rfl

theorem cell23_7898455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 3, 2, 1, 4].length) (baseStart_7898455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7898455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7898455 prefixEnd_7898455 := by exact prefixLift 7898455
  have htrace : WordTrace (prefixWord ++ tailWord_7898455) baseStart_7898455 baseEnd_7898455 := by
    simpa [prefixWord, tailWord_7898455, baseEnd_7898455] using wordTrace_append hprefix tailTrace_7898455
  have hstable : (prefixWord ++ tailWord_7898455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7898455).length < 2 ^ (prefixWord ++ tailWord_7898455).sum := by decide
  have hdescent : baseEnd_7898455 < baseStart_7898455 := by decide
  rcases family_descends (prefixWord ++ tailWord_7898455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7898468 : List Nat := [2, 3, 1, 1, 3, 4, 2, 1, 6]
def baseStart_7898468 : Nat := 118140960795 + 7898468 * 2 ^ 59
def prefixEnd_7898468 : Nat := 4983230072969 + 3 ^ 40 * 7898468 * 2
def baseEnd_7898468 : Nat := 450634502017389826813957

theorem tailTrace_7898468 : CollatzResearch.WordTrace tailWord_7898468 prefixEnd_7898468 450634502017389826813957 := by
  unfold tailWord_7898468
  simp only [CollatzResearch.WordTrace]
  refine ⟨144040397374603430892020029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192053863166137907856026705 144040397374603430892020029)
  ·
    refine ⟨54015149015476286584507511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144040397374603430892020029 54015149015476286584507511)
    ·
      refine ⟨81022723523214429876761267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54015149015476286584507511 81022723523214429876761267)
      ·
        refine ⟨121534085284821644815141901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81022723523214429876761267 121534085284821644815141901)
        ·
          refine ⟨45575281981808116805678213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121534085284821644815141901 45575281981808116805678213)
          ·
            refine ⟨8545365371589021901064665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45575281981808116805678213 8545365371589021901064665)
            ·
              refine ⟨6409024028691766425798499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8545365371589021901064665 6409024028691766425798499)
              ·
                refine ⟨9613536043037649638697749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6409024028691766425798499 9613536043037649638697749)
                ·
                  refine ⟨450634502017389826813957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9613536043037649638697749 450634502017389826813957)
                  ·
                    rfl

theorem cell23_7898468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 2, 1, 6].length) (baseStart_7898468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7898468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7898468 prefixEnd_7898468 := by exact prefixLift 7898468
  have htrace : WordTrace (prefixWord ++ tailWord_7898468) baseStart_7898468 baseEnd_7898468 := by
    simpa [prefixWord, tailWord_7898468, baseEnd_7898468] using wordTrace_append hprefix tailTrace_7898468
  have hstable : (prefixWord ++ tailWord_7898468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7898468).length < 2 ^ (prefixWord ++ tailWord_7898468).sum := by decide
  have hdescent : baseEnd_7898468 < baseStart_7898468 := by decide
  rcases family_descends (prefixWord ++ tailWord_7898468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7898481 : List Nat := [1, 2, 2, 2, 1, 2, 5, 2, 1, 5]
def baseStart_7898481 : Nat := 118140960795 + 7898481 * 2 ^ 59
def prefixEnd_7898481 : Nat := 4983230072969 + 3 ^ 40 * 7898481 * 2
def baseEnd_7898481 : Nat := 1351905731135005630154351

theorem tailTrace_7898481 : CollatzResearch.WordTrace tailWord_7898481 prefixEnd_7898481 1351905731135005630154351 := by
  unfold tailWord_7898481
  simp only [CollatzResearch.WordTrace]
  refine ⟨288081268898159765004263297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192054179265439843336175531 288081268898159765004263297)
  ·
    refine ⟨216060951673619823753197473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288081268898159765004263297 216060951673619823753197473)
    ·
      refine ⟨162045713755214867814898105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216060951673619823753197473 162045713755214867814898105)
      ·
        refine ⟨121534285316411150861173579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162045713755214867814898105 121534285316411150861173579)
        ·
          refine ⟨182301427974616726291760369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121534285316411150861173579 182301427974616726291760369)
          ·
            refine ⟨136726070980962544718820277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182301427974616726291760369 136726070980962544718820277)
            ·
              refine ⟨12818069154465238567389401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 136726070980962544718820277 12818069154465238567389401)
              ·
                refine ⟨9613551865848928925542051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12818069154465238567389401 9613551865848928925542051)
                ·
                  refine ⟨14420327798773393388313077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9613551865848928925542051 14420327798773393388313077)
                  ·
                    refine ⟨1351905731135005630154351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14420327798773393388313077 1351905731135005630154351)
                    ·
                      rfl

theorem cell23_7898481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 2, 1, 5].length) (baseStart_7898481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7898481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7898481 prefixEnd_7898481 := by exact prefixLift 7898481
  have htrace : WordTrace (prefixWord ++ tailWord_7898481) baseStart_7898481 baseEnd_7898481 := by
    simpa [prefixWord, tailWord_7898481, baseEnd_7898481] using wordTrace_append hprefix tailTrace_7898481
  have hstable : (prefixWord ++ tailWord_7898481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7898481).length < 2 ^ (prefixWord ++ tailWord_7898481).sum := by decide
  have hdescent : baseEnd_7898481 < baseStart_7898481 := by decide
  rcases family_descends (prefixWord ++ tailWord_7898481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7898501 : List Nat := [1, 3, 1, 1, 3, 1, 2, 5, 1, 1, 4]
def baseStart_7898501 : Nat := 118140960795 + 7898501 * 2 ^ 59
def prefixEnd_7898501 : Nat := 4983230072969 + 3 ^ 40 * 7898501 * 2
def baseEnd_7898501 : Nat := 4055727463018106812212961

theorem tailTrace_7898501 : CollatzResearch.WordTrace tailWord_7898501 prefixEnd_7898501 4055727463018106812212961 := by
  unfold tailWord_7898501
  simp only [CollatzResearch.WordTrace]
  refine ⟨288081998358087308419991357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192054665572058205613327571 288081998358087308419991357)
  ·
    refine ⟨108030749384282740657496759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288081998358087308419991357 108030749384282740657496759)
    ·
      refine ⟨162046124076424110986245139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108030749384282740657496759 162046124076424110986245139)
      ·
        refine ⟨243069186114636166479367709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162046124076424110986245139 243069186114636166479367709)
        ·
          refine ⟨91150944792988562429762891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 243069186114636166479367709 91150944792988562429762891)
          ·
            refine ⟨136726417189482843644644337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91150944792988562429762891 136726417189482843644644337)
            ·
              refine ⟨102544812892112132733483253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136726417189482843644644337 102544812892112132733483253)
              ·
                refine ⟨9613576208635512443764055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 102544812892112132733483253 9613576208635512443764055)
                ·
                  refine ⟨14420364312953268665646083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9613576208635512443764055 14420364312953268665646083)
                  ·
                    refine ⟨21630546469429902998469125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14420364312953268665646083 21630546469429902998469125)
                    ·
                      refine ⟨4055727463018106812212961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21630546469429902998469125 4055727463018106812212961)
                      ·
                        rfl

theorem cell23_7898501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 5, 1, 1, 4].length) (baseStart_7898501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7898501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7898501 prefixEnd_7898501 := by exact prefixLift 7898501
  have htrace : WordTrace (prefixWord ++ tailWord_7898501) baseStart_7898501 baseEnd_7898501 := by
    simpa [prefixWord, tailWord_7898501, baseEnd_7898501] using wordTrace_append hprefix tailTrace_7898501
  have hstable : (prefixWord ++ tailWord_7898501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7898501).length < 2 ^ (prefixWord ++ tailWord_7898501).sum := by decide
  have hdescent : baseEnd_7898501 < baseStart_7898501 := by decide
  rcases family_descends (prefixWord ++ tailWord_7898501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7898521 : List Nat := [1, 2, 1, 2, 1, 5, 1, 2, 3, 2, 3]
def baseStart_7898521 : Nat := 118140960795 + 7898521 * 2 ^ 59
def prefixEnd_7898521 : Nat := 4983230072969 + 3 ^ 40 * 7898521 * 2
def baseEnd_7898521 : Nat := 4055737732631196733962869

theorem tailTrace_7898521 : CollatzResearch.WordTrace tailWord_7898521 prefixEnd_7898521 4055737732631196733962869 := by
  unfold tailWord_7898521
  simp only [CollatzResearch.WordTrace]
  refine ⟨288082727818014851835719417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192055151878676567890479611 288082727818014851835719417)
  ·
    refine ⟨216062045863511138876789563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288082727818014851835719417 216062045863511138876789563)
    ·
      refine ⟨324093068795266708315184345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216062045863511138876789563 324093068795266708315184345)
      ·
        refine ⟨243069801596450031236388259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324093068795266708315184345 243069801596450031236388259)
        ·
          refine ⟨364604702394675046854582389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243069801596450031236388259 364604702394675046854582389)
          ·
            refine ⟨34181690849500785642617099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 364604702394675046854582389 34181690849500785642617099)
            ·
              refine ⟨51272536274251178463925649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34181690849500785642617099 51272536274251178463925649)
              ·
                refine ⟨38454402205688383847944237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51272536274251178463925649 38454402205688383847944237)
                ·
                  refine ⟨14420400827133143942979089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38454402205688383847944237 14420400827133143942979089)
                  ·
                    refine ⟨10815300620349857957234317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14420400827133143942979089 10815300620349857957234317)
                    ·
                      refine ⟨4055737732631196733962869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10815300620349857957234317 4055737732631196733962869)
                      ·
                        rfl

theorem cell23_7898521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 3, 2, 3].length) (baseStart_7898521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7898521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7898521 prefixEnd_7898521 := by exact prefixLift 7898521
  have htrace : WordTrace (prefixWord ++ tailWord_7898521) baseStart_7898521 baseEnd_7898521 := by
    simpa [prefixWord, tailWord_7898521, baseEnd_7898521] using wordTrace_append hprefix tailTrace_7898521
  have hstable : (prefixWord ++ tailWord_7898521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7898521).length < 2 ^ (prefixWord ++ tailWord_7898521).sum := by decide
  have hdescent : baseEnd_7898521 < baseStart_7898521 := by decide
  rcases family_descends (prefixWord ++ tailWord_7898521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7898531 : List Nat := [1, 1, 1, 4, 1, 3, 4, 1, 1, 2, 4]
def baseStart_7898531 : Nat := 118140960795 + 7898531 * 2 ^ 59
def prefixEnd_7898531 : Nat := 4983230072969 + 3 ^ 40 * 7898531 * 2
def baseEnd_7898531 : Nat := 4055742867437741694837823

theorem tailTrace_7898531 : CollatzResearch.WordTrace tailWord_7898531 prefixEnd_7898531 4055742867437741694837823 := by
  unfold tailWord_7898531
  simp only [CollatzResearch.WordTrace]
  refine ⟨288083092547978623543583447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192055395031985749029055631 288083092547978623543583447)
  ·
    refine ⟨432124638821967935315375171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288083092547978623543583447 432124638821967935315375171)
    ·
      refine ⟨648186958232951902973062757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432124638821967935315375171 648186958232951902973062757)
      ·
        refine ⟨121535054668678481807449267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 648186958232951902973062757 121535054668678481807449267)
        ·
          refine ⟨182302582003017722711173901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121535054668678481807449267 182302582003017722711173901)
          ·
            refine ⟨68363468251131646016690213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182302582003017722711173901 68363468251131646016690213)
            ·
              refine ⟨12818150297087183628129415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68363468251131646016690213 12818150297087183628129415)
              ·
                refine ⟨19227225445630775442194123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12818150297087183628129415 19227225445630775442194123)
                ·
                  refine ⟨28840838168446163163291185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19227225445630775442194123 28840838168446163163291185)
                  ·
                    refine ⟨21630628626334622372468389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28840838168446163163291185 21630628626334622372468389)
                    ·
                      refine ⟨4055742867437741694837823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21630628626334622372468389 4055742867437741694837823)
                      ·
                        rfl

theorem cell23_7898531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 1, 1, 2, 4].length) (baseStart_7898531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7898531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7898531 prefixEnd_7898531 := by exact prefixLift 7898531
  have htrace : WordTrace (prefixWord ++ tailWord_7898531) baseStart_7898531 baseEnd_7898531 := by
    simpa [prefixWord, tailWord_7898531, baseEnd_7898531] using wordTrace_append hprefix tailTrace_7898531
  have hstable : (prefixWord ++ tailWord_7898531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7898531).length < 2 ^ (prefixWord ++ tailWord_7898531).sum := by decide
  have hdescent : baseEnd_7898531 < baseStart_7898531 := by decide
  rcases family_descends (prefixWord ++ tailWord_7898531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7898535 : List Nat := [1, 1, 6, 1, 1, 1, 3, 2, 3, 2, 2]
def baseStart_7898535 : Nat := 118140960795 + 7898535 * 2 ^ 59
def prefixEnd_7898535 : Nat := 4983230072969 + 3 ^ 40 * 7898535 * 2
def baseEnd_7898535 : Nat := 4055744921360359679187805

theorem tailTrace_7898535 : CollatzResearch.WordTrace tailWord_7898535 prefixEnd_7898535 4055744921360359679187805 := by
  unfold tailWord_7898535
  simp only [CollatzResearch.WordTrace]
  refine ⟨288083238439964132226729059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192055492293309421484486039 288083238439964132226729059)
  ·
    refine ⟨432124857659946198340093589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288083238439964132226729059 432124857659946198340093589)
    ·
      refine ⟨20255852702809978047191887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 432124857659946198340093589 20255852702809978047191887)
      ·
        refine ⟨30383779054214967070787831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20255852702809978047191887 30383779054214967070787831)
        ·
          refine ⟨45575668581322450606181747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30383779054214967070787831 45575668581322450606181747)
          ·
            refine ⟨68363502871983675909272621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45575668581322450606181747 68363502871983675909272621)
            ·
              refine ⟨25636313576993878465977233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68363502871983675909272621 25636313576993878465977233)
              ·
                refine ⟨19227235182745408849482925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25636313576993878465977233 19227235182745408849482925)
                ·
                  refine ⟨7210213193529528318556097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19227235182745408849482925 7210213193529528318556097)
                  ·
                    refine ⟨5407659895147146238917073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7210213193529528318556097 5407659895147146238917073)
                    ·
                      refine ⟨4055744921360359679187805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5407659895147146238917073 4055744921360359679187805)
                      ·
                        rfl

theorem cell23_7898535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 2, 3, 2, 2].length) (baseStart_7898535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7898535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7898535 prefixEnd_7898535 := by exact prefixLift 7898535
  have htrace : WordTrace (prefixWord ++ tailWord_7898535) baseStart_7898535 baseEnd_7898535 := by
    simpa [prefixWord, tailWord_7898535, baseEnd_7898535] using wordTrace_append hprefix tailTrace_7898535
  have hstable : (prefixWord ++ tailWord_7898535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7898535).length < 2 ^ (prefixWord ++ tailWord_7898535).sum := by decide
  have hdescent : baseEnd_7898535 < baseStart_7898535 := by decide
  rcases family_descends (prefixWord ++ tailWord_7898535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7898551 : List Nat := [1, 1, 3, 1, 3, 2, 1, 4, 1, 3, 3]
def baseStart_7898551 : Nat := 118140960795 + 7898551 * 2 ^ 59
def prefixEnd_7898551 : Nat := 4983230072969 + 3 ^ 40 * 7898551 * 2
def baseEnd_7898551 : Nat := 4055753137050831616587731

theorem tailTrace_7898551 : CollatzResearch.WordTrace tailWord_7898551 prefixEnd_7898551 4055753137050831616587731 := by
  unfold tailWord_7898551
  simp only [CollatzResearch.WordTrace]
  refine ⟨288083822007906166959311507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192055881338604111306207671 288083822007906166959311507)
  ·
    refine ⟨432125733011859250438967261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288083822007906166959311507 432125733011859250438967261)
    ·
      refine ⟨162047149879447218914612723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 432125733011859250438967261 162047149879447218914612723)
      ·
        refine ⟨243070724819170828371919085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162047149879447218914612723 243070724819170828371919085)
        ·
          refine ⟨91151521807189060639469657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 243070724819170828371919085 91151521807189060639469657)
          ·
            refine ⟨68363641355391795479602243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91151521807189060639469657 68363641355391795479602243)
            ·
              refine ⟨102545462033087693219403365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68363641355391795479602243 102545462033087693219403365)
              ·
                refine ⟨19227274131203942478638131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102545462033087693219403365 19227274131203942478638131)
                ·
                  refine ⟨28840911196805913717957197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19227274131203942478638131 28840911196805913717957197)
                  ·
                    refine ⟨10815341698802217644233949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28840911196805913717957197 10815341698802217644233949)
                    ·
                      refine ⟨4055753137050831616587731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10815341698802217644233949 4055753137050831616587731)
                      ·
                        rfl

theorem cell23_7898551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 4, 1, 3, 3].length) (baseStart_7898551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7898551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7898551 prefixEnd_7898551 := by exact prefixLift 7898551
  have htrace : WordTrace (prefixWord ++ tailWord_7898551) baseStart_7898551 baseEnd_7898551 := by
    simpa [prefixWord, tailWord_7898551, baseEnd_7898551] using wordTrace_append hprefix tailTrace_7898551
  have hstable : (prefixWord ++ tailWord_7898551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7898551).length < 2 ^ (prefixWord ++ tailWord_7898551).sum := by decide
  have hdescent : baseEnd_7898551 < baseStart_7898551 := by decide
  rcases family_descends (prefixWord ++ tailWord_7898551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7898568 : List Nat := [2, 1, 3, 1, 3, 1, 3, 1, 4, 1, 3]
def baseStart_7898568 : Nat := 118140960795 + 7898568 * 2 ^ 59
def prefixEnd_7898568 : Nat := 4983230072969 + 3 ^ 40 * 7898568 * 2
def baseEnd_7898568 : Nat := 4055761866221958050075153

theorem tailTrace_7898568 : CollatzResearch.WordTrace tailWord_7898568 prefixEnd_7898568 4055761866221958050075153 := by
  unfold tailWord_7898568
  simp only [CollatzResearch.WordTrace]
  refine ⟨144042221024422289431340179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192056294699229719241786905 144042221024422289431340179)
  ·
    refine ⟨216063331536633434147010269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144042221024422289431340179 216063331536633434147010269)
    ·
      refine ⟨81023749326237537805128851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216063331536633434147010269 81023749326237537805128851)
      ·
        refine ⟨121535623989356306707693277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81023749326237537805128851 121535623989356306707693277)
        ·
          refine ⟨45575858996008615015384979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121535623989356306707693277 45575858996008615015384979)
          ·
            refine ⟨68363788494012922523077469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45575858996008615015384979 68363788494012922523077469)
            ·
              refine ⟨25636420685254845946154051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68363788494012922523077469 25636420685254845946154051)
              ·
                refine ⟨38454631027882268919231077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25636420685254845946154051 38454631027882268919231077)
                ·
                  refine ⟨7210243317727925422355827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38454631027882268919231077 7210243317727925422355827)
                  ·
                    refine ⟨10815364976591888133533741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7210243317727925422355827 10815364976591888133533741)
                    ·
                      refine ⟨4055761866221958050075153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10815364976591888133533741 4055761866221958050075153)
                      ·
                        rfl

theorem cell23_7898568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 4, 1, 3].length) (baseStart_7898568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7898568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7898568 prefixEnd_7898568 := by exact prefixLift 7898568
  have htrace : WordTrace (prefixWord ++ tailWord_7898568) baseStart_7898568 baseEnd_7898568 := by
    simpa [prefixWord, tailWord_7898568, baseEnd_7898568] using wordTrace_append hprefix tailTrace_7898568
  have hstable : (prefixWord ++ tailWord_7898568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7898568).length < 2 ^ (prefixWord ++ tailWord_7898568).sum := by decide
  have hdescent : baseEnd_7898568 < baseStart_7898568 := by decide
  rcases family_descends (prefixWord ++ tailWord_7898568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7898595 : List Nat := [1, 1, 1, 6, 2, 1, 1, 4, 1, 3, 2]
def baseStart_7898595 : Nat := 118140960795 + 7898595 * 2 ^ 59
def prefixEnd_7898595 : Nat := 4983230072969 + 3 ^ 40 * 7898595 * 2
def baseEnd_7898595 : Nat := 4055775730199629444437529

theorem tailTrace_7898595 : CollatzResearch.WordTrace tailWord_7898595 prefixEnd_7898595 4055775730199629444437529 := by
  unfold tailWord_7898595
  simp only [CollatzResearch.WordTrace]
  refine ⟨288085426819746762473913239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192056951213164508315942159 288085426819746762473913239)
  ·
    refine ⟨432128140229620143710869859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288085426819746762473913239 432128140229620143710869859)
    ·
      refine ⟨648192210344430215566304789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432128140229620143710869859 648192210344430215566304789)
      ·
        refine ⟨30384009859895166354670537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 648192210344430215566304789 30384009859895166354670537)
        ·
          refine ⟨22788007394921374766002903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30384009859895166354670537 22788007394921374766002903)
          ·
            refine ⟨34182011092382062149004355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22788007394921374766002903 34182011092382062149004355)
            ·
              refine ⟨51273016638573093223506533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34182011092382062149004355 51273016638573093223506533)
              ·
                refine ⟨9613690619732454979407475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51273016638573093223506533 9613690619732454979407475)
                ·
                  refine ⟨14420535929598682469111213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9613690619732454979407475 14420535929598682469111213)
                  ·
                    refine ⟨5407700973599505925916705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14420535929598682469111213 5407700973599505925916705)
                    ·
                      refine ⟨4055775730199629444437529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5407700973599505925916705 4055775730199629444437529)
                      ·
                        rfl

theorem cell23_7898595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 4, 1, 3, 2].length) (baseStart_7898595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7898595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7898595 prefixEnd_7898595 := by exact prefixLift 7898595
  have htrace : WordTrace (prefixWord ++ tailWord_7898595) baseStart_7898595 baseEnd_7898595 := by
    simpa [prefixWord, tailWord_7898595, baseEnd_7898595] using wordTrace_append hprefix tailTrace_7898595
  have hstable : (prefixWord ++ tailWord_7898595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7898595).length < 2 ^ (prefixWord ++ tailWord_7898595).sum := by decide
  have hdescent : baseEnd_7898595 < baseStart_7898595 := by decide
  rcases family_descends (prefixWord ++ tailWord_7898595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7898641 : List Nat := [1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 3]
def baseStart_7898641 : Nat := 118140960795 + 7898641 * 2 ^ 59
def prefixEnd_7898641 : Nat := 4983230072969 + 3 ^ 40 * 7898641 * 2
def baseEnd_7898641 : Nat := 4055799350309736264462317

theorem tailTrace_7898641 : CollatzResearch.WordTrace tailWord_7898641 prefixEnd_7898641 4055799350309736264462317 := by
  unfold tailWord_7898641
  simp only [CollatzResearch.WordTrace]
  refine ⟨288087104577580112330087777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192058069718386741553391851 288087104577580112330087777)
  ·
    refine ⟨216065328433185084247565833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288087104577580112330087777 216065328433185084247565833)
    ·
      refine ⟨162048996324888813185674375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216065328433185084247565833 162048996324888813185674375)
      ·
        refine ⟨243073494487333219778511563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162048996324888813185674375 243073494487333219778511563)
        ·
          refine ⟨364610241730999829667767345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243073494487333219778511563 364610241730999829667767345)
          ·
            refine ⟨273457681298249872250825509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 364610241730999829667767345 273457681298249872250825509)
            ·
              refine ⟨51273315243421851047029783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 273457681298249872250825509 51273315243421851047029783)
              ·
                refine ⟨76909972865132776570544675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51273315243421851047029783 76909972865132776570544675)
                ·
                  refine ⟨115364959297699164855817013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76909972865132776570544675 115364959297699164855817013)
                  ·
                    refine ⟨10815464934159296705232845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 115364959297699164855817013 10815464934159296705232845)
                    ·
                      refine ⟨4055799350309736264462317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10815464934159296705232845 4055799350309736264462317)
                      ·
                        rfl

theorem cell23_7898641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 3].length) (baseStart_7898641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7898641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7898641 prefixEnd_7898641 := by exact prefixLift 7898641
  have htrace : WordTrace (prefixWord ++ tailWord_7898641) baseStart_7898641 baseEnd_7898641 := by
    simpa [prefixWord, tailWord_7898641, baseEnd_7898641] using wordTrace_append hprefix tailTrace_7898641
  have hstable : (prefixWord ++ tailWord_7898641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7898641).length < 2 ^ (prefixWord ++ tailWord_7898641).sum := by decide
  have hdescent : baseEnd_7898641 < baseStart_7898641 := by decide
  rcases family_descends (prefixWord ++ tailWord_7898641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7898721 : List Nat := [1, 2, 3, 1, 1, 3, 2, 2, 8]
def baseStart_7898721 : Nat := 118140960795 + 7898721 * 2 ^ 59
def prefixEnd_7898721 : Nat := 4983230072969 + 3 ^ 40 * 7898721 * 2
def baseEnd_7898721 : Nat := 450648936529121772384661

theorem tailTrace_7898721 : CollatzResearch.WordTrace tailWord_7898721 prefixEnd_7898721 450648936529121772384661 := by
  unfold tailWord_7898721
  simp only [CollatzResearch.WordTrace]
  refine ⟨288090022417290285993000017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192060014944860190662000011 288090022417290285993000017)
  ·
    refine ⟨216067516812967714494750013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288090022417290285993000017 216067516812967714494750013)
    ·
      refine ⟨81025318804862892935531255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216067516812967714494750013 81025318804862892935531255)
      ·
        refine ⟨121537978207294339403296883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81025318804862892935531255 121537978207294339403296883)
        ·
          refine ⟨182306967310941509104945325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121537978207294339403296883 182306967310941509104945325)
          ·
            refine ⟨68365112741603065914354497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182306967310941509104945325 68365112741603065914354497)
            ·
              refine ⟨51273834556202299435765873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68365112741603065914354497 51273834556202299435765873)
              ·
                refine ⟨38455375917151724576824405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51273834556202299435765873 38455375917151724576824405)
                ·
                  refine ⟨450648936529121772384661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38455375917151724576824405 450648936529121772384661)
                  ·
                    rfl

theorem cell23_7898721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 8].length) (baseStart_7898721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7898721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7898721 prefixEnd_7898721 := by exact prefixLift 7898721
  have htrace : WordTrace (prefixWord ++ tailWord_7898721) baseStart_7898721 baseEnd_7898721 := by
    simpa [prefixWord, tailWord_7898721, baseEnd_7898721] using wordTrace_append hprefix tailTrace_7898721
  have hstable : (prefixWord ++ tailWord_7898721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7898721).length < 2 ^ (prefixWord ++ tailWord_7898721).sum := by decide
  have hdescent : baseEnd_7898721 < baseStart_7898721 := by decide
  rcases family_descends (prefixWord ++ tailWord_7898721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7898728 : List Nat := [2, 1, 4, 3, 1, 1, 1, 1, 2, 1, 6]
def baseStart_7898728 : Nat := 118140960795 + 7898728 * 2 ^ 59
def prefixEnd_7898728 : Nat := 4983230072969 + 3 ^ 40 * 7898728 * 2
def baseEnd_7898728 : Nat := 4055844023126677424074417

theorem tailTrace_7898728 : CollatzResearch.WordTrace tailWord_7898728 prefixEnd_7898728 4055844023126677424074417 := by
  unfold tailWord_7898728
  simp only [CollatzResearch.WordTrace]
  refine ⟨144045138864132463094252419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192060185152176617459003225 144045138864132463094252419)
  ·
    refine ⟨216067708296198694641378629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144045138864132463094252419 216067708296198694641378629)
    ·
      refine ⟨40512695305537255245258493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216067708296198694641378629 40512695305537255245258493)
      ·
        refine ⟨15192260739576470716971935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40512695305537255245258493 15192260739576470716971935)
        ·
          refine ⟨22788391109364706075457903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15192260739576470716971935 22788391109364706075457903)
          ·
            refine ⟨34182586664047059113186855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22788391109364706075457903 34182586664047059113186855)
            ·
              refine ⟨51273879996070588669780283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34182586664047059113186855 51273879996070588669780283)
              ·
                refine ⟨76910819994105883004670425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51273879996070588669780283 76910819994105883004670425)
                ·
                  refine ⟨57683114995579412253502819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76910819994105883004670425 57683114995579412253502819)
                  ·
                    refine ⟨86524672493369118380254229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57683114995579412253502819 86524672493369118380254229)
                    ·
                      refine ⟨4055844023126677424074417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86524672493369118380254229 4055844023126677424074417)
                      ·
                        rfl

theorem cell23_7898728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_7898728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7898728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7898728 prefixEnd_7898728 := by exact prefixLift 7898728
  have htrace : WordTrace (prefixWord ++ tailWord_7898728) baseStart_7898728 baseEnd_7898728 := by
    simpa [prefixWord, tailWord_7898728, baseEnd_7898728] using wordTrace_append hprefix tailTrace_7898728
  have hstable : (prefixWord ++ tailWord_7898728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7898728).length < 2 ^ (prefixWord ++ tailWord_7898728).sum := by decide
  have hdescent : baseEnd_7898728 < baseStart_7898728 := by decide
  rcases family_descends (prefixWord ++ tailWord_7898728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7898738 : List Nat := [3, 2, 1, 2, 3, 2, 1, 1, 8]
def baseStart_7898738 : Nat := 118140960795 + 7898738 * 2 ^ 59
def prefixEnd_7898738 : Nat := 4983230072969 + 3 ^ 40 * 7898738 * 2
def baseEnd_7898738 : Nat := 450649906437024709438819

theorem tailTrace_7898738 : CollatzResearch.WordTrace tailWord_7898738 prefixEnd_7898738 450649906437024709438819 := by
  unfold tailWord_7898738
  simp only [CollatzResearch.WordTrace]
  refine ⟨72022660614557174474092217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192060428305485798597579245 72022660614557174474092217)
  ·
    refine ⟨54016995460917880855569163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72022660614557174474092217 54016995460917880855569163)
    ·
      refine ⟨81025493191376821283353745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54016995460917880855569163 81025493191376821283353745)
      ·
        refine ⟨60769119893532615962515309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81025493191376821283353745 60769119893532615962515309)
        ·
          refine ⟨22788419960074730985943241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60769119893532615962515309 22788419960074730985943241)
          ·
            refine ⟨17091314970056048239457431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22788419960074730985943241 17091314970056048239457431)
            ·
              refine ⟨25636972455084072359186147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17091314970056048239457431 25636972455084072359186147)
              ·
                refine ⟨38455458682626108538779221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25636972455084072359186147 38455458682626108538779221)
                ·
                  refine ⟨450649906437024709438819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38455458682626108538779221 450649906437024709438819)
                  ·
                    rfl

theorem cell23_7898738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 8].length) (baseStart_7898738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7898738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7898738 prefixEnd_7898738 := by exact prefixLift 7898738
  have htrace : WordTrace (prefixWord ++ tailWord_7898738) baseStart_7898738 baseEnd_7898738 := by
    simpa [prefixWord, tailWord_7898738, baseEnd_7898738] using wordTrace_append hprefix tailTrace_7898738
  have hstable : (prefixWord ++ tailWord_7898738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7898738).length < 2 ^ (prefixWord ++ tailWord_7898738).sum := by decide
  have hdescent : baseEnd_7898738 < baseStart_7898738 := by decide
  rcases family_descends (prefixWord ++ tailWord_7898738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7898742 : List Nat := [5, 1, 1, 2, 2, 2, 2, 1, 3, 4]
def baseStart_7898742 : Nat := 118140960795 + 7898742 * 2 ^ 59
def prefixEnd_7898742 : Nat := 4983230072969 + 3 ^ 40 * 7898742 * 2
def baseEnd_7898742 : Nat := 1351950403951946789766451

theorem tailTrace_7898742 : CollatzResearch.WordTrace tailWord_7898742 prefixEnd_7898742 1351950403951946789766451 := by
  unfold tailWord_7898742
  simp only [CollatzResearch.WordTrace]
  refine ⟨18005674271888387911219655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 192060525566809471053009653 18005674271888387911219655)
  ·
    refine ⟨27008511407832581866829483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18005674271888387911219655 27008511407832581866829483)
    ·
      refine ⟨40512767111748872800244225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27008511407832581866829483 40512767111748872800244225)
      ·
        refine ⟨30384575333811654600183169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40512767111748872800244225 30384575333811654600183169)
        ·
          refine ⟨22788431500358740950137377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30384575333811654600183169 22788431500358740950137377)
          ·
            refine ⟨17091323625269055712603033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22788431500358740950137377 17091323625269055712603033)
            ·
              refine ⟨12818492718951791784452275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17091323625269055712603033 12818492718951791784452275)
              ·
                refine ⟨19227739078427687676678413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12818492718951791784452275 19227739078427687676678413)
                ·
                  refine ⟨7210402154410382878754405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19227739078427687676678413 7210402154410382878754405)
                  ·
                    refine ⟨1351950403951946789766451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7210402154410382878754405 1351950403951946789766451)
                    ·
                      rfl

theorem cell23_7898742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 1, 3, 4].length) (baseStart_7898742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7898742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7898742 prefixEnd_7898742 := by exact prefixLift 7898742
  have htrace : WordTrace (prefixWord ++ tailWord_7898742) baseStart_7898742 baseEnd_7898742 := by
    simpa [prefixWord, tailWord_7898742, baseEnd_7898742] using wordTrace_append hprefix tailTrace_7898742
  have hstable : (prefixWord ++ tailWord_7898742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7898742).length < 2 ^ (prefixWord ++ tailWord_7898742).sum := by decide
  have hdescent : baseEnd_7898742 < baseStart_7898742 := by decide
  rcases family_descends (prefixWord ++ tailWord_7898742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7898761 : List Nat := [1, 2, 1, 1, 4, 1, 2, 1, 2, 1, 7]
def baseStart_7898761 : Nat := 118140960795 + 7898761 * 2 ^ 59
def prefixEnd_7898761 : Nat := 4983230072969 + 3 ^ 40 * 7898761 * 2
def baseEnd_7898761 : Nat := 4055860967988275794961765

theorem tailTrace_7898761 : CollatzResearch.WordTrace tailWord_7898761 prefixEnd_7898761 4055860967988275794961765 := by
  unfold tailWord_7898761
  simp only [CollatzResearch.WordTrace]
  refine ⟨288091481337145372824456137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192060987558096915216304091 288091481337145372824456137)
  ·
    refine ⟨216068611002859029618342103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288091481337145372824456137 216068611002859029618342103)
    ·
      refine ⟨324102916504288544427513155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216068611002859029618342103 324102916504288544427513155)
      ·
        refine ⟨486154374756432816641269733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324102916504288544427513155 486154374756432816641269733)
        ·
          refine ⟨91153945266831153120238075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 486154374756432816641269733 91153945266831153120238075)
          ·
            refine ⟨136730917900246729680357113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91153945266831153120238075 136730917900246729680357113)
            ·
              refine ⟨102548188425185047260267835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136730917900246729680357113 102548188425185047260267835)
              ·
                refine ⟨153822282637777570890401753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102548188425185047260267835 153822282637777570890401753)
                ·
                  refine ⟨115366711978333178167801315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153822282637777570890401753 115366711978333178167801315)
                  ·
                    refine ⟨173050067967499767251701973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 115366711978333178167801315 173050067967499767251701973)
                    ·
                      refine ⟨4055860967988275794961765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 173050067967499767251701973 4055860967988275794961765)
                      ·
                        rfl

theorem cell23_7898761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 1, 7].length) (baseStart_7898761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7898761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7898761 prefixEnd_7898761 := by exact prefixLift 7898761
  have htrace : WordTrace (prefixWord ++ tailWord_7898761) baseStart_7898761 baseEnd_7898761 := by
    simpa [prefixWord, tailWord_7898761, baseEnd_7898761] using wordTrace_append hprefix tailTrace_7898761
  have hstable : (prefixWord ++ tailWord_7898761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7898761).length < 2 ^ (prefixWord ++ tailWord_7898761).sum := by decide
  have hdescent : baseEnd_7898761 < baseStart_7898761 := by decide
  rcases family_descends (prefixWord ++ tailWord_7898761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7898775 : List Nat := [1, 1, 3, 3, 2, 2, 2, 1, 1, 5, 2]
def baseStart_7898775 : Nat := 118140960795 + 7898775 * 2 ^ 59
def prefixEnd_7898775 : Nat := 4983230072969 + 3 ^ 40 * 7898775 * 2
def baseEnd_7898775 : Nat := 4055868156717438740186701

theorem tailTrace_7898775 : CollatzResearch.WordTrace tailWord_7898775 prefixEnd_7898775 4055868156717438740186701 := by
  unfold tailWord_7898775
  simp only [CollatzResearch.WordTrace]
  refine ⟨288091991959094653215465779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192061327972729768810310519 288091991959094653215465779)
  ·
    refine ⟨432137987938641979823198669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288091991959094653215465779 432137987938641979823198669)
    ·
      refine ⟨162051745476990742433699501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 432137987938641979823198669 162051745476990742433699501)
      ·
        refine ⟨60769404553871528412637313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162051745476990742433699501 60769404553871528412637313)
        ·
          refine ⟨45577053415403646309477985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60769404553871528412637313 45577053415403646309477985)
          ·
            refine ⟨34182790061552734732108489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45577053415403646309477985 34182790061552734732108489)
            ·
              refine ⟨25637092546164551049081367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34182790061552734732108489 25637092546164551049081367)
              ·
                refine ⟨38455638819246826573622051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25637092546164551049081367 38455638819246826573622051)
                ·
                  refine ⟨57683458228870239860433077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38455638819246826573622051 57683458228870239860433077)
                  ·
                    refine ⟨5407824208956584986915601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57683458228870239860433077 5407824208956584986915601)
                    ·
                      refine ⟨4055868156717438740186701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5407824208956584986915601 4055868156717438740186701)
                      ·
                        rfl

theorem cell23_7898775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 5, 2].length) (baseStart_7898775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7898775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7898775 prefixEnd_7898775 := by exact prefixLift 7898775
  have htrace : WordTrace (prefixWord ++ tailWord_7898775) baseStart_7898775 baseEnd_7898775 := by
    simpa [prefixWord, tailWord_7898775, baseEnd_7898775] using wordTrace_append hprefix tailTrace_7898775
  have hstable : (prefixWord ++ tailWord_7898775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7898775).length < 2 ^ (prefixWord ++ tailWord_7898775).sum := by decide
  have hdescent : baseEnd_7898775 < baseStart_7898775 := by decide
  rcases family_descends (prefixWord ++ tailWord_7898775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7898785 : List Nat := [1, 2, 3, 3, 2, 1, 2, 3, 1, 5]
def baseStart_7898785 : Nat := 118140960795 + 7898785 * 2 ^ 59
def prefixEnd_7898785 : Nat := 4983230072969 + 3 ^ 40 * 7898785 * 2
def baseEnd_7898785 : Nat := 1351957763841327900353885

theorem tailTrace_7898785 : CollatzResearch.WordTrace tailWord_7898785 prefixEnd_7898785 1351957763841327900353885 := by
  unfold tailWord_7898785
  simp only [CollatzResearch.WordTrace]
  refine ⟨288092356689058424923329809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192061571126038949948886539 288092356689058424923329809)
  ·
    refine ⟨216069267516793818692497357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288092356689058424923329809 216069267516793818692497357)
    ·
      refine ⟨81025975318797682009686509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216069267516793818692497357 81025975318797682009686509)
      ·
        refine ⟨30384740744549130753632441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81025975318797682009686509 30384740744549130753632441)
        ·
          refine ⟨22788555558411848065224331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30384740744549130753632441 22788555558411848065224331)
          ·
            refine ⟨34182833337617772097836497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22788555558411848065224331 34182833337617772097836497)
            ·
              refine ⟨25637125003213329073377373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34182833337617772097836497 25637125003213329073377373)
              ·
                refine ⟨9613921876204998402516515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25637125003213329073377373 9613921876204998402516515)
                ·
                  refine ⟨14420882814307497603774773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9613921876204998402516515 14420882814307497603774773)
                  ·
                    refine ⟨1351957763841327900353885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14420882814307497603774773 1351957763841327900353885)
                    ·
                      rfl

theorem cell23_7898785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 3, 1, 5].length) (baseStart_7898785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7898785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7898785 prefixEnd_7898785 := by exact prefixLift 7898785
  have htrace : WordTrace (prefixWord ++ tailWord_7898785) baseStart_7898785 baseEnd_7898785 := by
    simpa [prefixWord, tailWord_7898785, baseEnd_7898785] using wordTrace_append hprefix tailTrace_7898785
  have hstable : (prefixWord ++ tailWord_7898785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7898785).length < 2 ^ (prefixWord ++ tailWord_7898785).sum := by decide
  have hdescent : baseEnd_7898785 < baseStart_7898785 := by decide
  rcases family_descends (prefixWord ++ tailWord_7898785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7898799 : List Nat := [1, 1, 2, 1, 2, 4, 5, 2, 1, 1, 3]
def baseStart_7898799 : Nat := 118140960795 + 7898799 * 2 ^ 59
def prefixEnd_7898799 : Nat := 4983230072969 + 3 ^ 40 * 7898799 * 2
def baseEnd_7898799 : Nat := 4055880480253146646286591

theorem tailTrace_7898799 : CollatzResearch.WordTrace tailWord_7898799 prefixEnd_7898799 4055880480253146646286591 := by
  unfold tailWord_7898799
  simp only [CollatzResearch.WordTrace]
  refine ⟨288092867311007705314339451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192061911540671803542892967 288092867311007705314339451)
  ·
    refine ⟨432139300966511557971509177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288092867311007705314339451 432139300966511557971509177)
    ·
      refine ⟨324104475724883668478631883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432139300966511557971509177 324104475724883668478631883)
      ·
        refine ⟨486156713587325502717947825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324104475724883668478631883 486156713587325502717947825)
        ·
          refine ⟨364617535190494127038460869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 486156713587325502717947825 364617535190494127038460869)
          ·
            refine ⟨68365787848217648819711413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 364617535190494127038460869 68365787848217648819711413)
            ·
              refine ⟨6409292610770404576847945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68365787848217648819711413 6409292610770404576847945)
              ·
                refine ⟨4806969458077803432635959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6409292610770404576847945 4806969458077803432635959)
                ·
                  refine ⟨7210454187116705148953939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4806969458077803432635959 7210454187116705148953939)
                  ·
                    refine ⟨10815681280675057723430909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7210454187116705148953939 10815681280675057723430909)
                    ·
                      refine ⟨4055880480253146646286591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10815681280675057723430909 4055880480253146646286591)
                      ·
                        rfl

theorem cell23_7898799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 5, 2, 1, 1, 3].length) (baseStart_7898799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7898799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7898799 prefixEnd_7898799 := by exact prefixLift 7898799
  have htrace : WordTrace (prefixWord ++ tailWord_7898799) baseStart_7898799 baseEnd_7898799 := by
    simpa [prefixWord, tailWord_7898799, baseEnd_7898799] using wordTrace_append hprefix tailTrace_7898799
  have hstable : (prefixWord ++ tailWord_7898799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7898799).length < 2 ^ (prefixWord ++ tailWord_7898799).sum := by decide
  have hdescent : baseEnd_7898799 < baseStart_7898799 := by decide
  rcases family_descends (prefixWord ++ tailWord_7898799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7898815 : List Nat := [1, 1, 2, 2, 2, 3, 3, 3, 2, 4]
def baseStart_7898815 : Nat := 118140960795 + 7898815 * 2 ^ 59
def prefixEnd_7898815 : Nat := 4983230072969 + 3 ^ 40 * 7898815 * 2
def baseEnd_7898815 : Nat := 1351962898647872861228839

theorem tailTrace_7898815 : CollatzResearch.WordTrace tailWord_7898815 prefixEnd_7898815 1351962898647872861228839 := by
  unfold tailWord_7898815
  simp only [CollatzResearch.WordTrace]
  refine ⟨288093450878949740046921899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192062300585966493364614599 288093450878949740046921899)
  ·
    refine ⟨432140176318424610070382849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288093450878949740046921899 432140176318424610070382849)
    ·
      refine ⟨324105132238818457552787137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432140176318424610070382849 324105132238818457552787137)
      ·
        refine ⟨243078849179113843164590353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324105132238818457552787137 243078849179113843164590353)
        ·
          refine ⟨182309136884335382373442765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243078849179113843164590353 182309136884335382373442765)
          ·
            refine ⟨68365926331625768390041037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182309136884335382373442765 68365926331625768390041037)
            ·
              refine ⟨25637222374359663146265389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68365926331625768390041037 25637222374359663146265389)
              ·
                refine ⟨9613958390384873679849521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25637222374359663146265389 9613958390384873679849521)
                ·
                  refine ⟨7210468792788655259887141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9613958390384873679849521 7210468792788655259887141)
                  ·
                    refine ⟨1351962898647872861228839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7210468792788655259887141 1351962898647872861228839)
                    ·
                      rfl

theorem cell23_7898815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 2, 4].length) (baseStart_7898815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7898815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7898815 prefixEnd_7898815 := by exact prefixLift 7898815
  have htrace : WordTrace (prefixWord ++ tailWord_7898815) baseStart_7898815 baseEnd_7898815 := by
    simpa [prefixWord, tailWord_7898815, baseEnd_7898815] using wordTrace_append hprefix tailTrace_7898815
  have hstable : (prefixWord ++ tailWord_7898815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7898815).length < 2 ^ (prefixWord ++ tailWord_7898815).sum := by decide
  have hdescent : baseEnd_7898815 < baseStart_7898815 := by decide
  rcases family_descends (prefixWord ++ tailWord_7898815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7898839 : List Nat := [1, 1, 3, 2, 1, 3, 2, 5, 1, 2, 2]
def baseStart_7898839 : Nat := 118140960795 + 7898839 * 2 ^ 59
def prefixEnd_7898839 : Nat := 4983230072969 + 3 ^ 40 * 7898839 * 2
def baseEnd_7898839 : Nat := 4055901019479326489786407

theorem tailTrace_7898839 : CollatzResearch.WordTrace tailWord_7898839 prefixEnd_7898839 4055901019479326489786407 := by
  unfold tailWord_7898839
  simp only [CollatzResearch.WordTrace]
  refine ⟨288094326230862792145795571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192062884153908528097197047 288094326230862792145795571)
  ·
    refine ⟨432141489346294188218693357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288094326230862792145795571 432141489346294188218693357)
    ·
      refine ⟨162053058504860320582010009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 432141489346294188218693357 162053058504860320582010009)
      ·
        refine ⟨121539793878645240436507507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162053058504860320582010009 121539793878645240436507507)
        ·
          refine ⟨182309690817967860654761261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121539793878645240436507507 182309690817967860654761261)
          ·
            refine ⟨68366134056737947745535473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182309690817967860654761261 68366134056737947745535473)
            ·
              refine ⟨51274600542553460809151605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68366134056737947745535473 51274600542553460809151605)
              ·
                refine ⟨4806993800864386950857963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51274600542553460809151605 4806993800864386950857963)
                ·
                  refine ⟨7210490701296580426286945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4806993800864386950857963 7210490701296580426286945)
                  ·
                    refine ⟨5407868025972435319715209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7210490701296580426286945 5407868025972435319715209)
                    ·
                      refine ⟨4055901019479326489786407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5407868025972435319715209 4055901019479326489786407)
                      ·
                        rfl

theorem cell23_7898839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 5, 1, 2, 2].length) (baseStart_7898839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7898839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7898839 prefixEnd_7898839 := by exact prefixLift 7898839
  have htrace : WordTrace (prefixWord ++ tailWord_7898839) baseStart_7898839 baseEnd_7898839 := by
    simpa [prefixWord, tailWord_7898839, baseEnd_7898839] using wordTrace_append hprefix tailTrace_7898839
  have hstable : (prefixWord ++ tailWord_7898839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7898839).length < 2 ^ (prefixWord ++ tailWord_7898839).sum := by decide
  have hdescent : baseEnd_7898839 < baseStart_7898839 := by decide
  rcases family_descends (prefixWord ++ tailWord_7898839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7898845 : List Nat := [1, 4, 3, 3, 1, 11]
def baseStart_7898845 : Nat := 118140960795 + 7898845 * 2 ^ 59
def prefixEnd_7898845 : Nat := 4983230072969 + 3 ^ 40 * 7898845 * 2
def baseEnd_7898845 : Nat := 16690963375980466939553

theorem tailTrace_7898845 : CollatzResearch.WordTrace tailWord_7898845 prefixEnd_7898845 16690963375980466939553 := by
  unfold tailWord_7898845
  simp only [CollatzResearch.WordTrace]
  refine ⟨288094545068841055170513989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192063030045894036780342659 288094545068841055170513989)
  ·
    refine ⟨54017727200407697844471373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 288094545068841055170513989 54017727200407697844471373)
    ·
      refine ⟨20256647700152886691676765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54017727200407697844471373 20256647700152886691676765)
      ·
        refine ⟨7596242887557332509378787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20256647700152886691676765 7596242887557332509378787)
        ·
          refine ⟨11394364331335998764068181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7596242887557332509378787 11394364331335998764068181)
          ·
            refine ⟨16690963375980466939553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 11394364331335998764068181 16690963375980466939553)
            ·
              rfl

theorem cell23_7898845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 11].length) (baseStart_7898845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7898845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7898845 prefixEnd_7898845 := by exact prefixLift 7898845
  have htrace : WordTrace (prefixWord ++ tailWord_7898845) baseStart_7898845 baseEnd_7898845 := by
    simpa [prefixWord, tailWord_7898845, baseEnd_7898845] using wordTrace_append hprefix tailTrace_7898845
  have hstable : (prefixWord ++ tailWord_7898845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7898845).length < 2 ^ (prefixWord ++ tailWord_7898845).sum := by decide
  have hdescent : baseEnd_7898845 < baseStart_7898845 := by decide
  rcases family_descends (prefixWord ++ tailWord_7898845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7898856 : List Nat := [2, 1, 4, 1, 3, 2, 1, 4, 1, 2, 2]
def baseStart_7898856 : Nat := 118140960795 + 7898856 * 2 ^ 59
def prefixEnd_7898856 : Nat := 4983230072969 + 3 ^ 40 * 7898856 * 2
def baseEnd_7898856 : Nat := 4055909748650452923273829

theorem tailTrace_7898856 : CollatzResearch.WordTrace tailWord_7898856 prefixEnd_7898856 4055909748650452923273829 := by
  unfold tailWord_7898856
  simp only [CollatzResearch.WordTrace]
  refine ⟨144047473135900602024582211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192063297514534136032776281 144047473135900602024582211)
  ·
    refine ⟨216071209703850903036873317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144047473135900602024582211 216071209703850903036873317)
    ·
      refine ⟨40513351819472044319413747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216071209703850903036873317 40513351819472044319413747)
      ·
        refine ⟨60770027729208066479120621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40513351819472044319413747 60770027729208066479120621)
        ·
          refine ⟨22788760398453024929670233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60770027729208066479120621 22788760398453024929670233)
          ·
            refine ⟨17091570298839768697252675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22788760398453024929670233 17091570298839768697252675)
            ·
              refine ⟨25637355448259653045879013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17091570298839768697252675 25637355448259653045879013)
              ·
                refine ⟨4807004146548684946102315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25637355448259653045879013 4807004146548684946102315)
                ·
                  refine ⟨7210506219823027419153473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4807004146548684946102315 7210506219823027419153473)
                  ·
                    refine ⟨5407879664867270564365105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7210506219823027419153473 5407879664867270564365105)
                    ·
                      refine ⟨4055909748650452923273829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5407879664867270564365105 4055909748650452923273829)
                      ·
                        rfl

theorem cell23_7898856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 4, 1, 2, 2].length) (baseStart_7898856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7898856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7898856 prefixEnd_7898856 := by exact prefixLift 7898856
  have htrace : WordTrace (prefixWord ++ tailWord_7898856) baseStart_7898856 baseEnd_7898856 := by
    simpa [prefixWord, tailWord_7898856, baseEnd_7898856] using wordTrace_append hprefix tailTrace_7898856
  have hstable : (prefixWord ++ tailWord_7898856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7898856).length < 2 ^ (prefixWord ++ tailWord_7898856).sum := by decide
  have hdescent : baseEnd_7898856 < baseStart_7898856 := by decide
  rcases family_descends (prefixWord ++ tailWord_7898856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7898858 : List Nat := [3, 1, 3, 1, 1, 1, 3, 1, 2, 7]
def baseStart_7898858 : Nat := 118140960795 + 7898858 * 2 ^ 59
def prefixEnd_7898858 : Nat := 4983230072969 + 3 ^ 40 * 7898858 * 2
def baseEnd_7898858 : Nat := 1351970258537253971816273

theorem tailTrace_7898858 : CollatzResearch.WordTrace tailWord_7898858 prefixEnd_7898858 1351970258537253971816273 := by
  unfold tailWord_7898858
  simp only [CollatzResearch.WordTrace]
  refine ⟨72023754804448489597684307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192063346145195972260491485 72023754804448489597684307)
  ·
    refine ⟨108035632206672734396526461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72023754804448489597684307 108035632206672734396526461)
    ·
      refine ⟨40513362077502275398697423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108035632206672734396526461 40513362077502275398697423)
      ·
        refine ⟨60770043116253413098046135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40513362077502275398697423 60770043116253413098046135)
        ·
          refine ⟨91155064674380119647069203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60770043116253413098046135 91155064674380119647069203)
          ·
            refine ⟨136732597011570179470603805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91155064674380119647069203 136732597011570179470603805)
            ·
              refine ⟨51274723879338817301476427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136732597011570179470603805 51274723879338817301476427)
              ·
                refine ⟨76912085819008225952214641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51274723879338817301476427 76912085819008225952214641)
                ·
                  refine ⟨57684064364256169464160981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76912085819008225952214641 57684064364256169464160981)
                  ·
                    refine ⟨1351970258537253971816273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57684064364256169464160981 1351970258537253971816273)
                    ·
                      rfl

theorem cell23_7898858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_7898858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7898858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7898858 prefixEnd_7898858 := by exact prefixLift 7898858
  have htrace : WordTrace (prefixWord ++ tailWord_7898858) baseStart_7898858 baseEnd_7898858 := by
    simpa [prefixWord, tailWord_7898858, baseEnd_7898858] using wordTrace_append hprefix tailTrace_7898858
  have hstable : (prefixWord ++ tailWord_7898858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7898858).length < 2 ^ (prefixWord ++ tailWord_7898858).sum := by decide
  have hdescent : baseEnd_7898858 < baseStart_7898858 := by decide
  rcases family_descends (prefixWord ++ tailWord_7898858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7898888 : List Nat := [2, 1, 3, 2, 2, 1, 1, 2, 1, 8]
def baseStart_7898888 : Nat := 118140960795 + 7898888 * 2 ^ 59
def prefixEnd_7898888 : Nat := 4983230072969 + 3 ^ 40 * 7898888 * 2
def baseEnd_7898888 : Nat := 1351975393343798932691227

theorem tailTrace_7898888 : CollatzResearch.WordTrace tailWord_7898888 prefixEnd_7898888 1351975393343798932691227 := by
  unfold tailWord_7898888
  simp only [CollatzResearch.WordTrace]
  refine ⟨144048056703842636757164659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192064075605123515676219545 144048056703842636757164659)
  ·
    refine ⟨216072085055763955135746989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144048056703842636757164659 216072085055763955135746989)
    ·
      refine ⟨81027031895911483175905121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216072085055763955135746989 81027031895911483175905121)
      ·
        refine ⟨60770273921933612381928841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81027031895911483175905121 60770273921933612381928841)
        ·
          refine ⟨45577705441450209286446631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60770273921933612381928841 45577705441450209286446631)
          ·
            refine ⟨68366558162175313929669947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45577705441450209286446631 68366558162175313929669947)
            ·
              refine ⟨102549837243262970894504921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68366558162175313929669947 102549837243262970894504921)
              ·
                refine ⟨76912377932447228170878691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102549837243262970894504921 76912377932447228170878691)
                ·
                  refine ⟨115368566898670842256318037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76912377932447228170878691 115368566898670842256318037)
                  ·
                    refine ⟨1351975393343798932691227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 115368566898670842256318037 1351975393343798932691227)
                    ·
                      rfl

theorem cell23_7898888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 1, 8].length) (baseStart_7898888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7898888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7898888 prefixEnd_7898888 := by exact prefixLift 7898888
  have htrace : WordTrace (prefixWord ++ tailWord_7898888) baseStart_7898888 baseEnd_7898888 := by
    simpa [prefixWord, tailWord_7898888, baseEnd_7898888] using wordTrace_append hprefix tailTrace_7898888
  have hstable : (prefixWord ++ tailWord_7898888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7898888).length < 2 ^ (prefixWord ++ tailWord_7898888).sum := by decide
  have hdescent : baseEnd_7898888 < baseStart_7898888 := by decide
  rcases family_descends (prefixWord ++ tailWord_7898888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7898895 : List Nat := [1, 1, 2, 1, 1, 1, 4, 3, 3, 4, 2]
def baseStart_7898895 : Nat := 118140960795 + 7898895 * 2 ^ 59
def prefixEnd_7898895 : Nat := 4983230072969 + 3 ^ 40 * 7898895 * 2
def baseEnd_7898895 : Nat := 4055929774395978270686149

theorem tailTrace_7898895 : CollatzResearch.WordTrace tailWord_7898895 prefixEnd_7898895 4055929774395978270686149 := by
  unfold tailWord_7898895
  simp only [CollatzResearch.WordTrace]
  refine ⟨288096368718659913709834139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192064245812439942473222759 288096368718659913709834139)
  ·
    refine ⟨432144553077989870564751209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288096368718659913709834139 432144553077989870564751209)
    ·
      refine ⟨324108414808492402923563407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432144553077989870564751209 324108414808492402923563407)
      ·
        refine ⟨486162622212738604385345111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324108414808492402923563407 486162622212738604385345111)
        ·
          refine ⟨729243933319107906578017667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486162622212738604385345111 729243933319107906578017667)
          ·
            refine ⟨1093865899978661859867026501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 729243933319107906578017667 1093865899978661859867026501)
            ·
              refine ⟨205099856245999098725067469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1093865899978661859867026501 205099856245999098725067469)
              ·
                refine ⟨76912446092249662021900301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 205099856245999098725067469 76912446092249662021900301)
                ·
                  refine ⟨28842167284593623258212613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76912446092249662021900301 28842167284593623258212613)
                  ·
                    refine ⟨5407906365861304360914865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28842167284593623258212613 5407906365861304360914865)
                    ·
                      refine ⟨4055929774395978270686149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5407906365861304360914865 4055929774395978270686149)
                      ·
                        rfl

theorem cell23_7898895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 3, 4, 2].length) (baseStart_7898895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7898895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7898895 prefixEnd_7898895 := by exact prefixLift 7898895
  have htrace : WordTrace (prefixWord ++ tailWord_7898895) baseStart_7898895 baseEnd_7898895 := by
    simpa [prefixWord, tailWord_7898895, baseEnd_7898895] using wordTrace_append hprefix tailTrace_7898895
  have hstable : (prefixWord ++ tailWord_7898895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7898895).length < 2 ^ (prefixWord ++ tailWord_7898895).sum := by decide
  have hdescent : baseEnd_7898895 < baseStart_7898895 := by decide
  rcases family_descends (prefixWord ++ tailWord_7898895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7898900 : List Nat := [2, 4, 4, 1, 2, 1, 1, 2, 2, 4]
def baseStart_7898900 : Nat := 118140960795 + 7898900 * 2 ^ 59
def prefixEnd_7898900 : Nat := 4983230072969 + 3 ^ 40 * 7898900 * 2
def baseEnd_7898900 : Nat := 1351977447266416917041209

theorem tailTrace_7898900 : CollatzResearch.WordTrace tailWord_7898900 prefixEnd_7898900 1351977447266416917041209 := by
  unfold tailWord_7898900
  simp only [CollatzResearch.WordTrace]
  refine ⟨144048275541820899781883077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192064367389094533042510769 144048275541820899781883077)
  ·
    refine ⟨27009051664091418709103077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144048275541820899781883077 27009051664091418709103077)
    ·
      refine ⟨5064197187017141007956827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27009051664091418709103077 5064197187017141007956827)
      ·
        refine ⟨7596295780525711511935241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5064197187017141007956827 7596295780525711511935241)
        ·
          refine ⟨5697221835394283633951431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7596295780525711511935241 5697221835394283633951431)
          ·
            refine ⟨8545832753091425450927147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5697221835394283633951431 8545832753091425450927147)
            ·
              refine ⟨12818749129637138176390721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8545832753091425450927147 12818749129637138176390721)
              ·
                refine ⟨9614061847227853632293041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12818749129637138176390721 9614061847227853632293041)
                ·
                  refine ⟨7210546385420890224219781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9614061847227853632293041 7210546385420890224219781)
                  ·
                    refine ⟨1351977447266416917041209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7210546385420890224219781 1351977447266416917041209)
                    ·
                      rfl

theorem cell23_7898900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_7898900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7898900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7898900 prefixEnd_7898900 := by exact prefixLift 7898900
  have htrace : WordTrace (prefixWord ++ tailWord_7898900) baseStart_7898900 baseEnd_7898900 := by
    simpa [prefixWord, tailWord_7898900, baseEnd_7898900] using wordTrace_append hprefix tailTrace_7898900
  have hstable : (prefixWord ++ tailWord_7898900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7898900).length < 2 ^ (prefixWord ++ tailWord_7898900).sum := by decide
  have hdescent : baseEnd_7898900 < baseStart_7898900 := by decide
  rcases family_descends (prefixWord ++ tailWord_7898900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7898929 : List Nat := [1, 2, 2, 3, 2, 4, 1, 1, 1, 4, 2]
def baseStart_7898929 : Nat := 118140960795 + 7898929 * 2 ^ 59
def prefixEnd_7898929 : Nat := 4983230072969 + 3 ^ 40 * 7898929 * 2
def baseEnd_7898929 : Nat := 4055947232738231137660993

theorem tailTrace_7898929 : CollatzResearch.WordTrace tailWord_7898929 prefixEnd_7898929 4055947232738231137660993 := by
  unfold tailWord_7898929
  simp only [CollatzResearch.WordTrace]
  refine ⟨288097608800536737516571841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192065072533691158344381227 288097608800536737516571841)
  ·
    refine ⟨216073206600402553137428881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288097608800536737516571841 216073206600402553137428881)
    ·
      refine ⟨162054904950301914853071661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216073206600402553137428881 162054904950301914853071661)
      ·
        refine ⟨60770589356363218069901873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162054904950301914853071661 60770589356363218069901873)
        ·
          refine ⟨45577942017272413552426405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60770589356363218069901873 45577942017272413552426405)
          ·
            refine ⟨8545864128238577541079951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45577942017272413552426405 8545864128238577541079951)
            ·
              refine ⟨12818796192357866311619927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8545864128238577541079951 12818796192357866311619927)
              ·
                refine ⟨19228194288536799467429891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12818796192357866311619927 19228194288536799467429891)
                ·
                  refine ⟨28842291432805199201144837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19228194288536799467429891 28842291432805199201144837)
                  ·
                    refine ⟨5407929643650974850214657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28842291432805199201144837 5407929643650974850214657)
                    ·
                      refine ⟨4055947232738231137660993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5407929643650974850214657 4055947232738231137660993)
                      ·
                        rfl

theorem cell23_7898929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 1, 1, 4, 2].length) (baseStart_7898929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7898929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7898929 prefixEnd_7898929 := by exact prefixLift 7898929
  have htrace : WordTrace (prefixWord ++ tailWord_7898929) baseStart_7898929 baseEnd_7898929 := by
    simpa [prefixWord, tailWord_7898929, baseEnd_7898929] using wordTrace_append hprefix tailTrace_7898929
  have hstable : (prefixWord ++ tailWord_7898929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7898929).length < 2 ^ (prefixWord ++ tailWord_7898929).sum := by decide
  have hdescent : baseEnd_7898929 < baseStart_7898929 := by decide
  rcases family_descends (prefixWord ++ tailWord_7898929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7898952 : List Nat := [2, 1, 3, 1, 1, 4, 3, 3, 5]
def baseStart_7898952 : Nat := 118140960795 + 7898952 * 2 ^ 59
def prefixEnd_7898952 : Nat := 4983230072969 + 3 ^ 40 * 7898952 * 2
def baseEnd_7898952 : Nat := 450662115865920505297043

theorem tailTrace_7898952 : CollatzResearch.WordTrace tailWord_7898952 prefixEnd_7898952 450662115865920505297043 := by
  unfold tailWord_7898952
  simp only [CollatzResearch.WordTrace]
  refine ⟨144049223839726706222329555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192065631786302274963106073 144049223839726706222329555)
  ·
    refine ⟨216073835759590059333494333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144049223839726706222329555 216073835759590059333494333)
    ·
      refine ⟨81027688409846272250060375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216073835759590059333494333 81027688409846272250060375)
      ·
        refine ⟨121541532614769408375090563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81027688409846272250060375 121541532614769408375090563)
        ·
          refine ⟨182312298922154112562635845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121541532614769408375090563 182312298922154112562635845)
          ·
            refine ⟨34183556047903896105494221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 182312298922154112562635845 34183556047903896105494221)
            ·
              refine ⟨12818833517963961039560333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34183556047903896105494221 12818833517963961039560333)
              ·
                refine ⟨4807062569236485389835125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12818833517963961039560333 4807062569236485389835125)
                ·
                  refine ⟨450662115865920505297043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4807062569236485389835125 450662115865920505297043)
                  ·
                    rfl

theorem cell23_7898952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 3, 5].length) (baseStart_7898952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7898952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7898952 prefixEnd_7898952 := by exact prefixLift 7898952
  have htrace : WordTrace (prefixWord ++ tailWord_7898952) baseStart_7898952 baseEnd_7898952 := by
    simpa [prefixWord, tailWord_7898952, baseEnd_7898952] using wordTrace_append hprefix tailTrace_7898952
  have hstable : (prefixWord ++ tailWord_7898952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7898952).length < 2 ^ (prefixWord ++ tailWord_7898952).sum := by decide
  have hdescent : baseEnd_7898952 < baseStart_7898952 := by decide
  rcases family_descends (prefixWord ++ tailWord_7898952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7898965 : List Nat := [1, 3, 2, 2, 2, 2, 1, 1, 4, 5]
def baseStart_7898965 : Nat := 118140960795 + 7898965 * 2 ^ 59
def prefixEnd_7898965 : Nat := 4983230072969 + 3 ^ 40 * 7898965 * 2
def baseEnd_7898965 : Nat := 1351988572680597665603609

theorem tailTrace_7898965 : CollatzResearch.WordTrace tailWord_7898965 prefixEnd_7898965 1351988572680597665603609 := by
  unfold tailWord_7898965
  simp only [CollatzResearch.WordTrace]
  refine ⟨288098921828406315664882349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192065947885604210443254899 288098921828406315664882349)
  ·
    refine ⟨108037095685652368374330881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288098921828406315664882349 108037095685652368374330881)
    ·
      refine ⟨81027821764239276280748161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108037095685652368374330881 81027821764239276280748161)
      ·
        refine ⟨60770866323179457210561121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81027821764239276280748161 60770866323179457210561121)
        ·
          refine ⟨45578149742384592907920841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60770866323179457210561121 45578149742384592907920841)
          ·
            refine ⟨34183612306788444680940631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45578149742384592907920841 34183612306788444680940631)
            ·
              refine ⟨51275418460182667021410947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34183612306788444680940631 51275418460182667021410947)
              ·
                refine ⟨76913127690274000532116421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51275418460182667021410947 76913127690274000532116421)
                ·
                  refine ⟨14421211441926375099771829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76913127690274000532116421 14421211441926375099771829)
                  ·
                    refine ⟨1351988572680597665603609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14421211441926375099771829 1351988572680597665603609)
                    ·
                      rfl

theorem cell23_7898965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 4, 5].length) (baseStart_7898965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7898965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7898965 prefixEnd_7898965 := by exact prefixLift 7898965
  have htrace : WordTrace (prefixWord ++ tailWord_7898965) baseStart_7898965 baseEnd_7898965 := by
    simpa [prefixWord, tailWord_7898965, baseEnd_7898965] using wordTrace_append hprefix tailTrace_7898965
  have hstable : (prefixWord ++ tailWord_7898965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7898965).length < 2 ^ (prefixWord ++ tailWord_7898965).sum := by decide
  have hdescent : baseEnd_7898965 < baseStart_7898965 := by decide
  rcases family_descends (prefixWord ++ tailWord_7898965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7898968 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 2, 2, 8]
def baseStart_7898968 : Nat := 118140960795 + 7898968 * 2 ^ 59
def prefixEnd_7898968 : Nat := 4983230072969 + 3 ^ 40 * 7898968 * 2
def baseEnd_7898968 : Nat := 4055967258483756485073313

theorem tailTrace_7898968 : CollatzResearch.WordTrace tailWord_7898968 prefixEnd_7898968 4055967258483756485073313 := by
  unfold tailWord_7898968
  simp only [CollatzResearch.WordTrace]
  refine ⟨144049515623697723588620779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192066020831596964784827705 144049515623697723588620779)
  ·
    refine ⟨216074273435546585382931169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144049515623697723588620779 216074273435546585382931169)
    ·
      refine ⟨162055705076659939037198377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216074273435546585382931169 162055705076659939037198377)
      ·
        refine ⟨121541778807494954277898783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162055705076659939037198377 121541778807494954277898783)
        ·
          refine ⟨182312668211242431416848175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121541778807494954277898783 182312668211242431416848175)
          ·
            refine ⟨273469002316863647125272263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182312668211242431416848175 273469002316863647125272263)
            ·
              refine ⟨410203503475295470687908395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273469002316863647125272263 410203503475295470687908395)
              ·
                refine ⟨615305255212943206031862593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 410203503475295470687908395 615305255212943206031862593)
                ·
                  refine ⟨461478941409707404523896945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 615305255212943206031862593 461478941409707404523896945)
                  ·
                    refine ⟨346109206057280553392922709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 461478941409707404523896945 346109206057280553392922709)
                    ·
                      refine ⟨4055967258483756485073313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 346109206057280553392922709 4055967258483756485073313)
                      ·
                        rfl

theorem cell23_7898968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_7898968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7898968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7898968 prefixEnd_7898968 := by exact prefixLift 7898968
  have htrace : WordTrace (prefixWord ++ tailWord_7898968) baseStart_7898968 baseEnd_7898968 := by
    simpa [prefixWord, tailWord_7898968, baseEnd_7898968] using wordTrace_append hprefix tailTrace_7898968
  have hstable : (prefixWord ++ tailWord_7898968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7898968).length < 2 ^ (prefixWord ++ tailWord_7898968).sum := by decide
  have hdescent : baseEnd_7898968 < baseStart_7898968 := by decide
  rcases family_descends (prefixWord ++ tailWord_7898968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7898975 : List Nat := [1, 1, 2, 3, 1, 5, 1, 1, 1, 2, 5]
def baseStart_7898975 : Nat := 118140960795 + 7898975 * 2 ^ 59
def prefixEnd_7898975 : Nat := 4983230072969 + 3 ^ 40 * 7898975 * 2
def baseEnd_7898975 : Nat := 4055970852848337957685781

theorem tailTrace_7898975 : CollatzResearch.WordTrace tailWord_7898975 prefixEnd_7898975 4055970852848337957685781 := by
  unfold tailWord_7898975
  simp only [CollatzResearch.WordTrace]
  refine ⟨288099286558370087372746379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192066191038913391581830919 288099286558370087372746379)
  ·
    refine ⟨432148929837555131059119569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288099286558370087372746379 432148929837555131059119569)
    ·
      refine ⟨324111697378166348294339677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432148929837555131059119569 324111697378166348294339677)
      ·
        refine ⟨121541886516812380610377379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 324111697378166348294339677 121541886516812380610377379)
        ·
          refine ⟨182312829775218570915566069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121541886516812380610377379 182312829775218570915566069)
          ·
            refine ⟨17091827791426741023334319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 182312829775218570915566069 17091827791426741023334319)
            ·
              refine ⟨25637741687140111535001479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17091827791426741023334319 25637741687140111535001479)
              ·
                refine ⟨38456612530710167302502219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25637741687140111535001479 38456612530710167302502219)
                ·
                  refine ⟨57684918796065250953753329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38456612530710167302502219 57684918796065250953753329)
                  ·
                    refine ⟨43263689097048938215314997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57684918796065250953753329 43263689097048938215314997)
                    ·
                      refine ⟨4055970852848337957685781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43263689097048938215314997 4055970852848337957685781)
                      ·
                        rfl

theorem cell23_7898975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 2, 5].length) (baseStart_7898975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7898975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7898975 prefixEnd_7898975 := by exact prefixLift 7898975
  have htrace : WordTrace (prefixWord ++ tailWord_7898975) baseStart_7898975 baseEnd_7898975 := by
    simpa [prefixWord, tailWord_7898975, baseEnd_7898975] using wordTrace_append hprefix tailTrace_7898975
  have hstable : (prefixWord ++ tailWord_7898975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7898975).length < 2 ^ (prefixWord ++ tailWord_7898975).sum := by decide
  have hdescent : baseEnd_7898975 < baseStart_7898975 := by decide
  rcases family_descends (prefixWord ++ tailWord_7898975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7898980 : List Nat := [2, 3, 1, 1, 6, 1, 2, 1, 2, 2, 2]
def baseStart_7898980 : Nat := 118140960795 + 7898980 * 2 ^ 59
def prefixEnd_7898980 : Nat := 4983230072969 + 3 ^ 40 * 7898980 * 2
def baseEnd_7898980 : Nat := 4055973420251610438123259

theorem tailTrace_7898980 : CollatzResearch.WordTrace tailWord_7898980 prefixEnd_7898980 4055973420251610438123259 := by
  unfold tailWord_7898980
  simp only [CollatzResearch.WordTrace]
  refine ⟨144049734461675986613339197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192066312615567982151118929 144049734461675986613339197)
  ·
    refine ⟨54018650423128494980002199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144049734461675986613339197 54018650423128494980002199)
    ·
      refine ⟨81027975634692742470003299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54018650423128494980002199 81027975634692742470003299)
      ·
        refine ⟨121541963452039113705004949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81027975634692742470003299 121541963452039113705004949)
        ·
          refine ⟨5697279536814333454922107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 121541963452039113705004949 5697279536814333454922107)
          ·
            refine ⟨8545919305221500182383161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5697279536814333454922107 8545919305221500182383161)
            ·
              refine ⟨6409439478916125136787371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8545919305221500182383161 6409439478916125136787371)
              ·
                refine ⟨9614159218374187705181057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6409439478916125136787371 9614159218374187705181057)
                ·
                  refine ⟨7210619413780640778885793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9614159218374187705181057 7210619413780640778885793)
                  ·
                    refine ⟨5407964560335480584164345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7210619413780640778885793 5407964560335480584164345)
                    ·
                      refine ⟨4055973420251610438123259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5407964560335480584164345 4055973420251610438123259)
                      ·
                        rfl

theorem cell23_7898980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 2, 1, 2, 2, 2].length) (baseStart_7898980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7898980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7898980 prefixEnd_7898980 := by exact prefixLift 7898980
  have htrace : WordTrace (prefixWord ++ tailWord_7898980) baseStart_7898980 baseEnd_7898980 := by
    simpa [prefixWord, tailWord_7898980, baseEnd_7898980] using wordTrace_append hprefix tailTrace_7898980
  have hstable : (prefixWord ++ tailWord_7898980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7898980).length < 2 ^ (prefixWord ++ tailWord_7898980).sum := by decide
  have hdescent : baseEnd_7898980 < baseStart_7898980 := by decide
  rcases family_descends (prefixWord ++ tailWord_7898980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7898995 : List Nat := [1, 1, 1, 2, 2, 1, 3, 3, 5, 4]
def baseStart_7898995 : Nat := 118140960795 + 7898995 * 2 ^ 59
def prefixEnd_7898995 : Nat := 4983230072969 + 3 ^ 40 * 7898995 * 2
def baseEnd_7898995 : Nat := 1351993707487142626478563

theorem tailTrace_7898995 : CollatzResearch.WordTrace tailWord_7898995 prefixEnd_7898995 1351993707487142626478563 := by
  unfold tailWord_7898995
  simp only [CollatzResearch.WordTrace]
  refine ⟨288100016018297630788474439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192066677345531753858982959 288100016018297630788474439)
  ·
    refine ⟨432150024027446446182711659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288100016018297630788474439 432150024027446446182711659)
    ·
      refine ⟨648225036041169669274067489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432150024027446446182711659 648225036041169669274067489)
      ·
        refine ⟨486168777030877251955550617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 648225036041169669274067489 486168777030877251955550617)
        ·
          refine ⟨364626582773157938966662963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 486168777030877251955550617 364626582773157938966662963)
          ·
            refine ⟨546939874159736908449994445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364626582773157938966662963 546939874159736908449994445)
            ·
              refine ⟨205102452809901340668747917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 546939874159736908449994445 205102452809901340668747917)
              ·
                refine ⟨76913419803713002750780469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 205102452809901340668747917 76913419803713002750780469)
                ·
                  refine ⟨7210633106598094007885669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76913419803713002750780469 7210633106598094007885669)
                  ·
                    refine ⟨1351993707487142626478563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7210633106598094007885669 1351993707487142626478563)
                    ·
                      rfl

theorem cell23_7898995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 5, 4].length) (baseStart_7898995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7898995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7898995 prefixEnd_7898995 := by exact prefixLift 7898995
  have htrace : WordTrace (prefixWord ++ tailWord_7898995) baseStart_7898995 baseEnd_7898995 := by
    simpa [prefixWord, tailWord_7898995, baseEnd_7898995] using wordTrace_append hprefix tailTrace_7898995
  have hstable : (prefixWord ++ tailWord_7898995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7898995).length < 2 ^ (prefixWord ++ tailWord_7898995).sum := by decide
  have hdescent : baseEnd_7898995 < baseStart_7898995 := by decide
  rcases family_descends (prefixWord ++ tailWord_7898995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7899025 : List Nat := [1, 2, 2, 1, 1, 1, 5, 4, 6]
def baseStart_7899025 : Nat := 118140960795 + 7899025 * 2 ^ 59
def prefixEnd_7899025 : Nat := 4983230072969 + 3 ^ 40 * 7899025 * 2
def baseEnd_7899025 : Nat := 450666280764562529117839

theorem tailTrace_7899025 : CollatzResearch.WordTrace tailWord_7899025 prefixEnd_7899025 450666280764562529117839 := by
  unfold tailWord_7899025
  simp only [CollatzResearch.WordTrace]
  refine ⟨288101110208188945912066529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192067406805459297274711019 288101110208188945912066529)
  ·
    refine ⟨216075832656141709434049897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288101110208188945912066529 216075832656141709434049897)
    ·
      refine ⟨162056874492106282075537423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216075832656141709434049897 162056874492106282075537423)
      ·
        refine ⟨243085311738159423113306135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162056874492106282075537423 243085311738159423113306135)
        ·
          refine ⟨364627967607239134669959203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243085311738159423113306135 364627967607239134669959203)
          ·
            refine ⟨546941951410858702004938805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364627967607239134669959203 546941951410858702004938805)
            ·
              refine ⟨51275807944768003312963013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 546941951410858702004938805 51275807944768003312963013)
              ·
                refine ⟨9614213989644000621180565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51275807944768003312963013 9614213989644000621180565)
                ·
                  refine ⟨450666280764562529117839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9614213989644000621180565 450666280764562529117839)
                  ·
                    rfl

theorem cell23_7899025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 4, 6].length) (baseStart_7899025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7899025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7899025 prefixEnd_7899025 := by exact prefixLift 7899025
  have htrace : WordTrace (prefixWord ++ tailWord_7899025) baseStart_7899025 baseEnd_7899025 := by
    simpa [prefixWord, tailWord_7899025, baseEnd_7899025] using wordTrace_append hprefix tailTrace_7899025
  have hstable : (prefixWord ++ tailWord_7899025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7899025).length < 2 ^ (prefixWord ++ tailWord_7899025).sum := by decide
  have hdescent : baseEnd_7899025 < baseStart_7899025 := by decide
  rcases family_descends (prefixWord ++ tailWord_7899025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7899029 : List Nat := [1, 3, 2, 1, 1, 3, 3, 4, 1, 4]
def baseStart_7899029 : Nat := 118140960795 + 7899029 * 2 ^ 59
def prefixEnd_7899029 : Nat := 4983230072969 + 3 ^ 40 * 7899029 * 2
def baseEnd_7899029 : Nat := 1351999526934560248803511

theorem tailTrace_7899029 : CollatzResearch.WordTrace tailWord_7899029 prefixEnd_7899029 1351999526934560248803511 := by
  unfold tailWord_7899029
  simp only [CollatzResearch.WordTrace]
  refine ⟨288101256100174454595212141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192067504066782969730141427 288101256100174454595212141)
  ·
    refine ⟨108037971037565420473204553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288101256100174454595212141 108037971037565420473204553)
    ·
      refine ⟨81028478278174065354903415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108037971037565420473204553 81028478278174065354903415)
      ·
        refine ⟨121542717417261098032355123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81028478278174065354903415 121542717417261098032355123)
        ·
          refine ⟨182314076125891647048532685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121542717417261098032355123 182314076125891647048532685)
          ·
            refine ⟨68367778547209367643199757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182314076125891647048532685 68367778547209367643199757)
            ·
              refine ⟨25637916955203512866199909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68367778547209367643199757 25637916955203512866199909)
              ·
                refine ⟨4807109429100658662412483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25637916955203512866199909 4807109429100658662412483)
                ·
                  refine ⟨7210664143650987993618725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4807109429100658662412483 7210664143650987993618725)
                  ·
                    refine ⟨1351999526934560248803511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7210664143650987993618725 1351999526934560248803511)
                    ·
                      rfl

theorem cell23_7899029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 4, 1, 4].length) (baseStart_7899029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7899029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7899029 prefixEnd_7899029 := by exact prefixLift 7899029
  have htrace : WordTrace (prefixWord ++ tailWord_7899029) baseStart_7899029 baseEnd_7899029 := by
    simpa [prefixWord, tailWord_7899029, baseEnd_7899029] using wordTrace_append hprefix tailTrace_7899029
  have hstable : (prefixWord ++ tailWord_7899029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7899029).length < 2 ^ (prefixWord ++ tailWord_7899029).sum := by decide
  have hdescent : baseEnd_7899029 < baseStart_7899029 := by decide
  rcases family_descends (prefixWord ++ tailWord_7899029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7899055 : List Nat := [1, 1, 2, 1, 2, 2, 3, 3, 3, 5]
def baseStart_7899055 : Nat := 118140960795 + 7899055 * 2 ^ 59
def prefixEnd_7899055 : Nat := 4983230072969 + 3 ^ 40 * 7899055 * 2
def baseEnd_7899055 : Nat := 1352003977100232548228471

theorem tailTrace_7899055 : CollatzResearch.WordTrace tailWord_7899055 prefixEnd_7899055 1352003977100232548228471 := by
  unfold tailWord_7899055
  simp only [CollatzResearch.WordTrace]
  refine ⟨288102204398080261035658619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192068136265386840690439079 288102204398080261035658619)
  ·
    refine ⟨432153306597120391553487929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288102204398080261035658619 432153306597120391553487929)
    ·
      refine ⟨324114979947840293665115947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432153306597120391553487929 324114979947840293665115947)
      ·
        refine ⟨486172469921760440497673921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324114979947840293665115947 486172469921760440497673921)
        ·
          refine ⟨364629352441320330373255441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 486172469921760440497673921 364629352441320330373255441)
          ·
            refine ⟨273472014330990247779941581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 364629352441320330373255441 273472014330990247779941581)
            ·
              refine ⟨102552005374121342917478093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 273472014330990247779941581 102552005374121342917478093)
              ·
                refine ⟨38457002015295503594054285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102552005374121342917478093 38457002015295503594054285)
                ·
                  refine ⟨14421375755735813847770357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38457002015295503594054285 14421375755735813847770357)
                  ·
                    refine ⟨1352003977100232548228471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14421375755735813847770357 1352003977100232548228471)
                    ·
                      rfl

theorem cell23_7899055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 3, 5].length) (baseStart_7899055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7899055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7899055 prefixEnd_7899055 := by exact prefixLift 7899055
  have htrace : WordTrace (prefixWord ++ tailWord_7899055) baseStart_7899055 baseEnd_7899055 := by
    simpa [prefixWord, tailWord_7899055, baseEnd_7899055] using wordTrace_append hprefix tailTrace_7899055
  have hstable : (prefixWord ++ tailWord_7899055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7899055).length < 2 ^ (prefixWord ++ tailWord_7899055).sum := by decide
  have hdescent : baseEnd_7899055 < baseStart_7899055 := by decide
  rcases family_descends (prefixWord ++ tailWord_7899055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7899072 : List Nat := [2, 1, 1, 2, 3, 2, 3, 3, 1, 5]
def baseStart_7899072 : Nat := 118140960795 + 7899072 * 2 ^ 59
def prefixEnd_7899072 : Nat := 4983230072969 + 3 ^ 40 * 7899072 * 2
def baseEnd_7899072 : Nat := 1352006886823941359390945

theorem tailTrace_7899072 : CollatzResearch.WordTrace tailWord_7899072 prefixEnd_7899072 1352006886823941359390945 := by
  unfold tailWord_7899072
  simp only [CollatzResearch.WordTrace]
  refine ⟨144051412219509336469513735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192068549626012448626018313 144051412219509336469513735)
  ·
    refine ⟨216077118329264004704270603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144051412219509336469513735 216077118329264004704270603)
    ·
      refine ⟨324115677493896007056405905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216077118329264004704270603 324115677493896007056405905)
      ·
        refine ⟨243086758120422005292304429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324115677493896007056405905 243086758120422005292304429)
        ·
          refine ⟨91157534295158251984614161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 243086758120422005292304429 91157534295158251984614161)
          ·
            refine ⟨68368150721368688988460621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91157534295158251984614161 68368150721368688988460621)
            ·
              refine ⟨25638056520513258370672733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68368150721368688988460621 25638056520513258370672733)
              ·
                refine ⟨9614271195192471889002275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25638056520513258370672733 9614271195192471889002275)
                ·
                  refine ⟨14421406792788707833503413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9614271195192471889002275 14421406792788707833503413)
                  ·
                    refine ⟨1352006886823941359390945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14421406792788707833503413 1352006886823941359390945)
                    ·
                      rfl

theorem cell23_7899072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 3, 1, 5].length) (baseStart_7899072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7899072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7899072 prefixEnd_7899072 := by exact prefixLift 7899072
  have htrace : WordTrace (prefixWord ++ tailWord_7899072) baseStart_7899072 baseEnd_7899072 := by
    simpa [prefixWord, tailWord_7899072, baseEnd_7899072] using wordTrace_append hprefix tailTrace_7899072
  have hstable : (prefixWord ++ tailWord_7899072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7899072).length < 2 ^ (prefixWord ++ tailWord_7899072).sum := by decide
  have hdescent : baseEnd_7899072 < baseStart_7899072 := by decide
  rcases family_descends (prefixWord ++ tailWord_7899072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7899086 : List Nat := [4, 1, 1, 1, 2, 2, 1, 6, 1, 1, 3]
def baseStart_7899086 : Nat := 118140960795 + 7899086 * 2 ^ 59
def prefixEnd_7899086 : Nat := 4983230072969 + 3 ^ 40 * 7899086 * 2
def baseEnd_7899086 : Nat := 4056027849200987023397771

theorem tailTrace_7899086 : CollatzResearch.WordTrace tailWord_7899086 prefixEnd_7899086 4056027849200987023397771 := by
  unfold tailWord_7899086
  simp only [CollatzResearch.WordTrace]
  refine ⟨36012916882620994166254639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192068890040645302220024741 36012916882620994166254639)
  ·
    refine ⟨54019375323931491249381959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36012916882620994166254639 54019375323931491249381959)
    ·
      refine ⟨81029062985897236874072939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54019375323931491249381959 81029062985897236874072939)
      ·
        refine ⟨121543594478845855311109409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81029062985897236874072939 121543594478845855311109409)
        ·
          refine ⟨91157695859134391483332057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121543594478845855311109409 91157695859134391483332057)
          ·
            refine ⟨68368271894350793612499043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91157695859134391483332057 68368271894350793612499043)
            ·
              refine ⟨102552407841526190418748565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68368271894350793612499043 102552407841526190418748565)
              ·
                refine ⟨4807144117571540175878839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 102552407841526190418748565 4807144117571540175878839)
                ·
                  refine ⟨7210716176357310263818259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4807144117571540175878839 7210716176357310263818259)
                  ·
                    refine ⟨10816074264535965395727389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7210716176357310263818259 10816074264535965395727389)
                    ·
                      refine ⟨4056027849200987023397771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10816074264535965395727389 4056027849200987023397771)
                      ·
                        rfl

theorem cell23_7899086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 6, 1, 1, 3].length) (baseStart_7899086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7899086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7899086 prefixEnd_7899086 := by exact prefixLift 7899086
  have htrace : WordTrace (prefixWord ++ tailWord_7899086) baseStart_7899086 baseEnd_7899086 := by
    simpa [prefixWord, tailWord_7899086, baseEnd_7899086] using wordTrace_append hprefix tailTrace_7899086
  have hstable : (prefixWord ++ tailWord_7899086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7899086).length < 2 ^ (prefixWord ++ tailWord_7899086).sum := by decide
  have hdescent : baseEnd_7899086 < baseStart_7899086 := by decide
  rcases family_descends (prefixWord ++ tailWord_7899086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7899129 : List Nat := [1, 2, 1, 3, 1, 4, 2, 3, 1, 2, 3]
def baseStart_7899129 : Nat := 118140960795 + 7899129 * 2 ^ 59
def prefixEnd_7899129 : Nat := 4983230072969 + 3 ^ 40 * 7899129 * 2
def baseEnd_7899129 : Nat := 4056049928869130355160073

theorem tailTrace_7899129 : CollatzResearch.WordTrace tailWord_7899129 prefixEnd_7899129 4056049928869130355160073 := by
  unfold tailWord_7899129
  simp only [CollatzResearch.WordTrace]
  refine ⟨288104903399812171673852441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192069935599874781115901627 288104903399812171673852441)
  ·
    refine ⟨216078677549859128755389331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288104903399812171673852441 216078677549859128755389331)
    ·
      refine ⟨324118016324788693133083997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216078677549859128755389331 324118016324788693133083997)
      ·
        refine ⟨121544256121795759924906499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 324118016324788693133083997 121544256121795759924906499)
        ·
          refine ⟨182316384182693639887359749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121544256121795759924906499 182316384182693639887359749)
          ·
            refine ⟨34184322034255057478879953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 182316384182693639887359749 34184322034255057478879953)
            ·
              refine ⟨25638241525691293109159965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34184322034255057478879953 25638241525691293109159965)
              ·
                refine ⟨9614340572134234915934987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25638241525691293109159965 9614340572134234915934987)
                ·
                  refine ⟨14421510858201352373902481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9614340572134234915934987 14421510858201352373902481)
                  ·
                    refine ⟨10816133143651014280426861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14421510858201352373902481 10816133143651014280426861)
                    ·
                      refine ⟨4056049928869130355160073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10816133143651014280426861 4056049928869130355160073)
                      ·
                        rfl

theorem cell23_7899129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 3, 1, 2, 3].length) (baseStart_7899129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7899129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7899129 prefixEnd_7899129 := by exact prefixLift 7899129
  have htrace : WordTrace (prefixWord ++ tailWord_7899129) baseStart_7899129 baseEnd_7899129 := by
    simpa [prefixWord, tailWord_7899129, baseEnd_7899129] using wordTrace_append hprefix tailTrace_7899129
  have hstable : (prefixWord ++ tailWord_7899129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7899129).length < 2 ^ (prefixWord ++ tailWord_7899129).sum := by decide
  have hdescent : baseEnd_7899129 < baseStart_7899129 := by decide
  rcases family_descends (prefixWord ++ tailWord_7899129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7899143 : List Nat := [1, 1, 4, 3, 1, 4, 1, 1, 3, 2, 2]
def baseStart_7899143 : Nat := 118140960795 + 7899143 * 2 ^ 59
def prefixEnd_7899143 : Nat := 4983230072969 + 3 ^ 40 * 7899143 * 2
def baseEnd_7899143 : Nat := 4056057117598293300385009

theorem tailTrace_7899143 : CollatzResearch.WordTrace tailWord_7899143 prefixEnd_7899143 4056057117598293300385009 := by
  unfold tailWord_7899143
  simp only [CollatzResearch.WordTrace]
  refine ⟨288105414021761452064862083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192070276014507634709908055 288105414021761452064862083)
  ·
    refine ⟨432158121032642178097293125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288105414021761452064862083 432158121032642178097293125)
    ·
      refine ⟨81029647693620408393242461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 432158121032642178097293125 81029647693620408393242461)
      ·
        refine ⟨30386117885107653147465923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81029647693620408393242461 30386117885107653147465923)
        ·
          refine ⟨45579176827661479721198885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30386117885107653147465923 45579176827661479721198885)
          ·
            refine ⟨8546095655186527447724791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45579176827661479721198885 8546095655186527447724791)
            ·
              refine ⟨12819143482779791171587187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8546095655186527447724791 12819143482779791171587187)
              ·
                refine ⟨19228715224169686757380781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12819143482779791171587187 19228715224169686757380781)
                ·
                  refine ⟨7210768209063632534017793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19228715224169686757380781 7210768209063632534017793)
                  ·
                    refine ⟨5408076156797724400513345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7210768209063632534017793 5408076156797724400513345)
                    ·
                      refine ⟨4056057117598293300385009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5408076156797724400513345 4056057117598293300385009)
                      ·
                        rfl

theorem cell23_7899143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 1, 3, 2, 2].length) (baseStart_7899143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7899143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7899143 prefixEnd_7899143 := by exact prefixLift 7899143
  have htrace : WordTrace (prefixWord ++ tailWord_7899143) baseStart_7899143 baseEnd_7899143 := by
    simpa [prefixWord, tailWord_7899143, baseEnd_7899143] using wordTrace_append hprefix tailTrace_7899143
  have hstable : (prefixWord ++ tailWord_7899143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7899143).length < 2 ^ (prefixWord ++ tailWord_7899143).sum := by decide
  have hdescent : baseEnd_7899143 < baseStart_7899143 := by decide
  rcases family_descends (prefixWord ++ tailWord_7899143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7899193 : List Nat := [1, 2, 1, 5, 3, 1, 2, 2, 2, 1, 3]
def baseStart_7899193 : Nat := 118140960795 + 7899193 * 2 ^ 59
def prefixEnd_7899193 : Nat := 4983230072969 + 3 ^ 40 * 7899193 * 2
def baseEnd_7899193 : Nat := 4056082791631018104759779

theorem tailTrace_7899193 : CollatzResearch.WordTrace tailWord_7899193 prefixEnd_7899193 4056082791631018104759779 := by
  unfold tailWord_7899193
  simp only [CollatzResearch.WordTrace]
  refine ⟨288107237671580310604182233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192071491781053540402788155 288107237671580310604182233)
  ·
    refine ⟨216080428253685232953136675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288107237671580310604182233 216080428253685232953136675)
    ·
      refine ⟨324120642380527849429705013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216080428253685232953136675 324120642380527849429705013)
      ·
        refine ⟨30386310223174485884034845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 324120642380527849429705013 30386310223174485884034845)
        ·
          refine ⟨11394866333690432206513067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30386310223174485884034845 11394866333690432206513067)
          ·
            refine ⟨17092299500535648309769601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11394866333690432206513067 17092299500535648309769601)
            ·
              refine ⟨12819224625401736232327201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17092299500535648309769601 12819224625401736232327201)
              ·
                refine ⟨9614418469051302174245401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12819224625401736232327201 9614418469051302174245401)
                ·
                  refine ⟨7210813851788476630684051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9614418469051302174245401 7210813851788476630684051)
                  ·
                    refine ⟨10816220777682714946026077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7210813851788476630684051 10816220777682714946026077)
                    ·
                      refine ⟨4056082791631018104759779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10816220777682714946026077 4056082791631018104759779)
                      ·
                        rfl

theorem cell23_7899193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_7899193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7899193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7899193 prefixEnd_7899193 := by exact prefixLift 7899193
  have htrace : WordTrace (prefixWord ++ tailWord_7899193) baseStart_7899193 baseEnd_7899193 := by
    simpa [prefixWord, tailWord_7899193, baseEnd_7899193] using wordTrace_append hprefix tailTrace_7899193
  have hstable : (prefixWord ++ tailWord_7899193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7899193).length < 2 ^ (prefixWord ++ tailWord_7899193).sum := by decide
  have hdescent : baseEnd_7899193 < baseStart_7899193 := by decide
  rcases family_descends (prefixWord ++ tailWord_7899193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7899212 : List Nat := [2, 2, 1, 3, 1, 1, 3, 1, 1, 4, 4]
def baseStart_7899212 : Nat := 118140960795 + 7899212 * 2 ^ 59
def prefixEnd_7899212 : Nat := 4983230072969 + 3 ^ 40 * 7899212 * 2
def baseEnd_7899212 : Nat := 4056092547763453530422191

theorem tailTrace_7899212 : CollatzResearch.WordTrace tailWord_7899212 prefixEnd_7899212 4056092547763453530422191 := by
  unfold tailWord_7899212
  simp only [CollatzResearch.WordTrace]
  refine ⟨144053965329255738424561945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192071953772340984566082593 144053965329255738424561945)
  ·
    refine ⟨108040473996941803818421459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144053965329255738424561945 108040473996941803818421459)
    ·
      refine ⟨162060710995412705727632189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108040473996941803818421459 162060710995412705727632189)
      ·
        refine ⟨60772766623279764647862071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162060710995412705727632189 60772766623279764647862071)
        ·
          refine ⟨91159149934919646971793107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60772766623279764647862071 91159149934919646971793107)
          ·
            refine ⟨136738724902379470457689661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91159149934919646971793107 136738724902379470457689661)
            ·
              refine ⟨51277021838392301421633623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136738724902379470457689661 51277021838392301421633623)
              ·
                refine ⟨76915532757588452132450435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51277021838392301421633623 76915532757588452132450435)
                ·
                  refine ⟨115373299136382678198675653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76915532757588452132450435 115373299136382678198675653)
                  ·
                    refine ⟨21632493588071752162251685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 115373299136382678198675653 21632493588071752162251685)
                    ·
                      refine ⟨4056092547763453530422191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21632493588071752162251685 4056092547763453530422191)
                      ·
                        rfl

theorem cell23_7899212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_7899212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7899212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7899212 prefixEnd_7899212 := by exact prefixLift 7899212
  have htrace : WordTrace (prefixWord ++ tailWord_7899212) baseStart_7899212 baseEnd_7899212 := by
    simpa [prefixWord, tailWord_7899212, baseEnd_7899212] using wordTrace_append hprefix tailTrace_7899212
  have hstable : (prefixWord ++ tailWord_7899212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7899212).length < 2 ^ (prefixWord ++ tailWord_7899212).sum := by decide
  have hdescent : baseEnd_7899212 < baseStart_7899212 := by decide
  rcases family_descends (prefixWord ++ tailWord_7899212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7899250 : List Nat := [3, 2, 1, 2, 2, 4, 1, 2, 2, 2, 2]
def baseStart_7899250 : Nat := 118140960795 + 7899250 * 2 ^ 59
def prefixEnd_7899250 : Nat := 4983230072969 + 3 ^ 40 * 7899250 * 2
def baseEnd_7899250 : Nat := 4056112060028324381747017

theorem tailTrace_7899250 : CollatzResearch.WordTrace tailWord_7899250 prefixEnd_7899250 4056112060028324381747017 := by
  unfold tailWord_7899250
  simp only [CollatzResearch.WordTrace]
  refine ⟨72027329158093452334751801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192072877754915872892671469 72027329158093452334751801)
  ·
    refine ⟨54020496868570089251063851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72027329158093452334751801 54020496868570089251063851)
    ·
      refine ⟨81030745302855133876595777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54020496868570089251063851 81030745302855133876595777)
      ·
        refine ⟨60773058977141350407446833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81030745302855133876595777 60773058977141350407446833)
        ·
          refine ⟨45579794232856012805585125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60773058977141350407446833 45579794232856012805585125)
          ·
            refine ⟨8546211418660502401047211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45579794232856012805585125 8546211418660502401047211)
            ·
              refine ⟨12819317127990753601570817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8546211418660502401047211 12819317127990753601570817)
              ·
                refine ⟨9614487845993065201178113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12819317127990753601570817 9614487845993065201178113)
                ·
                  refine ⟨7210865884494798900883585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9614487845993065201178113 7210865884494798900883585)
                  ·
                    refine ⟨5408149413371099175662689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7210865884494798900883585 5408149413371099175662689)
                    ·
                      refine ⟨4056112060028324381747017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5408149413371099175662689 4056112060028324381747017)
                      ·
                        rfl

theorem cell23_7899250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 2, 2, 2, 2].length) (baseStart_7899250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7899250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7899250 prefixEnd_7899250 := by exact prefixLift 7899250
  have htrace : WordTrace (prefixWord ++ tailWord_7899250) baseStart_7899250 baseEnd_7899250 := by
    simpa [prefixWord, tailWord_7899250, baseEnd_7899250] using wordTrace_append hprefix tailTrace_7899250
  have hstable : (prefixWord ++ tailWord_7899250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7899250).length < 2 ^ (prefixWord ++ tailWord_7899250).sum := by decide
  have hdescent : baseEnd_7899250 < baseStart_7899250 := by decide
  rcases family_descends (prefixWord ++ tailWord_7899250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7899289 : List Nat := [1, 2, 1, 2, 1, 2, 1, 4, 1, 6, 2]
def baseStart_7899289 : Nat := 118140960795 + 7899289 * 2 ^ 59
def prefixEnd_7899289 : Nat := 4983230072969 + 3 ^ 40 * 7899289 * 2
def baseEnd_7899289 : Nat := 4056132085773849729159337

theorem tailTrace_7899289 : CollatzResearch.WordTrace tailWord_7899289 prefixEnd_7899289 4056132085773849729159337 := by
  unfold tailWord_7899289
  simp only [CollatzResearch.WordTrace]
  refine ⟨288110739079232518999676921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192073826052821679333117947 288110739079232518999676921)
  ·
    refine ⟨216083054309424389249757691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288110739079232518999676921 216083054309424389249757691)
    ·
      refine ⟨324124581464136583874636537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216083054309424389249757691 324124581464136583874636537)
      ·
        refine ⟨243093436098102437905977403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324124581464136583874636537 243093436098102437905977403)
        ·
          refine ⟨364640154147153656858966105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243093436098102437905977403 364640154147153656858966105)
          ·
            refine ⟨273480115610365242644224579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 364640154147153656858966105 273480115610365242644224579)
            ·
              refine ⟨410220173415547863966336869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273480115610365242644224579 410220173415547863966336869)
              ·
                refine ⟨76916282515415224493688163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 410220173415547863966336869 76916282515415224493688163)
                ·
                  refine ⟨115374423773122836740532245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76916282515415224493688163 115374423773122836740532245)
                  ·
                    refine ⟨5408176114365132972212449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 115374423773122836740532245 5408176114365132972212449)
                    ·
                      refine ⟨4056132085773849729159337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5408176114365132972212449 4056132085773849729159337)
                      ·
                        rfl

theorem cell23_7899289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 6, 2].length) (baseStart_7899289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7899289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7899289 prefixEnd_7899289 := by exact prefixLift 7899289
  have htrace : WordTrace (prefixWord ++ tailWord_7899289) baseStart_7899289 baseEnd_7899289 := by
    simpa [prefixWord, tailWord_7899289, baseEnd_7899289] using wordTrace_append hprefix tailTrace_7899289
  have hstable : (prefixWord ++ tailWord_7899289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7899289).length < 2 ^ (prefixWord ++ tailWord_7899289).sum := by decide
  have hdescent : baseEnd_7899289 < baseStart_7899289 := by decide
  rcases family_descends (prefixWord ++ tailWord_7899289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7899290 : List Nat := [3, 1, 1, 5, 3, 1, 1, 3, 5]
def baseStart_7899290 : Nat := 118140960795 + 7899290 * 2 ^ 59
def prefixEnd_7899290 : Nat := 4983230072969 + 3 ^ 40 * 7899290 * 2
def baseEnd_7899290 : Nat := 450681399917167136138537

theorem tailTrace_7899290 : CollatzResearch.WordTrace tailWord_7899290 prefixEnd_7899290 450681399917167136138537 := by
  unfold tailWord_7899290
  simp only [CollatzResearch.WordTrace]
  refine ⟨72027693888057224042615831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192073850368152597446975549 72027693888057224042615831)
  ·
    refine ⟨108041540832085836063923747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72027693888057224042615831 108041540832085836063923747)
    ·
      refine ⟨162062311248128754095885621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108041540832085836063923747 162062311248128754095885621)
      ·
        refine ⟨15193341679512070696489277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 162062311248128754095885621 15193341679512070696489277)
        ·
          refine ⟨5697503129817026511183479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15193341679512070696489277 5697503129817026511183479)
          ·
            refine ⟨8546254694725539766775219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5697503129817026511183479 8546254694725539766775219)
            ·
              refine ⟨12819382042088309650162829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8546254694725539766775219 12819382042088309650162829)
              ·
                refine ⟨4807268265783116118811061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12819382042088309650162829 4807268265783116118811061)
                ·
                  refine ⟨450681399917167136138537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4807268265783116118811061 450681399917167136138537)
                  ·
                    rfl

theorem cell23_7899290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 3, 5].length) (baseStart_7899290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7899290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7899290 prefixEnd_7899290 := by exact prefixLift 7899290
  have htrace : WordTrace (prefixWord ++ tailWord_7899290) baseStart_7899290 baseEnd_7899290 := by
    simpa [prefixWord, tailWord_7899290, baseEnd_7899290] using wordTrace_append hprefix tailTrace_7899290
  have hstable : (prefixWord ++ tailWord_7899290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7899290).length < 2 ^ (prefixWord ++ tailWord_7899290).sum := by decide
  have hdescent : baseEnd_7899290 < baseStart_7899290 := by decide
  rcases family_descends (prefixWord ++ tailWord_7899290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7899363 : List Nat := [1, 1, 1, 8, 1, 1, 2, 2, 6]
def baseStart_7899363 : Nat := 118140960795 + 7899363 * 2 ^ 59
def prefixEnd_7899363 : Nat := 4983230072969 + 3 ^ 40 * 7899363 * 2
def baseEnd_7899363 : Nat := 450685564815809159959333

theorem tailTrace_7899363 : CollatzResearch.WordTrace tailWord_7899363 prefixEnd_7899363 450685564815809159959333 := by
  unfold tailWord_7899363
  simp only [CollatzResearch.WordTrace]
  refine ⟨288113438080964429637870743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192075625387309619758580495 288113438080964429637870743)
  ·
    refine ⟨432170157121446644456806115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288113438080964429637870743 432170157121446644456806115)
    ·
      refine ⟨648255235682169966685209173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432170157121446644456806115 648255235682169966685209173)
      ·
        refine ⟨7596741043150429297092295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 648255235682169966685209173 7596741043150429297092295)
        ·
          refine ⟨11395111564725643945638443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7596741043150429297092295 11395111564725643945638443)
          ·
            refine ⟨17092667347088465918457665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11395111564725643945638443 17092667347088465918457665)
            ·
              refine ⟨12819500510316349438843249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17092667347088465918457665 12819500510316349438843249)
              ·
                refine ⟨9614625382737262079132437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12819500510316349438843249 9614625382737262079132437)
                ·
                  refine ⟨450685564815809159959333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9614625382737262079132437 450685564815809159959333)
                  ·
                    rfl

theorem cell23_7899363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 2, 6].length) (baseStart_7899363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7899363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7899363 prefixEnd_7899363 := by exact prefixLift 7899363
  have htrace : WordTrace (prefixWord ++ tailWord_7899363) baseStart_7899363 baseEnd_7899363 := by
    simpa [prefixWord, tailWord_7899363, baseEnd_7899363] using wordTrace_append hprefix tailTrace_7899363
  have hstable : (prefixWord ++ tailWord_7899363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7899363).length < 2 ^ (prefixWord ++ tailWord_7899363).sum := by decide
  have hdescent : baseEnd_7899363 < baseStart_7899363 := by decide
  rcases family_descends (prefixWord ++ tailWord_7899363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7899367 : List Nat := [1, 1, 5, 3, 1, 3, 2, 2, 1, 4]
def baseStart_7899367 : Nat := 118140960795 + 7899367 * 2 ^ 59
def prefixEnd_7899367 : Nat := 4983230072969 + 3 ^ 40 * 7899367 * 2
def baseEnd_7899367 : Nat := 1352057379088300141327993

theorem tailTrace_7899367 : CollatzResearch.WordTrace tailWord_7899367 prefixEnd_7899367 1352057379088300141327993 := by
  unfold tailWord_7899367
  simp only [CollatzResearch.WordTrace]
  refine ⟨288113583972949938321016355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192075722648633292214010903 288113583972949938321016355)
  ·
    refine ⟨432170375959424907481524533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288113583972949938321016355 432170375959424907481524533)
    ·
      refine ⟨40515972746196085076392925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 432170375959424907481524533 40515972746196085076392925)
      ·
        refine ⟨15193489779823531903647347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40515972746196085076392925 15193489779823531903647347)
        ·
          refine ⟨22790234669735297855471021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15193489779823531903647347 22790234669735297855471021)
          ·
            refine ⟨8546338001150736695801633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22790234669735297855471021 8546338001150736695801633)
            ·
              refine ⟨6409753500863052521851225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8546338001150736695801633 6409753500863052521851225)
              ·
                refine ⟨4807315125647289391388419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6409753500863052521851225 4807315125647289391388419)
                ·
                  refine ⟨7210972688470934087082629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4807315125647289391388419 7210972688470934087082629)
                  ·
                    refine ⟨1352057379088300141327993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7210972688470934087082629 1352057379088300141327993)
                    ·
                      rfl

theorem cell23_7899367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 2, 2, 1, 4].length) (baseStart_7899367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7899367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7899367 prefixEnd_7899367 := by exact prefixLift 7899367
  have htrace : WordTrace (prefixWord ++ tailWord_7899367) baseStart_7899367 baseEnd_7899367 := by
    simpa [prefixWord, tailWord_7899367, baseEnd_7899367] using wordTrace_append hprefix tailTrace_7899367
  have hstable : (prefixWord ++ tailWord_7899367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7899367).length < 2 ^ (prefixWord ++ tailWord_7899367).sum := by decide
  have hdescent : baseEnd_7899367 < baseStart_7899367 := by decide
  rcases family_descends (prefixWord ++ tailWord_7899367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7899379 : List Nat := [1, 1, 1, 2, 2, 4, 1, 1, 5, 1, 4]
def baseStart_7899379 : Nat := 118140960795 + 7899379 * 2 ^ 59
def prefixEnd_7899379 : Nat := 4983230072969 + 3 ^ 40 * 7899379 * 2
def baseEnd_7899379 : Nat := 4056178299032754377033923

theorem tailTrace_7899379 : CollatzResearch.WordTrace tailWord_7899379 prefixEnd_7899379 4056178299032754377033923 := by
  unfold tailWord_7899379
  simp only [CollatzResearch.WordTrace]
  refine ⟨288114021648906464370453191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192076014432604309580302127 288114021648906464370453191)
  ·
    refine ⟨432171032473359696555679787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288114021648906464370453191 432171032473359696555679787)
    ·
      refine ⟨648256548710039544833519681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432171032473359696555679787 648256548710039544833519681)
      ·
        refine ⟨486192411532529658625139761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 648256548710039544833519681 486192411532529658625139761)
        ·
          refine ⟨364644308649397243968854821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 486192411532529658625139761 364644308649397243968854821)
          ·
            refine ⟨68370807871761983244160279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 364644308649397243968854821 68370807871761983244160279)
            ·
              refine ⟨102556211807642974866240419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68370807871761983244160279 102556211807642974866240419)
              ·
                refine ⟨153834317711464462299360629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102556211807642974866240419 153834317711464462299360629)
                ·
                  refine ⟨14421967285449793340565059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 153834317711464462299360629 14421967285449793340565059)
                  ·
                    refine ⟨21632950928174690010847589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14421967285449793340565059 21632950928174690010847589)
                    ·
                      refine ⟨4056178299032754377033923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21632950928174690010847589 4056178299032754377033923)
                      ·
                        rfl

theorem cell23_7899379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 5, 1, 4].length) (baseStart_7899379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7899379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7899379 prefixEnd_7899379 := by exact prefixLift 7899379
  have htrace : WordTrace (prefixWord ++ tailWord_7899379) baseStart_7899379 baseEnd_7899379 := by
    simpa [prefixWord, tailWord_7899379, baseEnd_7899379] using wordTrace_append hprefix tailTrace_7899379
  have hstable : (prefixWord ++ tailWord_7899379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7899379).length < 2 ^ (prefixWord ++ tailWord_7899379).sum := by decide
  have hdescent : baseEnd_7899379 < baseStart_7899379 := by decide
  rcases family_descends (prefixWord ++ tailWord_7899379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7899400 : List Nat := [2, 1, 3, 2, 3, 3, 1, 1, 2, 3, 2]
def baseStart_7899400 : Nat := 118140960795 + 7899400 * 2 ^ 59
def prefixEnd_7899400 : Nat := 4983230072969 + 3 ^ 40 * 7899400 * 2
def baseEnd_7899400 : Nat := 4056189082126498794871327

theorem tailTrace_7899400 : CollatzResearch.WordTrace tailWord_7899400 prefixEnd_7899400 4056189082126498794871327 := by
  unfold tailWord_7899400
  simp only [CollatzResearch.WordTrace]
  refine ⟨144057393790915192478483827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192076525054553589971311769 144057393790915192478483827)
  ·
    refine ⟨216086090686372788717725741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144057393790915192478483827 216086090686372788717725741)
    ·
      refine ⟨81032284007389795769147153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216086090686372788717725741 81032284007389795769147153)
      ·
        refine ⟨60774213005542346826860365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81032284007389795769147153 60774213005542346826860365)
        ·
          refine ⟨22790329877078380060072637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60774213005542346826860365 22790329877078380060072637)
          ·
            refine ⟨8546373703904392522527239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22790329877078380060072637 8546373703904392522527239)
            ·
              refine ⟨12819560555856588783790859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8546373703904392522527239 12819560555856588783790859)
              ·
                refine ⟨19229340833784883175686289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12819560555856588783790859 19229340833784883175686289)
                ·
                  refine ⟨14422005625338662381764717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19229340833784883175686289 14422005625338662381764717)
                  ·
                    refine ⟨5408252109501998393161769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14422005625338662381764717 5408252109501998393161769)
                    ·
                      refine ⟨4056189082126498794871327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5408252109501998393161769 4056189082126498794871327)
                      ·
                        rfl

theorem cell23_7899400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 1, 2, 3, 2].length) (baseStart_7899400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7899400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7899400 prefixEnd_7899400 := by exact prefixLift 7899400
  have htrace : WordTrace (prefixWord ++ tailWord_7899400) baseStart_7899400 baseEnd_7899400 := by
    simpa [prefixWord, tailWord_7899400, baseEnd_7899400] using wordTrace_append hprefix tailTrace_7899400
  have hstable : (prefixWord ++ tailWord_7899400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7899400).length < 2 ^ (prefixWord ++ tailWord_7899400).sum := by decide
  have hdescent : baseEnd_7899400 < baseStart_7899400 := by decide
  rcases family_descends (prefixWord ++ tailWord_7899400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7899406 : List Nat := [4, 1, 1, 2, 1, 2, 2, 2, 4, 4]
def baseStart_7899406 : Nat := 118140960795 + 7899406 * 2 ^ 59
def prefixEnd_7899406 : Nat := 4983230072969 + 3 ^ 40 * 7899406 * 2
def baseEnd_7899406 : Nat := 1352064054336808590465433

theorem tailTrace_7899406 : CollatzResearch.WordTrace tailWord_7899406 prefixEnd_7899406 1352064054336808590465433 := by
  unfold tailWord_7899406
  simp only [CollatzResearch.WordTrace]
  refine ⟨36014375802476080997710759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192076670946539098654457381 36014375802476080997710759)
  ·
    refine ⟨54021563703714121496566139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36014375802476080997710759 54021563703714121496566139)
    ·
      refine ⟨81032345555571182244849209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54021563703714121496566139 81032345555571182244849209)
      ·
        refine ⟨60774259166678386683636907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81032345555571182244849209 60774259166678386683636907)
        ·
          refine ⟨91161388750017580025455361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60774259166678386683636907 91161388750017580025455361)
          ·
            refine ⟨68371041562513185019091521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91161388750017580025455361 68371041562513185019091521)
            ·
              refine ⟨51278281171884888764318641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68371041562513185019091521 51278281171884888764318641)
              ·
                refine ⟨38458710878913666573238981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51278281171884888764318641 38458710878913666573238981)
                ·
                  refine ⟨7211008289796312482482309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38458710878913666573238981 7211008289796312482482309)
                  ·
                    refine ⟨1352064054336808590465433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7211008289796312482482309 1352064054336808590465433)
                    ·
                      rfl

theorem cell23_7899406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 4, 4].length) (baseStart_7899406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7899406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7899406 prefixEnd_7899406 := by exact prefixLift 7899406
  have htrace : WordTrace (prefixWord ++ tailWord_7899406) baseStart_7899406 baseEnd_7899406 := by
    simpa [prefixWord, tailWord_7899406, baseEnd_7899406] using wordTrace_append hprefix tailTrace_7899406
  have hstable : (prefixWord ++ tailWord_7899406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7899406).length < 2 ^ (prefixWord ++ tailWord_7899406).sum := by decide
  have hdescent : baseEnd_7899406 < baseStart_7899406 := by decide
  rcases family_descends (prefixWord ++ tailWord_7899406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7899413 : List Nat := [1, 3, 2, 1, 2, 1, 6, 1, 1, 1, 4]
def baseStart_7899413 : Nat := 118140960795 + 7899413 * 2 ^ 59
def prefixEnd_7899413 : Nat := 4983230072969 + 3 ^ 40 * 7899413 * 2
def baseEnd_7899413 : Nat := 4056195757375007244008767

theorem tailTrace_7899413 : CollatzResearch.WordTrace tailWord_7899413 prefixEnd_7899413 4056195757375007244008767 := by
  unfold tailWord_7899413
  simp only [CollatzResearch.WordTrace]
  refine ⟨288115261730783288177190893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192076841153855525451460595 288115261730783288177190893)
  ·
    refine ⟨108043223149043733066446585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288115261730783288177190893 108043223149043733066446585)
    ·
      refine ⟨81032417361782799799834939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108043223149043733066446585 81032417361782799799834939)
      ·
        refine ⟨121548626042674199699752409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81032417361782799799834939 121548626042674199699752409)
        ·
          refine ⟨91161469532005649774814307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121548626042674199699752409 91161469532005649774814307)
          ·
            refine ⟨136742204298008474662221461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91161469532005649774814307 136742204298008474662221461)
            ·
              refine ⟨6409790826469147249791631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 136742204298008474662221461 6409790826469147249791631)
              ·
                refine ⟨9614686239703720874687447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6409790826469147249791631 9614686239703720874687447)
                ·
                  refine ⟨14422029359555581312031171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9614686239703720874687447 14422029359555581312031171)
                  ·
                    refine ⟨21633044039333371968046757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14422029359555581312031171 21633044039333371968046757)
                    ·
                      refine ⟨4056195757375007244008767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21633044039333371968046757 4056195757375007244008767)
                      ·
                        rfl

theorem cell23_7899413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 6, 1, 1, 1, 4].length) (baseStart_7899413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7899413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7899413 prefixEnd_7899413 := by exact prefixLift 7899413
  have htrace : WordTrace (prefixWord ++ tailWord_7899413) baseStart_7899413 baseEnd_7899413 := by
    simpa [prefixWord, tailWord_7899413, baseEnd_7899413] using wordTrace_append hprefix tailTrace_7899413
  have hstable : (prefixWord ++ tailWord_7899413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7899413).length < 2 ^ (prefixWord ++ tailWord_7899413).sum := by decide
  have hdescent : baseEnd_7899413 < baseStart_7899413 := by decide
  rcases family_descends (prefixWord ++ tailWord_7899413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7899423 : List Nat := [1, 1, 2, 4, 3, 1, 3, 2, 2, 4]
def baseStart_7899423 : Nat := 118140960795 + 7899423 * 2 ^ 59
def prefixEnd_7899423 : Nat := 4983230072969 + 3 ^ 40 * 7899423 * 2
def baseEnd_7899423 : Nat := 1352066964060517401627907

theorem tailTrace_7899423 : CollatzResearch.WordTrace tailWord_7899423 prefixEnd_7899423 1352066964060517401627907 := by
  unfold tailWord_7899423
  simp only [CollatzResearch.WordTrace]
  refine ⟨288115626460747059885054923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192077084307164706590036615 288115626460747059885054923)
  ·
    refine ⟨432173439691120589827582385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288115626460747059885054923 432173439691120589827582385)
    ·
      refine ⟨324130079768340442370686789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432173439691120589827582385 324130079768340442370686789)
      ·
        refine ⟨60774389956563832944503773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 324130079768340442370686789 60774389956563832944503773)
        ·
          refine ⟨22790396233711437354188915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60774389956563832944503773 22790396233711437354188915)
          ·
            refine ⟨34185594350567156031283373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22790396233711437354188915 34185594350567156031283373)
            ·
              refine ⟨12819597881462683511731265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34185594350567156031283373 12819597881462683511731265)
              ·
                refine ⟨9614698411097012633798449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12819597881462683511731265 9614698411097012633798449)
                ·
                  refine ⟨7211023808322759475348837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9614698411097012633798449 7211023808322759475348837)
                  ·
                    refine ⟨1352066964060517401627907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7211023808322759475348837 1352066964060517401627907)
                    ·
                      rfl

theorem cell23_7899423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 2, 2, 4].length) (baseStart_7899423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7899423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7899423 prefixEnd_7899423 := by exact prefixLift 7899423
  have htrace : WordTrace (prefixWord ++ tailWord_7899423) baseStart_7899423 baseEnd_7899423 := by
    simpa [prefixWord, tailWord_7899423, baseEnd_7899423] using wordTrace_append hprefix tailTrace_7899423
  have hstable : (prefixWord ++ tailWord_7899423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7899423).length < 2 ^ (prefixWord ++ tailWord_7899423).sum := by decide
  have hdescent : baseEnd_7899423 < baseStart_7899423 := by decide
  rcases family_descends (prefixWord ++ tailWord_7899423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7899459 : List Nat := [1, 1, 1, 3, 1, 3, 3, 1, 2, 2, 5]
def baseStart_7899459 : Nat := 118140960795 + 7899459 * 2 ^ 59
def prefixEnd_7899459 : Nat := 4983230072969 + 3 ^ 40 * 7899459 * 2
def baseEnd_7899459 : Nat := 4056219377485114064033555

theorem tailTrace_7899459 : CollatzResearch.WordTrace tailWord_7899459 prefixEnd_7899459 4056219377485114064033555 := by
  unfold tailWord_7899459
  simp only [CollatzResearch.WordTrace]
  refine ⟨288116939488616638033365431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192077959659077758688910287 288116939488616638033365431)
  ·
    refine ⟨432175409232924957050048147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288116939488616638033365431 432175409232924957050048147)
    ·
      refine ⟨648263113849387435575072221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432175409232924957050048147 648263113849387435575072221)
      ·
        refine ⟨243098667693520288340652083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 648263113849387435575072221 243098667693520288340652083)
        ·
          refine ⟨364648001540280432510978125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243098667693520288340652083 364648001540280432510978125)
          ·
            refine ⟨136743000577605162191616797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 364648001540280432510978125 136743000577605162191616797)
            ·
              refine ⟨51278625216601935821856299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136743000577605162191616797 51278625216601935821856299)
              ·
                refine ⟨76917937824902903732784449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51278625216601935821856299 76917937824902903732784449)
                ·
                  refine ⟨57688453368677177799588337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76917937824902903732784449 57688453368677177799588337)
                  ·
                    refine ⟨43266340026507883349691253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57688453368677177799588337 43266340026507883349691253)
                    ·
                      refine ⟨4056219377485114064033555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43266340026507883349691253 4056219377485114064033555)
                      ·
                        rfl

theorem cell23_7899459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 2, 5].length) (baseStart_7899459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7899459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7899459 prefixEnd_7899459 := by exact prefixLift 7899459
  have htrace : WordTrace (prefixWord ++ tailWord_7899459) baseStart_7899459 baseEnd_7899459 := by
    simpa [prefixWord, tailWord_7899459, baseEnd_7899459] using wordTrace_append hprefix tailTrace_7899459
  have hstable : (prefixWord ++ tailWord_7899459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7899459).length < 2 ^ (prefixWord ++ tailWord_7899459).sum := by decide
  have hdescent : baseEnd_7899459 < baseStart_7899459 := by decide
  rcases family_descends (prefixWord ++ tailWord_7899459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7899503 : List Nat := [1, 1, 2, 1, 3, 1, 2, 2, 6, 2, 2]
def baseStart_7899503 : Nat := 118140960795 + 7899503 * 2 ^ 59
def prefixEnd_7899503 : Nat := 4983230072969 + 3 ^ 40 * 7899503 * 2
def baseEnd_7899503 : Nat := 4056241970633911891883353

theorem tailTrace_7899503 : CollatzResearch.WordTrace tailWord_7899503 prefixEnd_7899503 4056241970633911891883353 := by
  unfold tailWord_7899503
  simp only [CollatzResearch.WordTrace]
  refine ⟨288118544300457233547967163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192079029533638155698644775 288118544300457233547967163)
  ·
    refine ⟨432177816450685850321950745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288118544300457233547967163 432177816450685850321950745)
    ·
      refine ⟨324133362338014387741463059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432177816450685850321950745 324133362338014387741463059)
      ·
        refine ⟨486200043507021581612194589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324133362338014387741463059 486200043507021581612194589)
        ·
          refine ⟨182325016315133093104572971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 486200043507021581612194589 182325016315133093104572971)
          ·
            refine ⟨273487524472699639656859457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182325016315133093104572971 273487524472699639656859457)
            ·
              refine ⟨205115643354524729742644593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273487524472699639656859457 205115643354524729742644593)
              ·
                refine ⟨153836732515893547306983445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205115643354524729742644593 153836732515893547306983445)
                ·
                  refine ⟨7211096836682510030014849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 153836732515893547306983445 7211096836682510030014849)
                  ·
                    refine ⟨5408322627511882522511137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7211096836682510030014849 5408322627511882522511137)
                    ·
                      refine ⟨4056241970633911891883353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5408322627511882522511137 4056241970633911891883353)
                      ·
                        rfl

theorem cell23_7899503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 6, 2, 2].length) (baseStart_7899503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7899503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7899503 prefixEnd_7899503 := by exact prefixLift 7899503
  have htrace : WordTrace (prefixWord ++ tailWord_7899503) baseStart_7899503 baseEnd_7899503 := by
    simpa [prefixWord, tailWord_7899503, baseEnd_7899503] using wordTrace_append hprefix tailTrace_7899503
  have hstable : (prefixWord ++ tailWord_7899503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7899503).length < 2 ^ (prefixWord ++ tailWord_7899503).sum := by decide
  have hdescent : baseEnd_7899503 < baseStart_7899503 := by decide
  rcases family_descends (prefixWord ++ tailWord_7899503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7899506 : List Nat := [3, 2, 1, 2, 1, 3, 1, 2, 2, 1, 5]
def baseStart_7899506 : Nat := 118140960795 + 7899506 * 2 ^ 59
def prefixEnd_7899506 : Nat := 4983230072969 + 3 ^ 40 * 7899506 * 2
def baseEnd_7899506 : Nat := 4056243511075875380145839

theorem tailTrace_7899506 : CollatzResearch.WordTrace tailWord_7899506 prefixEnd_7899506 4056243511075875380145839 := by
  unfold tailWord_7899506
  simp only [CollatzResearch.WordTrace]
  refine ⟨72029663429861591265081593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192079102479630910040217581 72029663429861591265081593)
  ·
    refine ⟨54022247572396193448811195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72029663429861591265081593 54022247572396193448811195)
    ·
      refine ⟨81033371358594290173216793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54022247572396193448811195 81033371358594290173216793)
      ·
        refine ⟨60775028518945717629912595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81033371358594290173216793 60775028518945717629912595)
        ·
          refine ⟨91162542778418576444868893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60775028518945717629912595 91162542778418576444868893)
          ·
            refine ⟨34185953541906966166825835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91162542778418576444868893 34185953541906966166825835)
            ·
              refine ⟨51278930312860449250238753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34185953541906966166825835 51278930312860449250238753)
              ·
                refine ⟨38459197734645336937679065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51278930312860449250238753 38459197734645336937679065)
                ·
                  refine ⟨28844398300984002703259299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38459197734645336937679065 28844398300984002703259299)
                  ·
                    refine ⟨43266597451476004054888949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28844398300984002703259299 43266597451476004054888949)
                    ·
                      refine ⟨4056243511075875380145839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43266597451476004054888949 4056243511075875380145839)
                      ·
                        rfl

theorem cell23_7899506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_7899506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7899506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7899506 prefixEnd_7899506 := by exact prefixLift 7899506
  have htrace : WordTrace (prefixWord ++ tailWord_7899506) baseStart_7899506 baseEnd_7899506 := by
    simpa [prefixWord, tailWord_7899506, baseEnd_7899506] using wordTrace_append hprefix tailTrace_7899506
  have hstable : (prefixWord ++ tailWord_7899506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7899506).length < 2 ^ (prefixWord ++ tailWord_7899506).sum := by decide
  have hdescent : baseEnd_7899506 < baseStart_7899506 := by decide
  rcases family_descends (prefixWord ++ tailWord_7899506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7899550 : List Nat := [4, 3, 1, 2, 1, 2, 1, 1, 2, 2, 4]
def baseStart_7899550 : Nat := 118140960795 + 7899550 * 2 ^ 59
def prefixEnd_7899550 : Nat := 4983230072969 + 3 ^ 40 * 7899550 * 2
def baseEnd_7899550 : Nat := 4056266104224673207995637

theorem tailTrace_7899550 : CollatzResearch.WordTrace tailWord_7899550 prefixEnd_7899550 4056266104224673207995637 := by
  unfold tailWord_7899550
  simp only [CollatzResearch.WordTrace]
  refine ⟨36015032316410870071866013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192080172354191307049952069 36015032316410870071866013)
  ·
    refine ⟨13505637118654076276949755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36015032316410870071866013 13505637118654076276949755)
    ·
      refine ⟨20258455677981114415424633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13505637118654076276949755 20258455677981114415424633)
      ·
        refine ⟨15193841758485835811568475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20258455677981114415424633 15193841758485835811568475)
        ·
          refine ⟨22790762637728753717352713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15193841758485835811568475 22790762637728753717352713)
          ·
            refine ⟨17093071978296565288014535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22790762637728753717352713 17093071978296565288014535)
            ·
              refine ⟨25639607967444847932021803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17093071978296565288014535 25639607967444847932021803)
              ·
                refine ⟨38459411951167271898032705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25639607967444847932021803 38459411951167271898032705)
                ·
                  refine ⟨28844558963375453923524529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38459411951167271898032705 28844558963375453923524529)
                  ·
                    refine ⟨21633419222531590442643397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28844558963375453923524529 21633419222531590442643397)
                    ·
                      refine ⟨4056266104224673207995637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21633419222531590442643397 4056266104224673207995637)
                      ·
                        rfl

theorem cell23_7899550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_7899550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7899550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7899550 prefixEnd_7899550 := by exact prefixLift 7899550
  have htrace : WordTrace (prefixWord ++ tailWord_7899550) baseStart_7899550 baseEnd_7899550 := by
    simpa [prefixWord, tailWord_7899550, baseEnd_7899550] using wordTrace_append hprefix tailTrace_7899550
  have hstable : (prefixWord ++ tailWord_7899550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7899550).length < 2 ^ (prefixWord ++ tailWord_7899550).sum := by decide
  have hdescent : baseEnd_7899550 < baseStart_7899550 := by decide
  rcases family_descends (prefixWord ++ tailWord_7899550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7899556 : List Nat := [2, 3, 1, 2, 1, 1, 2, 2, 4, 5]
def baseStart_7899556 : Nat := 118140960795 + 7899556 * 2 ^ 59
def prefixEnd_7899556 : Nat := 4983230072969 + 3 ^ 40 * 7899556 * 2
def baseEnd_7899556 : Nat := 1352089728369533394840203

theorem tailTrace_7899556 : CollatzResearch.WordTrace tailWord_7899556 prefixEnd_7899556 1352089728369533394840203 := by
  unfold tailWord_7899556
  simp only [CollatzResearch.WordTrace]
  refine ⟨144060238684632611799823261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192080318246176815733097681 144060238684632611799823261)
  ·
    refine ⟨54022589506737229424933723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144060238684632611799823261 54022589506737229424933723)
    ·
      refine ⟨81033884260105844137400585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54022589506737229424933723 81033884260105844137400585)
      ·
        refine ⟨60775413195079383103050439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81033884260105844137400585 60775413195079383103050439)
        ·
          refine ⟨91163119792619074654575659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60775413195079383103050439 91163119792619074654575659)
          ·
            refine ⟨136744679688928611981863489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91163119792619074654575659 136744679688928611981863489)
            ·
              refine ⟨102558509766696458986397617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136744679688928611981863489 102558509766696458986397617)
              ·
                refine ⟨76918882325022344239798213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102558509766696458986397617 76918882325022344239798213)
                ·
                  refine ⟨14422290435941689544962165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76918882325022344239798213 14422290435941689544962165)
                  ·
                    refine ⟨1352089728369533394840203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14422290435941689544962165 1352089728369533394840203)
                    ·
                      rfl

theorem cell23_7899556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 4, 5].length) (baseStart_7899556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7899556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7899556 prefixEnd_7899556 := by exact prefixLift 7899556
  have htrace : WordTrace (prefixWord ++ tailWord_7899556) baseStart_7899556 baseEnd_7899556 := by
    simpa [prefixWord, tailWord_7899556, baseEnd_7899556] using wordTrace_append hprefix tailTrace_7899556
  have hstable : (prefixWord ++ tailWord_7899556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7899556).length < 2 ^ (prefixWord ++ tailWord_7899556).sum := by decide
  have hdescent : baseEnd_7899556 < baseStart_7899556 := by decide
  rcases family_descends (prefixWord ++ tailWord_7899556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7899573 : List Nat := [1, 3, 3, 2, 3, 1, 1, 1, 1, 7]
def baseStart_7899573 : Nat := 118140960795 + 7899573 * 2 ^ 59
def prefixEnd_7899573 : Nat := 4983230072969 + 3 ^ 40 * 7899573 * 2
def baseEnd_7899573 : Nat := 1352092638093242206002677

theorem tailTrace_7899573 : CollatzResearch.WordTrace tailWord_7899573 prefixEnd_7899573 1352092638093242206002677 := by
  unfold tailWord_7899573
  simp only [CollatzResearch.WordTrace]
  refine ⟨288121097410203635503015373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192080731606802423668676915 288121097410203635503015373)
  ·
    refine ⟨108045411528826363313630765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288121097410203635503015373 108045411528826363313630765)
    ·
      refine ⟨40517029323309886242611537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108045411528826363313630765 40517029323309886242611537)
      ·
        refine ⟨30387771992482414681958653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40517029323309886242611537 30387771992482414681958653)
        ·
          refine ⟨11395414497180905505734495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30387771992482414681958653 11395414497180905505734495)
          ·
            refine ⟨17093121745771358258601743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11395414497180905505734495 17093121745771358258601743)
            ·
              refine ⟨25639682618657037387902615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17093121745771358258601743 25639682618657037387902615)
              ·
                refine ⟨38459523927985556081853923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25639682618657037387902615 38459523927985556081853923)
                ·
                  refine ⟨57689285891978334122780885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38459523927985556081853923 57689285891978334122780885)
                  ·
                    refine ⟨1352092638093242206002677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57689285891978334122780885 1352092638093242206002677)
                    ·
                      rfl

theorem cell23_7899573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 7].length) (baseStart_7899573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7899573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7899573 prefixEnd_7899573 := by exact prefixLift 7899573
  have htrace : WordTrace (prefixWord ++ tailWord_7899573) baseStart_7899573 baseEnd_7899573 := by
    simpa [prefixWord, tailWord_7899573, baseEnd_7899573] using wordTrace_append hprefix tailTrace_7899573
  have hstable : (prefixWord ++ tailWord_7899573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7899573).length < 2 ^ (prefixWord ++ tailWord_7899573).sum := by decide
  have hdescent : baseEnd_7899573 < baseStart_7899573 := by decide
  rcases family_descends (prefixWord ++ tailWord_7899573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7899593 : List Nat := [1, 2, 1, 1, 2, 1, 5, 2, 2, 4, 2]
def baseStart_7899593 : Nat := 118140960795 + 7899593 * 2 ^ 59
def prefixEnd_7899593 : Nat := 4983230072969 + 3 ^ 40 * 7899593 * 2
def baseEnd_7899593 : Nat := 4056288183892816539757939

theorem tailTrace_7899593 : CollatzResearch.WordTrace tailWord_7899593 prefixEnd_7899593 4056288183892816539757939 := by
  unfold tailWord_7899593
  simp only [CollatzResearch.WordTrace]
  refine ⟨288121826870131178918743433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192081217913420785945828955 288121826870131178918743433)
  ·
    refine ⟨216091370152598384189057575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288121826870131178918743433 216091370152598384189057575)
    ·
      refine ⟨324137055228897576283586363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216091370152598384189057575 324137055228897576283586363)
      ·
        refine ⟨486205582843346364425379545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324137055228897576283586363 486205582843346364425379545)
        ·
          refine ⟨364654187132509773319034659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 486205582843346364425379545 364654187132509773319034659)
          ·
            refine ⟨546981280698764659978551989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364654187132509773319034659 546981280698764659978551989)
            ·
              refine ⟨51279495065509186872989249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 546981280698764659978551989 51279495065509186872989249)
              ·
                refine ⟨38459621299131890154741937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51279495065509186872989249 38459621299131890154741937)
                ·
                  refine ⟨28844715974348917616056453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38459621299131890154741937 28844715974348917616056453)
                  ·
                    refine ⟨5408384245190422053010585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28844715974348917616056453 5408384245190422053010585)
                    ·
                      refine ⟨4056288183892816539757939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5408384245190422053010585 4056288183892816539757939)
                      ·
                        rfl

theorem cell23_7899593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 2, 4, 2].length) (baseStart_7899593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7899593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7899593 prefixEnd_7899593 := by exact prefixLift 7899593
  have htrace : WordTrace (prefixWord ++ tailWord_7899593) baseStart_7899593 baseEnd_7899593 := by
    simpa [prefixWord, tailWord_7899593, baseEnd_7899593] using wordTrace_append hprefix tailTrace_7899593
  have hstable : (prefixWord ++ tailWord_7899593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7899593).length < 2 ^ (prefixWord ++ tailWord_7899593).sum := by decide
  have hdescent : baseEnd_7899593 < baseStart_7899593 := by decide
  rcases family_descends (prefixWord ++ tailWord_7899593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7899613 : List Nat := [1, 4, 3, 1, 1, 1, 1, 1, 3, 4, 3]
def baseStart_7899613 : Nat := 118140960795 + 7899613 * 2 ^ 59
def prefixEnd_7899613 : Nat := 4983230072969 + 3 ^ 40 * 7899613 * 2
def baseEnd_7899613 : Nat := 4056298453505906461507847

theorem tailTrace_7899613 : CollatzResearch.WordTrace tailWord_7899613 prefixEnd_7899613 4056298453505906461507847 := by
  unfold tailWord_7899613
  simp only [CollatzResearch.WordTrace]
  refine ⟨288122556330058722334471493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192081704220039148222980995 288122556330058722334471493)
  ·
    refine ⟨54022979311886010437713405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 288122556330058722334471493 54022979311886010437713405)
    ·
      refine ⟨20258617241957253914142527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54022979311886010437713405 20258617241957253914142527)
      ·
        refine ⟨30387925862935880871213791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20258617241957253914142527 30387925862935880871213791)
        ·
          refine ⟨45581888794403821306820687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30387925862935880871213791 45581888794403821306820687)
          ·
            refine ⟨68372833191605731960231031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45581888794403821306820687 68372833191605731960231031)
            ·
              refine ⟨102559249787408597940346547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68372833191605731960231031 102559249787408597940346547)
              ·
                refine ⟨153838874681112896910519821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102559249787408597940346547 153838874681112896910519821)
                ·
                  refine ⟨57689578005417336341444933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 153838874681112896910519821 57689578005417336341444933)
                  ·
                    refine ⟨10816795876015750564020925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57689578005417336341444933 10816795876015750564020925)
                    ·
                      refine ⟨4056298453505906461507847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10816795876015750564020925 4056298453505906461507847)
                      ·
                        rfl

theorem cell23_7899613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_7899613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7899613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7899613 prefixEnd_7899613 := by exact prefixLift 7899613
  have htrace : WordTrace (prefixWord ++ tailWord_7899613) baseStart_7899613 baseEnd_7899613 := by
    simpa [prefixWord, tailWord_7899613, baseEnd_7899613] using wordTrace_append hprefix tailTrace_7899613
  have hstable : (prefixWord ++ tailWord_7899613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7899613).length < 2 ^ (prefixWord ++ tailWord_7899613).sum := by decide
  have hdescent : baseEnd_7899613 < baseStart_7899613 := by decide
  rcases family_descends (prefixWord ++ tailWord_7899613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7899656 : List Nat := [2, 1, 3, 2, 1, 1, 1, 2, 2, 1, 7]
def baseStart_7899656 : Nat := 118140960795 + 7899656 * 2 ^ 59
def prefixEnd_7899656 : Nat := 4983230072969 + 3 ^ 40 * 7899656 * 2
def baseEnd_7899656 : Nat := 4056320533174049793270149

theorem tailTrace_7899656 : CollatzResearch.WordTrace tailWord_7899656 prefixEnd_7899656 4056320533174049793270149 := by
  unfold tailWord_7899656
  simp only [CollatzResearch.WordTrace]
  refine ⟨144062062334451470339143411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192082749779268627118857881 144062062334451470339143411)
  ·
    refine ⟨216093093501677205508715117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144062062334451470339143411 216093093501677205508715117)
    ·
      refine ⟨81034910063128952065768169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216093093501677205508715117 81034910063128952065768169)
      ·
        refine ⟨60776182547346714049326127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81034910063128952065768169 60776182547346714049326127)
        ·
          refine ⟨91164273821020071073989191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60776182547346714049326127 91164273821020071073989191)
          ·
            refine ⟨136746410731530106610983787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91164273821020071073989191 136746410731530106610983787)
            ·
              refine ⟨205119616097295159916475681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136746410731530106610983787 205119616097295159916475681)
              ·
                refine ⟨153839712072971369937356761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205119616097295159916475681 153839712072971369937356761)
                ·
                  refine ⟨115379784054728527453017571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153839712072971369937356761 115379784054728527453017571)
                  ·
                    refine ⟨173069676082092791179526357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 115379784054728527453017571 173069676082092791179526357)
                    ·
                      refine ⟨4056320533174049793270149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 173069676082092791179526357 4056320533174049793270149)
                      ·
                        rfl

theorem cell23_7899656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_7899656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7899656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7899656 prefixEnd_7899656 := by exact prefixLift 7899656
  have htrace : WordTrace (prefixWord ++ tailWord_7899656) baseStart_7899656 baseEnd_7899656 := by
    simpa [prefixWord, tailWord_7899656, baseEnd_7899656] using wordTrace_append hprefix tailTrace_7899656
  have hstable : (prefixWord ++ tailWord_7899656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7899656).length < 2 ^ (prefixWord ++ tailWord_7899656).sum := by decide
  have hdescent : baseEnd_7899656 < baseStart_7899656 := by decide
  rcases family_descends (prefixWord ++ tailWord_7899656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7899680 : List Nat := [2, 1, 1, 6, 2, 1, 1, 1, 3, 5]
def baseStart_7899680 : Nat := 118140960795 + 7899680 * 2 ^ 59
def prefixEnd_7899680 : Nat := 4983230072969 + 3 ^ 40 * 7899680 * 2
def baseEnd_7899680 : Nat := 1352110952236585899790013

theorem tailTrace_7899680 : CollatzResearch.WordTrace tailWord_7899680 prefixEnd_7899680 1352110952236585899790013 := by
  unfold tailWord_7899680
  simp only [CollatzResearch.WordTrace]
  refine ⟨144062500010407996388580247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192083333347210661851440329 144062500010407996388580247)
  ·
    refine ⟨216093750015611994582870371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144062500010407996388580247 216093750015611994582870371)
    ·
      refine ⟨324140625023417991874305557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216093750015611994582870371 324140625023417991874305557)
      ·
        refine ⟨15194091797972718369108073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 324140625023417991874305557 15194091797972718369108073)
        ·
          refine ⟨11395568848479538776831055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15194091797972718369108073 11395568848479538776831055)
          ·
            refine ⟨17093353272719308165246583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11395568848479538776831055 17093353272719308165246583)
            ·
              refine ⟨25640029909078962247869875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17093353272719308165246583 25640029909078962247869875)
              ·
                refine ⟨38460044863618443371804813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25640029909078962247869875 38460044863618443371804813)
                ·
                  refine ⟨14422516823856916264426805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38460044863618443371804813 14422516823856916264426805)
                  ·
                    refine ⟨1352110952236585899790013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14422516823856916264426805 1352110952236585899790013)
                    ·
                      rfl

theorem cell23_7899680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 3, 5].length) (baseStart_7899680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7899680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7899680 prefixEnd_7899680 := by exact prefixLift 7899680
  have htrace : WordTrace (prefixWord ++ tailWord_7899680) baseStart_7899680 baseEnd_7899680 := by
    simpa [prefixWord, tailWord_7899680, baseEnd_7899680] using wordTrace_append hprefix tailTrace_7899680
  have hstable : (prefixWord ++ tailWord_7899680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7899680).length < 2 ^ (prefixWord ++ tailWord_7899680).sum := by decide
  have hdescent : baseEnd_7899680 < baseStart_7899680 := by decide
  rcases family_descends (prefixWord ++ tailWord_7899680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7899706 : List Nat := [3, 1, 1, 1, 3, 14]
def baseStart_7899706 : Nat := 118140960795 + 7899706 * 2 ^ 59
def prefixEnd_7899706 : Nat := 4983230072969 + 3 ^ 40 * 7899706 * 2
def baseEnd_7899706 : Nat := 16692782745706891348333

theorem tailTrace_7899706 : CollatzResearch.WordTrace tailWord_7899706 prefixEnd_7899706 16692782745706891348333 := by
  unfold tailWord_7899706
  simp only [CollatzResearch.WordTrace]
  refine ⟨72031487079680449804401743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192083965545814532811737981 72031487079680449804401743)
  ·
    refine ⟨108047230619520674706602615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72031487079680449804401743 108047230619520674706602615)
    ·
      refine ⟨162070845929281012059903923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108047230619520674706602615 162070845929281012059903923)
      ·
        refine ⟨243106268893921518089855885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162070845929281012059903923 243106268893921518089855885)
        ·
          refine ⟨91164850835220569283695957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 243106268893921518089855885 91164850835220569283695957)
          ·
            refine ⟨16692782745706891348333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 91164850835220569283695957 16692782745706891348333)
            ·
              rfl

theorem cell23_7899706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 14].length) (baseStart_7899706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7899706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7899706 prefixEnd_7899706 := by exact prefixLift 7899706
  have htrace : WordTrace (prefixWord ++ tailWord_7899706) baseStart_7899706 baseEnd_7899706 := by
    simpa [prefixWord, tailWord_7899706, baseEnd_7899706] using wordTrace_append hprefix tailTrace_7899706
  have hstable : (prefixWord ++ tailWord_7899706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7899706).length < 2 ^ (prefixWord ++ tailWord_7899706).sum := by decide
  have hdescent : baseEnd_7899706 < baseStart_7899706 := by decide
  rcases family_descends (prefixWord ++ tailWord_7899706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7899730 : List Nat := [3, 2, 2, 1, 2, 1, 4, 1, 1, 2, 4]
def baseStart_7899730 : Nat := 118140960795 + 7899730 * 2 ^ 59
def prefixEnd_7899730 : Nat := 4983230072969 + 3 ^ 40 * 7899730 * 2
def baseEnd_7899730 : Nat := 4056358530742482503744809

theorem tailTrace_7899730 : CollatzResearch.WordTrace tailWord_7899730 prefixEnd_7899730 4056358530742482503744809 := by
  unfold tailWord_7899730
  simp only [CollatzResearch.WordTrace]
  refine ⟨72031705917658712829120161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192084549113756567544320429 72031705917658712829120161)
  ·
    refine ⟨54023779438244034621840121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72031705917658712829120161 54023779438244034621840121)
    ·
      refine ⟨40517834578683025966380091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54023779438244034621840121 40517834578683025966380091)
      ·
        refine ⟨60776751868024538949570137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40517834578683025966380091 60776751868024538949570137)
        ·
          refine ⟨45582563901018404212177603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60776751868024538949570137 45582563901018404212177603)
          ·
            refine ⟨68373845851527606318266405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45582563901018404212177603 68373845851527606318266405)
            ·
              refine ⟨12820096097161426184674951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68373845851527606318266405 12820096097161426184674951)
              ·
                refine ⟨19230144145742139277012427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12820096097161426184674951 19230144145742139277012427)
                ·
                  refine ⟨28845216218613208915518641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19230144145742139277012427 28845216218613208915518641)
                  ·
                    refine ⟨21633912163959906686638981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28845216218613208915518641 21633912163959906686638981)
                    ·
                      refine ⟨4056358530742482503744809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21633912163959906686638981 4056358530742482503744809)
                      ·
                        rfl

theorem cell23_7899730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 1, 1, 2, 4].length) (baseStart_7899730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7899730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7899730 prefixEnd_7899730 := by exact prefixLift 7899730
  have htrace : WordTrace (prefixWord ++ tailWord_7899730) baseStart_7899730 baseEnd_7899730 := by
    simpa [prefixWord, tailWord_7899730, baseEnd_7899730] using wordTrace_append hprefix tailTrace_7899730
  have hstable : (prefixWord ++ tailWord_7899730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7899730).length < 2 ^ (prefixWord ++ tailWord_7899730).sum := by decide
  have hdescent : baseEnd_7899730 < baseStart_7899730 := by decide
  rcases family_descends (prefixWord ++ tailWord_7899730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7899767 : List Nat := [1, 1, 3, 1, 1, 3, 5, 2, 2, 1, 3]
def baseStart_7899767 : Nat := 118140960795 + 7899767 * 2 ^ 59
def prefixEnd_7899767 : Nat := 4983230072969 + 3 ^ 40 * 7899767 * 2
def baseEnd_7899767 : Nat := 4056377529526698858982139

theorem tailTrace_7899767 : CollatzResearch.WordTrace tailWord_7899767 prefixEnd_7899767 4056377529526698858982139 := by
  unfold tailWord_7899767
  simp only [CollatzResearch.WordTrace]
  refine ⟨288128173171500806635577555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192085448781000537757051703 288128173171500806635577555)
  ·
    refine ⟨432192259757251209953366333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288128173171500806635577555 432192259757251209953366333)
    ·
      refine ⟨162072097408969203732512375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 432192259757251209953366333 162072097408969203732512375)
      ·
        refine ⟨243108146113453805598768563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162072097408969203732512375 243108146113453805598768563)
        ·
          refine ⟨364662219170180708398152845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243108146113453805598768563 364662219170180708398152845)
          ·
            refine ⟨136748332188817765649307317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 364662219170180708398152845 136748332188817765649307317)
            ·
              refine ⟨12820156142701665529622561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 136748332188817765649307317 12820156142701665529622561)
              ·
                refine ⟨9615117107026249147216921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12820156142701665529622561 9615117107026249147216921)
                ·
                  refine ⟨7211337830269686860412691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9615117107026249147216921 7211337830269686860412691)
                  ·
                    refine ⟨10817006745404530290619037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7211337830269686860412691 10817006745404530290619037)
                    ·
                      refine ⟨4056377529526698858982139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10817006745404530290619037 4056377529526698858982139)
                      ·
                        rfl

theorem cell23_7899767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 2, 2, 1, 3].length) (baseStart_7899767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7899767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7899767 prefixEnd_7899767 := by exact prefixLift 7899767
  have htrace : WordTrace (prefixWord ++ tailWord_7899767) baseStart_7899767 baseEnd_7899767 := by
    simpa [prefixWord, tailWord_7899767, baseEnd_7899767] using wordTrace_append hprefix tailTrace_7899767
  have hstable : (prefixWord ++ tailWord_7899767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7899767).length < 2 ^ (prefixWord ++ tailWord_7899767).sum := by decide
  have hdescent : baseEnd_7899767 < baseStart_7899767 := by decide
  rcases family_descends (prefixWord ++ tailWord_7899767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7899778 : List Nat := [3, 4, 3, 1, 2, 1, 1, 1, 1, 6]
def baseStart_7899778 : Nat := 118140960795 + 7899778 * 2 ^ 59
def prefixEnd_7899778 : Nat := 4983230072969 + 3 ^ 40 * 7899778 * 2
def baseEnd_7899778 : Nat := 1352127725937966105314863

theorem tailTrace_7899778 : CollatzResearch.WordTrace tailWord_7899778 prefixEnd_7899778 1352127725937966105314863 := by
  unfold tailWord_7899778
  simp only [CollatzResearch.WordTrace]
  refine ⟨72032143593615238878556997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192085716249640637009485325 72032143593615238878556997)
  ·
    refine ⟨13506026923802857289729437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72032143593615238878556997 13506026923802857289729437)
    ·
      refine ⟨5064760096426071483648539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13506026923802857289729437 5064760096426071483648539)
      ·
        refine ⟨7597140144639107225472809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5064760096426071483648539 7597140144639107225472809)
        ·
          refine ⟨5697855108479330419104607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7597140144639107225472809 5697855108479330419104607)
          ·
            refine ⟨8546782662718995628656911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5697855108479330419104607 8546782662718995628656911)
            ·
              refine ⟨12820173994078493442985367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8546782662718995628656911 12820173994078493442985367)
              ·
                refine ⟨19230260991117740164478051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12820173994078493442985367 19230260991117740164478051)
                ·
                  refine ⟨28845391486676610246717077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19230260991117740164478051 28845391486676610246717077)
                  ·
                    refine ⟨1352127725937966105314863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28845391486676610246717077 1352127725937966105314863)
                    ·
                      rfl

theorem cell23_7899778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_7899778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7899778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7899778 prefixEnd_7899778 := by exact prefixLift 7899778
  have htrace : WordTrace (prefixWord ++ tailWord_7899778) baseStart_7899778 baseEnd_7899778 := by
    simpa [prefixWord, tailWord_7899778, baseEnd_7899778] using wordTrace_append hprefix tailTrace_7899778
  have hstable : (prefixWord ++ tailWord_7899778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7899778).length < 2 ^ (prefixWord ++ tailWord_7899778).sum := by decide
  have hdescent : baseEnd_7899778 < baseStart_7899778 := by decide
  rcases family_descends (prefixWord ++ tailWord_7899778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7899783 : List Nat := [1, 1, 4, 2, 1, 2, 1, 3, 2, 6]
def baseStart_7899783 : Nat := 118140960795 + 7899783 * 2 ^ 59
def prefixEnd_7899783 : Nat := 4983230072969 + 3 ^ 40 * 7899783 * 2
def baseEnd_7899783 : Nat := 1352128581739056932127355

theorem tailTrace_7899783 : CollatzResearch.WordTrace tailWord_7899783 prefixEnd_7899783 1352128581739056932127355 := by
  unfold tailWord_7899783
  simp only [CollatzResearch.WordTrace]
  refine ⟨288128756739442841368160003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192085837826295227578773335 288128756739442841368160003)
  ·
    refine ⟨432193135109164262052240005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288128756739442841368160003 432193135109164262052240005)
    ·
      refine ⟨81036212832968299134795001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 432193135109164262052240005 81036212832968299134795001)
      ·
        refine ⟨60777159624726224351096251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81036212832968299134795001 60777159624726224351096251)
        ·
          refine ⟨91165739437089336526644377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60777159624726224351096251 91165739437089336526644377)
          ·
            refine ⟨68374304577817002394983283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91165739437089336526644377 68374304577817002394983283)
            ·
              refine ⟨102561456866725503592474925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68374304577817002394983283 102561456866725503592474925)
              ·
                refine ⟨38460546325022063847178097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102561456866725503592474925 38460546325022063847178097)
                ·
                  refine ⟨28845409743766547885383573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38460546325022063847178097 28845409743766547885383573)
                  ·
                    refine ⟨1352128581739056932127355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28845409743766547885383573 1352128581739056932127355)
                    ·
                      rfl

theorem cell23_7899783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 2, 6].length) (baseStart_7899783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7899783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7899783 prefixEnd_7899783 := by exact prefixLift 7899783
  have htrace : WordTrace (prefixWord ++ tailWord_7899783) baseStart_7899783 baseEnd_7899783 := by
    simpa [prefixWord, tailWord_7899783, baseEnd_7899783] using wordTrace_append hprefix tailTrace_7899783
  have hstable : (prefixWord ++ tailWord_7899783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7899783).length < 2 ^ (prefixWord ++ tailWord_7899783).sum := by decide
  have hdescent : baseEnd_7899783 < baseStart_7899783 := by decide
  rcases family_descends (prefixWord ++ tailWord_7899783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7899793 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 3]
def baseStart_7899793 : Nat := 118140960795 + 7899793 * 2 ^ 59
def prefixEnd_7899793 : Nat := 4983230072969 + 3 ^ 40 * 7899793 * 2
def baseEnd_7899793 : Nat := 4056390880023715757257019

theorem tailTrace_7899793 : CollatzResearch.WordTrace tailWord_7899793 prefixEnd_7899793 4056390880023715757257019 := by
  unfold tailWord_7899793
  simp only [CollatzResearch.WordTrace]
  refine ⟨288129121469406613076024033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192086080979604408717349355 288129121469406613076024033)
  ·
    refine ⟨216096841102054959807018025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288129121469406613076024033 216096841102054959807018025)
    ·
      refine ⟨162072630826541219855263519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216096841102054959807018025 162072630826541219855263519)
      ·
        refine ⟨243108946239811829782895279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162072630826541219855263519 243108946239811829782895279)
        ·
          refine ⟨364663419359717744674342919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243108946239811829782895279 364663419359717744674342919)
          ·
            refine ⟨546995129039576617011514379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364663419359717744674342919 546995129039576617011514379)
            ·
              refine ⟨820492693559364925517271569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 546995129039576617011514379 820492693559364925517271569)
              ·
                refine ⟨615369520169523694137953677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 820492693559364925517271569 615369520169523694137953677)
                ·
                  refine ⟨230763570063571385301732629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 615369520169523694137953677 230763570063571385301732629)
                  ·
                    refine ⟨10817042346729908686018717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 230763570063571385301732629 10817042346729908686018717)
                    ·
                      refine ⟨4056390880023715757257019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10817042346729908686018717 4056390880023715757257019)
                      ·
                        rfl

theorem cell23_7899793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 3].length) (baseStart_7899793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7899793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7899793 prefixEnd_7899793 := by exact prefixLift 7899793
  have htrace : WordTrace (prefixWord ++ tailWord_7899793) baseStart_7899793 baseEnd_7899793 := by
    simpa [prefixWord, tailWord_7899793, baseEnd_7899793] using wordTrace_append hprefix tailTrace_7899793
  have hstable : (prefixWord ++ tailWord_7899793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7899793).length < 2 ^ (prefixWord ++ tailWord_7899793).sum := by decide
  have hdescent : baseEnd_7899793 < baseStart_7899793 := by decide
  rcases family_descends (prefixWord ++ tailWord_7899793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7899794 : List Nat := [3, 2, 3, 1, 2, 1, 1, 4, 1, 3, 2]
def baseStart_7899794 : Nat := 118140960795 + 7899794 * 2 ^ 59
def prefixEnd_7899794 : Nat := 4983230072969 + 3 ^ 40 * 7899794 * 2
def baseEnd_7899794 : Nat := 4056391393504370253344515

theorem tailTrace_7899794 : CollatzResearch.WordTrace tailWord_7899794 prefixEnd_7899794 4056391393504370253344515 := by
  unfold tailWord_7899794
  simp only [CollatzResearch.WordTrace]
  refine ⟨72032289485600747561702609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192086105294935326831206957 72032289485600747561702609)
  ·
    refine ⟨54024217114200560671276957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72032289485600747561702609 54024217114200560671276957)
    ·
      refine ⟨20259081417825210251728859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54024217114200560671276957 20259081417825210251728859)
      ·
        refine ⟨30388622126737815377593289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20259081417825210251728859 30388622126737815377593289)
        ·
          refine ⟨22791466595053361533194967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30388622126737815377593289 22791466595053361533194967)
          ·
            refine ⟨34187199892580042299792451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22791466595053361533194967 34187199892580042299792451)
            ·
              refine ⟨51280799838870063449688677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34187199892580042299792451 51280799838870063449688677)
              ·
                refine ⟨9615149969788136896816627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51280799838870063449688677 9615149969788136896816627)
                ·
                  refine ⟨14422724954682205345224941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9615149969788136896816627 14422724954682205345224941)
                  ·
                    refine ⟨5408521858005827004459353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14422724954682205345224941 5408521858005827004459353)
                    ·
                      refine ⟨4056391393504370253344515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5408521858005827004459353 4056391393504370253344515)
                      ·
                        rfl

theorem cell23_7899794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 4, 1, 3, 2].length) (baseStart_7899794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7899794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7899794 prefixEnd_7899794 := by exact prefixLift 7899794
  have htrace : WordTrace (prefixWord ++ tailWord_7899794) baseStart_7899794 baseEnd_7899794 := by
    simpa [prefixWord, tailWord_7899794, baseEnd_7899794] using wordTrace_append hprefix tailTrace_7899794
  have hstable : (prefixWord ++ tailWord_7899794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7899794).length < 2 ^ (prefixWord ++ tailWord_7899794).sum := by decide
  have hdescent : baseEnd_7899794 < baseStart_7899794 := by decide
  rcases family_descends (prefixWord ++ tailWord_7899794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7899883 : List Nat := [1, 1, 1, 1, 2, 4, 1, 1, 1, 5, 5]
def baseStart_7899883 : Nat := 118140960795 + 7899883 * 2 ^ 59
def prefixEnd_7899883 : Nat := 4983230072969 + 3 ^ 40 * 7899883 * 2
def baseEnd_7899883 : Nat := 4056437093282620405131605

theorem tailTrace_7899883 : CollatzResearch.WordTrace tailWord_7899883 prefixEnd_7899883 4056437093282620405131605 := by
  unfold tailWord_7899883
  simp only [CollatzResearch.WordTrace]
  refine ⟨288132404039080558446800303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192088269359387038964533535 288132404039080558446800303)
  ·
    refine ⟨432198606058620837670200455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288132404039080558446800303 432198606058620837670200455)
    ·
      refine ⟨648297909087931256505300683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432198606058620837670200455 648297909087931256505300683)
      ·
        refine ⟨972446863631896884757951025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 648297909087931256505300683 972446863631896884757951025)
        ·
          refine ⟨729335147723922663568463269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 972446863631896884757951025 729335147723922663568463269)
          ·
            refine ⟨136750340198235499419086863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 729335147723922663568463269 136750340198235499419086863)
            ·
              refine ⟨205125510297353249128630295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136750340198235499419086863 205125510297353249128630295)
              ·
                refine ⟨307688265446029873692945443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205125510297353249128630295 307688265446029873692945443)
                ·
                  refine ⟨461532398169044810539418165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 307688265446029873692945443 461532398169044810539418165)
                  ·
                    refine ⟨43268662328347950988070453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 461532398169044810539418165 43268662328347950988070453)
                    ·
                      refine ⟨4056437093282620405131605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43268662328347950988070453 4056437093282620405131605)
                      ·
                        rfl

theorem cell23_7899883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 5, 5].length) (baseStart_7899883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7899883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7899883 prefixEnd_7899883 := by exact prefixLift 7899883
  have htrace : WordTrace (prefixWord ++ tailWord_7899883) baseStart_7899883 baseEnd_7899883 := by
    simpa [prefixWord, tailWord_7899883, baseEnd_7899883] using wordTrace_append hprefix tailTrace_7899883
  have hstable : (prefixWord ++ tailWord_7899883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7899883).length < 2 ^ (prefixWord ++ tailWord_7899883).sum := by decide
  have hdescent : baseEnd_7899883 < baseStart_7899883 := by decide
  rcases family_descends (prefixWord ++ tailWord_7899883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7899903 : List Nat := [1, 1, 2, 2, 1, 3, 1, 2, 10]
def baseStart_7899903 : Nat := 118140960795 + 7899903 * 2 ^ 59
def prefixEnd_7899903 : Nat := 4983230072969 + 3 ^ 40 * 7899903 * 2
def baseEnd_7899903 : Nat := 450716373655078925209057

theorem tailTrace_7899903 : CollatzResearch.WordTrace tailWord_7899903 prefixEnd_7899903 450716373655078925209057 := by
  unfold tailWord_7899903
  simp only [CollatzResearch.WordTrace]
  refine ⟨288133133499008101862528363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192088755666005401241685575 288133133499008101862528363)
  ·
    refine ⟨432199700248512152793792545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288133133499008101862528363 432199700248512152793792545)
    ·
      refine ⟨324149775186384114595344409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432199700248512152793792545 324149775186384114595344409)
      ·
        refine ⟨243112331389788085946508307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324149775186384114595344409 243112331389788085946508307)
        ·
          refine ⟨364668497084682128919762461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243112331389788085946508307 364668497084682128919762461)
          ·
            refine ⟨136750686406755798344910923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 364668497084682128919762461 136750686406755798344910923)
            ·
              refine ⟨205126029610133697517366385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136750686406755798344910923 205126029610133697517366385)
              ·
                refine ⟨153844522207600273138024789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205126029610133697517366385 153844522207600273138024789)
                ·
                  refine ⟨450716373655078925209057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 153844522207600273138024789 450716373655078925209057)
                  ·
                    rfl

theorem cell23_7899903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 10].length) (baseStart_7899903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7899903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7899903 prefixEnd_7899903 := by exact prefixLift 7899903
  have htrace : WordTrace (prefixWord ++ tailWord_7899903) baseStart_7899903 baseEnd_7899903 := by
    simpa [prefixWord, tailWord_7899903, baseEnd_7899903] using wordTrace_append hprefix tailTrace_7899903
  have hstable : (prefixWord ++ tailWord_7899903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7899903).length < 2 ^ (prefixWord ++ tailWord_7899903).sum := by decide
  have hdescent : baseEnd_7899903 < baseStart_7899903 := by decide
  rcases family_descends (prefixWord ++ tailWord_7899903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7899947 : List Nat := [1, 1, 1, 1, 2, 1, 2, 7, 3, 1, 3]
def baseStart_7899947 : Nat := 118140960795 + 7899947 * 2 ^ 59
def prefixEnd_7899947 : Nat := 4983230072969 + 3 ^ 40 * 7899947 * 2
def baseEnd_7899947 : Nat := 4056469956044508154731311

theorem tailTrace_7899947 : CollatzResearch.WordTrace tailWord_7899947 prefixEnd_7899947 4056469956044508154731311 := by
  unfold tailWord_7899947
  simp only [CollatzResearch.WordTrace]
  refine ⟨288134738310848697377130095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192089825540565798251420063 288134738310848697377130095)
  ·
    refine ⟨432202107466273046065695143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288134738310848697377130095 432202107466273046065695143)
    ·
      refine ⟨648303161199409569098542715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432202107466273046065695143 648303161199409569098542715)
      ·
        refine ⟨972454741799114353647814073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 648303161199409569098542715 972454741799114353647814073)
        ·
          refine ⟨729341056349335765235860555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 972454741799114353647814073 729341056349335765235860555)
          ·
            refine ⟨1094011584524003647853790833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 729341056349335765235860555 1094011584524003647853790833)
            ·
              refine ⟨820508688393002735890343125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1094011584524003647853790833 820508688393002735890343125)
              ·
                refine ⟨19230672384211001622429917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 820508688393002735890343125 19230672384211001622429917)
                ·
                  refine ⟨7211502144079125608411219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19230672384211001622429917 7211502144079125608411219)
                  ·
                    refine ⟨10817253216118688412616829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7211502144079125608411219 10817253216118688412616829)
                    ·
                      refine ⟨4056469956044508154731311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10817253216118688412616829 4056469956044508154731311)
                      ·
                        rfl

theorem cell23_7899947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 7, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 7, 3, 1, 3].length) (baseStart_7899947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7899947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7899947 prefixEnd_7899947 := by exact prefixLift 7899947
  have htrace : WordTrace (prefixWord ++ tailWord_7899947) baseStart_7899947 baseEnd_7899947 := by
    simpa [prefixWord, tailWord_7899947, baseEnd_7899947] using wordTrace_append hprefix tailTrace_7899947
  have hstable : (prefixWord ++ tailWord_7899947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7899947).length < 2 ^ (prefixWord ++ tailWord_7899947).sum := by decide
  have hdescent : baseEnd_7899947 < baseStart_7899947 := by decide
  rcases family_descends (prefixWord ++ tailWord_7899947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7899967 : List Nat := [1, 1, 2, 2, 5, 1, 1, 4, 1, 5]
def baseStart_7899967 : Nat := 118140960795 + 7899967 * 2 ^ 59
def prefixEnd_7899967 : Nat := 4983230072969 + 3 ^ 40 * 7899967 * 2
def baseEnd_7899967 : Nat := 1352160075219199358827073

theorem tailTrace_7899967 : CollatzResearch.WordTrace tailWord_7899967 prefixEnd_7899967 1352160075219199358827073 := by
  unfold tailWord_7899967
  simp only [CollatzResearch.WordTrace]
  refine ⟨288135467770776240792858155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192090311847184160528572103 288135467770776240792858155)
  ·
    refine ⟨432203201656164361189287233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288135467770776240792858155 432203201656164361189287233)
    ·
      refine ⟨324152401242123270891965425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432203201656164361189287233 324152401242123270891965425)
      ·
        refine ⟨243114300931592453168974069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324152401242123270891965425 243114300931592453168974069)
        ·
          refine ⟨22791965712336792484591319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 243114300931592453168974069 22791965712336792484591319)
          ·
            refine ⟨34187948568505188726886979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22791965712336792484591319 34187948568505188726886979)
            ·
              refine ⟨51281922852757783090330469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34187948568505188726886979 51281922852757783090330469)
              ·
                refine ⟨9615360534892084329436963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51281922852757783090330469 9615360534892084329436963)
                ·
                  refine ⟨14423040802338126494155445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9615360534892084329436963 14423040802338126494155445)
                  ·
                    refine ⟨1352160075219199358827073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14423040802338126494155445 1352160075219199358827073)
                    ·
                      rfl

theorem cell23_7899967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 4, 1, 5].length) (baseStart_7899967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7899967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7899967 prefixEnd_7899967 := by exact prefixLift 7899967
  have htrace : WordTrace (prefixWord ++ tailWord_7899967) baseStart_7899967 baseEnd_7899967 := by
    simpa [prefixWord, tailWord_7899967, baseEnd_7899967] using wordTrace_append hprefix tailTrace_7899967
  have hstable : (prefixWord ++ tailWord_7899967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7899967).length < 2 ^ (prefixWord ++ tailWord_7899967).sum := by decide
  have hdescent : baseEnd_7899967 < baseStart_7899967 := by decide
  rcases family_descends (prefixWord ++ tailWord_7899967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7900000 : List Nat := [2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 6]
def baseStart_7900000 : Nat := 118140960795 + 7900000 * 2 ^ 59
def prefixEnd_7900000 : Nat := 4983230072969 + 3 ^ 40 * 7900000 * 2
def baseEnd_7900000 : Nat := 4056497170519196447368567

theorem tailTrace_7900000 : CollatzResearch.WordTrace tailWord_7900000 prefixEnd_7900000 4056497170519196447368567 := by
  unfold tailWord_7900000
  simp only [CollatzResearch.WordTrace]
  refine ⟨144068335689828343714404727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192091114253104458285872969 144068335689828343714404727)
  ·
    refine ⟨216102503534742515571607091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144068335689828343714404727 216102503534742515571607091)
    ·
      refine ⟨324153755302113773357410637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216102503534742515571607091 324153755302113773357410637)
      ·
        refine ⟨121557658238292665009028989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 324153755302113773357410637 121557658238292665009028989)
        ·
          refine ⟨45584121839359749378385871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121557658238292665009028989 45584121839359749378385871)
          ·
            refine ⟨68376182759039624067578807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45584121839359749378385871 68376182759039624067578807)
            ·
              refine ⟨102564274138559436101368211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68376182759039624067578807 102564274138559436101368211)
              ·
                refine ⟨153846411207839154152052317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102564274138559436101368211 153846411207839154152052317)
                ·
                  refine ⟨57692404202939682807019619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 153846411207839154152052317 57692404202939682807019619)
                  ·
                    refine ⟨86538606304409524210529429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57692404202939682807019619 86538606304409524210529429)
                    ·
                      refine ⟨4056497170519196447368567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86538606304409524210529429 4056497170519196447368567)
                      ·
                        rfl

theorem cell23_7900000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_7900000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7900000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7900000 prefixEnd_7900000 := by exact prefixLift 7900000
  have htrace : WordTrace (prefixWord ++ tailWord_7900000) baseStart_7900000 baseEnd_7900000 := by
    simpa [prefixWord, tailWord_7900000, baseEnd_7900000] using wordTrace_append hprefix tailTrace_7900000
  have hstable : (prefixWord ++ tailWord_7900000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7900000).length < 2 ^ (prefixWord ++ tailWord_7900000).sum := by decide
  have hdescent : baseEnd_7900000 < baseStart_7900000 := by decide
  rcases family_descends (prefixWord ++ tailWord_7900000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7900007 : List Nat := [1, 1, 5, 1, 2, 2, 2, 2, 1, 1, 5]
def baseStart_7900007 : Nat := 118140960795 + 7900007 * 2 ^ 59
def prefixEnd_7900007 : Nat := 4983230072969 + 3 ^ 40 * 7900007 * 2
def baseEnd_7900007 : Nat := 4056500764883777919981035

theorem tailTrace_7900007 : CollatzResearch.WordTrace tailWord_7900007 prefixEnd_7900007 4056500764883777919981035 := by
  unfold tailWord_7900007
  simp only [CollatzResearch.WordTrace]
  refine ⟨288136926690631327624314275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192091284460420885082876183 288136926690631327624314275)
  ·
    refine ⟨432205390035946991436471413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288136926690631327624314275 432205390035946991436471413)
    ·
      refine ⟨40519255315870030447169195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 432205390035946991436471413 40519255315870030447169195)
      ·
        refine ⟨60778882973805045670753793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40519255315870030447169195 60778882973805045670753793)
        ·
          refine ⟨45584162230353784253065345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60778882973805045670753793 45584162230353784253065345)
          ·
            refine ⟨34188121672765338189799009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45584162230353784253065345 34188121672765338189799009)
            ·
              refine ⟨25641091254574003642349257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34188121672765338189799009 25641091254574003642349257)
              ·
                refine ⟨19230818440930502731761943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25641091254574003642349257 19230818440930502731761943)
                ·
                  refine ⟨28846227661395754097642915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19230818440930502731761943 28846227661395754097642915)
                  ·
                    refine ⟨43269341492093631146464373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28846227661395754097642915 43269341492093631146464373)
                    ·
                      refine ⟨4056500764883777919981035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43269341492093631146464373 4056500764883777919981035)
                      ·
                        rfl

theorem cell23_7900007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_7900007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7900007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7900007 prefixEnd_7900007 := by exact prefixLift 7900007
  have htrace : WordTrace (prefixWord ++ tailWord_7900007) baseStart_7900007 baseEnd_7900007 := by
    simpa [prefixWord, tailWord_7900007, baseEnd_7900007] using wordTrace_append hprefix tailTrace_7900007
  have hstable : (prefixWord ++ tailWord_7900007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7900007).length < 2 ^ (prefixWord ++ tailWord_7900007).sum := by decide
  have hdescent : baseEnd_7900007 < baseStart_7900007 := by decide
  rcases family_descends (prefixWord ++ tailWord_7900007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7900021 : List Nat := [1, 3, 4, 1, 1, 4, 1, 2, 1, 1, 4]
def baseStart_7900021 : Nat := 118140960795 + 7900021 * 2 ^ 59
def prefixEnd_7900021 : Nat := 4983230072969 + 3 ^ 40 * 7900021 * 2
def baseEnd_7900021 : Nat := 4056507953612940865205971

theorem tailTrace_7900021 : CollatzResearch.WordTrace tailWord_7900021 prefixEnd_7900021 4056507953612940865205971 := by
  unfold tailWord_7900021
  simp only [CollatzResearch.WordTrace]
  refine ⟨288137437312580608015323917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192091624875053738676882611 288137437312580608015323917)
  ·
    refine ⟨108051538992217728005746469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288137437312580608015323917 108051538992217728005746469)
    ·
      refine ⟨20259663561040824001077463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108051538992217728005746469 20259663561040824001077463)
      ·
        refine ⟨30389495341561236001616195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20259663561040824001077463 30389495341561236001616195)
        ·
          refine ⟨45584243012341854002424293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30389495341561236001616195 45584243012341854002424293)
          ·
            refine ⟨8547045564814097625454555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45584243012341854002424293 8547045564814097625454555)
            ·
              refine ⟨12820568347221146438181833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8547045564814097625454555 12820568347221146438181833)
              ·
                refine ⟨9615426260415859828636375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12820568347221146438181833 9615426260415859828636375)
                ·
                  refine ⟨14423139390623789742954563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9615426260415859828636375 14423139390623789742954563)
                  ·
                    refine ⟨21634709085935684614431845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14423139390623789742954563 21634709085935684614431845)
                    ·
                      refine ⟨4056507953612940865205971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21634709085935684614431845 4056507953612940865205971)
                      ·
                        rfl

theorem cell23_7900021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_7900021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7900021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7900021 prefixEnd_7900021 := by exact prefixLift 7900021
  have htrace : WordTrace (prefixWord ++ tailWord_7900021) baseStart_7900021 baseEnd_7900021 := by
    simpa [prefixWord, tailWord_7900021, baseEnd_7900021] using wordTrace_append hprefix tailTrace_7900021
  have hstable : (prefixWord ++ tailWord_7900021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7900021).length < 2 ^ (prefixWord ++ tailWord_7900021).sum := by decide
  have hdescent : baseEnd_7900021 < baseStart_7900021 := by decide
  rcases family_descends (prefixWord ++ tailWord_7900021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7900037 : List Nat := [1, 3, 1, 1, 3, 3, 1, 1, 3, 3, 3]
def baseStart_7900037 : Nat := 118140960795 + 7900037 * 2 ^ 59
def prefixEnd_7900037 : Nat := 4983230072969 + 3 ^ 40 * 7900037 * 2
def baseEnd_7900037 : Nat := 4056516169303412802605897

theorem tailTrace_7900037 : CollatzResearch.WordTrace tailWord_7900037 prefixEnd_7900037 4056516169303412802605897 := by
  unfold tailWord_7900037
  simp only [CollatzResearch.WordTrace]
  refine ⟨288138020880522642747906365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192092013920348428498604243 288138020880522642747906365)
  ·
    refine ⟨108051757830195991030464887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288138020880522642747906365 108051757830195991030464887)
    ·
      refine ⟨162077636745293986545697331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108051757830195991030464887 162077636745293986545697331)
      ·
        refine ⟨243116455117940979818545997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162077636745293986545697331 243116455117940979818545997)
        ·
          refine ⟨91168670669227867431954749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 243116455117940979818545997 91168670669227867431954749)
          ·
            refine ⟨34188251500960450286983031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91168670669227867431954749 34188251500960450286983031)
            ·
              refine ⟨51282377251440675430474547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34188251500960450286983031 51282377251440675430474547)
              ·
                refine ⟨76923565877161013145711821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51282377251440675430474547 76923565877161013145711821)
                ·
                  refine ⟨28846337203935379929641933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76923565877161013145711821 28846337203935379929641933)
                  ·
                    refine ⟨10817376451475767473615725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28846337203935379929641933 10817376451475767473615725)
                    ·
                      refine ⟨4056516169303412802605897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10817376451475767473615725 4056516169303412802605897)
                      ·
                        rfl

theorem cell23_7900037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 3, 3, 3].length) (baseStart_7900037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7900037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7900037 prefixEnd_7900037 := by exact prefixLift 7900037
  have htrace : WordTrace (prefixWord ++ tailWord_7900037) baseStart_7900037 baseEnd_7900037 := by
    simpa [prefixWord, tailWord_7900037, baseEnd_7900037] using wordTrace_append hprefix tailTrace_7900037
  have hstable : (prefixWord ++ tailWord_7900037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7900037).length < 2 ^ (prefixWord ++ tailWord_7900037).sum := by decide
  have hdescent : baseEnd_7900037 < baseStart_7900037 := by decide
  rcases family_descends (prefixWord ++ tailWord_7900037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7900041 : List Nat := [1, 2, 1, 1, 5, 3, 3, 1, 1, 2, 3]
def baseStart_7900041 : Nat := 118140960795 + 7900041 * 2 ^ 59
def prefixEnd_7900041 : Nat := 4983230072969 + 3 ^ 40 * 7900041 * 2
def baseEnd_7900041 : Nat := 4056518223226030786955879

theorem tailTrace_7900041 : CollatzResearch.WordTrace tailWord_7900041 prefixEnd_7900041 4056518223226030786955879 := by
  unfold tailWord_7900041
  simp only [CollatzResearch.WordTrace]
  refine ⟨288138166772508151431051977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192092111181672100954034651 288138166772508151431051977)
  ·
    refine ⟨216103625079381113573288983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288138166772508151431051977 216103625079381113573288983)
    ·
      refine ⟨324155437619071670359933475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216103625079381113573288983 324155437619071670359933475)
      ·
        refine ⟨486233156428607505539900213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324155437619071670359933475 486233156428607505539900213)
        ·
          refine ⟨45584358415181953644365645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 486233156428607505539900213 45584358415181953644365645)
          ·
            refine ⟨17094134405693232616637117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45584358415181953644365645 17094134405693232616637117)
            ·
              refine ⟨6410300402134962231238919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17094134405693232616637117 6410300402134962231238919)
              ·
                refine ⟨9615450603202443346858379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6410300402134962231238919 9615450603202443346858379)
                ·
                  refine ⟨14423175904803665020287569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9615450603202443346858379 14423175904803665020287569)
                  ·
                    refine ⟨10817381928602748765215677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14423175904803665020287569 10817381928602748765215677)
                    ·
                      refine ⟨4056518223226030786955879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10817381928602748765215677 4056518223226030786955879)
                      ·
                        rfl

theorem cell23_7900041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 3, 1, 1, 2, 3].length) (baseStart_7900041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7900041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7900041 prefixEnd_7900041 := by exact prefixLift 7900041
  have htrace : WordTrace (prefixWord ++ tailWord_7900041) baseStart_7900041 baseEnd_7900041 := by
    simpa [prefixWord, tailWord_7900041, baseEnd_7900041] using wordTrace_append hprefix tailTrace_7900041
  have hstable : (prefixWord ++ tailWord_7900041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7900041).length < 2 ^ (prefixWord ++ tailWord_7900041).sum := by decide
  have hdescent : baseEnd_7900041 < baseStart_7900041 := by decide
  rcases family_descends (prefixWord ++ tailWord_7900041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7900064 : List Nat := [2, 1, 1, 4, 1, 1, 3, 2, 3, 3, 2]
def baseStart_7900064 : Nat := 118140960795 + 7900064 * 2 ^ 59
def prefixEnd_7900064 : Nat := 4983230072969 + 3 ^ 40 * 7900064 * 2
def baseEnd_7900064 : Nat := 4056530033281084196968273

theorem tailTrace_7900064 : CollatzResearch.WordTrace tailWord_7900064 prefixEnd_7900064 4056530033281084196968273 := by
  unfold tailWord_7900064
  simp only [CollatzResearch.WordTrace]
  refine ⟨144069502825712413179569623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192092670434283217572759497 144069502825712413179569623)
  ·
    refine ⟨216104254238568619769354435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144069502825712413179569623 216104254238568619769354435)
    ·
      refine ⟨324156381357852929654031653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216104254238568619769354435 324156381357852929654031653)
      ·
        refine ⟨60779321504597424310130935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 324156381357852929654031653 60779321504597424310130935)
        ·
          refine ⟨91168982256896136465196403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60779321504597424310130935 91168982256896136465196403)
          ·
            refine ⟨136753473385344204697794605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91168982256896136465196403 136753473385344204697794605)
            ·
              refine ⟨51282552519504076761672977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136753473385344204697794605 51282552519504076761672977)
              ·
                refine ⟨38461914389628057571254733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51282552519504076761672977 38461914389628057571254733)
                ·
                  refine ⟨14423217896110521589220525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38461914389628057571254733 14423217896110521589220525)
                  ·
                    refine ⟨5408706711041445595957697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14423217896110521589220525 5408706711041445595957697)
                    ·
                      refine ⟨4056530033281084196968273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5408706711041445595957697 4056530033281084196968273)
                      ·
                        rfl

theorem cell23_7900064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 3, 3, 2].length) (baseStart_7900064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7900064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7900064 prefixEnd_7900064 := by exact prefixLift 7900064
  have htrace : WordTrace (prefixWord ++ tailWord_7900064) baseStart_7900064 baseEnd_7900064 := by
    simpa [prefixWord, tailWord_7900064, baseEnd_7900064] using wordTrace_append hprefix tailTrace_7900064
  have hstable : (prefixWord ++ tailWord_7900064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7900064).length < 2 ^ (prefixWord ++ tailWord_7900064).sum := by decide
  have hdescent : baseEnd_7900064 < baseStart_7900064 := by decide
  rcases family_descends (prefixWord ++ tailWord_7900064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7900071 : List Nat := [1, 1, 6, 1, 3, 1, 2, 1, 1, 3, 3]
def baseStart_7900071 : Nat := 118140960795 + 7900071 * 2 ^ 59
def prefixEnd_7900071 : Nat := 4983230072969 + 3 ^ 40 * 7900071 * 2
def baseEnd_7900071 : Nat := 4056533627645665669580741

theorem tailTrace_7900071 : CollatzResearch.WordTrace tailWord_7900071 prefixEnd_7900071 4056533627645665669580741 := by
  unfold tailWord_7900071
  simp only [CollatzResearch.WordTrace]
  refine ⟨288139260962399466554644067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192092840641599644369762711 288139260962399466554644067)
  ·
    refine ⟨432208891443599199831966101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288139260962399466554644067 432208891443599199831966101)
    ·
      refine ⟨20259791786418712492123411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 432208891443599199831966101 20259791786418712492123411)
      ·
        refine ⟨30389687679628068738185117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20259791786418712492123411 30389687679628068738185117)
        ·
          refine ⟨11396132879860525776819419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30389687679628068738185117 11396132879860525776819419)
          ·
            refine ⟨17094199319790788665229129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11396132879860525776819419 17094199319790788665229129)
            ·
              refine ⟨12820649489843091498921847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17094199319790788665229129 12820649489843091498921847)
              ·
                refine ⟨19230974234764637248382771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12820649489843091498921847 19230974234764637248382771)
                ·
                  refine ⟨28846461352146955872574157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19230974234764637248382771 28846461352146955872574157)
                  ·
                    refine ⟨10817423007055108452215309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28846461352146955872574157 10817423007055108452215309)
                    ·
                      refine ⟨4056533627645665669580741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10817423007055108452215309 4056533627645665669580741)
                      ·
                        rfl

theorem cell23_7900071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_7900071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7900071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7900071 prefixEnd_7900071 := by exact prefixLift 7900071
  have htrace : WordTrace (prefixWord ++ tailWord_7900071) baseStart_7900071 baseEnd_7900071 := by
    simpa [prefixWord, tailWord_7900071, baseEnd_7900071] using wordTrace_append hprefix tailTrace_7900071
  have hstable : (prefixWord ++ tailWord_7900071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7900071).length < 2 ^ (prefixWord ++ tailWord_7900071).sum := by decide
  have hdescent : baseEnd_7900071 < baseStart_7900071 := by decide
  rcases family_descends (prefixWord ++ tailWord_7900071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7900107 : List Nat := [1, 1, 1, 1, 3, 5, 1, 2, 2, 2, 4]
def baseStart_7900107 : Nat := 118140960795 + 7900107 * 2 ^ 59
def prefixEnd_7900107 : Nat := 4983230072969 + 3 ^ 40 * 7900107 * 2
def baseEnd_7900107 : Nat := 4056552112949227528730575

theorem tailTrace_7900107 : CollatzResearch.WordTrace tailWord_7900107 prefixEnd_7900107 4056552112949227528730575 := by
  unfold tailWord_7900107
  simp only [CollatzResearch.WordTrace]
  refine ⟨288140573990269044702954575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192093715993512696468636383 288140573990269044702954575)
  ·
    refine ⟨432210860985403567054431863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288140573990269044702954575 432210860985403567054431863)
    ·
      refine ⟨648316291478105350581647795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432210860985403567054431863 648316291478105350581647795)
      ·
        refine ⟨972474437217158025872471693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 648316291478105350581647795 972474437217158025872471693)
        ·
          refine ⟨364677913956434259702176885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 972474437217158025872471693 364677913956434259702176885)
          ·
            refine ⟨34188554433415711847079083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 364677913956434259702176885 34188554433415711847079083)
            ·
              refine ⟨51282831650123567770618625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34188554433415711847079083 51282831650123567770618625)
              ·
                refine ⟨38462123737592675827963969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51282831650123567770618625 38462123737592675827963969)
                ·
                  refine ⟨28846592803194506870972977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38462123737592675827963969 28846592803194506870972977)
                  ·
                    refine ⟨21634944602395880153229733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28846592803194506870972977 21634944602395880153229733)
                    ·
                      refine ⟨4056552112949227528730575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21634944602395880153229733 4056552112949227528730575)
                      ·
                        rfl

theorem cell23_7900107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 2, 2, 4].length) (baseStart_7900107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7900107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7900107 prefixEnd_7900107 := by exact prefixLift 7900107
  have htrace : WordTrace (prefixWord ++ tailWord_7900107) baseStart_7900107 baseEnd_7900107 := by
    simpa [prefixWord, tailWord_7900107, baseEnd_7900107] using wordTrace_append hprefix tailTrace_7900107
  have hstable : (prefixWord ++ tailWord_7900107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7900107).length < 2 ^ (prefixWord ++ tailWord_7900107).sum := by decide
  have hdescent : baseEnd_7900107 < baseStart_7900107 := by decide
  rcases family_descends (prefixWord ++ tailWord_7900107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7900111 : List Nat := [1, 1, 2, 1, 1, 7, 1, 1, 4, 2, 2]
def baseStart_7900111 : Nat := 118140960795 + 7900111 * 2 ^ 59
def prefixEnd_7900111 : Nat := 4983230072969 + 3 ^ 40 * 7900111 * 2
def baseEnd_7900111 : Nat := 4056554166871845513080557

theorem tailTrace_7900111 : CollatzResearch.WordTrace tailWord_7900111 prefixEnd_7900111 4056554166871845513080557 := by
  unfold tailWord_7900111
  simp only [CollatzResearch.WordTrace]
  refine ⟨288140719882254553386100187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192093813254836368924066791 288140719882254553386100187)
  ·
    refine ⟨432211079823381830079150281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288140719882254553386100187 432211079823381830079150281)
    ·
      refine ⟨324158309867536372559362711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432211079823381830079150281 324158309867536372559362711)
      ·
        refine ⟨486237464801304558839044067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324158309867536372559362711 486237464801304558839044067)
        ·
          refine ⟨729356197201956838258566101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486237464801304558839044067 729356197201956838258566101)
          ·
            refine ⟨17094285871920863396685143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 729356197201956838258566101 17094285871920863396685143)
            ·
              refine ⟨25641428807881295095027715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17094285871920863396685143 25641428807881295095027715)
              ·
                refine ⟨38462143211821942642541573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25641428807881295095027715 38462143211821942642541573)
                ·
                  refine ⟨7211651852216614245476545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38462143211821942642541573 7211651852216614245476545)
                  ·
                    refine ⟨5408738889162460684107409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7211651852216614245476545 5408738889162460684107409)
                    ·
                      refine ⟨4056554166871845513080557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5408738889162460684107409 4056554166871845513080557)
                      ·
                        rfl

theorem cell23_7900111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 4, 2, 2].length) (baseStart_7900111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7900111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7900111 prefixEnd_7900111 := by exact prefixLift 7900111
  have htrace : WordTrace (prefixWord ++ tailWord_7900111) baseStart_7900111 baseEnd_7900111 := by
    simpa [prefixWord, tailWord_7900111, baseEnd_7900111] using wordTrace_append hprefix tailTrace_7900111
  have hstable : (prefixWord ++ tailWord_7900111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7900111).length < 2 ^ (prefixWord ++ tailWord_7900111).sum := by decide
  have hdescent : baseEnd_7900111 < baseStart_7900111 := by decide
  rcases family_descends (prefixWord ++ tailWord_7900111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7900157 : List Nat := [1, 4, 1, 1, 1, 2, 1, 4, 1, 2, 5]
def baseStart_7900157 : Nat := 118140960795 + 7900157 * 2 ^ 59
def prefixEnd_7900157 : Nat := 4983230072969 + 3 ^ 40 * 7900157 * 2
def baseEnd_7900157 : Nat := 4056577786981952333105345

theorem tailTrace_7900157 : CollatzResearch.WordTrace tailWord_7900157 prefixEnd_7900157 4056577786981952333105345 := by
  unfold tailWord_7900157
  simp only [CollatzResearch.WordTrace]
  refine ⟨288142397640087903242274725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192094931760058602161516483 288142397640087903242274725)
  ·
    refine ⟨54026699557516481857926511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 288142397640087903242274725 54026699557516481857926511)
    ·
      refine ⟨81040049336274722786889767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54026699557516481857926511 81040049336274722786889767)
      ·
        refine ⟨121560074004412084180334651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81040049336274722786889767 121560074004412084180334651)
        ·
          refine ⟨182340111006618126270501977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121560074004412084180334651 182340111006618126270501977)
          ·
            refine ⟨136755083254963594702876483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182340111006618126270501977 136755083254963594702876483)
            ·
              refine ⟨205132624882445392054314725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136755083254963594702876483 205132624882445392054314725)
              ·
                refine ⟨38462367165458511010184011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 205132624882445392054314725 38462367165458511010184011)
                ·
                  refine ⟨57693550748187766515276017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38462367165458511010184011 57693550748187766515276017)
                  ·
                    refine ⟨43270163061140824886457013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57693550748187766515276017 43270163061140824886457013)
                    ·
                      refine ⟨4056577786981952333105345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43270163061140824886457013 4056577786981952333105345)
                      ·
                        rfl

theorem cell23_7900157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 2, 5].length) (baseStart_7900157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7900157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7900157 prefixEnd_7900157 := by exact prefixLift 7900157
  have htrace : WordTrace (prefixWord ++ tailWord_7900157) baseStart_7900157 baseEnd_7900157 := by
    simpa [prefixWord, tailWord_7900157, baseEnd_7900157] using wordTrace_append hprefix tailTrace_7900157
  have hstable : (prefixWord ++ tailWord_7900157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7900157).length < 2 ^ (prefixWord ++ tailWord_7900157).sum := by decide
  have hdescent : baseEnd_7900157 < baseStart_7900157 := by decide
  rcases family_descends (prefixWord ++ tailWord_7900157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7900174 : List Nat := [4, 1, 1, 2, 2, 3, 1, 1, 1, 2, 5]
def baseStart_7900174 : Nat := 118140960795 + 7900174 * 2 ^ 59
def prefixEnd_7900174 : Nat := 4983230072969 + 3 ^ 40 * 7900174 * 2
def baseEnd_7900174 : Nat := 4056586516153078766592767

theorem tailTrace_7900174 : CollatzResearch.WordTrace tailWord_7900174 prefixEnd_7900174 4056586516153078766592767 := by
  unfold tailWord_7900174
  simp only [CollatzResearch.WordTrace]
  refine ⟨36017877210128289393205447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192095345120684210097095717 36017877210128289393205447)
  ·
    refine ⟨54026815815192434089808171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36017877210128289393205447 54026815815192434089808171)
    ·
      refine ⟨81040223722788651134712257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54026815815192434089808171 81040223722788651134712257)
      ·
        refine ⟨60780167792091488351034193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81040223722788651134712257 60780167792091488351034193)
        ·
          refine ⟨45585125844068616263275645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60780167792091488351034193 45585125844068616263275645)
          ·
            refine ⟨17094422191525731098728367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45585125844068616263275645 17094422191525731098728367)
            ·
              refine ⟨25641633287288596648092551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17094422191525731098728367 25641633287288596648092551)
              ·
                refine ⟨38462449930932894972138827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25641633287288596648092551 38462449930932894972138827)
                ·
                  refine ⟨57693674896399342458208241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38462449930932894972138827 57693674896399342458208241)
                  ·
                    refine ⟨43270256172299506843656181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57693674896399342458208241 43270256172299506843656181)
                    ·
                      refine ⟨4056586516153078766592767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43270256172299506843656181 4056586516153078766592767)
                      ·
                        rfl

theorem cell23_7900174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_7900174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7900174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7900174 prefixEnd_7900174 := by exact prefixLift 7900174
  have htrace : WordTrace (prefixWord ++ tailWord_7900174) baseStart_7900174 baseEnd_7900174 := by
    simpa [prefixWord, tailWord_7900174, baseEnd_7900174] using wordTrace_append hprefix tailTrace_7900174
  have hstable : (prefixWord ++ tailWord_7900174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7900174).length < 2 ^ (prefixWord ++ tailWord_7900174).sum := by decide
  have hdescent : baseEnd_7900174 < baseStart_7900174 := by decide
  rcases family_descends (prefixWord ++ tailWord_7900174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7900211 : List Nat := [1, 1, 1, 2, 4, 1, 1, 7, 1, 4]
def baseStart_7900211 : Nat := 118140960795 + 7900211 * 2 ^ 59
def prefixEnd_7900211 : Nat := 4983230072969 + 3 ^ 40 * 7900211 * 2
def baseEnd_7900211 : Nat := 1352201838312431707276699

theorem tailTrace_7900211 : CollatzResearch.WordTrace tailWord_7900211 prefixEnd_7900211 1352201838312431707276699 := by
  unfold tailWord_7900211
  simp only [CollatzResearch.WordTrace]
  refine ⟨288144367181892270464740487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192096244787928180309826991 288144367181892270464740487)
  ·
    refine ⟨432216550772838405697110731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288144367181892270464740487 432216550772838405697110731)
    ·
      refine ⟨648324826159257608545666097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432216550772838405697110731 648324826159257608545666097)
      ·
        refine ⟨486243619619443206409249573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 648324826159257608545666097 486243619619443206409249573)
        ·
          refine ⟨91170678678645601201734295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 486243619619443206409249573 91170678678645601201734295)
          ·
            refine ⟨136756018017968401802601443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91170678678645601201734295 136756018017968401802601443)
            ·
              refine ⟨205134027026952602703902165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136756018017968401802601443 205134027026952602703902165)
              ·
                refine ⟨4807828758444201625872707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 205134027026952602703902165 4807828758444201625872707)
                ·
                  refine ⟨7211743137666302438809061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4807828758444201625872707 7211743137666302438809061)
                  ·
                    refine ⟨1352201838312431707276699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7211743137666302438809061 1352201838312431707276699)
                    ·
                      rfl

theorem cell23_7900211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 7, 1, 4].length) (baseStart_7900211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7900211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7900211 prefixEnd_7900211 := by exact prefixLift 7900211
  have htrace : WordTrace (prefixWord ++ tailWord_7900211) baseStart_7900211 baseEnd_7900211 := by
    simpa [prefixWord, tailWord_7900211, baseEnd_7900211] using wordTrace_append hprefix tailTrace_7900211
  have hstable : (prefixWord ++ tailWord_7900211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7900211).length < 2 ^ (prefixWord ++ tailWord_7900211).sum := by decide
  have hdescent : baseEnd_7900211 < baseStart_7900211 := by decide
  rcases family_descends (prefixWord ++ tailWord_7900211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7900221 : List Nat := [1, 4, 1, 3, 1, 2, 2, 2, 2, 2, 3]
def baseStart_7900221 : Nat := 118140960795 + 7900221 * 2 ^ 59
def prefixEnd_7900221 : Nat := 4983230072969 + 3 ^ 40 * 7900221 * 2
def baseEnd_7900221 : Nat := 4056610649743840082705051

theorem tailTrace_7900221 : CollatzResearch.WordTrace tailWord_7900221 prefixEnd_7900221 4056610649743840082705051 := by
  unfold tailWord_7900221
  simp only [CollatzResearch.WordTrace]
  refine ⟨288144731911856042172604517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192096487941237361448403011 288144731911856042172604517)
  ·
    refine ⟨54027137233473007907363347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 288144731911856042172604517 54027137233473007907363347)
    ·
      refine ⟨81040705850209511861045021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54027137233473007907363347 81040705850209511861045021)
      ·
        refine ⟨30390264693828566947891883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81040705850209511861045021 30390264693828566947891883)
        ·
          refine ⟨45585397040742850421837825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30390264693828566947891883 45585397040742850421837825)
          ·
            refine ⟨34189047780557137816378369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45585397040742850421837825 34189047780557137816378369)
            ·
              refine ⟨25641785835417853362283777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34189047780557137816378369 25641785835417853362283777)
              ·
                refine ⟨19231339376563390021712833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25641785835417853362283777 19231339376563390021712833)
                ·
                  refine ⟨14423504532422542516284625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19231339376563390021712833 14423504532422542516284625)
                  ·
                    refine ⟨10817628399316906887213469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14423504532422542516284625 10817628399316906887213469)
                    ·
                      refine ⟨4056610649743840082705051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10817628399316906887213469 4056610649743840082705051)
                      ·
                        rfl

theorem cell23_7900221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_7900221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7900221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7900221 prefixEnd_7900221 := by exact prefixLift 7900221
  have htrace : WordTrace (prefixWord ++ tailWord_7900221) baseStart_7900221 baseEnd_7900221 := by
    simpa [prefixWord, tailWord_7900221, baseEnd_7900221] using wordTrace_append hprefix tailTrace_7900221
  have hstable : (prefixWord ++ tailWord_7900221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7900221).length < 2 ^ (prefixWord ++ tailWord_7900221).sum := by decide
  have hdescent : baseEnd_7900221 < baseStart_7900221 := by decide
  rcases family_descends (prefixWord ++ tailWord_7900221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7900224 : List Nat := [2, 1, 1, 2, 2, 3, 4, 2, 6]
def baseStart_7900224 : Nat := 118140960795 + 7900224 * 2 ^ 59
def prefixEnd_7900224 : Nat := 4983230072969 + 3 ^ 40 * 7900224 * 2
def baseEnd_7900224 : Nat := 450734687798422618996393

theorem tailTrace_7900224 : CollatzResearch.WordTrace tailWord_7900224 prefixEnd_7900224 450734687798422618996393 := by
  unfold tailWord_7900224
  simp only [CollatzResearch.WordTrace]
  refine ⟨144072420665422586842481863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192096560887230115789975817 144072420665422586842481863)
  ·
    refine ⟨216108630998133880263722795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144072420665422586842481863 216108630998133880263722795)
    ·
      refine ⟨324162946497200820395584193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216108630998133880263722795 324162946497200820395584193)
      ·
        refine ⟨243122209872900615296688145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324162946497200820395584193 243122209872900615296688145)
        ·
          refine ⟨182341657404675461472516109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243122209872900615296688145 182341657404675461472516109)
          ·
            refine ⟨68378121526753298052193541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182341657404675461472516109 68378121526753298052193541)
            ·
              refine ⟨12820897786266243384786289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68378121526753298052193541 12820897786266243384786289)
              ·
                refine ⟨9615673339699682538589717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12820897786266243384786289 9615673339699682538589717)
                ·
                  refine ⟨450734687798422618996393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9615673339699682538589717 450734687798422618996393)
                  ·
                    rfl

theorem cell23_7900224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 2, 6].length) (baseStart_7900224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7900224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7900224 prefixEnd_7900224 := by exact prefixLift 7900224
  have htrace : WordTrace (prefixWord ++ tailWord_7900224) baseStart_7900224 baseEnd_7900224 := by
    simpa [prefixWord, tailWord_7900224, baseEnd_7900224] using wordTrace_append hprefix tailTrace_7900224
  have hstable : (prefixWord ++ tailWord_7900224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7900224).length < 2 ^ (prefixWord ++ tailWord_7900224).sum := by decide
  have hdescent : baseEnd_7900224 < baseStart_7900224 := by decide
  rcases family_descends (prefixWord ++ tailWord_7900224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7900227 : List Nat := [1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 6]
def baseStart_7900227 : Nat := 118140960795 + 7900227 * 2 ^ 59
def prefixEnd_7900227 : Nat := 4983230072969 + 3 ^ 40 * 7900227 * 2
def baseEnd_7900227 : Nat := 4056613730627767059230023

theorem tailTrace_7900227 : CollatzResearch.WordTrace tailWord_7900227 prefixEnd_7900227 4056613730627767059230023 := by
  unfold tailWord_7900227
  simp only [CollatzResearch.WordTrace]
  refine ⟨288144950749834305197322935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192096633833222870131548623 288144950749834305197322935)
  ·
    refine ⟨432217426124751457795984403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288144950749834305197322935 432217426124751457795984403)
    ·
      refine ⟨648326139187127186693976605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432217426124751457795984403 648326139187127186693976605)
      ·
        refine ⟨243122302195172695010241227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 648326139187127186693976605 243122302195172695010241227)
        ·
          refine ⟨364683453292759042515361841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243122302195172695010241227 364683453292759042515361841)
          ·
            refine ⟨273512589969569281886521381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 364683453292759042515361841 273512589969569281886521381)
            ·
              refine ⟨51283610619294240353722759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 273512589969569281886521381 51283610619294240353722759)
              ·
                refine ⟨76925415928941360530584139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51283610619294240353722759 76925415928941360530584139)
                ·
                  refine ⟨115388123893412040795876209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76925415928941360530584139 115388123893412040795876209)
                  ·
                    refine ⟨86541092920059030596907157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 115388123893412040795876209 86541092920059030596907157)
                    ·
                      refine ⟨4056613730627767059230023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86541092920059030596907157 4056613730627767059230023)
                      ·
                        rfl

theorem cell23_7900227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 6].length) (baseStart_7900227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7900227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7900227 prefixEnd_7900227 := by exact prefixLift 7900227
  have htrace : WordTrace (prefixWord ++ tailWord_7900227) baseStart_7900227 baseEnd_7900227 := by
    simpa [prefixWord, tailWord_7900227, baseEnd_7900227] using wordTrace_append hprefix tailTrace_7900227
  have hstable : (prefixWord ++ tailWord_7900227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7900227).length < 2 ^ (prefixWord ++ tailWord_7900227).sum := by decide
  have hdescent : baseEnd_7900227 < baseStart_7900227 := by decide
  rcases family_descends (prefixWord ++ tailWord_7900227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7900247 : List Nat := [1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 7]
def baseStart_7900247 : Nat := 118140960795 + 7900247 * 2 ^ 59
def prefixEnd_7900247 : Nat := 4983230072969 + 3 ^ 40 * 7900247 * 2
def baseEnd_7900247 : Nat := 4056624000240856980979931

theorem tailTrace_7900247 : CollatzResearch.WordTrace tailWord_7900247 prefixEnd_7900247 4056624000240856980979931 := by
  unfold tailWord_7900247
  simp only [CollatzResearch.WordTrace]
  refine ⟨288145680209761848613050995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192097120139841232408700663 288145680209761848613050995)
  ·
    refine ⟨432218520314642772919576493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288145680209761848613050995 432218520314642772919576493)
    ·
      refine ⟨162081945117991039844841185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 432218520314642772919576493 162081945117991039844841185)
      ·
        refine ⟨121561458838493279883630889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162081945117991039844841185 121561458838493279883630889)
        ·
          refine ⟨91171094128869959912723167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121561458838493279883630889 91171094128869959912723167)
          ·
            refine ⟨136756641193304939869084751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91171094128869959912723167 136756641193304939869084751)
            ·
              refine ⟨205134961789957409803627127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136756641193304939869084751 205134961789957409803627127)
              ·
                refine ⟨307702442684936114705440691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205134961789957409803627127 307702442684936114705440691)
                ·
                  refine ⟨461553664027404172058161037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 307702442684936114705440691 461553664027404172058161037)
                  ·
                    refine ⟨173082624010276564521810389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 461553664027404172058161037 173082624010276564521810389)
                    ·
                      refine ⟨4056624000240856980979931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 173082624010276564521810389 4056624000240856980979931)
                      ·
                        rfl

theorem cell23_7900247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_7900247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7900247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7900247 prefixEnd_7900247 := by exact prefixLift 7900247
  have htrace : WordTrace (prefixWord ++ tailWord_7900247) baseStart_7900247 baseEnd_7900247 := by
    simpa [prefixWord, tailWord_7900247, baseEnd_7900247] using wordTrace_append hprefix tailTrace_7900247
  have hstable : (prefixWord ++ tailWord_7900247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7900247).length < 2 ^ (prefixWord ++ tailWord_7900247).sum := by decide
  have hdescent : baseEnd_7900247 < baseStart_7900247 := by decide
  rcases family_descends (prefixWord ++ tailWord_7900247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7900261 : List Nat := [1, 3, 1, 3, 2, 1, 3, 1, 1, 5, 2]
def baseStart_7900261 : Nat := 118140960795 + 7900261 * 2 ^ 59
def prefixEnd_7900261 : Nat := 4983230072969 + 3 ^ 40 * 7900261 * 2
def baseEnd_7900261 : Nat := 4056631188970019926204867

theorem tailTrace_7900261 : CollatzResearch.WordTrace tailWord_7900261 prefixEnd_7900261 4056631188970019926204867 := by
  unfold tailWord_7900261
  simp only [CollatzResearch.WordTrace]
  refine ⟨288146190831711129004060637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192097460554474086002707091 288146190831711129004060637)
  ·
    refine ⟨108054821561891673376522739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288146190831711129004060637 108054821561891673376522739)
    ·
      refine ⟨162082232342837510064784109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108054821561891673376522739 162082232342837510064784109)
      ·
        refine ⟨60780837128564066274294041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162082232342837510064784109 60780837128564066274294041)
        ·
          refine ⟨45585627846423049705720531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60780837128564066274294041 45585627846423049705720531)
          ·
            refine ⟨68378441769634574558580797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45585627846423049705720531 68378441769634574558580797)
            ·
              refine ⟨25641915663612965459467799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68378441769634574558580797 25641915663612965459467799)
              ·
                refine ⟨38462873495419448189201699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25641915663612965459467799 38462873495419448189201699)
                ·
                  refine ⟨57694310243129172283802549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38462873495419448189201699 57694310243129172283802549)
                  ·
                    refine ⟨5408841585293359901606489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57694310243129172283802549 5408841585293359901606489)
                    ·
                      refine ⟨4056631188970019926204867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5408841585293359901606489 4056631188970019926204867)
                      ·
                        rfl

theorem cell23_7900261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 5, 2].length) (baseStart_7900261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7900261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7900261 prefixEnd_7900261 := by exact prefixLift 7900261
  have htrace : WordTrace (prefixWord ++ tailWord_7900261) baseStart_7900261 baseEnd_7900261 := by
    simpa [prefixWord, tailWord_7900261, baseEnd_7900261] using wordTrace_append hprefix tailTrace_7900261
  have hstable : (prefixWord ++ tailWord_7900261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7900261).length < 2 ^ (prefixWord ++ tailWord_7900261).sum := by decide
  have hdescent : baseEnd_7900261 < baseStart_7900261 := by decide
  rcases family_descends (prefixWord ++ tailWord_7900261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7900278 : List Nat := [5, 1, 1, 2, 1, 1, 2, 1, 4, 3, 2]
def baseStart_7900278 : Nat := 118140960795 + 7900278 * 2 ^ 59
def prefixEnd_7900278 : Nat := 4983230072969 + 3 ^ 40 * 7900278 * 2
def baseEnd_7900278 : Nat := 4056639918141146359692289

theorem tailTrace_7900278 : CollatzResearch.WordTrace tailWord_7900278 prefixEnd_7900278 4056639918141146359692289 := by
  unfold tailWord_7900278
  simp only [CollatzResearch.WordTrace]
  refine ⟨18009175679540596306714343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 192097873915099693938286325 18009175679540596306714343)
  ·
    refine ⟨27013763519310894460071515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18009175679540596306714343 27013763519310894460071515)
    ·
      refine ⟨40520645278966341690107273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27013763519310894460071515 40520645278966341690107273)
      ·
        refine ⟨30390483959224756267580455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40520645278966341690107273 30390483959224756267580455)
        ·
          refine ⟨45585725938837134401370683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30390483959224756267580455 45585725938837134401370683)
          ·
            refine ⟨68378588908255701602056025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45585725938837134401370683 68378588908255701602056025)
            ·
              refine ⟨51283941681191776201542019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68378588908255701602056025 51283941681191776201542019)
              ·
                refine ⟨76925912521787664302313029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51283941681191776201542019 76925912521787664302313029)
                ·
                  refine ⟨14423608597835187056683693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76925912521787664302313029 14423608597835187056683693)
                  ·
                    refine ⟨5408853224188195146256385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14423608597835187056683693 5408853224188195146256385)
                    ·
                      refine ⟨4056639918141146359692289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5408853224188195146256385 4056639918141146359692289)
                      ·
                        rfl

theorem cell23_7900278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 4, 3, 2].length) (baseStart_7900278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7900278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7900278 prefixEnd_7900278 := by exact prefixLift 7900278
  have htrace : WordTrace (prefixWord ++ tailWord_7900278) baseStart_7900278 baseEnd_7900278 := by
    simpa [prefixWord, tailWord_7900278, baseEnd_7900278] using wordTrace_append hprefix tailTrace_7900278
  have hstable : (prefixWord ++ tailWord_7900278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7900278).length < 2 ^ (prefixWord ++ tailWord_7900278).sum := by decide
  have hdescent : baseEnd_7900278 < baseStart_7900278 := by decide
  rcases family_descends (prefixWord ++ tailWord_7900278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7900304 : List Nat := [2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 4]
def baseStart_7900304 : Nat := 118140960795 + 7900304 * 2 ^ 59
def prefixEnd_7900304 : Nat := 4983230072969 + 3 ^ 40 * 7900304 * 2
def baseEnd_7900304 : Nat := 4056653268638163257967169

theorem tailTrace_7900304 : CollatzResearch.WordTrace tailWord_7900304 prefixEnd_7900304 4056653268638163257967169 := by
  unfold tailWord_7900304
  simp only [CollatzResearch.WordTrace]
  refine ⟨144073879585277673673937983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192098506113703564898583977 144073879585277673673937983)
  ·
    refine ⟨216110819377916510510906975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144073879585277673673937983 216110819377916510510906975)
    ·
      refine ⟨324166229066874765766360463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216110819377916510510906975 324166229066874765766360463)
      ·
        refine ⟨486249343600312148649540695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324166229066874765766360463 486249343600312148649540695)
        ·
          refine ⟨729374015400468222974311043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486249343600312148649540695 729374015400468222974311043)
          ·
            refine ⟨1094061023100702334461466565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 729374015400468222974311043 1094061023100702334461466565)
            ·
              refine ⟨205136441831381687711524981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1094061023100702334461466565 205136441831381687711524981)
              ·
                refine ⟨19231541421692033222955467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 205136441831381687711524981 19231541421692033222955467)
                ·
                  refine ⟨28847312132538049834433201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19231541421692033222955467 28847312132538049834433201)
                  ·
                    refine ⟨21635484099403537375824901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28847312132538049834433201 21635484099403537375824901)
                    ·
                      refine ⟨4056653268638163257967169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21635484099403537375824901 4056653268638163257967169)
                      ·
                        rfl

theorem cell23_7900304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 4].length) (baseStart_7900304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7900304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7900304 prefixEnd_7900304 := by exact prefixLift 7900304
  have htrace : WordTrace (prefixWord ++ tailWord_7900304) baseStart_7900304 baseEnd_7900304 := by
    simpa [prefixWord, tailWord_7900304, baseEnd_7900304] using wordTrace_append hprefix tailTrace_7900304
  have hstable : (prefixWord ++ tailWord_7900304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7900304).length < 2 ^ (prefixWord ++ tailWord_7900304).sum := by decide
  have hdescent : baseEnd_7900304 < baseStart_7900304 := by decide
  rcases family_descends (prefixWord ++ tailWord_7900304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7900318 : List Nat := [4, 3, 1, 1, 2, 1, 1, 2, 4, 4]
def baseStart_7900318 : Nat := 118140960795 + 7900318 * 2 ^ 59
def prefixEnd_7900318 : Nat := 4983230072969 + 3 ^ 40 * 7900318 * 2
def baseEnd_7900318 : Nat := 1352220152455775401064035

theorem tailTrace_7900318 : CollatzResearch.WordTrace tailWord_7900318 prefixEnd_7900318 1352220152455775401064035 := by
  unfold tailWord_7900318
  simp only [CollatzResearch.WordTrace]
  refine ⟨36018533724063078467360701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192098846528336418492590405 36018533724063078467360701)
  ·
    refine ⟨13506950146523654425260263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36018533724063078467360701 13506950146523654425260263)
    ·
      refine ⟨20260425219785481637890395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13506950146523654425260263 20260425219785481637890395)
      ·
        refine ⟨30390637829678222456835593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20260425219785481637890395 30390637829678222456835593)
        ·
          refine ⟨22792978372258666842626695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30390637829678222456835593 22792978372258666842626695)
          ·
            refine ⟨34189467558388000263940043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22792978372258666842626695 34189467558388000263940043)
            ·
              refine ⟨51284201337582000395910065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34189467558388000263940043 51284201337582000395910065)
              ·
                refine ⟨38463151003186500296932549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51284201337582000395910065 38463151003186500296932549)
                ·
                  refine ⟨7211840813097468805674853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38463151003186500296932549 7211840813097468805674853)
                  ·
                    refine ⟨1352220152455775401064035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7211840813097468805674853 1352220152455775401064035)
                    ·
                      rfl

theorem cell23_7900318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_7900318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7900318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7900318 prefixEnd_7900318 := by exact prefixLift 7900318
  have htrace : WordTrace (prefixWord ++ tailWord_7900318) baseStart_7900318 baseEnd_7900318 := by
    simpa [prefixWord, tailWord_7900318, baseEnd_7900318] using wordTrace_append hprefix tailTrace_7900318
  have hstable : (prefixWord ++ tailWord_7900318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7900318).length < 2 ^ (prefixWord ++ tailWord_7900318).sum := by decide
  have hdescent : baseEnd_7900318 < baseStart_7900318 := by decide
  rcases family_descends (prefixWord ++ tailWord_7900318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7900319 : List Nat := [1, 1, 2, 6, 3, 1, 1, 3, 1, 1, 3]
def baseStart_7900319 : Nat := 118140960795 + 7900319 * 2 ^ 59
def prefixEnd_7900319 : Nat := 4983230072969 + 3 ^ 40 * 7900319 * 2
def baseEnd_7900319 : Nat := 4056660970847980699279601

theorem tailTrace_7900319 : CollatzResearch.WordTrace tailWord_7900319 prefixEnd_7900319 4056660970847980699279601 := by
  unfold tailWord_7900319
  simp only [CollatzResearch.WordTrace]
  refine ⟨288148306265501004909672011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192098870843667336606448007 288148306265501004909672011)
  ·
    refine ⟨432222459398251507364508017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288148306265501004909672011 432222459398251507364508017)
    ·
      refine ⟨324166844548688630523381013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432222459398251507364508017 324166844548688630523381013)
      ·
        refine ⟨15195320838219779555783485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 324166844548688630523381013 15195320838219779555783485)
        ·
          refine ⟨5698245314332417333418807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15195320838219779555783485 5698245314332417333418807)
          ·
            refine ⟨8547367971498626000128211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5698245314332417333418807 8547367971498626000128211)
            ·
              refine ⟨12821051957247939000192317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8547367971498626000128211 12821051957247939000192317)
              ·
                refine ⟨4807894483967977125072119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12821051957247939000192317 4807894483967977125072119)
                ·
                  refine ⟨7211841725951965687608179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4807894483967977125072119 7211841725951965687608179)
                  ·
                    refine ⟨10817762588927948531412269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7211841725951965687608179 10817762588927948531412269)
                    ·
                      refine ⟨4056660970847980699279601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10817762588927948531412269 4056660970847980699279601)
                      ·
                        rfl

theorem cell23_7900319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_7900319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7900319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7900319 prefixEnd_7900319 := by exact prefixLift 7900319
  have htrace : WordTrace (prefixWord ++ tailWord_7900319) baseStart_7900319 baseEnd_7900319 := by
    simpa [prefixWord, tailWord_7900319, baseEnd_7900319] using wordTrace_append hprefix tailTrace_7900319
  have hstable : (prefixWord ++ tailWord_7900319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7900319).length < 2 ^ (prefixWord ++ tailWord_7900319).sum := by decide
  have hdescent : baseEnd_7900319 < baseStart_7900319 := by decide
  rcases family_descends (prefixWord ++ tailWord_7900319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7900352 : List Nat := [2, 1, 1, 2, 7, 1, 2, 1, 2, 4]
def baseStart_7900352 : Nat := 118140960795 + 7900352 * 2 ^ 59
def prefixEnd_7900352 : Nat := 4983230072969 + 3 ^ 40 * 7900352 * 2
def baseEnd_7900352 : Nat := 1352225971903193023388983

theorem tailTrace_7900352 : CollatzResearch.WordTrace tailWord_7900352 prefixEnd_7900352 1352225971903193023388983 := by
  unfold tailWord_7900352
  simp only [CollatzResearch.WordTrace]
  refine ⟨144074754937190725772811655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192099673249587634363748873 144074754937190725772811655)
  ·
    refine ⟨216112132405786088659217483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144074754937190725772811655 216112132405786088659217483)
    ·
      refine ⟨324168198608679132988826225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216112132405786088659217483 324168198608679132988826225)
      ·
        refine ⟨243126148956509349741619669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324168198608679132988826225 243126148956509349741619669)
        ·
          refine ⟨5698269116168187884569211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 243126148956509349741619669 5698269116168187884569211)
          ·
            refine ⟨8547403674252281826853817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5698269116168187884569211 8547403674252281826853817)
            ·
              refine ⟨6410552755689211370140363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8547403674252281826853817 6410552755689211370140363)
              ·
                refine ⟨9615829133533817055210545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6410552755689211370140363 9615829133533817055210545)
                ·
                  refine ⟨7211871850150362791407909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9615829133533817055210545 7211871850150362791407909)
                  ·
                    refine ⟨1352225971903193023388983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7211871850150362791407909 1352225971903193023388983)
                    ·
                      rfl

theorem cell23_7900352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 2, 1, 2, 4].length) (baseStart_7900352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7900352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7900352 prefixEnd_7900352 := by exact prefixLift 7900352
  have htrace : WordTrace (prefixWord ++ tailWord_7900352) baseStart_7900352 baseEnd_7900352 := by
    simpa [prefixWord, tailWord_7900352, baseEnd_7900352] using wordTrace_append hprefix tailTrace_7900352
  have hstable : (prefixWord ++ tailWord_7900352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7900352).length < 2 ^ (prefixWord ++ tailWord_7900352).sum := by decide
  have hdescent : baseEnd_7900352 < baseStart_7900352 := by decide
  rcases family_descends (prefixWord ++ tailWord_7900352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7900415 : List Nat := [1, 1, 2, 2, 1, 5, 2, 3, 2, 2, 2]
def baseStart_7900415 : Nat := 118140960795 + 7900415 * 2 ^ 59
def prefixEnd_7900415 : Nat := 4983230072969 + 3 ^ 40 * 7900415 * 2
def baseEnd_7900415 : Nat := 4056710264990812323679159

theorem tailTrace_7900415 : CollatzResearch.WordTrace tailWord_7900415 prefixEnd_7900415 4056710264990812323679159 := by
  unfold tailWord_7900415
  simp only [CollatzResearch.WordTrace]
  refine ⟨288151807673153213305166699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192101205115435475536777799 288151807673153213305166699)
  ·
    refine ⟨432227711509729819957750049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288151807673153213305166699 432227711509729819957750049)
    ·
      refine ⟨324170783632297364968312537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432227711509729819957750049 324170783632297364968312537)
      ·
        refine ⟨243128087724223023726234403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324170783632297364968312537 243128087724223023726234403)
        ·
          refine ⟨364692131586334535589351605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243128087724223023726234403 364692131586334535589351605)
          ·
            refine ⟨34189887336218862711501713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 364692131586334535589351605 34189887336218862711501713)
            ·
              refine ⟨25642415502164147033626285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34189887336218862711501713 25642415502164147033626285)
              ·
                refine ⟨9615905813311555137609857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25642415502164147033626285 9615905813311555137609857)
                ·
                  refine ⟨7211929359983666353207393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9615905813311555137609857 7211929359983666353207393)
                  ·
                    refine ⟨5408947019987749764905545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7211929359983666353207393 5408947019987749764905545)
                    ·
                      refine ⟨4056710264990812323679159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5408947019987749764905545 4056710264990812323679159)
                      ·
                        rfl

theorem cell23_7900415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 3, 2, 2, 2].length) (baseStart_7900415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7900415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7900415 prefixEnd_7900415 := by exact prefixLift 7900415
  have htrace : WordTrace (prefixWord ++ tailWord_7900415) baseStart_7900415 baseEnd_7900415 := by
    simpa [prefixWord, tailWord_7900415, baseEnd_7900415] using wordTrace_append hprefix tailTrace_7900415
  have hstable : (prefixWord ++ tailWord_7900415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7900415).length < 2 ^ (prefixWord ++ tailWord_7900415).sum := by decide
  have hdescent : baseEnd_7900415 < baseStart_7900415 := by decide
  rcases family_descends (prefixWord ++ tailWord_7900415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7900511 : List Nat := [1, 1, 2, 3, 1, 2, 1, 6, 6]
def baseStart_7900511 : Nat := 118140960795 + 7900511 * 2 ^ 59
def prefixEnd_7900511 : Nat := 4983230072969 + 3 ^ 40 * 7900511 * 2
def baseEnd_7900511 : Nat := 450751062125960438675413

theorem tailTrace_7900511 : CollatzResearch.WordTrace tailWord_7900511 prefixEnd_7900511 450751062125960438675413 := by
  unfold tailWord_7900511
  simp only [CollatzResearch.WordTrace]
  refine ⟨288155309080805421700661387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192103539387203614467107591 288155309080805421700661387)
  ·
    refine ⟨432232963621208132550992081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288155309080805421700661387 432232963621208132550992081)
    ·
      refine ⟨324174722715906099413244061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432232963621208132550992081 324174722715906099413244061)
      ·
        refine ⟨121565521018464787279966523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 324174722715906099413244061 121565521018464787279966523)
        ·
          refine ⟨182348281527697180919949785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121565521018464787279966523 182348281527697180919949785)
          ·
            refine ⟨136761211145772885689962339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182348281527697180919949785 136761211145772885689962339)
            ·
              refine ⟨205141816718659328534943509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136761211145772885689962339 205141816718659328534943509)
              ·
                refine ⟨9616022658687156025075477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 205141816718659328534943509 9616022658687156025075477)
                ·
                  refine ⟨450751062125960438675413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9616022658687156025075477 450751062125960438675413)
                  ·
                    rfl

theorem cell23_7900511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 6, 6].length) (baseStart_7900511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7900511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7900511 prefixEnd_7900511 := by exact prefixLift 7900511
  have htrace : WordTrace (prefixWord ++ tailWord_7900511) baseStart_7900511 baseEnd_7900511 := by
    simpa [prefixWord, tailWord_7900511, baseEnd_7900511] using wordTrace_append hprefix tailTrace_7900511
  have hstable : (prefixWord ++ tailWord_7900511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7900511).length < 2 ^ (prefixWord ++ tailWord_7900511).sum := by decide
  have hdescent : baseEnd_7900511 < baseStart_7900511 := by decide
  rcases family_descends (prefixWord ++ tailWord_7900511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7900515 : List Nat := [1, 1, 1, 5, 2, 4, 1, 1, 3, 4]
def baseStart_7900515 : Nat := 118140960795 + 7900515 * 2 ^ 59
def prefixEnd_7900515 : Nat := 4983230072969 + 3 ^ 40 * 7900515 * 2
def baseEnd_7900515 : Nat := 1352253871018753977476233

theorem tailTrace_7900515 : CollatzResearch.WordTrace tailWord_7900515 prefixEnd_7900515 1352253871018753977476233 := by
  unfold tailWord_7900515
  simp only [CollatzResearch.WordTrace]
  refine ⟨288155454972790930383806999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192103636648527286922537999 288155454972790930383806999)
  ·
    refine ⟨432233182459186395575710499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288155454972790930383806999 432233182459186395575710499)
    ·
      refine ⟨648349773688779593363565749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432233182459186395575710499 648349773688779593363565749)
      ·
        refine ⟨60782791283323086877834289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 648349773688779593363565749 60782791283323086877834289)
        ·
          refine ⟨45587093462492315158375717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60782791283323086877834289 45587093462492315158375717)
          ·
            refine ⟨8547580024217309092195447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45587093462492315158375717 8547580024217309092195447)
            ·
              refine ⟨12821370036325963638293171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8547580024217309092195447 12821370036325963638293171)
              ·
                refine ⟨19232055054488945457439757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12821370036325963638293171 19232055054488945457439757)
                ·
                  refine ⟨7212020645433354546539909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19232055054488945457439757 7212020645433354546539909)
                  ·
                    refine ⟨1352253871018753977476233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7212020645433354546539909 1352253871018753977476233)
                    ·
                      rfl

theorem cell23_7900515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 1, 3, 4].length) (baseStart_7900515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7900515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7900515 prefixEnd_7900515 := by exact prefixLift 7900515
  have htrace : WordTrace (prefixWord ++ tailWord_7900515) baseStart_7900515 baseEnd_7900515 := by
    simpa [prefixWord, tailWord_7900515, baseEnd_7900515] using wordTrace_append hprefix tailTrace_7900515
  have hstable : (prefixWord ++ tailWord_7900515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7900515).length < 2 ^ (prefixWord ++ tailWord_7900515).sum := by decide
  have hdescent : baseEnd_7900515 < baseStart_7900515 := by decide
  rcases family_descends (prefixWord ++ tailWord_7900515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7900521 : List Nat := [1, 2, 1, 1, 1, 3, 2, 2, 2, 5, 3]
def baseStart_7900521 : Nat := 118140960795 + 7900521 * 2 ^ 59
def prefixEnd_7900521 : Nat := 4983230072969 + 3 ^ 40 * 7900521 * 2
def baseEnd_7900521 : Nat := 4056764693940188908953671

theorem tailTrace_7900521 : CollatzResearch.WordTrace tailWord_7900521 prefixEnd_7900521 4056764693940188908953671 := by
  unfold tailWord_7900521
  simp only [CollatzResearch.WordTrace]
  refine ⟨288155673810769193408525417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192103782540512795605683611 288155673810769193408525417)
  ·
    refine ⟨216116755358076895056394063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288155673810769193408525417 216116755358076895056394063)
    ·
      refine ⟨324175133037115342584591095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216116755358076895056394063 324175133037115342584591095)
      ·
        refine ⟨486262699555673013876886643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324175133037115342584591095 486262699555673013876886643)
        ·
          refine ⟨729394049333509520815329965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486262699555673013876886643 729394049333509520815329965)
          ·
            refine ⟨273522768500066070305748737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 729394049333509520815329965 273522768500066070305748737)
            ·
              refine ⟨205142076375049552729311553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273522768500066070305748737 205142076375049552729311553)
              ·
                refine ⟨153856557281287164546983665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205142076375049552729311553 153856557281287164546983665)
                ·
                  refine ⟨115392417960965373410237749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153856557281287164546983665 115392417960965373410237749)
                  ·
                    refine ⟨10818039183840503757209789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 115392417960965373410237749 10818039183840503757209789)
                    ·
                      refine ⟨4056764693940188908953671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10818039183840503757209789 4056764693940188908953671)
                      ·
                        rfl

theorem cell23_7900521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 5, 3].length) (baseStart_7900521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7900521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7900521 prefixEnd_7900521 := by exact prefixLift 7900521
  have htrace : WordTrace (prefixWord ++ tailWord_7900521) baseStart_7900521 baseEnd_7900521 := by
    simpa [prefixWord, tailWord_7900521, baseEnd_7900521] using wordTrace_append hprefix tailTrace_7900521
  have hstable : (prefixWord ++ tailWord_7900521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7900521).length < 2 ^ (prefixWord ++ tailWord_7900521).sum := by decide
  have hdescent : baseEnd_7900521 < baseStart_7900521 := by decide
  rcases family_descends (prefixWord ++ tailWord_7900521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7900562 : List Nat := [3, 2, 3, 3, 1, 1, 2, 2, 6]
def baseStart_7900562 : Nat := 118140960795 + 7900562 * 2 ^ 59
def prefixEnd_7900562 : Nat := 4983230072969 + 3 ^ 40 * 7900562 * 2
def baseEnd_7900562 : Nat := 450753971849669249837887

theorem tailTrace_7900562 : CollatzResearch.WordTrace tailWord_7900562 prefixEnd_7900562 450753971849669249837887 := by
  unfold tailWord_7900562
  simp only [CollatzResearch.WordTrace]
  refine ⟨72039292300905164352691985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192104779469080438273845293 72039292300905164352691985)
  ·
    refine ⟨54029469225678873264518989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72039292300905164352691985 54029469225678873264518989)
    ·
      refine ⟨20261050959629577474194621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54029469225678873264518989 20261050959629577474194621)
      ·
        refine ⟨7597894109861091552822983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20261050959629577474194621 7597894109861091552822983)
        ·
          refine ⟨11396841164791637329234475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7597894109861091552822983 11396841164791637329234475)
          ·
            refine ⟨17095261747187455993851713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11396841164791637329234475 17095261747187455993851713)
            ·
              refine ⟨12821446310390591995388785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17095261747187455993851713 12821446310390591995388785)
              ·
                refine ⟨9616084732792943996541589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12821446310390591995388785 9616084732792943996541589)
                ·
                  refine ⟨450753971849669249837887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9616084732792943996541589 450753971849669249837887)
                  ·
                    rfl

theorem cell23_7900562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 2, 6].length) (baseStart_7900562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7900562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7900562 prefixEnd_7900562 := by exact prefixLift 7900562
  have htrace : WordTrace (prefixWord ++ tailWord_7900562) baseStart_7900562 baseEnd_7900562 := by
    simpa [prefixWord, tailWord_7900562, baseEnd_7900562] using wordTrace_append hprefix tailTrace_7900562
  have hstable : (prefixWord ++ tailWord_7900562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7900562).length < 2 ^ (prefixWord ++ tailWord_7900562).sum := by decide
  have hdescent : baseEnd_7900562 < baseStart_7900562 := by decide
  rcases family_descends (prefixWord ++ tailWord_7900562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7900565 : List Nat := [1, 3, 2, 1, 1, 2, 4, 2, 2, 3, 2]
def baseStart_7900565 : Nat := 118140960795 + 7900565 * 2 ^ 59
def prefixEnd_7900565 : Nat := 4983230072969 + 3 ^ 40 * 7900565 * 2
def baseEnd_7900565 : Nat := 4056787287088986736803469

theorem tailTrace_7900565 : CollatzResearch.WordTrace tailWord_7900565 prefixEnd_7900565 4056787287088986736803469 := by
  unfold tailWord_7900565
  simp only [CollatzResearch.WordTrace]
  refine ⟨288157278622609788923127149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192104852415073192615418099 288157278622609788923127149)
  ·
    refine ⟨108058979483478670846172681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288157278622609788923127149 108058979483478670846172681)
    ·
      refine ⟨81044234612609003134629511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108058979483478670846172681 81044234612609003134629511)
      ·
        refine ⟨121566351918913504701944267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81044234612609003134629511 121566351918913504701944267)
        ·
          refine ⟨182349527878370257052916401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121566351918913504701944267 182349527878370257052916401)
          ·
            refine ⟨136762145908777692789687301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182349527878370257052916401 136762145908777692789687301)
            ·
              refine ⟨25642902357895817398066369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 136762145908777692789687301 25642902357895817398066369)
              ·
                refine ⟨19232176768421863048549777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25642902357895817398066369 19232176768421863048549777)
                ·
                  refine ⟨14424132576316397286412333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19232176768421863048549777 14424132576316397286412333)
                  ·
                    refine ⟨5409049716118648982404625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14424132576316397286412333 5409049716118648982404625)
                    ·
                      refine ⟨4056787287088986736803469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5409049716118648982404625 4056787287088986736803469)
                      ·
                        rfl

theorem cell23_7900565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 2, 2, 3, 2].length) (baseStart_7900565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7900565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7900565 prefixEnd_7900565 := by exact prefixLift 7900565
  have htrace : WordTrace (prefixWord ++ tailWord_7900565) baseStart_7900565 baseEnd_7900565 := by
    simpa [prefixWord, tailWord_7900565, baseEnd_7900565] using wordTrace_append hprefix tailTrace_7900565
  have hstable : (prefixWord ++ tailWord_7900565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7900565).length < 2 ^ (prefixWord ++ tailWord_7900565).sum := by decide
  have hdescent : baseEnd_7900565 < baseStart_7900565 := by decide
  rcases family_descends (prefixWord ++ tailWord_7900565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7900591 : List Nat := [1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 6]
def baseStart_7900591 : Nat := 118140960795 + 7900591 * 2 ^ 59
def prefixEnd_7900591 : Nat := 4983230072969 + 3 ^ 40 * 7900591 * 2
def baseEnd_7900591 : Nat := 4056800637586003635078349

theorem tailTrace_7900591 : CollatzResearch.WordTrace tailWord_7900591 prefixEnd_7900591 4056800637586003635078349 := by
  unfold tailWord_7900591
  simp only [CollatzResearch.WordTrace]
  refine ⟨288158226920515595363573627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192105484613677063575715751 288158226920515595363573627)
  ·
    refine ⟨432237340380773393045360441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288158226920515595363573627 432237340380773393045360441)
    ·
      refine ⟨324178005285580044784020331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432237340380773393045360441 324178005285580044784020331)
      ·
        refine ⟨486267007928370067176030497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324178005285580044784020331 486267007928370067176030497)
        ·
          refine ⟨364700255946277550382022873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 486267007928370067176030497 364700255946277550382022873)
          ·
            refine ⟨273525191959708162786517155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 364700255946277550382022873 273525191959708162786517155)
            ·
              refine ⟨410287787939562244179775733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273525191959708162786517155 410287787939562244179775733)
              ·
                refine ⟨38464480119333960391853975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 410287787939562244179775733 38464480119333960391853975)
                ·
                  refine ⟨57696720179000940587780963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38464480119333960391853975 57696720179000940587780963)
                  ·
                    refine ⟨86545080268501410881671445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57696720179000940587780963 86545080268501410881671445)
                    ·
                      refine ⟨4056800637586003635078349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86545080268501410881671445 4056800637586003635078349)
                      ·
                        rfl

theorem cell23_7900591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 6].length) (baseStart_7900591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7900591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7900591 prefixEnd_7900591 := by exact prefixLift 7900591
  have htrace : WordTrace (prefixWord ++ tailWord_7900591) baseStart_7900591 baseEnd_7900591 := by
    simpa [prefixWord, tailWord_7900591, baseEnd_7900591] using wordTrace_append hprefix tailTrace_7900591
  have hstable : (prefixWord ++ tailWord_7900591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7900591).length < 2 ^ (prefixWord ++ tailWord_7900591).sum := by decide
  have hdescent : baseEnd_7900591 < baseStart_7900591 := by decide
  rcases family_descends (prefixWord ++ tailWord_7900591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7900608 : List Nat := [2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 4]
def baseStart_7900608 : Nat := 118140960795 + 7900608 * 2 ^ 59
def prefixEnd_7900608 : Nat := 4983230072969 + 3 ^ 40 * 7900608 * 2
def baseEnd_7900608 : Nat := 4056809366757130068565771

theorem tailTrace_7900608 : CollatzResearch.WordTrace tailWord_7900608 prefixEnd_7900608 4056809366757130068565771 := by
  unfold tailWord_7900608
  simp only [CollatzResearch.WordTrace]
  refine ⟨144079423480727003633471239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192105897974302671511294985 144079423480727003633471239)
  ·
    refine ⟨216119135221090505450206859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144079423480727003633471239 216119135221090505450206859)
    ·
      refine ⟨324178702831635758175310289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216119135221090505450206859 324178702831635758175310289)
      ·
        refine ⟨243134027123726818631482717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324178702831635758175310289 243134027123726818631482717)
        ·
          refine ⟨91175260171397556986806019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 243134027123726818631482717 91175260171397556986806019)
          ·
            refine ⟨136762890257096335480209029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91175260171397556986806019 136762890257096335480209029)
            ·
              refine ⟨25643041923205562902539193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 136762890257096335480209029 25643041923205562902539193)
              ·
                refine ⟨19232281442404172176904395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25643041923205562902539193 19232281442404172176904395)
                ·
                  refine ⟨28848422163606258265356593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19232281442404172176904395 28848422163606258265356593)
                  ·
                    refine ⟨21636316622704693699017445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28848422163606258265356593 21636316622704693699017445)
                    ·
                      refine ⟨4056809366757130068565771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21636316622704693699017445 4056809366757130068565771)
                      ·
                        rfl

theorem cell23_7900608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 4].length) (baseStart_7900608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7900608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7900608 prefixEnd_7900608 := by exact prefixLift 7900608
  have htrace : WordTrace (prefixWord ++ tailWord_7900608) baseStart_7900608 baseEnd_7900608 := by
    simpa [prefixWord, tailWord_7900608, baseEnd_7900608] using wordTrace_append hprefix tailTrace_7900608
  have hstable : (prefixWord ++ tailWord_7900608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7900608).length < 2 ^ (prefixWord ++ tailWord_7900608).sum := by decide
  have hdescent : baseEnd_7900608 < baseStart_7900608 := by decide
  rcases family_descends (prefixWord ++ tailWord_7900608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7900612 : List Nat := [2, 3, 3, 2, 1, 2, 1, 3, 1, 1, 4]
def baseStart_7900612 : Nat := 118140960795 + 7900612 * 2 ^ 59
def prefixEnd_7900612 : Nat := 4983230072969 + 3 ^ 40 * 7900612 * 2
def baseEnd_7900612 : Nat := 4056811420679748052915753

theorem tailTrace_7900612 : CollatzResearch.WordTrace tailWord_7900612 prefixEnd_7900612 4056811420679748052915753 := by
  unfold tailWord_7900612
  simp only [CollatzResearch.WordTrace]
  refine ⟨144079496426719757975044045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192105995235626343966725393 144079496426719757975044045)
  ·
    refine ⟨54029811160019909240641517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144079496426719757975044045 54029811160019909240641517)
    ·
      refine ⟨20261179185007465965240569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54029811160019909240641517 20261179185007465965240569)
      ·
        refine ⟨15195884388755599473930427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20261179185007465965240569 15195884388755599473930427)
        ·
          refine ⟨22793826583133399210895641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15195884388755599473930427 22793826583133399210895641)
          ·
            refine ⟨17095369937350049408171731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22793826583133399210895641 17095369937350049408171731)
            ·
              refine ⟨25643054906025074112257597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17095369937350049408171731 25643054906025074112257597)
              ·
                refine ⟨9616145589759402792096599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25643054906025074112257597 9616145589759402792096599)
                ·
                  refine ⟨14424218384639104188144899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9616145589759402792096599 14424218384639104188144899)
                  ·
                    refine ⟨21636327576958656282217349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14424218384639104188144899 21636327576958656282217349)
                    ·
                      refine ⟨4056811420679748052915753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21636327576958656282217349 4056811420679748052915753)
                      ·
                        rfl

theorem cell23_7900612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_7900612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7900612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7900612 prefixEnd_7900612 := by exact prefixLift 7900612
  have htrace : WordTrace (prefixWord ++ tailWord_7900612) baseStart_7900612 baseEnd_7900612 := by
    simpa [prefixWord, tailWord_7900612, baseEnd_7900612] using wordTrace_append hprefix tailTrace_7900612
  have hstable : (prefixWord ++ tailWord_7900612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7900612).length < 2 ^ (prefixWord ++ tailWord_7900612).sum := by decide
  have hdescent : baseEnd_7900612 < baseStart_7900612 := by decide
  rcases family_descends (prefixWord ++ tailWord_7900612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7900615 : List Nat := [1, 1, 4, 1, 1, 3, 3, 3, 1, 2, 3]
def baseStart_7900615 : Nat := 118140960795 + 7900615 * 2 ^ 59
def prefixEnd_7900615 : Nat := 4983230072969 + 3 ^ 40 * 7900615 * 2
def baseEnd_7900615 : Nat := 4056812961121711541178239

theorem tailTrace_7900615 : CollatzResearch.WordTrace tailWord_7900615 prefixEnd_7900615 4056812961121711541178239 := by
  unfold tailWord_7900615
  simp only [CollatzResearch.WordTrace]
  refine ⟨288159102272428647462447299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192106068181619098308298199 288159102272428647462447299)
  ·
    refine ⟨432238653408642971193670949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288159102272428647462447299 432238653408642971193670949)
    ·
      refine ⟨81044747514120557098813303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 432238653408642971193670949 81044747514120557098813303)
      ·
        refine ⟨121567121271180835648219955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81044747514120557098813303 121567121271180835648219955)
        ·
          refine ⟨182350681906771253472329933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121567121271180835648219955 182350681906771253472329933)
          ·
            refine ⟨68381505715039220052123725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182350681906771253472329933 68381505715039220052123725)
            ·
              refine ⟨25643064643139707519546397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68381505715039220052123725 25643064643139707519546397)
              ·
                refine ⟨9616149241177390319829899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25643064643139707519546397 9616149241177390319829899)
                ·
                  refine ⟨14424223861766085479744849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9616149241177390319829899 14424223861766085479744849)
                  ·
                    refine ⟨10818167896324564109808637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14424223861766085479744849 10818167896324564109808637)
                    ·
                      refine ⟨4056812961121711541178239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10818167896324564109808637 4056812961121711541178239)
                      ·
                        rfl

theorem cell23_7900615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 3, 1, 2, 3].length) (baseStart_7900615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7900615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7900615 prefixEnd_7900615 := by exact prefixLift 7900615
  have htrace : WordTrace (prefixWord ++ tailWord_7900615) baseStart_7900615 baseEnd_7900615 := by
    simpa [prefixWord, tailWord_7900615, baseEnd_7900615] using wordTrace_append hprefix tailTrace_7900615
  have hstable : (prefixWord ++ tailWord_7900615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7900615).length < 2 ^ (prefixWord ++ tailWord_7900615).sum := by decide
  have hdescent : baseEnd_7900615 < baseStart_7900615 := by decide
  rcases family_descends (prefixWord ++ tailWord_7900615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7900629 : List Nat := [1, 3, 2, 3, 1, 1, 1, 6, 1, 2, 2]
def baseStart_7900629 : Nat := 118140960795 + 7900629 * 2 ^ 59
def prefixEnd_7900629 : Nat := 4983230072969 + 3 ^ 40 * 7900629 * 2
def baseEnd_7900629 : Nat := 4056820149850874486403175

theorem tailTrace_7900629 : CollatzResearch.WordTrace tailWord_7900629 prefixEnd_7900629 4056820149850874486403175 := by
  unfold tailWord_7900629
  simp only [CollatzResearch.WordTrace]
  refine ⟨288159612894377927853456941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192106408596251951902304627 288159612894377927853456941)
  ·
    refine ⟨108059854835391722945046353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288159612894377927853456941 108059854835391722945046353)
    ·
      refine ⟨81044891126543792208784765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108059854835391722945046353 81044891126543792208784765)
      ·
        refine ⟨30391834172453922078294287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81044891126543792208784765 30391834172453922078294287)
        ·
          refine ⟨45587751258680883117441431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30391834172453922078294287 45587751258680883117441431)
          ·
            refine ⟨68381626888021324676162147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45587751258680883117441431 68381626888021324676162147)
            ·
              refine ⟨102572440332031987014243221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68381626888021324676162147 102572440332031987014243221)
              ·
                refine ⟨4808083140563999391292651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 102572440332031987014243221 4808083140563999391292651)
                ·
                  refine ⟨7212124710845999086938977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4808083140563999391292651 7212124710845999086938977)
                  ·
                    refine ⟨5409093533134499315204233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7212124710845999086938977 5409093533134499315204233)
                    ·
                      refine ⟨4056820149850874486403175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5409093533134499315204233 4056820149850874486403175)
                      ·
                        rfl

theorem cell23_7900629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 6, 1, 2, 2].length) (baseStart_7900629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7900629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7900629 prefixEnd_7900629 := by exact prefixLift 7900629
  have htrace : WordTrace (prefixWord ++ tailWord_7900629) baseStart_7900629 baseEnd_7900629 := by
    simpa [prefixWord, tailWord_7900629, baseEnd_7900629] using wordTrace_append hprefix tailTrace_7900629
  have hstable : (prefixWord ++ tailWord_7900629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7900629).length < 2 ^ (prefixWord ++ tailWord_7900629).sum := by decide
  have hdescent : baseEnd_7900629 < baseStart_7900629 := by decide
  rcases family_descends (prefixWord ++ tailWord_7900629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7900631 : List Nat := [1, 1, 3, 2, 1, 1, 1, 3, 1, 9]
def baseStart_7900631 : Nat := 118140960795 + 7900631 * 2 ^ 59
def prefixEnd_7900631 : Nat := 4983230072969 + 3 ^ 40 * 7900631 * 2
def baseEnd_7900631 : Nat := 1352273725604061159526055

theorem tailTrace_7900631 : CollatzResearch.WordTrace tailWord_7900631 prefixEnd_7900631 1352273725604061159526055 := by
  unfold tailWord_7900631
  simp only [CollatzResearch.WordTrace]
  refine ⟨288159685840370682195029747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192106457226913788130019831 288159685840370682195029747)
  ·
    refine ⟨432239528760556023292544621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288159685840370682195029747 432239528760556023292544621)
    ·
      refine ⟨162089823285208508734704233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 432239528760556023292544621 162089823285208508734704233)
      ·
        refine ⟨121567367463906381551028175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162089823285208508734704233 121567367463906381551028175)
        ·
          refine ⟨182351051195859572326542263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121567367463906381551028175 182351051195859572326542263)
          ·
            refine ⟨273526576793789358489813395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182351051195859572326542263 273526576793789358489813395)
            ·
              refine ⟨410289865190684037734720093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273526576793789358489813395 410289865190684037734720093)
              ·
                refine ⟨153858699446506514150520035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 410289865190684037734720093 153858699446506514150520035)
                ·
                  refine ⟨230788049169759771225780053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153858699446506514150520035 230788049169759771225780053)
                  ·
                    refine ⟨1352273725604061159526055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 230788049169759771225780053 1352273725604061159526055)
                    ·
                      rfl

theorem cell23_7900631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 9].length) (baseStart_7900631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7900631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7900631 prefixEnd_7900631 := by exact prefixLift 7900631
  have htrace : WordTrace (prefixWord ++ tailWord_7900631) baseStart_7900631 baseEnd_7900631 := by
    simpa [prefixWord, tailWord_7900631, baseEnd_7900631] using wordTrace_append hprefix tailTrace_7900631
  have hstable : (prefixWord ++ tailWord_7900631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7900631).length < 2 ^ (prefixWord ++ tailWord_7900631).sum := by decide
  have hdescent : baseEnd_7900631 < baseStart_7900631 := by decide
  rcases family_descends (prefixWord ++ tailWord_7900631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7900651 : List Nat := [1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 8]
def baseStart_7900651 : Nat := 118140960795 + 7900651 * 2 ^ 59
def prefixEnd_7900651 : Nat := 4983230072969 + 3 ^ 40 * 7900651 * 2
def baseEnd_7900651 : Nat := 4056831446425273400328073

theorem tailTrace_7900651 : CollatzResearch.WordTrace tailWord_7900651 prefixEnd_7900651 4056831446425273400328073 := by
  unfold tailWord_7900651
  simp only [CollatzResearch.WordTrace]
  refine ⟨288160415300298225610757807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192106943533532150407171871 288160415300298225610757807)
  ·
    refine ⟨432240622950447338416136711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288160415300298225610757807 432240622950447338416136711)
    ·
      refine ⟨648360934425671007624205067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432240622950447338416136711 648360934425671007624205067)
      ·
        refine ⟨972541401638506511436307601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 648360934425671007624205067 972541401638506511436307601)
        ·
          refine ⟨729406051228879883577230701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 972541401638506511436307601 729406051228879883577230701)
          ·
            refine ⟨273527269210829956341461513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 729406051228879883577230701 273527269210829956341461513)
            ·
              refine ⟨205145451908122467256096135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273527269210829956341461513 205145451908122467256096135)
              ·
                refine ⟨307718177862183700884144203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205145451908122467256096135 307718177862183700884144203)
                ·
                  refine ⟨461577266793275551326216305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 307718177862183700884144203 461577266793275551326216305)
                  ·
                    refine ⟨346182950094956663494662229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 461577266793275551326216305 346182950094956663494662229)
                    ·
                      refine ⟨4056831446425273400328073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 346182950094956663494662229 4056831446425273400328073)
                      ·
                        rfl

theorem cell23_7900651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 8].length) (baseStart_7900651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7900651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7900651 prefixEnd_7900651 := by exact prefixLift 7900651
  have htrace : WordTrace (prefixWord ++ tailWord_7900651) baseStart_7900651 baseEnd_7900651 := by
    simpa [prefixWord, tailWord_7900651, baseEnd_7900651] using wordTrace_append hprefix tailTrace_7900651
  have hstable : (prefixWord ++ tailWord_7900651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7900651).length < 2 ^ (prefixWord ++ tailWord_7900651).sum := by decide
  have hdescent : baseEnd_7900651 < baseStart_7900651 := by decide
  rcases family_descends (prefixWord ++ tailWord_7900651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7900655 : List Nat := [1, 1, 2, 1, 4, 1, 2, 3, 3, 3, 2]
def baseStart_7900655 : Nat := 118140960795 + 7900655 * 2 ^ 59
def prefixEnd_7900655 : Nat := 4983230072969 + 3 ^ 40 * 7900655 * 2
def baseEnd_7900655 : Nat := 4056833500347891384678055

theorem tailTrace_7900655 : CollatzResearch.WordTrace tailWord_7900655 prefixEnd_7900655 4056833500347891384678055 := by
  unfold tailWord_7900655
  simp only [CollatzResearch.WordTrace]
  refine ⟨288160561192283734293903419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192107040794855822862602279 288160561192283734293903419)
  ·
    refine ⟨432240841788425601440855129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288160561192283734293903419 432240841788425601440855129)
    ·
      refine ⟨324180631341319201080641347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432240841788425601440855129 324180631341319201080641347)
      ·
        refine ⟨486270947011978801620962021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324180631341319201080641347 486270947011978801620962021)
        ·
          refine ⟨91175802564746025303930379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 486270947011978801620962021 91175802564746025303930379)
          ·
            refine ⟨136763703847119037955895569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91175802564746025303930379 136763703847119037955895569)
            ·
              refine ⟨102572777885339278466921677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136763703847119037955895569 102572777885339278466921677)
              ·
                refine ⟨38464791707002229425095629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102572777885339278466921677 38464791707002229425095629)
                ·
                  refine ⟨14424296890125836034410861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38464791707002229425095629 14424296890125836034410861)
                  ·
                    refine ⟨5409111333797188512904073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14424296890125836034410861 5409111333797188512904073)
                    ·
                      refine ⟨4056833500347891384678055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5409111333797188512904073 4056833500347891384678055)
                      ·
                        rfl

theorem cell23_7900655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 3, 3, 2].length) (baseStart_7900655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7900655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7900655 prefixEnd_7900655 := by exact prefixLift 7900655
  have htrace : WordTrace (prefixWord ++ tailWord_7900655) baseStart_7900655 baseEnd_7900655 := by
    simpa [prefixWord, tailWord_7900655, baseEnd_7900655] using wordTrace_append hprefix tailTrace_7900655
  have hstable : (prefixWord ++ tailWord_7900655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7900655).length < 2 ^ (prefixWord ++ tailWord_7900655).sum := by decide
  have hdescent : baseEnd_7900655 < baseStart_7900655 := by decide
  rcases family_descends (prefixWord ++ tailWord_7900655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7900662 : List Nat := [5, 1, 1, 1, 2, 2, 1, 2, 4, 1, 3]
def baseStart_7900662 : Nat := 118140960795 + 7900662 * 2 ^ 59
def prefixEnd_7900662 : Nat := 4983230072969 + 3 ^ 40 * 7900662 * 2
def baseEnd_7900662 : Nat := 4056837094712472857290523

theorem tailTrace_7900662 : CollatzResearch.WordTrace tailWord_7900662 prefixEnd_7900662 4056837094712472857290523 := by
  unfold tailWord_7900662
  simp only [CollatzResearch.WordTrace]
  refine ⟨18010051031453648405588015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 192107211002172249659605493 18010051031453648405588015)
  ·
    refine ⟨27015076547180472608382023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18010051031453648405588015 27015076547180472608382023)
    ·
      refine ⟨40522614820770708912573035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27015076547180472608382023 40522614820770708912573035)
      ·
        refine ⟨60783922231156063368859553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40522614820770708912573035 60783922231156063368859553)
        ·
          refine ⟨45587941673367047526644665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60783922231156063368859553 45587941673367047526644665)
          ·
            refine ⟨34190956255025285644983499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45587941673367047526644665 34190956255025285644983499)
            ·
              refine ⟨51286434382537928467475249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34190956255025285644983499 51286434382537928467475249)
              ·
                refine ⟨38464825786903446350606437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51286434382537928467475249 38464825786903446350606437)
                ·
                  refine ⟨7212154835044396190738707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38464825786903446350606437 7212154835044396190738707)
                  ·
                    refine ⟨10818232252566594286108061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7212154835044396190738707 10818232252566594286108061)
                    ·
                      refine ⟨4056837094712472857290523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10818232252566594286108061 4056837094712472857290523)
                      ·
                        rfl

theorem cell23_7900662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 4, 1, 3].length) (baseStart_7900662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7900662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7900662 prefixEnd_7900662 := by exact prefixLift 7900662
  have htrace : WordTrace (prefixWord ++ tailWord_7900662) baseStart_7900662 baseEnd_7900662 := by
    simpa [prefixWord, tailWord_7900662, baseEnd_7900662] using wordTrace_append hprefix tailTrace_7900662
  have hstable : (prefixWord ++ tailWord_7900662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7900662).length < 2 ^ (prefixWord ++ tailWord_7900662).sum := by decide
  have hdescent : baseEnd_7900662 < baseStart_7900662 := by decide
  rcases family_descends (prefixWord ++ tailWord_7900662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7900696 : List Nat := [2, 1, 2, 3, 4, 2, 2, 1, 2, 1, 3]
def baseStart_7900696 : Nat := 118140960795 + 7900696 * 2 ^ 59
def prefixEnd_7900696 : Nat := 4983230072969 + 3 ^ 40 * 7900696 * 2
def baseEnd_7900696 : Nat := 4056854553054725724265367

theorem tailTrace_7900696 : CollatzResearch.WordTrace tailWord_7900696 prefixEnd_7900696 4056854553054725724265367 := by
  unfold tailWord_7900696
  simp only [CollatzResearch.WordTrace]
  refine ⟨144081028292567599148072971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192108037723423465530763961 144081028292567599148072971)
  ·
    refine ⟨216121542438851398722109457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144081028292567599148072971 216121542438851398722109457)
    ·
      refine ⟨162091156829138549041582093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216121542438851398722109457 162091156829138549041582093)
      ·
        refine ⟨60784183810926955890593285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162091156829138549041582093 60784183810926955890593285)
        ·
          refine ⟨11397034464548804229486241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60784183810926955890593285 11397034464548804229486241)
          ·
            refine ⟨8547775848411603172114681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11397034464548804229486241 8547775848411603172114681)
            ·
              refine ⟨6410831886308702379086011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8547775848411603172114681 6410831886308702379086011)
              ·
                refine ⟨9616247829463053568629017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6410831886308702379086011 9616247829463053568629017)
                ·
                  refine ⟨7212185872097290176471763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9616247829463053568629017 7212185872097290176471763)
                  ·
                    refine ⟨10818278808145935264707645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7212185872097290176471763 10818278808145935264707645)
                    ·
                      refine ⟨4056854553054725724265367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10818278808145935264707645 4056854553054725724265367)
                      ·
                        rfl

theorem cell23_7900696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 2, 1, 2, 1, 3].length) (baseStart_7900696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7900696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7900696 prefixEnd_7900696 := by exact prefixLift 7900696
  have htrace : WordTrace (prefixWord ++ tailWord_7900696) baseStart_7900696 baseEnd_7900696 := by
    simpa [prefixWord, tailWord_7900696, baseEnd_7900696] using wordTrace_append hprefix tailTrace_7900696
  have hstable : (prefixWord ++ tailWord_7900696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7900696).length < 2 ^ (prefixWord ++ tailWord_7900696).sum := by decide
  have hdescent : baseEnd_7900696 < baseStart_7900696 := by decide
  rcases family_descends (prefixWord ++ tailWord_7900696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7900698 : List Nat := [3, 1, 1, 3, 1, 1, 1, 3, 1, 4, 4]
def baseStart_7900698 : Nat := 118140960795 + 7900698 * 2 ^ 59
def prefixEnd_7900698 : Nat := 4983230072969 + 3 ^ 40 * 7900698 * 2
def baseEnd_7900698 : Nat := 4056855580016034716440357

theorem tailTrace_7900698 : CollatzResearch.WordTrace tailWord_7900698 prefixEnd_7900698 4056855580016034716440357 := by
  unfold tailWord_7900698
  simp only [CollatzResearch.WordTrace]
  refine ⟨72040532382781988159429687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192108086354085301758479165 72040532382781988159429687)
  ·
    refine ⟨108060798574172982239144531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72040532382781988159429687 108060798574172982239144531)
    ·
      refine ⟨162091197861259473358716797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108060798574172982239144531 162091197861259473358716797)
      ·
        refine ⟨60784199197972302509518799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162091197861259473358716797 60784199197972302509518799)
        ·
          refine ⟨91176298796958453764278199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60784199197972302509518799 91176298796958453764278199)
          ·
            refine ⟨136764448195437680646417299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91176298796958453764278199 136764448195437680646417299)
            ·
              refine ⟨205146672293156520969625949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136764448195437680646417299 205146672293156520969625949)
              ·
                refine ⟨76930002109933695363609731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 205146672293156520969625949 76930002109933695363609731)
                ·
                  refine ⟨115395003164900543045414597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76930002109933695363609731 115395003164900543045414597)
                  ·
                    refine ⟨21636563093418851821015237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 115395003164900543045414597 21636563093418851821015237)
                    ·
                      refine ⟨4056855580016034716440357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21636563093418851821015237 4056855580016034716440357)
                      ·
                        rfl

theorem cell23_7900698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_7900698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7900698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7900698 prefixEnd_7900698 := by exact prefixLift 7900698
  have htrace : WordTrace (prefixWord ++ tailWord_7900698) baseStart_7900698 baseEnd_7900698 := by
    simpa [prefixWord, tailWord_7900698, baseEnd_7900698] using wordTrace_append hprefix tailTrace_7900698
  have hstable : (prefixWord ++ tailWord_7900698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7900698).length < 2 ^ (prefixWord ++ tailWord_7900698).sum := by decide
  have hdescent : baseEnd_7900698 < baseStart_7900698 := by decide
  rcases family_descends (prefixWord ++ tailWord_7900698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7900772 : List Nat := [2, 3, 1, 1, 2, 5, 1, 1, 2, 5]
def baseStart_7900772 : Nat := 118140960795 + 7900772 * 2 ^ 59
def prefixEnd_7900772 : Nat := 4983230072969 + 3 ^ 40 * 7900772 * 2
def baseEnd_7900772 : Nat := 1352297859194822475638339

theorem tailTrace_7900772 : CollatzResearch.WordTrace tailWord_7900772 prefixEnd_7900772 1352297859194822475638339 := by
  unfold tailWord_7900772
  simp only [CollatzResearch.WordTrace]
  refine ⟨144082414266429931637956285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192109885688573242183941713 144082414266429931637956285)
  ·
    refine ⟨54030905349911224364233607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144082414266429931637956285 54030905349911224364233607)
    ·
      refine ⟨81046358024866836546350411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54030905349911224364233607 81046358024866836546350411)
      ·
        refine ⟨121569537037300254819525617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81046358024866836546350411 121569537037300254819525617)
        ·
          refine ⟨91177152777975191114644213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121569537037300254819525617 91177152777975191114644213)
          ·
            refine ⟨8547858072935174166997895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91177152777975191114644213 8547858072935174166997895)
            ·
              refine ⟨12821787109402761250496843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8547858072935174166997895 12821787109402761250496843)
              ·
                refine ⟨19232680664104141875745265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12821787109402761250496843 19232680664104141875745265)
                ·
                  refine ⟨14424510498078106406808949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19232680664104141875745265 14424510498078106406808949)
                  ·
                    refine ⟨1352297859194822475638339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14424510498078106406808949 1352297859194822475638339)
                    ·
                      rfl

theorem cell23_7900772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 1, 2, 5].length) (baseStart_7900772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7900772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7900772 prefixEnd_7900772 := by exact prefixLift 7900772
  have htrace : WordTrace (prefixWord ++ tailWord_7900772) baseStart_7900772 baseEnd_7900772 := by
    simpa [prefixWord, tailWord_7900772, baseEnd_7900772] using wordTrace_append hprefix tailTrace_7900772
  have hstable : (prefixWord ++ tailWord_7900772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7900772).length < 2 ^ (prefixWord ++ tailWord_7900772).sum := by decide
  have hdescent : baseEnd_7900772 < baseStart_7900772 := by decide
  rcases family_descends (prefixWord ++ tailWord_7900772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7900795 : List Nat := [1, 1, 1, 1, 1, 4, 4, 1, 4, 2, 3]
def baseStart_7900795 : Nat := 118140960795 + 7900795 * 2 ^ 59
def prefixEnd_7900795 : Nat := 4983230072969 + 3 ^ 40 * 7900795 * 2
def baseEnd_7900795 : Nat := 4056905387639520836927411

theorem tailTrace_7900795 : CollatzResearch.WordTrace tailWord_7900795 prefixEnd_7900795 4056905387639520836927411 := by
  unfold tailWord_7900795
  simp only [CollatzResearch.WordTrace]
  refine ⟨288165667411776538203999839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192110444941184358802666559 288165667411776538203999839)
  ·
    refine ⟨432248501117664807305999759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288165667411776538203999839 432248501117664807305999759)
    ·
      refine ⟨648372751676497210958999639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432248501117664807305999759 648372751676497210958999639)
      ·
        refine ⟨972559127514745816438499459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 648372751676497210958999639 972559127514745816438499459)
        ·
          refine ⟨1458838691272118724657749189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 972559127514745816438499459 1458838691272118724657749189)
          ·
            refine ⟨273532254613522260873327973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1458838691272118724657749189 273532254613522260873327973)
            ·
              refine ⟨51287297740035423913748995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 273532254613522260873327973 51287297740035423913748995)
              ·
                refine ⟨76930946610053135870623493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51287297740035423913748995 76930946610053135870623493)
                ·
                  refine ⟨14424552489384962975741905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76930946610053135870623493 14424552489384962975741905)
                  ·
                    refine ⟨10818414367038722231806429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14424552489384962975741905 10818414367038722231806429)
                    ·
                      refine ⟨4056905387639520836927411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10818414367038722231806429 4056905387639520836927411)
                      ·
                        rfl

theorem cell23_7900795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 4, 2, 3].length) (baseStart_7900795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7900795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7900795 prefixEnd_7900795 := by exact prefixLift 7900795
  have htrace : WordTrace (prefixWord ++ tailWord_7900795) baseStart_7900795 baseEnd_7900795 := by
    simpa [prefixWord, tailWord_7900795, baseEnd_7900795] using wordTrace_append hprefix tailTrace_7900795
  have hstable : (prefixWord ++ tailWord_7900795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7900795).length < 2 ^ (prefixWord ++ tailWord_7900795).sum := by decide
  have hdescent : baseEnd_7900795 < baseStart_7900795 := by decide
  rcases family_descends (prefixWord ++ tailWord_7900795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7900836 : List Nat := [2, 3, 1, 2, 2, 4, 1, 3, 1, 4]
def baseStart_7900836 : Nat := 118140960795 + 7900836 * 2 ^ 59
def prefixEnd_7900836 : Nat := 4983230072969 + 3 ^ 40 * 7900836 * 2
def baseEnd_7900836 : Nat := 1352308813448785058838241

theorem tailTrace_7900836 : CollatzResearch.WordTrace tailWord_7900836 prefixEnd_7900836 1352308813448785058838241 := by
  unfold tailWord_7900836
  simp only [CollatzResearch.WordTrace]
  refine ⟨144083581402314001103121181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192111441869752001470828241 144083581402314001103121181)
  ·
    refine ⟨54031343025867750413670443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144083581402314001103121181 54031343025867750413670443)
    ·
      refine ⟨81047014538801625620505665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54031343025867750413670443 81047014538801625620505665)
      ·
        refine ⟨60785260904101219215379249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81047014538801625620505665 60785260904101219215379249)
        ·
          refine ⟨45588945678075914411534437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60785260904101219215379249 45588945678075914411534437)
          ·
            refine ⟨8547927314639233952162707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45588945678075914411534437 8547927314639233952162707)
            ·
              refine ⟨12821890971958850928244061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8547927314639233952162707 12821890971958850928244061)
              ·
                refine ⟨4808209114484569098091523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12821890971958850928244061 4808209114484569098091523)
                ·
                  refine ⟨7212313671726853647137285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4808209114484569098091523 7212313671726853647137285)
                  ·
                    refine ⟨1352308813448785058838241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7212313671726853647137285 1352308813448785058838241)
                    ·
                      rfl

theorem cell23_7900836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 3, 1, 4].length) (baseStart_7900836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7900836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7900836 prefixEnd_7900836 := by exact prefixLift 7900836
  have htrace : WordTrace (prefixWord ++ tailWord_7900836) baseStart_7900836 baseEnd_7900836 := by
    simpa [prefixWord, tailWord_7900836, baseEnd_7900836] using wordTrace_append hprefix tailTrace_7900836
  have hstable : (prefixWord ++ tailWord_7900836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7900836).length < 2 ^ (prefixWord ++ tailWord_7900836).sum := by decide
  have hdescent : baseEnd_7900836 < baseStart_7900836 := by decide
  rcases family_descends (prefixWord ++ tailWord_7900836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7900846 : List Nat := [4, 1, 4, 1, 2, 1, 1, 2, 2, 2, 3]
def baseStart_7900846 : Nat := 118140960795 + 7900846 * 2 ^ 59
def prefixEnd_7900846 : Nat := 4983230072969 + 3 ^ 40 * 7900846 * 2
def baseEnd_7900846 : Nat := 4056931575152900137389677

theorem tailTrace_7900846 : CollatzResearch.WordTrace tailWord_7900846 prefixEnd_7900846 4056931575152900137389677 := by
  unfold tailWord_7900846
  simp only [CollatzResearch.WordTrace]
  refine ⟨36020940941823971739263299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192111685023061182609404261 36020940941823971739263299)
  ·
    refine ⟨54031411412735957608894949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36020940941823971739263299 54031411412735957608894949)
    ·
      refine ⟨10130889639887992051667803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54031411412735957608894949 10130889639887992051667803)
      ·
        refine ⟨15196334459831988077501705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10130889639887992051667803 15196334459831988077501705)
        ·
          refine ⟨11397250844873991058126279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15196334459831988077501705 11397250844873991058126279)
          ·
            refine ⟨17095876267310986587189419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11397250844873991058126279 17095876267310986587189419)
            ·
              refine ⟨25643814400966479880784129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17095876267310986587189419 25643814400966479880784129)
              ·
                refine ⟨19232860800724859910588097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25643814400966479880784129 19232860800724859910588097)
                ·
                  refine ⟨14424645600543644932941073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19232860800724859910588097 14424645600543644932941073)
                  ·
                    refine ⟨10818484200407733699705805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14424645600543644932941073 10818484200407733699705805)
                    ·
                      refine ⟨4056931575152900137389677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10818484200407733699705805 4056931575152900137389677)
                      ·
                        rfl

theorem cell23_7900846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_7900846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7900846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7900846 prefixEnd_7900846 := by exact prefixLift 7900846
  have htrace : WordTrace (prefixWord ++ tailWord_7900846) baseStart_7900846 baseEnd_7900846 := by
    simpa [prefixWord, tailWord_7900846, baseEnd_7900846] using wordTrace_append hprefix tailTrace_7900846
  have hstable : (prefixWord ++ tailWord_7900846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7900846).length < 2 ^ (prefixWord ++ tailWord_7900846).sum := by decide
  have hdescent : baseEnd_7900846 < baseStart_7900846 := by decide
  rcases family_descends (prefixWord ++ tailWord_7900846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7900853 : List Nat := [1, 3, 3, 3, 2, 1, 3, 2, 1, 4]
def baseStart_7900853 : Nat := 118140960795 + 7900853 * 2 ^ 59
def prefixEnd_7900853 : Nat := 4983230072969 + 3 ^ 40 * 7900853 * 2
def baseEnd_7900853 : Nat := 1352311723172493870000715

theorem tailTrace_7900853 : CollatzResearch.WordTrace tailWord_7900853 prefixEnd_7900853 1352311723172493870000715 := by
  unfold tailWord_7900853
  simp only [CollatzResearch.WordTrace]
  refine ⟨288167782845566414109611213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192111855230377609406407475 288167782845566414109611213)
  ·
    refine ⟨108062918567087405291104205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288167782845566414109611213 108062918567087405291104205)
    ·
      refine ⟨40523594462657776984164077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108062918567087405291104205 40523594462657776984164077)
      ·
        refine ⟨15196347923496666369061529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40523594462657776984164077 15196347923496666369061529)
        ·
          refine ⟨11397260942622499776796147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15196347923496666369061529 11397260942622499776796147)
          ·
            refine ⟨17095891413933749665194221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11397260942622499776796147 17095891413933749665194221)
            ·
              refine ⟨6410959280225156124447833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17095891413933749665194221 6410959280225156124447833)
              ·
                refine ⟨4808219460168867093335875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6410959280225156124447833 4808219460168867093335875)
                ·
                  refine ⟨7212329190253300640003813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4808219460168867093335875 7212329190253300640003813)
                  ·
                    refine ⟨1352311723172493870000715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7212329190253300640003813 1352311723172493870000715)
                    ·
                      rfl

theorem cell23_7900853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 3, 2, 1, 4].length) (baseStart_7900853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7900853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7900853 prefixEnd_7900853 := by exact prefixLift 7900853
  have htrace : WordTrace (prefixWord ++ tailWord_7900853) baseStart_7900853 baseEnd_7900853 := by
    simpa [prefixWord, tailWord_7900853, baseEnd_7900853] using wordTrace_append hprefix tailTrace_7900853
  have hstable : (prefixWord ++ tailWord_7900853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7900853).length < 2 ^ (prefixWord ++ tailWord_7900853).sum := by decide
  have hdescent : baseEnd_7900853 < baseStart_7900853 := by decide
  rcases family_descends (prefixWord ++ tailWord_7900853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7900859 : List Nat := [1, 1, 1, 1, 1, 2, 3, 8, 1, 1, 3]
def baseStart_7900859 : Nat := 118140960795 + 7900859 * 2 ^ 59
def prefixEnd_7900859 : Nat := 4983230072969 + 3 ^ 40 * 7900859 * 2
def baseEnd_7900859 : Nat := 4056938250401408586527117

theorem tailTrace_7900859 : CollatzResearch.WordTrace tailWord_7900859 prefixEnd_7900859 4056938250401408586527117 := by
  unfold tailWord_7900859
  simp only [CollatzResearch.WordTrace]
  refine ⟨288168001683544677134329631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192112001122363118089553087 288168001683544677134329631)
  ·
    refine ⟨432252002525317015701494447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288168001683544677134329631 432252002525317015701494447)
    ·
      refine ⟨648378003787975523552241671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432252002525317015701494447 648378003787975523552241671)
      ·
        refine ⟨972567005681963285328362507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 648378003787975523552241671 972567005681963285328362507)
        ·
          refine ⟨1458850508522944927992543761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 972567005681963285328362507 1458850508522944927992543761)
          ·
            refine ⟨1094137881392208695994407821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1458850508522944927992543761 1094137881392208695994407821)
            ·
              refine ⟨410301705522078260997902933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1094137881392208695994407821 410301705522078260997902933)
              ·
                refine ⟨4808223111586854621069175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 410301705522078260997902933 4808223111586854621069175)
                ·
                  refine ⟨7212334667380281931603763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4808223111586854621069175 7212334667380281931603763)
                  ·
                    refine ⟨10818502001070422897405645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7212334667380281931603763 10818502001070422897405645)
                    ·
                      refine ⟨4056938250401408586527117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10818502001070422897405645 4056938250401408586527117)
                      ·
                        rfl

theorem cell23_7900859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 8, 1, 1, 3].length) (baseStart_7900859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7900859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7900859 prefixEnd_7900859 := by exact prefixLift 7900859
  have htrace : WordTrace (prefixWord ++ tailWord_7900859) baseStart_7900859 baseEnd_7900859 := by
    simpa [prefixWord, tailWord_7900859, baseEnd_7900859] using wordTrace_append hprefix tailTrace_7900859
  have hstable : (prefixWord ++ tailWord_7900859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7900859).length < 2 ^ (prefixWord ++ tailWord_7900859).sum := by decide
  have hdescent : baseEnd_7900859 < baseStart_7900859 := by decide
  rcases family_descends (prefixWord ++ tailWord_7900859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7900909 : List Nat := [1, 5, 1, 2, 1, 2, 1, 4, 2, 4]
def baseStart_7900909 : Nat := 118140960795 + 7900909 * 2 ^ 59
def prefixEnd_7900909 : Nat := 4983230072969 + 3 ^ 40 * 7900909 * 2
def baseEnd_7900909 : Nat := 1352321308144711130300629

theorem tailTrace_7900909 : CollatzResearch.WordTrace tailWord_7900909 prefixEnd_7900909 1352321308144711130300629 := by
  unfold tailWord_7900909
  simp only [CollatzResearch.WordTrace]
  refine ⟨288169825333363535673649781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192113216888909023782433187 288169825333363535673649781)
  ·
    refine ⟨27015921125002831469404667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 288169825333363535673649781 27015921125002831469404667)
    ·
      refine ⟨40523881687504247204107001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27015921125002831469404667 40523881687504247204107001)
      ·
        refine ⟨30392911265628185403080251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40523881687504247204107001 30392911265628185403080251)
        ·
          refine ⟨45589366898442278104620377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30392911265628185403080251 45589366898442278104620377)
          ·
            refine ⟨34192025173831708578465283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45589366898442278104620377 34192025173831708578465283)
            ·
              refine ⟨51288037760747562867697925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34192025173831708578465283 51288037760747562867697925)
              ·
                refine ⟨9616507080140168037693361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51288037760747562867697925 9616507080140168037693361)
                ·
                  refine ⟨7212380310105126028270021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9616507080140168037693361 7212380310105126028270021)
                  ·
                    refine ⟨1352321308144711130300629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7212380310105126028270021 1352321308144711130300629)
                    ·
                      rfl

theorem cell23_7900909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 4, 2, 4].length) (baseStart_7900909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7900909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7900909 prefixEnd_7900909 := by exact prefixLift 7900909
  have htrace : WordTrace (prefixWord ++ tailWord_7900909) baseStart_7900909 baseEnd_7900909 := by
    simpa [prefixWord, tailWord_7900909, baseEnd_7900909] using wordTrace_append hprefix tailTrace_7900909
  have hstable : (prefixWord ++ tailWord_7900909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7900909).length < 2 ^ (prefixWord ++ tailWord_7900909).sum := by decide
  have hdescent : baseEnd_7900909 < baseStart_7900909 := by decide
  rcases family_descends (prefixWord ++ tailWord_7900909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7900916 : List Nat := [2, 6, 1, 1, 1, 1, 1, 2, 3, 1, 4]
def baseStart_7900916 : Nat := 118140960795 + 7900916 * 2 ^ 59
def prefixEnd_7900916 : Nat := 4983230072969 + 3 ^ 40 * 7900916 * 2
def baseEnd_7900916 : Nat := 4056967518798714863514355

theorem tailTrace_7900916 : CollatzResearch.WordTrace tailWord_7900916 prefixEnd_7900916 4056967518798714863514355 := by
  unfold tailWord_7900916
  simp only [CollatzResearch.WordTrace]
  refine ⟨144085040322169087934577301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192113387096225450579436401 144085040322169087934577301)
  ·
    refine ⟨6753986265101675996933311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 144085040322169087934577301 6753986265101675996933311)
    ·
      refine ⟨10130979397652513995399967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6753986265101675996933311 10130979397652513995399967)
      ·
        refine ⟨15196469096478770993099951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10130979397652513995399967 15196469096478770993099951)
        ·
          refine ⟨22794703644718156489649927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15196469096478770993099951 22794703644718156489649927)
          ·
            refine ⟨34192055467077234734474891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22794703644718156489649927 34192055467077234734474891)
            ·
              refine ⟨51288083200615852101712337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34192055467077234734474891 51288083200615852101712337)
              ·
                refine ⟨38466062400461889076284253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51288083200615852101712337 38466062400461889076284253)
                ·
                  refine ⟨14424773400173208403606595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38466062400461889076284253 14424773400173208403606595)
                  ·
                    refine ⟨21637160100259812605409893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14424773400173208403606595 21637160100259812605409893)
                    ·
                      refine ⟨4056967518798714863514355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21637160100259812605409893 4056967518798714863514355)
                      ·
                        rfl

theorem cell23_7900916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_7900916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7900916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7900916 prefixEnd_7900916 := by exact prefixLift 7900916
  have htrace : WordTrace (prefixWord ++ tailWord_7900916) baseStart_7900916 baseEnd_7900916 := by
    simpa [prefixWord, tailWord_7900916, baseEnd_7900916] using wordTrace_append hprefix tailTrace_7900916
  have hstable : (prefixWord ++ tailWord_7900916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7900916).length < 2 ^ (prefixWord ++ tailWord_7900916).sum := by decide
  have hdescent : baseEnd_7900916 < baseStart_7900916 := by decide
  rcases family_descends (prefixWord ++ tailWord_7900916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7900945 : List Nat := [1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 5]
def baseStart_7900945 : Nat := 118140960795 + 7900945 * 2 ^ 59
def prefixEnd_7900945 : Nat := 4983230072969 + 3 ^ 40 * 7900945 * 2
def baseEnd_7900945 : Nat := 4056982409737695250051721

theorem tailTrace_7900945 : CollatzResearch.WordTrace tailWord_7900945 prefixEnd_7900945 4056982409737695250051721 := by
  unfold tailWord_7900945
  simp only [CollatzResearch.WordTrace]
  refine ⟨288171138361233113821960289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192114092240822075881306859 288171138361233113821960289)
  ·
    refine ⟨216128353770924835366470217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288171138361233113821960289 216128353770924835366470217)
    ·
      refine ⟨162096265328193626524852663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216128353770924835366470217 162096265328193626524852663)
      ·
        refine ⟨243144397992290439787278995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162096265328193626524852663 243144397992290439787278995)
        ·
          refine ⟨364716596988435659680918493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243144397992290439787278995 364716596988435659680918493)
          ·
            refine ⟨136768723870663372380344435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 364716596988435659680918493 136768723870663372380344435)
            ·
              refine ⟨205153085805995058570516653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136768723870663372380344435 205153085805995058570516653)
              ·
                refine ⟨76932407177248146963943745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 205153085805995058570516653 76932407177248146963943745)
                ·
                  refine ⟨57699305382936110222957809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76932407177248146963943745 57699305382936110222957809)
                  ·
                    refine ⟨43274479037202082667218357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57699305382936110222957809 43274479037202082667218357)
                    ·
                      refine ⟨4056982409737695250051721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43274479037202082667218357 4056982409737695250051721)
                      ·
                        rfl

theorem cell23_7900945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 5].length) (baseStart_7900945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7900945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7900945 prefixEnd_7900945 := by exact prefixLift 7900945
  have htrace : WordTrace (prefixWord ++ tailWord_7900945) baseStart_7900945 baseEnd_7900945 := by
    simpa [prefixWord, tailWord_7900945, baseEnd_7900945] using wordTrace_append hprefix tailTrace_7900945
  have hstable : (prefixWord ++ tailWord_7900945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7900945).length < 2 ^ (prefixWord ++ tailWord_7900945).sum := by decide
  have hdescent : baseEnd_7900945 < baseStart_7900945 := by decide
  rcases family_descends (prefixWord ++ tailWord_7900945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7900955 : List Nat := [1, 1, 1, 1, 1, 1, 4, 2, 4, 3, 4]
def baseStart_7900955 : Nat := 118140960795 + 7900955 * 2 ^ 59
def prefixEnd_7900955 : Nat := 4983230072969 + 3 ^ 40 * 7900955 * 2
def baseEnd_7900955 : Nat := 4056987544544240210926675

theorem tailTrace_7900955 : CollatzResearch.WordTrace tailWord_7900955 prefixEnd_7900955 4056987544544240210926675 := by
  unfold tailWord_7900955
  simp only [CollatzResearch.WordTrace]
  refine ⟨288171503091196885529824319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192114335394131257019882879 288171503091196885529824319)
  ·
    refine ⟨432257254636795328294736479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288171503091196885529824319 432257254636795328294736479)
    ·
      refine ⟨648385881955192992442104719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432257254636795328294736479 648385881955192992442104719)
      ·
        refine ⟨972578822932789488663157079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 648385881955192992442104719 972578822932789488663157079)
        ·
          refine ⟨1458868234399184232994735619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 972578822932789488663157079 1458868234399184232994735619)
          ·
            refine ⟨2188302351598776349492103429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1458868234399184232994735619 2188302351598776349492103429)
            ·
              refine ⟨410306690924770565529769393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2188302351598776349492103429 410306690924770565529769393)
              ·
                refine ⟨307730018193577924147327045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 410306690924770565529769393 307730018193577924147327045)
                ·
                  refine ⟨57699378411295860777623821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 307730018193577924147327045 57699378411295860777623821)
                  ·
                    refine ⟨21637266904235947791608933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57699378411295860777623821 21637266904235947791608933)
                    ·
                      refine ⟨4056987544544240210926675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21637266904235947791608933 4056987544544240210926675)
                      ·
                        rfl

theorem cell23_7900955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 3, 4].length) (baseStart_7900955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7900955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7900955 prefixEnd_7900955 := by exact prefixLift 7900955
  have htrace : WordTrace (prefixWord ++ tailWord_7900955) baseStart_7900955 baseEnd_7900955 := by
    simpa [prefixWord, tailWord_7900955, baseEnd_7900955] using wordTrace_append hprefix tailTrace_7900955
  have hstable : (prefixWord ++ tailWord_7900955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7900955).length < 2 ^ (prefixWord ++ tailWord_7900955).sum := by decide
  have hdescent : baseEnd_7900955 < baseStart_7900955 := by decide
  rcases family_descends (prefixWord ++ tailWord_7900955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7900975 : List Nat := [1, 1, 2, 1, 2, 1, 2, 4, 1, 3, 5]
def baseStart_7900975 : Nat := 118140960795 + 7900975 * 2 ^ 59
def prefixEnd_7900975 : Nat := 4983230072969 + 3 ^ 40 * 7900975 * 2
def baseEnd_7900975 : Nat := 4056997814157330132676583

theorem tailTrace_7900975 : CollatzResearch.WordTrace tailWord_7900975 prefixEnd_7900975 4056997814157330132676583 := by
  unfold tailWord_7900975
  simp only [CollatzResearch.WordTrace]
  refine ⟨288172232551124428945552379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192114821700749619297034919 288172232551124428945552379)
  ·
    refine ⟨432258348826686643418328569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288172232551124428945552379 432258348826686643418328569)
    ·
      refine ⟨324193761620014982563746427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432258348826686643418328569 324193761620014982563746427)
      ·
        refine ⟨486290642430022473845619641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324193761620014982563746427 486290642430022473845619641)
        ·
          refine ⟨364717981822516855384214731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 486290642430022473845619641 364717981822516855384214731)
          ·
            refine ⟨547076972733775283076322097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364717981822516855384214731 547076972733775283076322097)
            ·
              refine ⟨410307729550331462307241573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 547076972733775283076322097 410307729550331462307241573)
              ·
                refine ⟨76932699290687149182607795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 410307729550331462307241573 76932699290687149182607795)
                ·
                  refine ⟨115399048936030723773911693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76932699290687149182607795 115399048936030723773911693)
                  ·
                    refine ⟨43274643351011521415216885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 115399048936030723773911693 43274643351011521415216885)
                    ·
                      refine ⟨4056997814157330132676583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43274643351011521415216885 4056997814157330132676583)
                      ·
                        rfl

theorem cell23_7900975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 3, 5].length) (baseStart_7900975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7900975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7900975 prefixEnd_7900975 := by exact prefixLift 7900975
  have htrace : WordTrace (prefixWord ++ tailWord_7900975) baseStart_7900975 baseEnd_7900975 := by
    simpa [prefixWord, tailWord_7900975, baseEnd_7900975] using wordTrace_append hprefix tailTrace_7900975
  have hstable : (prefixWord ++ tailWord_7900975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7900975).length < 2 ^ (prefixWord ++ tailWord_7900975).sum := by decide
  have hdescent : baseEnd_7900975 < baseStart_7900975 := by decide
  rcases family_descends (prefixWord ++ tailWord_7900975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7901042 : List Nat := [3, 2, 1, 2, 1, 1, 1, 1, 6, 5]
def baseStart_7901042 : Nat := 118140960795 + 7901042 * 2 ^ 59
def prefixEnd_7901042 : Nat := 4983230072969 + 3 ^ 40 * 7901042 * 2
def baseEnd_7901042 : Nat := 1352344072453727123512925

theorem tailTrace_7901042 : CollatzResearch.WordTrace tailWord_7901042 prefixEnd_7901042 1352344072453727123512925 := by
  unfold tailWord_7901042
  simp only [CollatzResearch.WordTrace]
  refine ⟨72043669060470424847060345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192116450827921132925494253 72043669060470424847060345)
  ·
    refine ⟨54032751795352818635295259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72043669060470424847060345 54032751795352818635295259)
    ·
      refine ⟨81049127693029227952942889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54032751795352818635295259 81049127693029227952942889)
      ·
        refine ⟨60786845769771920964707167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81049127693029227952942889 60786845769771920964707167)
        ·
          refine ⟨91180268654657881447060751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60786845769771920964707167 91180268654657881447060751)
          ·
            refine ⟨136770402981986822170591127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91180268654657881447060751 136770402981986822170591127)
            ·
              refine ⟨205155604472980233255886691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136770402981986822170591127 205155604472980233255886691)
              ·
                refine ⟨307733406709470349883830037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205155604472980233255886691 307733406709470349883830037)
                ·
                  refine ⟨14425003439506422650804533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 307733406709470349883830037 14425003439506422650804533)
                  ·
                    refine ⟨1352344072453727123512925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14425003439506422650804533 1352344072453727123512925)
                    ·
                      rfl

theorem cell23_7901042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 6, 5].length) (baseStart_7901042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7901042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7901042 prefixEnd_7901042 := by exact prefixLift 7901042
  have htrace : WordTrace (prefixWord ++ tailWord_7901042) baseStart_7901042 baseEnd_7901042 := by
    simpa [prefixWord, tailWord_7901042, baseEnd_7901042] using wordTrace_append hprefix tailTrace_7901042
  have hstable : (prefixWord ++ tailWord_7901042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7901042).length < 2 ^ (prefixWord ++ tailWord_7901042).sum := by decide
  have hdescent : baseEnd_7901042 < baseStart_7901042 := by decide
  rcases family_descends (prefixWord ++ tailWord_7901042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7901059 : List Nat := [1, 1, 1, 3, 4, 3, 2, 1, 2, 5]
def baseStart_7901059 : Nat := 118140960795 + 7901059 * 2 ^ 59
def prefixEnd_7901059 : Nat := 4983230072969 + 3 ^ 40 * 7901059 * 2
def baseEnd_7901059 : Nat := 1352346982177435934675399

theorem tailTrace_7901059 : CollatzResearch.WordTrace tailWord_7901059 prefixEnd_7901059 1352346982177435934675399 := by
  unfold tailWord_7901059
  simp only [CollatzResearch.WordTrace]
  refine ⟨288175296282820111291610231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192116864188546740861073487 288175296282820111291610231)
  ·
    refine ⟨432262944424230166937415347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288175296282820111291610231 432262944424230166937415347)
    ·
      refine ⟨648394416636345250406123021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432262944424230166937415347 648394416636345250406123021)
      ·
        refine ⟨243147906238629468902296133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 648394416636345250406123021 243147906238629468902296133)
        ·
          refine ⟨45590232419743025419180525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 243147906238629468902296133 45590232419743025419180525)
          ·
            refine ⟨17096337157403634532192697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45590232419743025419180525 17096337157403634532192697)
            ·
              refine ⟨12822252868052725899144523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17096337157403634532192697 12822252868052725899144523)
              ·
                refine ⟨19233379302079088848716785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12822252868052725899144523 19233379302079088848716785)
                ·
                  refine ⟨14425034476559316636537589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19233379302079088848716785 14425034476559316636537589)
                  ·
                    refine ⟨1352346982177435934675399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14425034476559316636537589 1352346982177435934675399)
                    ·
                      rfl

theorem cell23_7901059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 1, 2, 5].length) (baseStart_7901059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7901059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7901059 prefixEnd_7901059 := by exact prefixLift 7901059
  have htrace : WordTrace (prefixWord ++ tailWord_7901059) baseStart_7901059 baseEnd_7901059 := by
    simpa [prefixWord, tailWord_7901059, baseEnd_7901059] using wordTrace_append hprefix tailTrace_7901059
  have hstable : (prefixWord ++ tailWord_7901059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7901059).length < 2 ^ (prefixWord ++ tailWord_7901059).sum := by decide
  have hdescent : baseEnd_7901059 < baseStart_7901059 := by decide
  rcases family_descends (prefixWord ++ tailWord_7901059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7901079 : List Nat := [1, 1, 3, 3, 1, 3, 2, 2, 2, 1, 4]
def baseStart_7901079 : Nat := 118140960795 + 7901079 * 2 ^ 59
def prefixEnd_7901079 : Nat := 4983230072969 + 3 ^ 40 * 7901079 * 2
def baseEnd_7901079 : Nat := 4057051216145397725776105

theorem tailTrace_7901079 : CollatzResearch.WordTrace tailWord_7901079 prefixEnd_7901079 4057051216145397725776105 := by
  unfold tailWord_7901079
  simp only [CollatzResearch.WordTrace]
  refine ⟨288176025742747654707338291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192117350495165103138225527 288176025742747654707338291)
  ·
    refine ⟨432264038614121482061007437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288176025742747654707338291 432264038614121482061007437)
    ·
      refine ⟨162099014480295555772877789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 432264038614121482061007437 162099014480295555772877789)
      ·
        refine ⟨60787130430110833414829171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162099014480295555772877789 60787130430110833414829171)
        ·
          refine ⟨91180695645166250122243757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60787130430110833414829171 91180695645166250122243757)
          ·
            refine ⟨34192760866937343795841409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91180695645166250122243757 34192760866937343795841409)
            ·
              refine ⟨25644570650203007846881057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34192760866937343795841409 25644570650203007846881057)
              ·
                refine ⟨19233427987652255885160793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25644570650203007846881057 19233427987652255885160793)
                ·
                  refine ⟨14425070990739191913870595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19233427987652255885160793 14425070990739191913870595)
                  ·
                    refine ⟨21637606486108787870805893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14425070990739191913870595 21637606486108787870805893)
                    ·
                      refine ⟨4057051216145397725776105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21637606486108787870805893 4057051216145397725776105)
                      ·
                        rfl

theorem cell23_7901079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_7901079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7901079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7901079 prefixEnd_7901079 := by exact prefixLift 7901079
  have htrace : WordTrace (prefixWord ++ tailWord_7901079) baseStart_7901079 baseEnd_7901079 := by
    simpa [prefixWord, tailWord_7901079, baseEnd_7901079] using wordTrace_append hprefix tailTrace_7901079
  have hstable : (prefixWord ++ tailWord_7901079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7901079).length < 2 ^ (prefixWord ++ tailWord_7901079).sum := by decide
  have hdescent : baseEnd_7901079 < baseStart_7901079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7901079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7901080 : List Nat := [2, 1, 2, 6, 1, 2, 2, 2, 5]
def baseStart_7901080 : Nat := 118140960795 + 7901080 * 2 ^ 59
def prefixEnd_7901080 : Nat := 4983230072969 + 3 ^ 40 * 7901080 * 2
def baseEnd_7901080 : Nat := 450783525514005802429289

theorem tailTrace_7901080 : CollatzResearch.WordTrace tailWord_7901080 prefixEnd_7901080 450783525514005802429289 := by
  unfold tailWord_7901080
  simp only [CollatzResearch.WordTrace]
  refine ⟨144088031107872015939062347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192117374810496021252083129 144088031107872015939062347)
  ·
    refine ⟨216132046661808023908593521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144088031107872015939062347 216132046661808023908593521)
    ·
      refine ⟨162099034996356017931445141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216132046661808023908593521 162099034996356017931445141)
      ·
        refine ⟨7598392265454188340536491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 162099034996356017931445141 7598392265454188340536491)
        ·
          refine ⟨11397588398181282510804737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7598392265454188340536491 11397588398181282510804737)
          ·
            refine ⟨8548191298635961883103553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11397588398181282510804737 8548191298635961883103553)
            ·
              refine ⟨6411143473976971412327665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8548191298635961883103553 6411143473976971412327665)
              ·
                refine ⟨4808357605482728559245749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6411143473976971412327665 4808357605482728559245749)
                ·
                  refine ⟨450783525514005802429289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4808357605482728559245749 450783525514005802429289)
                  ·
                    rfl

theorem cell23_7901080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 2, 2, 5].length) (baseStart_7901080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7901080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7901080 prefixEnd_7901080 := by exact prefixLift 7901080
  have htrace : WordTrace (prefixWord ++ tailWord_7901080) baseStart_7901080 baseEnd_7901080 := by
    simpa [prefixWord, tailWord_7901080, baseEnd_7901080] using wordTrace_append hprefix tailTrace_7901080
  have hstable : (prefixWord ++ tailWord_7901080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7901080).length < 2 ^ (prefixWord ++ tailWord_7901080).sum := by decide
  have hdescent : baseEnd_7901080 < baseStart_7901080 := by decide
  rcases family_descends (prefixWord ++ tailWord_7901080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7901166 : List Nat := [4, 1, 2, 1, 3, 1, 1, 4, 1, 5]
def baseStart_7901166 : Nat := 118140960795 + 7901166 * 2 ^ 59
def prefixEnd_7901166 : Nat := 4983230072969 + 3 ^ 40 * 7901166 * 2
def baseEnd_7901166 : Nat := 1352365296320779628462735

theorem tailTrace_7901166 : CollatzResearch.WordTrace tailWord_7901166 prefixEnd_7901166 1352365296320779628462735 := by
  unfold tailWord_7901166
  simp only [CollatzResearch.WordTrace]
  refine ⟨36022399861679058570719419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192119465928954979043836901 36022399861679058570719419)
  ·
    refine ⟨54033599792518587856079129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36022399861679058570719419 54033599792518587856079129)
    ·
      refine ⟨40525199844388940892059347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54033599792518587856079129 40525199844388940892059347)
      ·
        refine ⟨60787799766583411338089021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40525199844388940892059347 60787799766583411338089021)
        ·
          refine ⟨22795424912468779251783383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60787799766583411338089021 22795424912468779251783383)
          ·
            refine ⟨34193137368703168877675075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22795424912468779251783383 34193137368703168877675075)
            ·
              refine ⟨51289706053054753316512613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34193137368703168877675075 51289706053054753316512613)
              ·
                refine ⟨9616819884947766246846115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51289706053054753316512613 9616819884947766246846115)
                ·
                  refine ⟨14425229827421649370269173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9616819884947766246846115 14425229827421649370269173)
                  ·
                    refine ⟨1352365296320779628462735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14425229827421649370269173 1352365296320779628462735)
                    ·
                      rfl

theorem cell23_7901166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 4, 1, 5].length) (baseStart_7901166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7901166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7901166 prefixEnd_7901166 := by exact prefixLift 7901166
  have htrace : WordTrace (prefixWord ++ tailWord_7901166) baseStart_7901166 baseEnd_7901166 := by
    simpa [prefixWord, tailWord_7901166, baseEnd_7901166] using wordTrace_append hprefix tailTrace_7901166
  have hstable : (prefixWord ++ tailWord_7901166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7901166).length < 2 ^ (prefixWord ++ tailWord_7901166).sum := by decide
  have hdescent : baseEnd_7901166 < baseStart_7901166 := by decide
  rcases family_descends (prefixWord ++ tailWord_7901166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
