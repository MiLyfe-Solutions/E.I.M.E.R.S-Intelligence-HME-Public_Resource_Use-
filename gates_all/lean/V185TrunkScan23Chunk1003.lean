import V185TrunkScan23Chunk1002

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5939225 : List Nat := [1, 2, 1, 2, 1, 1, 3, 1, 1, 3, 7]
def baseStart_5939225 : Nat := 118140960795 + 5939225 * 2 ^ 59
def prefixEnd_5939225 : Nat := 4983230072969 + 3 ^ 40 * 5939225 * 2
def baseEnd_5939225 : Nat := 3049677140199630488573507

theorem tailTrace_5939225 : CollatzResearch.WordTrace tailWord_5939225 prefixEnd_5939225 3049677140199630488573507 := by
  unfold tailWord_5939225
  simp only [CollatzResearch.WordTrace]
  refine ⟨216621331908209638719467129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144414221272139759146311419 216621331908209638719467129)
  ·
    refine ⟨162465998931157229039600347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216621331908209638719467129 162465998931157229039600347)
    ·
      refine ⟨243698998396735843559400521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162465998931157229039600347 243698998396735843559400521)
      ·
        refine ⟨182774248797551882669550391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243698998396735843559400521 182774248797551882669550391)
        ·
          refine ⟨274161373196327824004325587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182774248797551882669550391 274161373196327824004325587)
          ·
            refine ⟨411242059794491736006488381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274161373196327824004325587 411242059794491736006488381)
            ·
              refine ⟨154215772422934401002433143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 411242059794491736006488381 154215772422934401002433143)
              ·
                refine ⟨231323658634401601503649715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154215772422934401002433143 231323658634401601503649715)
                ·
                  refine ⟨346985487951602402255474573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 231323658634401601503649715 346985487951602402255474573)
                  ·
                    refine ⟨130119557981850900845802965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 346985487951602402255474573 130119557981850900845802965)
                    ·
                      refine ⟨3049677140199630488573507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 130119557981850900845802965 3049677140199630488573507)
                      ·
                        rfl

theorem cell23_5939225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 3, 7].length) (baseStart_5939225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5939225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5939225 prefixEnd_5939225 := by exact prefixLift 5939225
  have htrace : WordTrace (prefixWord ++ tailWord_5939225) baseStart_5939225 baseEnd_5939225 := by
    simpa [prefixWord, tailWord_5939225, baseEnd_5939225] using wordTrace_append hprefix tailTrace_5939225
  have hstable : (prefixWord ++ tailWord_5939225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5939225).length < 2 ^ (prefixWord ++ tailWord_5939225).sum := by decide
  have hdescent : baseEnd_5939225 < baseStart_5939225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5939225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5939233 : List Nat := [1, 2, 3, 2, 5, 1, 1, 1, 2, 2, 3]
def baseStart_5939233 : Nat := 118140960795 + 5939233 * 2 ^ 59
def prefixEnd_5939233 : Nat := 4983230072969 + 3 ^ 40 * 5939233 * 2
def baseEnd_5939233 : Nat := 3049681248044866457273471

theorem tailTrace_5939233 : CollatzResearch.WordTrace tailWord_5939233 prefixEnd_5939233 3049681248044866457273471 := by
  unfold tailWord_5939233
  simp only [CollatzResearch.WordTrace]
  refine ⟨216621623692180656085758353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144414415794787104057172235 216621623692180656085758353)
  ·
    refine ⟨162466217769135492064318765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216621623692180656085758353 162466217769135492064318765)
    ·
      refine ⟨60924831663425809524119537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162466217769135492064318765 60924831663425809524119537)
      ·
        refine ⟨45693623747569357143089653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60924831663425809524119537 45693623747569357143089653)
        ·
          refine ⟨4283777226334627232164655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45693623747569357143089653 4283777226334627232164655)
          ·
            refine ⟨6425665839501940848246983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4283777226334627232164655 6425665839501940848246983)
            ·
              refine ⟨9638498759252911272370475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6425665839501940848246983 9638498759252911272370475)
              ·
                refine ⟨14457748138879366908555713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9638498759252911272370475 14457748138879366908555713)
                ·
                  refine ⟨10843311104159525181416785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14457748138879366908555713 10843311104159525181416785)
                  ·
                    refine ⟨8132483328119643886062589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10843311104159525181416785 8132483328119643886062589)
                    ·
                      refine ⟨3049681248044866457273471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8132483328119643886062589 3049681248044866457273471)
                      ·
                        rfl

theorem cell23_5939233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 1, 2, 2, 3].length) (baseStart_5939233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5939233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5939233 prefixEnd_5939233 := by exact prefixLift 5939233
  have htrace : WordTrace (prefixWord ++ tailWord_5939233) baseStart_5939233 baseEnd_5939233 := by
    simpa [prefixWord, tailWord_5939233, baseEnd_5939233] using wordTrace_append hprefix tailTrace_5939233
  have hstable : (prefixWord ++ tailWord_5939233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5939233).length < 2 ^ (prefixWord ++ tailWord_5939233).sum := by decide
  have hdescent : baseEnd_5939233 < baseStart_5939233 := by decide
  rcases family_descends (prefixWord ++ tailWord_5939233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5939240 : List Nat := [2, 1, 5, 3, 1, 1, 2, 3, 1, 4]
def baseStart_5939240 : Nat := 118140960795 + 5939240 * 2 ^ 59
def prefixEnd_5939240 : Nat := 4983230072969 + 3 ^ 40 * 5939240 * 2
def baseEnd_5939240 : Nat := 1016561614136482643295313

theorem tailTrace_5939240 : CollatzResearch.WordTrace tailWord_5939240 prefixEnd_5939240 1016561614136482643295313 := by
  unfold tailWord_5939240
  simp only [CollatzResearch.WordTrace]
  refine ⟨108310939501577648140631587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144414586002103530854175449 108310939501577648140631587)
  ·
    refine ⟨162466409252366472210947381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108310939501577648140631587 162466409252366472210947381)
    ·
      refine ⟨15231225867409356769776317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 162466409252366472210947381 15231225867409356769776317)
      ·
        refine ⟨5711709700278508788666119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15231225867409356769776317 5711709700278508788666119)
        ·
          refine ⟨8567564550417763182999179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5711709700278508788666119 8567564550417763182999179)
          ·
            refine ⟨12851346825626644774498769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8567564550417763182999179 12851346825626644774498769)
            ·
              refine ⟨9638510119219983580874077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12851346825626644774498769 9638510119219983580874077)
              ·
                refine ⟨3614441294707493842827779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9638510119219983580874077 3614441294707493842827779)
                ·
                  refine ⟨5421661942061240764241669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3614441294707493842827779 5421661942061240764241669)
                  ·
                    refine ⟨1016561614136482643295313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5421661942061240764241669 1016561614136482643295313)
                    ·
                      rfl

theorem cell23_5939240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_5939240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5939240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5939240 prefixEnd_5939240 := by exact prefixLift 5939240
  have htrace : WordTrace (prefixWord ++ tailWord_5939240) baseStart_5939240 baseEnd_5939240 := by
    simpa [prefixWord, tailWord_5939240, baseEnd_5939240] using wordTrace_append hprefix tailTrace_5939240
  have hstable : (prefixWord ++ tailWord_5939240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5939240).length < 2 ^ (prefixWord ++ tailWord_5939240).sum := by decide
  have hdescent : baseEnd_5939240 < baseStart_5939240 := by decide
  rcases family_descends (prefixWord ++ tailWord_5939240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5939249 : List Nat := [1, 2, 2, 3, 1, 4, 1, 3, 1, 5]
def baseStart_5939249 : Nat := 118140960795 + 5939249 * 2 ^ 59
def prefixEnd_5939249 : Nat := 4983230072969 + 3 ^ 40 * 5939249 * 2
def baseEnd_5939249 : Nat := 1016563154578446131557799

theorem tailTrace_5939249 : CollatzResearch.WordTrace tailWord_5939249 prefixEnd_5939249 1016563154578446131557799 := by
  unfold tailWord_5939249
  simp only [CollatzResearch.WordTrace]
  refine ⟨216622207260122690818340801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144414804840081793878893867 216622207260122690818340801)
  ·
    refine ⟨162466655445092018113755601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216622207260122690818340801 162466655445092018113755601)
    ·
      refine ⟨121849991583819013585316701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162466655445092018113755601 121849991583819013585316701)
      ·
        refine ⟨45693746843932130094493763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121849991583819013585316701 45693746843932130094493763)
        ·
          refine ⟨68540620265898195141740645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45693746843932130094493763 68540620265898195141740645)
          ·
            refine ⟨12851366299855911589076371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68540620265898195141740645 12851366299855911589076371)
            ·
              refine ⟨19277049449783867383614557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12851366299855911589076371 19277049449783867383614557)
              ·
                refine ⟨7228893543668950268855459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19277049449783867383614557 7228893543668950268855459)
                ·
                  refine ⟨10843340315503425403283189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7228893543668950268855459 10843340315503425403283189)
                  ·
                    refine ⟨1016563154578446131557799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10843340315503425403283189 1016563154578446131557799)
                    ·
                      rfl

theorem cell23_5939249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 3, 1, 5].length) (baseStart_5939249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5939249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5939249 prefixEnd_5939249 := by exact prefixLift 5939249
  have htrace : WordTrace (prefixWord ++ tailWord_5939249) baseStart_5939249 baseEnd_5939249 := by
    simpa [prefixWord, tailWord_5939249, baseEnd_5939249] using wordTrace_append hprefix tailTrace_5939249
  have hstable : (prefixWord ++ tailWord_5939249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5939249).length < 2 ^ (prefixWord ++ tailWord_5939249).sum := by decide
  have hdescent : baseEnd_5939249 < baseStart_5939249 := by decide
  rcases family_descends (prefixWord ++ tailWord_5939249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5939272 : List Nat := [2, 1, 3, 1, 1, 1, 2, 1, 2, 6, 3]
def baseStart_5939272 : Nat := 118140960795 + 5939272 * 2 ^ 59
def prefixEnd_5939272 : Nat := 4983230072969 + 3 ^ 40 * 5939272 * 2
def baseEnd_5939272 : Nat := 3049701273790391804685791

theorem tailTrace_5939272 : CollatzResearch.WordTrace tailWord_5939272 prefixEnd_5939272 3049701273790391804685791 := by
  unfold tailWord_5939272
  simp only [CollatzResearch.WordTrace]
  refine ⟨108311523069519682873214035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144415364092692910497618713 108311523069519682873214035)
  ·
    refine ⟨162467284604279524309821053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108311523069519682873214035 162467284604279524309821053)
    ·
      refine ⟨60925231726604821616182895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162467284604279524309821053 60925231726604821616182895)
      ·
        refine ⟨91387847589907232424274343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60925231726604821616182895 91387847589907232424274343)
        ·
          refine ⟨137081771384860848636411515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91387847589907232424274343 137081771384860848636411515)
          ·
            refine ⟨205622657077291272954617273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137081771384860848636411515 205622657077291272954617273)
            ·
              refine ⟨154216992807968454715962955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 205622657077291272954617273 154216992807968454715962955)
              ·
                refine ⟨231325489211952682073944433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154216992807968454715962955 231325489211952682073944433)
                ·
                  refine ⟨173494116908964511555458325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 231325489211952682073944433 173494116908964511555458325)
                  ·
                    refine ⟨8132536730107711479162109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 173494116908964511555458325 8132536730107711479162109)
                    ·
                      refine ⟨3049701273790391804685791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8132536730107711479162109 3049701273790391804685791)
                      ·
                        rfl

theorem cell23_5939272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 2, 6, 3].length) (baseStart_5939272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5939272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5939272 prefixEnd_5939272 := by exact prefixLift 5939272
  have htrace : WordTrace (prefixWord ++ tailWord_5939272) baseStart_5939272 baseEnd_5939272 := by
    simpa [prefixWord, tailWord_5939272, baseEnd_5939272] using wordTrace_append hprefix tailTrace_5939272
  have hstable : (prefixWord ++ tailWord_5939272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5939272).length < 2 ^ (prefixWord ++ tailWord_5939272).sum := by decide
  have hdescent : baseEnd_5939272 < baseStart_5939272 := by decide
  rcases family_descends (prefixWord ++ tailWord_5939272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5939306 : List Nat := [3, 1, 3, 2, 3, 1, 2, 1, 1, 1, 5]
def baseStart_5939306 : Nat := 118140960795 + 5939306 * 2 ^ 59
def prefixEnd_5939306 : Nat := 4983230072969 + 3 ^ 40 * 5939306 * 2
def baseEnd_5939306 : Nat := 3049718732132644671660635

theorem tailTrace_5939306 : CollatzResearch.WordTrace tailWord_5939306 prefixEnd_5939306 3049718732132644671660635 := by
  unfold tailWord_5939306
  simp only [CollatzResearch.WordTrace]
  refine ⟨54156071555229047388291443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144416190813944126368777181 54156071555229047388291443)
  ·
    refine ⟨81234107332843571082437165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54156071555229047388291443 81234107332843571082437165)
    ·
      refine ⟨30462790249816339155913937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81234107332843571082437165 30462790249816339155913937)
      ·
        refine ⟨22847092687362254366935453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30462790249816339155913937 22847092687362254366935453)
        ·
          refine ⟨8567659757760845387600795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22847092687362254366935453 8567659757760845387600795)
          ·
            refine ⟨12851489636641268081401193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8567659757760845387600795 12851489636641268081401193)
            ·
              refine ⟨9638617227480951061050895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12851489636641268081401193 9638617227480951061050895)
              ·
                refine ⟨14457925841221426591576343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9638617227480951061050895 14457925841221426591576343)
                ·
                  refine ⟨21686888761832139887364515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14457925841221426591576343 21686888761832139887364515)
                  ·
                    refine ⟨32530333142748209831046773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21686888761832139887364515 32530333142748209831046773)
                    ·
                      refine ⟨3049718732132644671660635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32530333142748209831046773 3049718732132644671660635)
                      ·
                        rfl

theorem cell23_5939306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_5939306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5939306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5939306 prefixEnd_5939306 := by exact prefixLift 5939306
  have htrace : WordTrace (prefixWord ++ tailWord_5939306) baseStart_5939306 baseEnd_5939306 := by
    simpa [prefixWord, tailWord_5939306, baseEnd_5939306] using wordTrace_append hprefix tailTrace_5939306
  have hstable : (prefixWord ++ tailWord_5939306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5939306).length < 2 ^ (prefixWord ++ tailWord_5939306).sum := by decide
  have hdescent : baseEnd_5939306 < baseStart_5939306 := by decide
  rcases family_descends (prefixWord ++ tailWord_5939306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5939414 : List Nat := [5, 2, 1, 2, 1, 3, 2, 1, 1, 3, 2]
def baseStart_5939414 : Nat := 118140960795 + 5939414 * 2 ^ 59
def prefixEnd_5939414 : Nat := 4983230072969 + 3 ^ 40 * 5939414 * 2
def baseEnd_5939414 : Nat := 3049774188043330249110139

theorem tailTrace_5939414 : CollatzResearch.WordTrace tailWord_5939414 prefixEnd_5939414 3049774188043330249110139 := by
  unfold tailWord_5939414
  simp only [CollatzResearch.WordTrace]
  refine ⟨13539264081532807749881081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 144418816869683282665398197 13539264081532807749881081)
  ·
    refine ⟨10154448061149605812410811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13539264081532807749881081 10154448061149605812410811)
    ·
      refine ⟨15231672091724408718616217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10154448061149605812410811 15231672091724408718616217)
      ·
        refine ⟨11423754068793306538962163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15231672091724408718616217 11423754068793306538962163)
        ·
          refine ⟨17135631103189959808443245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11423754068793306538962163 17135631103189959808443245)
          ·
            refine ⟨6425861663696234928166217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17135631103189959808443245 6425861663696234928166217)
            ·
              refine ⟨4819396247772176196124663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6425861663696234928166217 4819396247772176196124663)
              ·
                refine ⟨7229094371658264294186995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4819396247772176196124663 7229094371658264294186995)
                ·
                  refine ⟨10843641557487396441280493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7229094371658264294186995 10843641557487396441280493)
                  ·
                    refine ⟨4066365584057773665480185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10843641557487396441280493 4066365584057773665480185)
                    ·
                      refine ⟨3049774188043330249110139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4066365584057773665480185 3049774188043330249110139)
                      ·
                        rfl

theorem cell23_5939414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_5939414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5939414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5939414 prefixEnd_5939414 := by exact prefixLift 5939414
  have htrace : WordTrace (prefixWord ++ tailWord_5939414) baseStart_5939414 baseEnd_5939414 := by
    simpa [prefixWord, tailWord_5939414, baseEnd_5939414] using wordTrace_append hprefix tailTrace_5939414
  have hstable : (prefixWord ++ tailWord_5939414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5939414).length < 2 ^ (prefixWord ++ tailWord_5939414).sum := by decide
  have hdescent : baseEnd_5939414 < baseStart_5939414 := by decide
  rcases family_descends (prefixWord ++ tailWord_5939414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5939416 : List Nat := [2, 1, 2, 2, 4, 1, 1, 5, 5]
def baseStart_5939416 : Nat := 118140960795 + 5939416 * 2 ^ 59
def prefixEnd_5939416 : Nat := 4983230072969 + 3 ^ 40 * 5939416 * 2
def baseEnd_5939416 : Nat := 338863912778293249031681

theorem tailTrace_5939416 : CollatzResearch.WordTrace tailWord_5939416 prefixEnd_5939416 338863912778293249031681 := by
  unfold tailWord_5939416
  simp only [CollatzResearch.WordTrace]
  refine ⟨108314149125258839169835051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144418865500345118893113401 108314149125258839169835051)
  ·
    refine ⟨162471223687888258754752577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108314149125258839169835051 162471223687888258754752577)
    ·
      refine ⟨121853417765916194066064433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162471223687888258754752577 121853417765916194066064433)
      ·
        refine ⟨91390063324437145549548325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121853417765916194066064433 91390063324437145549548325)
        ·
          refine ⟨17135636873331964790540311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91390063324437145549548325 17135636873331964790540311)
          ·
            refine ⟨25703455309997947185810467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17135636873331964790540311 25703455309997947185810467)
            ·
              refine ⟨38555182964996920778715701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25703455309997947185810467 38555182964996920778715701)
              ·
                refine ⟨3614548402968461323004597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38555182964996920778715701 3614548402968461323004597)
                ·
                  refine ⟨338863912778293249031681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3614548402968461323004597 338863912778293249031681)
                  ·
                    rfl

theorem cell23_5939416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 5, 5].length) (baseStart_5939416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5939416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5939416 prefixEnd_5939416 := by exact prefixLift 5939416
  have htrace : WordTrace (prefixWord ++ tailWord_5939416) baseStart_5939416 baseEnd_5939416 := by
    simpa [prefixWord, tailWord_5939416, baseEnd_5939416] using wordTrace_append hprefix tailTrace_5939416
  have hstable : (prefixWord ++ tailWord_5939416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5939416).length < 2 ^ (prefixWord ++ tailWord_5939416).sum := by decide
  have hdescent : baseEnd_5939416 < baseStart_5939416 := by decide
  rcases family_descends (prefixWord ++ tailWord_5939416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5939449 : List Nat := [1, 2, 1, 3, 1, 1, 2, 1, 6, 1, 4]
def baseStart_5939449 : Nat := 118140960795 + 5939449 * 2 ^ 59
def prefixEnd_5939449 : Nat := 4983230072969 + 3 ^ 40 * 5939449 * 2
def baseEnd_5939449 : Nat := 3049792159866237612172477

theorem tailTrace_5939449 : CollatzResearch.WordTrace tailWord_5939449 prefixEnd_5939449 3049792159866237612172477 := by
  unfold tailWord_5939449
  simp only [CollatzResearch.WordTrace]
  refine ⟨216629501859398124975621401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144419667906265416650414267 216629501859398124975621401)
  ·
    refine ⟨162472126394548593731716051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216629501859398124975621401 162472126394548593731716051)
    ·
      refine ⟨243708189591822890597574077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162472126394548593731716051 243708189591822890597574077)
      ·
        refine ⟨91390571096933583974090279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 243708189591822890597574077 91390571096933583974090279)
        ·
          refine ⟨137085856645400375961135419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91390571096933583974090279 137085856645400375961135419)
          ·
            refine ⟨205628784968100563941703129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137085856645400375961135419 205628784968100563941703129)
            ·
              refine ⟨154221588726075422956277347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 205628784968100563941703129 154221588726075422956277347)
              ·
                refine ⟨231332383089113134434416021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154221588726075422956277347 231332383089113134434416021)
                ·
                  refine ⟨10843705457302178176613251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 231332383089113134434416021 10843705457302178176613251)
                  ·
                    refine ⟨16265558185953267264919877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10843705457302178176613251 16265558185953267264919877)
                    ·
                      refine ⟨3049792159866237612172477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16265558185953267264919877 3049792159866237612172477)
                      ·
                        rfl

theorem cell23_5939449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 6, 1, 4].length) (baseStart_5939449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5939449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5939449 prefixEnd_5939449 := by exact prefixLift 5939449
  have htrace : WordTrace (prefixWord ++ tailWord_5939449) baseStart_5939449 baseEnd_5939449 := by
    simpa [prefixWord, tailWord_5939449, baseEnd_5939449] using wordTrace_append hprefix tailTrace_5939449
  have hstable : (prefixWord ++ tailWord_5939449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5939449).length < 2 ^ (prefixWord ++ tailWord_5939449).sum := by decide
  have hdescent : baseEnd_5939449 < baseStart_5939449 := by decide
  rcases family_descends (prefixWord ++ tailWord_5939449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5939466 : List Nat := [3, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2]
def baseStart_5939466 : Nat := 118140960795 + 5939466 * 2 ^ 59
def prefixEnd_5939466 : Nat := 4983230072969 + 3 ^ 40 * 5939466 * 2
def baseEnd_5939466 : Nat := 3049800889037364045659899

theorem tailTrace_5939466 : CollatzResearch.WordTrace tailWord_5939466 prefixEnd_5939466 3049800889037364045659899 := by
  unfold tailWord_5939466
  simp only [CollatzResearch.WordTrace]
  refine ⟨54157530475084134219747563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144420081266891024585993501 54157530475084134219747563)
  ·
    refine ⟨81236295712626201329621345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54157530475084134219747563 81236295712626201329621345)
    ·
      refine ⟨60927221784469650997216009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81236295712626201329621345 60927221784469650997216009)
      ·
        refine ⟨45695416338352238247912007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60927221784469650997216009 45695416338352238247912007)
        ·
          refine ⟨68543124507528357371868011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45695416338352238247912007 68543124507528357371868011)
          ·
            refine ⟨102814686761292536057802017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68543124507528357371868011 102814686761292536057802017)
            ·
              refine ⟨77111015070969402043351513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102814686761292536057802017 77111015070969402043351513)
              ·
                refine ⟨57833261303227051532513635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77111015070969402043351513 57833261303227051532513635)
                ·
                  refine ⟨86749891954840577298770453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57833261303227051532513635 86749891954840577298770453)
                  ·
                    refine ⟨4066401185383152060879865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 86749891954840577298770453 4066401185383152060879865)
                    ·
                      refine ⟨3049800889037364045659899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4066401185383152060879865 3049800889037364045659899)
                      ·
                        rfl

theorem cell23_5939466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2].length) (baseStart_5939466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5939466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5939466 prefixEnd_5939466 := by exact prefixLift 5939466
  have htrace : WordTrace (prefixWord ++ tailWord_5939466) baseStart_5939466 baseEnd_5939466 := by
    simpa [prefixWord, tailWord_5939466, baseEnd_5939466] using wordTrace_append hprefix tailTrace_5939466
  have hstable : (prefixWord ++ tailWord_5939466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5939466).length < 2 ^ (prefixWord ++ tailWord_5939466).sum := by decide
  have hdescent : baseEnd_5939466 < baseStart_5939466 := by decide
  rcases family_descends (prefixWord ++ tailWord_5939466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5939489 : List Nat := [1, 2, 3, 2, 1, 1, 4, 1, 8]
def baseStart_5939489 : Nat := 118140960795 + 5939489 * 2 ^ 59
def prefixEnd_5939489 : Nat := 4983230072969 + 3 ^ 40 * 5939489 * 2
def baseEnd_5939489 : Nat := 338868077676935272852477

theorem tailTrace_5939489 : CollatzResearch.WordTrace tailWord_5939489 prefixEnd_5939489 338868077676935272852477 := by
  unfold tailWord_5939489
  simp only [CollatzResearch.WordTrace]
  refine ⟨216630960779253211807077521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144420640519502141204718347 216630960779253211807077521)
  ·
    refine ⟨162473220584439908855308141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216630960779253211807077521 162473220584439908855308141)
    ·
      refine ⟨60927457719164965820740553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162473220584439908855308141 60927457719164965820740553)
      ·
        refine ⟨45695593289373724365555415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60927457719164965820740553 45695593289373724365555415)
        ·
          refine ⟨68543389934060586548333123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45695593289373724365555415 68543389934060586548333123)
          ·
            refine ⟨102815084901090879822499685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68543389934060586548333123 102815084901090879822499685)
            ·
              refine ⟨19277828418954539966718691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102815084901090879822499685 19277828418954539966718691)
              ·
                refine ⟨28916742628431809950078037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19277828418954539966718691 28916742628431809950078037)
                ·
                  refine ⟨338868077676935272852477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28916742628431809950078037 338868077676935272852477)
                  ·
                    rfl

theorem cell23_5939489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 8].length) (baseStart_5939489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5939489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5939489 prefixEnd_5939489 := by exact prefixLift 5939489
  have htrace : WordTrace (prefixWord ++ tailWord_5939489) baseStart_5939489 baseEnd_5939489 := by
    simpa [prefixWord, tailWord_5939489, baseEnd_5939489] using wordTrace_append hprefix tailTrace_5939489
  have hstable : (prefixWord ++ tailWord_5939489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5939489).length < 2 ^ (prefixWord ++ tailWord_5939489).sum := by decide
  have hdescent : baseEnd_5939489 < baseStart_5939489 := by decide
  rcases family_descends (prefixWord ++ tailWord_5939489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5939543 : List Nat := [1, 1, 3, 2, 3, 1, 1, 4, 2, 3, 2]
def baseStart_5939543 : Nat := 118140960795 + 5939543 * 2 ^ 59
def prefixEnd_5939543 : Nat := 4983230072969 + 3 ^ 40 * 5939543 * 2
def baseEnd_5939543 : Nat := 3049840427047760244397045

theorem tailTrace_5939543 : CollatzResearch.WordTrace tailWord_5939543 prefixEnd_5939543 3049840427047760244397045 := by
  unfold tailWord_5939543
  simp only [CollatzResearch.WordTrace]
  refine ⟨216632930321057579029543283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144421953547371719353028855 216632930321057579029543283)
  ·
    refine ⟨324949395481586368544314925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216632930321057579029543283 324949395481586368544314925)
    ·
      refine ⟨121856023305594888204118097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 324949395481586368544314925 121856023305594888204118097)
      ·
        refine ⟨91392017479196166153088573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121856023305594888204118097 91392017479196166153088573)
        ·
          refine ⟨34272006554698562307408215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91392017479196166153088573 34272006554698562307408215)
          ·
            refine ⟨51408009832047843461112323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34272006554698562307408215 51408009832047843461112323)
            ·
              refine ⟨77112014748071765191668485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51408009832047843461112323 77112014748071765191668485)
              ·
                refine ⟨14458502765263455973437841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77112014748071765191668485 14458502765263455973437841)
                ·
                  refine ⟨10843877073947591980078381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14458502765263455973437841 10843877073947591980078381)
                  ·
                    refine ⟨4066453902730346992529393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10843877073947591980078381 4066453902730346992529393)
                    ·
                      refine ⟨3049840427047760244397045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4066453902730346992529393 3049840427047760244397045)
                      ·
                        rfl

theorem cell23_5939543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 4, 2, 3, 2].length) (baseStart_5939543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5939543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5939543 prefixEnd_5939543 := by exact prefixLift 5939543
  have htrace : WordTrace (prefixWord ++ tailWord_5939543) baseStart_5939543 baseEnd_5939543 := by
    simpa [prefixWord, tailWord_5939543, baseEnd_5939543] using wordTrace_append hprefix tailTrace_5939543
  have hstable : (prefixWord ++ tailWord_5939543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5939543).length < 2 ^ (prefixWord ++ tailWord_5939543).sum := by decide
  have hdescent : baseEnd_5939543 < baseStart_5939543 := by decide
  rcases family_descends (prefixWord ++ tailWord_5939543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5939556 : List Nat := [2, 3, 1, 1, 3, 1, 1, 1, 5, 1, 4]
def baseStart_5939556 : Nat := 118140960795 + 5939556 * 2 ^ 59
def prefixEnd_5939556 : Nat := 4983230072969 + 3 ^ 40 * 5939556 * 2
def baseEnd_5939556 : Nat := 3049847102296268693534485

theorem tailTrace_5939556 : CollatzResearch.WordTrace tailWord_5939556 prefixEnd_5939556 3049847102296268693534485 := by
  unfold tailWord_5939556
  simp only [CollatzResearch.WordTrace]
  refine ⟨108316702235005241124883261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144422269646673654833177681 108316702235005241124883261)
  ·
    refine ⟨40618763338126965421831223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108316702235005241124883261 40618763338126965421831223)
    ·
      refine ⟨60928145007190448132746835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40618763338126965421831223 60928145007190448132746835)
      ·
        refine ⟨91392217510785672199120253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60928145007190448132746835 91392217510785672199120253)
        ·
          refine ⟨34272081566544627074670095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91392217510785672199120253 34272081566544627074670095)
          ·
            refine ⟨51408122349816940612005143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34272081566544627074670095 51408122349816940612005143)
            ·
              refine ⟨77112183524725410918007715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51408122349816940612005143 77112183524725410918007715)
              ·
                refine ⟨115668275287088116377011573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77112183524725410918007715 115668275287088116377011573)
                ·
                  refine ⟨10843900808164510910344835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 115668275287088116377011573 10843900808164510910344835)
                  ·
                    refine ⟨16265851212246766365517253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10843900808164510910344835 16265851212246766365517253)
                    ·
                      refine ⟨3049847102296268693534485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16265851212246766365517253 3049847102296268693534485)
                      ·
                        rfl

theorem cell23_5939556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 5, 1, 4].length) (baseStart_5939556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5939556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5939556 prefixEnd_5939556 := by exact prefixLift 5939556
  have htrace : WordTrace (prefixWord ++ tailWord_5939556) baseStart_5939556 baseEnd_5939556 := by
    simpa [prefixWord, tailWord_5939556, baseEnd_5939556] using wordTrace_append hprefix tailTrace_5939556
  have hstable : (prefixWord ++ tailWord_5939556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5939556).length < 2 ^ (prefixWord ++ tailWord_5939556).sum := by decide
  have hdescent : baseEnd_5939556 < baseStart_5939556 := by decide
  rcases family_descends (prefixWord ++ tailWord_5939556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5939573 : List Nat := [1, 3, 4, 1, 2, 1, 2, 1, 3, 1, 4]
def baseStart_5939573 : Nat := 118140960795 + 5939573 * 2 ^ 59
def prefixEnd_5939573 : Nat := 4983230072969 + 3 ^ 40 * 5939573 * 2
def baseEnd_5939573 : Nat := 3049855831467395127021907

theorem tailTrace_5939573 : CollatzResearch.WordTrace tailWord_5939573 prefixEnd_5939573 3049855831467395127021907 := by
  unfold tailWord_5939573
  simp only [CollatzResearch.WordTrace]
  refine ⟨216634024510948894153135373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144422683007299262768756915 216634024510948894153135373)
  ·
    refine ⟨81237759191605835307425765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216634024510948894153135373 81237759191605835307425765)
    ·
      refine ⟨15232079848426094120142331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81237759191605835307425765 15232079848426094120142331)
      ·
        refine ⟨22848119772639141180213497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15232079848426094120142331 22848119772639141180213497)
        ·
          refine ⟨17136089829479355885160123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22848119772639141180213497 17136089829479355885160123)
          ·
            refine ⟨25704134744219033827740185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17136089829479355885160123 25704134744219033827740185)
            ·
              refine ⟨19278101058164275370805139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25704134744219033827740185 19278101058164275370805139)
              ·
                refine ⟨28917151587246413056207709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19278101058164275370805139 28917151587246413056207709)
                ·
                  refine ⟨10843931845217404896077891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28917151587246413056207709 10843931845217404896077891)
                  ·
                    refine ⟨16265897767826107344116837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10843931845217404896077891 16265897767826107344116837)
                    ·
                      refine ⟨3049855831467395127021907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16265897767826107344116837 3049855831467395127021907)
                      ·
                        rfl

theorem cell23_5939573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_5939573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5939573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5939573 prefixEnd_5939573 := by exact prefixLift 5939573
  have htrace : WordTrace (prefixWord ++ tailWord_5939573) baseStart_5939573 baseEnd_5939573 := by
    simpa [prefixWord, tailWord_5939573, baseEnd_5939573] using wordTrace_append hprefix tailTrace_5939573
  have hstable : (prefixWord ++ tailWord_5939573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5939573).length < 2 ^ (prefixWord ++ tailWord_5939573).sum := by decide
  have hdescent : baseEnd_5939573 < baseStart_5939573 := by decide
  rcases family_descends (prefixWord ++ tailWord_5939573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5939587 : List Nat := [1, 1, 1, 3, 7, 1, 2, 1, 1, 5]
def baseStart_5939587 : Nat := 118140960795 + 5939587 * 2 ^ 59
def prefixEnd_5939587 : Nat := 4983230072969 + 3 ^ 40 * 5939587 * 2
def baseEnd_5939587 : Nat := 1016621006732186024082281

theorem tailTrace_5939587 : CollatzResearch.WordTrace tailWord_5939587 prefixEnd_5939587 1016621006732186024082281 := by
  unfold tailWord_5939587
  simp only [CollatzResearch.WordTrace]
  refine ⟨216634535132898174544145015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144423023421932116362763343 216634535132898174544145015)
  ·
    refine ⟨324951802699347261816217523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216634535132898174544145015 324951802699347261816217523)
    ·
      refine ⟨487427704049020892724326285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324951802699347261816217523 487427704049020892724326285)
      ·
        refine ⟨182785389018382834771622357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 487427704049020892724326285 182785389018382834771622357)
        ·
          refine ⟨4284032555118347689959899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 182785389018382834771622357 4284032555118347689959899)
          ·
            refine ⟨6426048832677521534939849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4284032555118347689959899 6426048832677521534939849)
            ·
              refine ⟨4819536624508141151204887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6426048832677521534939849 4819536624508141151204887)
              ·
                refine ⟨7229304936762211726807331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4819536624508141151204887 7229304936762211726807331)
                ·
                  refine ⟨10843957405143317590210997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7229304936762211726807331 10843957405143317590210997)
                  ·
                    refine ⟨1016621006732186024082281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10843957405143317590210997 1016621006732186024082281)
                    ·
                      rfl

theorem cell23_5939587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 2, 1, 1, 5].length) (baseStart_5939587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5939587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5939587 prefixEnd_5939587 := by exact prefixLift 5939587
  have htrace : WordTrace (prefixWord ++ tailWord_5939587) baseStart_5939587 baseEnd_5939587 := by
    simpa [prefixWord, tailWord_5939587, baseEnd_5939587] using wordTrace_append hprefix tailTrace_5939587
  have hstable : (prefixWord ++ tailWord_5939587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5939587).length < 2 ^ (prefixWord ++ tailWord_5939587).sum := by decide
  have hdescent : baseEnd_5939587 < baseStart_5939587 := by decide
  rcases family_descends (prefixWord ++ tailWord_5939587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5939607 : List Nat := [1, 1, 3, 3, 1, 1, 4, 4, 1, 2, 2]
def baseStart_5939607 : Nat := 118140960795 + 5939607 * 2 ^ 59
def prefixEnd_5939607 : Nat := 4983230072969 + 3 ^ 40 * 5939607 * 2
def baseEnd_5939607 : Nat := 3049873289809647993996751

theorem tailTrace_5939607 : CollatzResearch.WordTrace tailWord_5939607 prefixEnd_5939607 3049873289809647993996751 := by
  unfold tailWord_5939607
  simp only [CollatzResearch.WordTrace]
  refine ⟨216635264592825717959873075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144423509728550478639915383 216635264592825717959873075)
  ·
    refine ⟨324952896889238576939809613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216635264592825717959873075 324952896889238576939809613)
    ·
      refine ⟨121857336333464466352428605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 324952896889238576939809613 121857336333464466352428605)
      ·
        refine ⟨45696501125049174882160727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121857336333464466352428605 45696501125049174882160727)
        ·
          refine ⟨68544751687573762323241091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45696501125049174882160727 68544751687573762323241091)
          ·
            refine ⟨102817127531360643484861637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68544751687573762323241091 102817127531360643484861637)
            ·
              refine ⟨19278211412130120653411557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102817127531360643484861637 19278211412130120653411557)
              ·
                refine ⟨3614664639774397622514667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19278211412130120653411557 3614664639774397622514667)
                ·
                  refine ⟨5421996959661596433772001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3614664639774397622514667 5421996959661596433772001)
                  ·
                    refine ⟨4066497719746197325329001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5421996959661596433772001 4066497719746197325329001)
                    ·
                      refine ⟨3049873289809647993996751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4066497719746197325329001 3049873289809647993996751)
                      ·
                        rfl

theorem cell23_5939607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 4, 1, 2, 2].length) (baseStart_5939607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5939607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5939607 prefixEnd_5939607 := by exact prefixLift 5939607
  have htrace : WordTrace (prefixWord ++ tailWord_5939607) baseStart_5939607 baseEnd_5939607 := by
    simpa [prefixWord, tailWord_5939607, baseEnd_5939607] using wordTrace_append hprefix tailTrace_5939607
  have hstable : (prefixWord ++ tailWord_5939607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5939607).length < 2 ^ (prefixWord ++ tailWord_5939607).sum := by decide
  have hdescent : baseEnd_5939607 < baseStart_5939607 := by decide
  rcases family_descends (prefixWord ++ tailWord_5939607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5939617 : List Nat := [1, 2, 3, 5, 2, 1, 1, 1, 1, 6]
def baseStart_5939617 : Nat := 118140960795 + 5939617 * 2 ^ 59
def prefixEnd_5939617 : Nat := 4983230072969 + 3 ^ 40 * 5939617 * 2
def baseEnd_5939617 : Nat := 1016626141538730984957235

theorem tailTrace_5939617 : CollatzResearch.WordTrace tailWord_5939617 prefixEnd_5939617 1016626141538730984957235 := by
  unfold tailWord_5939617
  simp only [CollatzResearch.WordTrace]
  refine ⟨216635629322789489667737105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144423752881859659778491403 216635629322789489667737105)
  ·
    refine ⟨162476721992092117250802829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216635629322789489667737105 162476721992092117250802829)
    ·
      refine ⟨60928770747034543969051061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162476721992092117250802829 60928770747034543969051061)
      ·
        refine ⟨5712072257534488497098537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60928770747034543969051061 5712072257534488497098537)
        ·
          refine ⟨4284054193150866372823903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5712072257534488497098537 4284054193150866372823903)
          ·
            refine ⟨6426081289726299559235855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4284054193150866372823903 6426081289726299559235855)
            ·
              refine ⟨9639121934589449338853783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6426081289726299559235855 9639121934589449338853783)
              ·
                refine ⟨14458682901884174008280675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9639121934589449338853783 14458682901884174008280675)
                ·
                  refine ⟨21688024352826261012421013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14458682901884174008280675 21688024352826261012421013)
                  ·
                    refine ⟨1016626141538730984957235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21688024352826261012421013 1016626141538730984957235)
                    ·
                      rfl

theorem cell23_5939617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 1, 1, 6].length) (baseStart_5939617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5939617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5939617 prefixEnd_5939617 := by exact prefixLift 5939617
  have htrace : WordTrace (prefixWord ++ tailWord_5939617) baseStart_5939617 baseEnd_5939617 := by
    simpa [prefixWord, tailWord_5939617, baseEnd_5939617] using wordTrace_append hprefix tailTrace_5939617
  have hstable : (prefixWord ++ tailWord_5939617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5939617).length < 2 ^ (prefixWord ++ tailWord_5939617).sum := by decide
  have hdescent : baseEnd_5939617 < baseStart_5939617 := by decide
  rcases family_descends (prefixWord ++ tailWord_5939617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5939701 : List Nat := [1, 3, 5, 1, 2, 1, 3, 1, 1, 3, 2]
def baseStart_5939701 : Nat := 118140960795 + 5939701 * 2 ^ 59
def prefixEnd_5939701 : Nat := 4983230072969 + 3 ^ 40 * 5939701 * 2
def baseEnd_5939701 : Nat := 3049921556991170626221319

theorem tailTrace_5939701 : CollatzResearch.WordTrace tailWord_5939701 prefixEnd_5939701 3049921556991170626221319 := by
  unfold tailWord_5939701
  simp only [CollatzResearch.WordTrace]
  refine ⟨216638693054485172013794957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144425795369656781342529971 216638693054485172013794957)
  ·
    refine ⟨81239509895431939505173109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216638693054485172013794957 81239509895431939505173109)
    ·
      refine ⟨7616204052696744328609979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81239509895431939505173109 7616204052696744328609979)
      ·
        refine ⟨11424306079045116492914969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7616204052696744328609979 11424306079045116492914969)
        ·
          refine ⟨8568229559283837369686227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11424306079045116492914969 8568229559283837369686227)
          ·
            refine ⟨12852344338925756054529341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8568229559283837369686227 12852344338925756054529341)
            ·
              refine ⟨4819629127097158520448503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12852344338925756054529341 4819629127097158520448503)
              ·
                refine ⟨7229443690645737780672755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4819629127097158520448503 7229443690645737780672755)
                ·
                  refine ⟨10844165535968606671009133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7229443690645737780672755 10844165535968606671009133)
                  ·
                    refine ⟨4066562075988227501628425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10844165535968606671009133 4066562075988227501628425)
                    ·
                      refine ⟨3049921556991170626221319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4066562075988227501628425 3049921556991170626221319)
                      ·
                        rfl

theorem cell23_5939701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_5939701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5939701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5939701 prefixEnd_5939701 := by exact prefixLift 5939701
  have htrace : WordTrace (prefixWord ++ tailWord_5939701) baseStart_5939701 baseEnd_5939701 := by
    simpa [prefixWord, tailWord_5939701, baseEnd_5939701] using wordTrace_append hprefix tailTrace_5939701
  have hstable : (prefixWord ++ tailWord_5939701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5939701).length < 2 ^ (prefixWord ++ tailWord_5939701).sum := by decide
  have hdescent : baseEnd_5939701 < baseStart_5939701 := by decide
  rcases family_descends (prefixWord ++ tailWord_5939701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5939763 : List Nat := [1, 1, 1, 2, 4, 2, 1, 2, 5, 4]
def baseStart_5939763 : Nat := 118140960795 + 5939763 * 2 ^ 59
def prefixEnd_5939763 : Nat := 4983230072969 + 3 ^ 40 * 5939763 * 2
def baseEnd_5939763 : Nat := 1016651130930583127882011

theorem tailTrace_5939763 : CollatzResearch.WordTrace tailWord_5939763 prefixEnd_5939763 1016651130930583127882011 := by
  unfold tailWord_5939763
  simp only [CollatzResearch.WordTrace]
  refine ⟨216640954380260556602551943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144427302920173704401701295 216640954380260556602551943)
  ·
    refine ⟨324961431570390834903827915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216640954380260556602551943 324961431570390834903827915)
    ·
      refine ⟨487442147355586252355741873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324961431570390834903827915 487442147355586252355741873)
      ·
        refine ⟨365581610516689689266806405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 487442147355586252355741873 365581610516689689266806405)
        ·
          refine ⟨68546551971879316737526201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 365581610516689689266806405 68546551971879316737526201)
          ·
            refine ⟨51409913978909487553144651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68546551971879316737526201 51409913978909487553144651)
            ·
              refine ⟨77114870968364231329716977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51409913978909487553144651 77114870968364231329716977)
              ·
                refine ⟨57836153226273173497287733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77114870968364231329716977 57836153226273173497287733)
                ·
                  refine ⟨5422139364963110015370725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57836153226273173497287733 5422139364963110015370725)
                  ·
                    refine ⟨1016651130930583127882011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5422139364963110015370725 1016651130930583127882011)
                    ·
                      rfl

theorem cell23_5939763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 5, 4].length) (baseStart_5939763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5939763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5939763 prefixEnd_5939763 := by exact prefixLift 5939763
  have htrace : WordTrace (prefixWord ++ tailWord_5939763) baseStart_5939763 baseEnd_5939763 := by
    simpa [prefixWord, tailWord_5939763, baseEnd_5939763] using wordTrace_append hprefix tailTrace_5939763
  have hstable : (prefixWord ++ tailWord_5939763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5939763).length < 2 ^ (prefixWord ++ tailWord_5939763).sum := by decide
  have hdescent : baseEnd_5939763 < baseStart_5939763 := by decide
  rcases family_descends (prefixWord ++ tailWord_5939763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5939770 : List Nat := [3, 1, 1, 1, 3, 3, 1, 2, 2, 4, 2]
def baseStart_5939770 : Nat := 118140960795 + 5939770 * 2 ^ 59
def prefixEnd_5939770 : Nat := 4983230072969 + 3 ^ 40 * 5939770 * 2
def baseEnd_5939770 : Nat := 3049956987156330856258501

theorem tailTrace_5939770 : CollatzResearch.WordTrace tailWord_5939770 prefixEnd_5939770 3049956987156330856258501 := by
  unfold tailWord_5939770
  simp only [CollatzResearch.WordTrace]
  refine ⟨54160302422808799199514191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144427473127490131198704509 54160302422808799199514191)
  ·
    refine ⟨81240453634213198799271287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54160302422808799199514191 81240453634213198799271287)
    ·
      refine ⟨121860680451319798198906931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81240453634213198799271287 121860680451319798198906931)
      ·
        refine ⟨182791020676979697298360397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121860680451319798198906931 182791020676979697298360397)
        ·
          refine ⟨68546632753867386486885149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182791020676979697298360397 68546632753867386486885149)
          ·
            refine ⟨25704987282700269932581931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68546632753867386486885149 25704987282700269932581931)
            ·
              refine ⟨38557480924050404898872897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25704987282700269932581931 38557480924050404898872897)
              ·
                refine ⟨28918110693037803674154673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38557480924050404898872897 28918110693037803674154673)
                ·
                  refine ⟨21688583019778352755616005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28918110693037803674154673 21688583019778352755616005)
                  ·
                    refine ⟨4066609316208441141678001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21688583019778352755616005 4066609316208441141678001)
                    ·
                      refine ⟨3049956987156330856258501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4066609316208441141678001 3049956987156330856258501)
                      ·
                        rfl

theorem cell23_5939770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 2, 4, 2].length) (baseStart_5939770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5939770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5939770 prefixEnd_5939770 := by exact prefixLift 5939770
  have htrace : WordTrace (prefixWord ++ tailWord_5939770) baseStart_5939770 baseEnd_5939770 := by
    simpa [prefixWord, tailWord_5939770, baseEnd_5939770] using wordTrace_append hprefix tailTrace_5939770
  have hstable : (prefixWord ++ tailWord_5939770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5939770).length < 2 ^ (prefixWord ++ tailWord_5939770).sum := by decide
  have hdescent : baseEnd_5939770 < baseStart_5939770 := by decide
  rcases family_descends (prefixWord ++ tailWord_5939770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5939820 : List Nat := [2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 3]
def baseStart_5939820 : Nat := 118140960795 + 5939820 * 2 ^ 59
def prefixEnd_5939820 : Nat := 4983230072969 + 3 ^ 40 * 5939820 * 2
def baseEnd_5939820 : Nat := 3049982661189055660633271

theorem tailTrace_5939820 : CollatzResearch.WordTrace tailWord_5939820 prefixEnd_5939820 3049982661189055660633271 := by
  unfold tailWord_5939820
  simp only [CollatzResearch.WordTrace]
  refine ⟨108321516670527027668688457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144428688894036036891584609 108321516670527027668688457)
  ·
    refine ⟨81241137502895270751516343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108321516670527027668688457 81241137502895270751516343)
    ·
      refine ⟨121861706254342906127274515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81241137502895270751516343 121861706254342906127274515)
      ·
        refine ⟨182792559381514359190911773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121861706254342906127274515 182792559381514359190911773)
        ·
          refine ⟨68547209768067884696591915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182792559381514359190911773 68547209768067884696591915)
          ·
            refine ⟨102820814652101827044887873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68547209768067884696591915 102820814652101827044887873)
            ·
              refine ⟨77115610989076370283665905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102820814652101827044887873 77115610989076370283665905)
              ·
                refine ⟨57836708241807277712749429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77115610989076370283665905 57836708241807277712749429)
                ·
                  refine ⟨5422191397669432285570259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57836708241807277712749429 5422191397669432285570259)
                  ·
                    refine ⟨8133287096504148428355389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5422191397669432285570259 8133287096504148428355389)
                    ·
                      refine ⟨3049982661189055660633271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8133287096504148428355389 3049982661189055660633271)
                      ·
                        rfl

theorem cell23_5939820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 3].length) (baseStart_5939820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5939820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5939820 prefixEnd_5939820 := by exact prefixLift 5939820
  have htrace : WordTrace (prefixWord ++ tailWord_5939820) baseStart_5939820 baseEnd_5939820 := by
    simpa [prefixWord, tailWord_5939820, baseEnd_5939820] using wordTrace_append hprefix tailTrace_5939820
  have hstable : (prefixWord ++ tailWord_5939820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5939820).length < 2 ^ (prefixWord ++ tailWord_5939820).sum := by decide
  have hdescent : baseEnd_5939820 < baseStart_5939820 := by decide
  rcases family_descends (prefixWord ++ tailWord_5939820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5939887 : List Nat := [1, 1, 2, 1, 2, 6, 2, 2, 2, 4]
def baseStart_5939887 : Nat := 118140960795 + 5939887 * 2 ^ 59
def prefixEnd_5939887 : Nat := 4983230072969 + 3 ^ 40 * 5939887 * 2
def baseEnd_5939887 : Nat := 1016672354797635632831821

theorem tailTrace_5939887 : CollatzResearch.WordTrace tailWord_5939887 prefixEnd_5939887 1016672354797635632831821 := by
  unfold tailWord_5939887
  simp only [CollatzResearch.WordTrace]
  refine ⟨216645477031811325780065915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144430318021207550520043943 216645477031811325780065915)
  ·
    refine ⟨324968215547716988670098873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216645477031811325780065915 324968215547716988670098873)
    ·
      refine ⟨243726161660787741502574155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 324968215547716988670098873 243726161660787741502574155)
      ·
        refine ⟨365589242491181612253861233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243726161660787741502574155 365589242491181612253861233)
        ·
          refine ⟨274191931868386209190395925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 365589242491181612253861233 274191931868386209190395925)
          ·
            refine ⟨12852746806330603555799809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 274191931868386209190395925 12852746806330603555799809)
            ·
              refine ⟨9639560104747952666849857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12852746806330603555799809 9639560104747952666849857)
              ·
                refine ⟨7229670078560964500137393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9639560104747952666849857 7229670078560964500137393)
                ·
                  refine ⟨5422252558920723375103045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7229670078560964500137393 5422252558920723375103045)
                  ·
                    refine ⟨1016672354797635632831821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5422252558920723375103045 1016672354797635632831821)
                    ·
                      rfl

theorem cell23_5939887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 2, 2, 4].length) (baseStart_5939887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5939887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5939887 prefixEnd_5939887 := by exact prefixLift 5939887
  have htrace : WordTrace (prefixWord ++ tailWord_5939887) baseStart_5939887 baseEnd_5939887 := by
    simpa [prefixWord, tailWord_5939887, baseEnd_5939887] using wordTrace_append hprefix tailTrace_5939887
  have hstable : (prefixWord ++ tailWord_5939887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5939887).length < 2 ^ (prefixWord ++ tailWord_5939887).sum := by decide
  have hdescent : baseEnd_5939887 < baseStart_5939887 := by decide
  rcases family_descends (prefixWord ++ tailWord_5939887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5939944 : List Nat := [2, 1, 4, 1, 4, 1, 1, 1, 4, 1, 3]
def baseStart_5939944 : Nat := 118140960795 + 5939944 * 2 ^ 59
def prefixEnd_5939944 : Nat := 4983230072969 + 3 ^ 40 * 5939944 * 2
def baseEnd_5939944 : Nat := 3050046332790213175482701

theorem tailTrace_5939944 : CollatzResearch.WordTrace tailWord_5939944 prefixEnd_5939944 3050046332790213175482701 := by
  unfold tailWord_5939944
  simp only [CollatzResearch.WordTrace]
  refine ⟨108323777996302412257445443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144431703995069883009927257 108323777996302412257445443)
  ·
    refine ⟨162485666994453618386168165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108323777996302412257445443 162485666994453618386168165)
    ·
      refine ⟨30466062561460053447406531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 162485666994453618386168165 30466062561460053447406531)
      ·
        refine ⟨45699093842190080171109797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30466062561460053447406531 45699093842190080171109797)
        ·
          refine ⟨8568580095410640032083087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45699093842190080171109797 8568580095410640032083087)
          ·
            refine ⟨12852870143115960048124631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8568580095410640032083087 12852870143115960048124631)
            ·
              refine ⟨19279305214673940072186947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12852870143115960048124631 19279305214673940072186947)
              ·
                refine ⟨28918957822010910108280421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19279305214673940072186947 28918957822010910108280421)
                ·
                  refine ⟨5422304591627045645302579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28918957822010910108280421 5422304591627045645302579)
                  ·
                    refine ⟨8133456887440568467953869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5422304591627045645302579 8133456887440568467953869)
                    ·
                      refine ⟨3050046332790213175482701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8133456887440568467953869 3050046332790213175482701)
                      ·
                        rfl

theorem cell23_5939944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 4, 1, 3].length) (baseStart_5939944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5939944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5939944 prefixEnd_5939944 := by exact prefixLift 5939944
  have htrace : WordTrace (prefixWord ++ tailWord_5939944) baseStart_5939944 baseEnd_5939944 := by
    simpa [prefixWord, tailWord_5939944, baseEnd_5939944] using wordTrace_append hprefix tailTrace_5939944
  have hstable : (prefixWord ++ tailWord_5939944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5939944).length < 2 ^ (prefixWord ++ tailWord_5939944).sum := by decide
  have hdescent : baseEnd_5939944 < baseStart_5939944 := by decide
  rcases family_descends (prefixWord ++ tailWord_5939944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5940057 : List Nat := [1, 2, 1, 2, 2, 4, 2, 2, 2, 1, 4]
def baseStart_5940057 : Nat := 118140960795 + 5940057 * 2 ^ 59
def prefixEnd_5940057 : Nat := 4983230072969 + 3 ^ 40 * 5940057 * 2
def baseEnd_5940057 : Nat := 3050104356104171233369681

theorem tailTrace_5940057 : CollatzResearch.WordTrace tailWord_5940057 prefixEnd_5940057 3050104356104171233369681 := by
  unfold tailWord_5940057
  simp only [CollatzResearch.WordTrace]
  refine ⟨216651677441195444813754425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144434451627463629875836283 216651677441195444813754425)
  ·
    refine ⟨162488758080896583610315819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216651677441195444813754425 162488758080896583610315819)
    ·
      refine ⟨243733137121344875415473729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162488758080896583610315819 243733137121344875415473729)
      ·
        refine ⟨182799852841008656561605297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243733137121344875415473729 182799852841008656561605297)
        ·
          refine ⟨137099889630756492421203973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182799852841008656561605297 137099889630756492421203973)
          ·
            refine ⟨25706229305766842328975745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 137099889630756492421203973 25706229305766842328975745)
            ·
              refine ⟨19279671979325131746731809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25706229305766842328975745 19279671979325131746731809)
              ·
                refine ⟨14459753984493848810048857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19279671979325131746731809 14459753984493848810048857)
                ·
                  refine ⟨10844815488370386607536643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14459753984493848810048857 10844815488370386607536643)
                  ·
                    refine ⟨16267223232555579911304965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10844815488370386607536643 16267223232555579911304965)
                    ·
                      refine ⟨3050104356104171233369681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16267223232555579911304965 3050104356104171233369681)
                      ·
                        rfl

theorem cell23_5940057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 2, 2, 1, 4].length) (baseStart_5940057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5940057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5940057 prefixEnd_5940057 := by exact prefixLift 5940057
  have htrace : WordTrace (prefixWord ++ tailWord_5940057) baseStart_5940057 baseEnd_5940057 := by
    simpa [prefixWord, tailWord_5940057, baseEnd_5940057] using wordTrace_append hprefix tailTrace_5940057
  have hstable : (prefixWord ++ tailWord_5940057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5940057).length < 2 ^ (prefixWord ++ tailWord_5940057).sum := by decide
  have hdescent : baseEnd_5940057 < baseStart_5940057 := by decide
  rcases family_descends (prefixWord ++ tailWord_5940057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5940077 : List Nat := [1, 5, 1, 1, 1, 1, 1, 4, 1, 4, 3]
def baseStart_5940077 : Nat := 118140960795 + 5940077 * 2 ^ 59
def prefixEnd_5940077 : Nat := 4983230072969 + 3 ^ 40 * 5940077 * 2
def baseEnd_5940077 : Nat := 3050114625717261155119589

theorem tailTrace_5940077 : CollatzResearch.WordTrace tailWord_5940077 prefixEnd_5940077 3050114625717261155119589 := by
  unfold tailWord_5940077
  simp only [CollatzResearch.WordTrace]
  refine ⟨216652406901122988229482485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144434937934081992152988323 216652406901122988229482485)
  ·
    refine ⟨20311163146980280146513983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 216652406901122988229482485 20311163146980280146513983)
    ·
      refine ⟨30466744720470420219770975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20311163146980280146513983 30466744720470420219770975)
      ·
        refine ⟨45700117080705630329656463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30466744720470420219770975 45700117080705630329656463)
        ·
          refine ⟨68550175621058445494484695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45700117080705630329656463 68550175621058445494484695)
          ·
            refine ⟨102825263431587668241727043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68550175621058445494484695 102825263431587668241727043)
            ·
              refine ⟨154237895147381502362590565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102825263431587668241727043 154237895147381502362590565)
              ·
                refine ⟨28919605340134031692985731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 154237895147381502362590565 28919605340134031692985731)
                ·
                  refine ⟨43379408010201047539478597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28919605340134031692985731 43379408010201047539478597)
                  ·
                    refine ⟨8133639001912696413652237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43379408010201047539478597 8133639001912696413652237)
                    ·
                      refine ⟨3050114625717261155119589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8133639001912696413652237 3050114625717261155119589)
                      ·
                        rfl

theorem cell23_5940077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 4, 3].length) (baseStart_5940077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5940077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5940077 prefixEnd_5940077 := by exact prefixLift 5940077
  have htrace : WordTrace (prefixWord ++ tailWord_5940077) baseStart_5940077 baseEnd_5940077 := by
    simpa [prefixWord, tailWord_5940077, baseEnd_5940077] using wordTrace_append hprefix tailTrace_5940077
  have hstable : (prefixWord ++ tailWord_5940077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5940077).length < 2 ^ (prefixWord ++ tailWord_5940077).sum := by decide
  have hdescent : baseEnd_5940077 < baseStart_5940077 := by decide
  rcases family_descends (prefixWord ++ tailWord_5940077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5940101 : List Nat := [1, 3, 1, 1, 3, 4, 2, 3, 1, 4]
def baseStart_5940101 : Nat := 118140960795 + 5940101 * 2 ^ 59
def prefixEnd_5940101 : Nat := 4983230072969 + 3 ^ 40 * 5940101 * 2
def baseEnd_5940101 : Nat := 1016708983084323020406493

theorem tailTrace_5940101 : CollatzResearch.WordTrace tailWord_5940101 prefixEnd_5940101 1016708983084323020406493 := by
  unfold tailWord_5940101
  simp only [CollatzResearch.WordTrace]
  refine ⟨216653282253036040328356157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144435521502024026885570771 216653282253036040328356157)
  ·
    refine ⟨81244980844888515123133559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216653282253036040328356157 81244980844888515123133559)
    ·
      refine ⟨121867471267332772684700339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81244980844888515123133559 121867471267332772684700339)
      ·
        refine ⟨182801206900999159027050509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121867471267332772684700339 182801206900999159027050509)
        ·
          refine ⟨68550452587874684635143941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182801206900999159027050509 68550452587874684635143941)
          ·
            refine ⟨12853209860226503369089489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68550452587874684635143941 12853209860226503369089489)
            ·
              refine ⟨9639907395169877526817117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12853209860226503369089489 9639907395169877526817117)
              ·
                refine ⟨3614965273188704072556419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9639907395169877526817117 3614965273188704072556419)
                ·
                  refine ⟨5422447909783056108834629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3614965273188704072556419 5422447909783056108834629)
                  ·
                    refine ⟨1016708983084323020406493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5422447909783056108834629 1016708983084323020406493)
                    ·
                      rfl

theorem cell23_5940101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 3, 1, 4].length) (baseStart_5940101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5940101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5940101 prefixEnd_5940101 := by exact prefixLift 5940101
  have htrace : WordTrace (prefixWord ++ tailWord_5940101) baseStart_5940101 baseEnd_5940101 := by
    simpa [prefixWord, tailWord_5940101, baseEnd_5940101] using wordTrace_append hprefix tailTrace_5940101
  have hstable : (prefixWord ++ tailWord_5940101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5940101).length < 2 ^ (prefixWord ++ tailWord_5940101).sum := by decide
  have hdescent : baseEnd_5940101 < baseStart_5940101 := by decide
  rcases family_descends (prefixWord ++ tailWord_5940101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5940114 : List Nat := [3, 2, 3, 2, 2, 1, 1, 1, 8]
def baseStart_5940114 : Nat := 118140960795 + 5940114 * 2 ^ 59
def prefixEnd_5940114 : Nat := 4983230072969 + 3 ^ 40 * 5940114 * 2
def baseEnd_5940114 : Nat := 338903736055719723372991

theorem tailTrace_5940114 : CollatzResearch.WordTrace tailWord_5940114 prefixEnd_5940114 338903736055719723372991 := by
  unfold tailWord_5940114
  simp only [CollatzResearch.WordTrace]
  refine ⟨54163439100497235887144849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144435837601325962365719597 54163439100497235887144849)
  ·
    refine ⟨40622579325372926915358637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54163439100497235887144849 40622579325372926915358637)
    ·
      refine ⟨15233467247014847593259489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40622579325372926915358637 15233467247014847593259489)
      ·
        refine ⟨11425100435261135694944617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15233467247014847593259489 11425100435261135694944617)
        ·
          refine ⟨8568825326445851771208463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11425100435261135694944617 8568825326445851771208463)
          ·
            refine ⟨12853237989668777656812695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8568825326445851771208463 12853237989668777656812695)
            ·
              refine ⟨19279856984503166485219043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12853237989668777656812695 19279856984503166485219043)
              ·
                refine ⟨28919785476754749727828565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19279856984503166485219043 28919785476754749727828565)
                ·
                  refine ⟨338903736055719723372991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28919785476754749727828565 338903736055719723372991)
                  ·
                    rfl

theorem cell23_5940114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 8].length) (baseStart_5940114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5940114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5940114 prefixEnd_5940114 := by exact prefixLift 5940114
  have htrace : WordTrace (prefixWord ++ tailWord_5940114) baseStart_5940114 baseEnd_5940114 := by
    simpa [prefixWord, tailWord_5940114, baseEnd_5940114] using wordTrace_append hprefix tailTrace_5940114
  have hstable : (prefixWord ++ tailWord_5940114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5940114).length < 2 ^ (prefixWord ++ tailWord_5940114).sum := by decide
  have hdescent : baseEnd_5940114 < baseStart_5940114 := by decide
  rcases family_descends (prefixWord ++ tailWord_5940114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5940118 : List Nat := [5, 3, 1, 1, 1, 1, 1, 3, 3, 4]
def baseStart_5940118 : Nat := 118140960795 + 5940118 * 2 ^ 59
def prefixEnd_5940118 : Nat := 4983230072969 + 3 ^ 40 * 5940118 * 2
def baseEnd_5940118 : Nat := 1016711892808031831568967

theorem tailTrace_5940118 : CollatzResearch.WordTrace tailWord_5940118 prefixEnd_5940118 1016711892808031831568967 := by
  unfold tailWord_5940118
  simp only [CollatzResearch.WordTrace]
  refine ⟨13540868893373403264482813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 144435934862649634821150005 13540868893373403264482813)
  ·
    refine ⟨5077825835015026224181055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13540868893373403264482813 5077825835015026224181055)
    ·
      refine ⟨7616738752522539336271583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5077825835015026224181055 7616738752522539336271583)
      ·
        refine ⟨11425108128783809004407375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7616738752522539336271583 11425108128783809004407375)
        ·
          refine ⟨17137662193175713506611063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11425108128783809004407375 17137662193175713506611063)
          ·
            refine ⟨25706493289763570259916595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17137662193175713506611063 25706493289763570259916595)
            ·
              refine ⟨38559739934645355389874893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25706493289763570259916595 38559739934645355389874893)
              ·
                refine ⟨14459902475492008271203085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38559739934645355389874893 14459902475492008271203085)
                ·
                  refine ⟨5422463428309503101701157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14459902475492008271203085 5422463428309503101701157)
                  ·
                    refine ⟨1016711892808031831568967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5422463428309503101701157 1016711892808031831568967)
                    ·
                      rfl

theorem cell23_5940118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_5940118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5940118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5940118 prefixEnd_5940118 := by exact prefixLift 5940118
  have htrace : WordTrace (prefixWord ++ tailWord_5940118) baseStart_5940118 baseEnd_5940118 := by
    simpa [prefixWord, tailWord_5940118, baseEnd_5940118] using wordTrace_append hprefix tailTrace_5940118
  have hstable : (prefixWord ++ tailWord_5940118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5940118).length < 2 ^ (prefixWord ++ tailWord_5940118).sum := by decide
  have hdescent : baseEnd_5940118 < baseStart_5940118 := by decide
  rcases family_descends (prefixWord ++ tailWord_5940118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5940167 : List Nat := [1, 1, 4, 1, 1, 2, 3, 3, 1, 1, 5]
def baseStart_5940167 : Nat := 118140960795 + 5940167 * 2 ^ 59
def prefixEnd_5940167 : Nat := 4983230072969 + 3 ^ 40 * 5940167 * 2
def baseEnd_5940167 : Nat := 3050160838976165802994175

theorem tailTrace_5940167 : CollatzResearch.WordTrace tailWord_5940167 prefixEnd_5940167 3050160838976165802994175 := by
  unfold tailWord_5940167
  simp only [CollatzResearch.WordTrace]
  refine ⟨216655689470796933600258755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144437126313864622400172503 216655689470796933600258755)
  ·
    refine ⟨324983534206195400400388133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216655689470796933600258755 324983534206195400400388133)
    ·
      refine ⟨60934412663661637575072775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 324983534206195400400388133 60934412663661637575072775)
      ·
        refine ⟨91401618995492456362609163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60934412663661637575072775 91401618995492456362609163)
        ·
          refine ⟨137102428493238684543913745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91401618995492456362609163 137102428493238684543913745)
          ·
            refine ⟨102826821369929013407935309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137102428493238684543913745 102826821369929013407935309)
            ·
              refine ⟨38560058013723380027975741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102826821369929013407935309 38560058013723380027975741)
              ·
                refine ⟨14460021755146267510490903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38560058013723380027975741 14460021755146267510490903)
                ·
                  refine ⟨21690032632719401265736355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14460021755146267510490903 21690032632719401265736355)
                  ·
                    refine ⟨32535048949079101898604533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21690032632719401265736355 32535048949079101898604533)
                    ·
                      refine ⟨3050160838976165802994175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32535048949079101898604533 3050160838976165802994175)
                      ·
                        rfl

theorem cell23_5940167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 3, 1, 1, 5].length) (baseStart_5940167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5940167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5940167 prefixEnd_5940167 := by exact prefixLift 5940167
  have htrace : WordTrace (prefixWord ++ tailWord_5940167) baseStart_5940167 baseEnd_5940167 := by
    simpa [prefixWord, tailWord_5940167, baseEnd_5940167] using wordTrace_append hprefix tailTrace_5940167
  have hstable : (prefixWord ++ tailWord_5940167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5940167).length < 2 ^ (prefixWord ++ tailWord_5940167).sum := by decide
  have hdescent : baseEnd_5940167 < baseStart_5940167 := by decide
  rcases family_descends (prefixWord ++ tailWord_5940167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5940174 : List Nat := [4, 1, 1, 1, 2, 3, 2, 1, 4, 4]
def baseStart_5940174 : Nat := 118140960795 + 5940174 * 2 ^ 59
def prefixEnd_5940174 : Nat := 4983230072969 + 3 ^ 40 * 5940174 * 2
def baseEnd_5940174 : Nat := 1016721477780249091868881

theorem tailTrace_5940174 : CollatzResearch.WordTrace tailWord_5940174 prefixEnd_5940174 1016721477780249091868881 := by
  unfold tailWord_5940174
  simp only [CollatzResearch.WordTrace]
  refine ⟨27081993097721446724470447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144437296521181049197175717 27081993097721446724470447)
  ·
    refine ⟨40622989646582170086705671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27081993097721446724470447 40622989646582170086705671)
    ·
      refine ⟨60934484469873255130058507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40622989646582170086705671 60934484469873255130058507)
      ·
        refine ⟨91401726704809882695087761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60934484469873255130058507 91401726704809882695087761)
        ·
          refine ⟨68551295028607412021315821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91401726704809882695087761 68551295028607412021315821)
          ·
            refine ⟨25706735635727779507993433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68551295028607412021315821 25706735635727779507993433)
            ·
              refine ⟨19280051726795834630995075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25706735635727779507993433 19280051726795834630995075)
              ·
                refine ⟨28920077590193751946492613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19280051726795834630995075 28920077590193751946492613)
                ·
                  refine ⟨5422514548161328489967365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28920077590193751946492613 5422514548161328489967365)
                  ·
                    refine ⟨1016721477780249091868881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5422514548161328489967365 1016721477780249091868881)
                    ·
                      rfl

theorem cell23_5940174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 4, 4].length) (baseStart_5940174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5940174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5940174 prefixEnd_5940174 := by exact prefixLift 5940174
  have htrace : WordTrace (prefixWord ++ tailWord_5940174) baseStart_5940174 baseEnd_5940174 := by
    simpa [prefixWord, tailWord_5940174, baseEnd_5940174] using wordTrace_append hprefix tailTrace_5940174
  have hstable : (prefixWord ++ tailWord_5940174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5940174).length < 2 ^ (prefixWord ++ tailWord_5940174).sum := by decide
  have hdescent : baseEnd_5940174 < baseStart_5940174 := by decide
  rcases family_descends (prefixWord ++ tailWord_5940174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5940191 : List Nat := [1, 1, 2, 3, 5, 1, 1, 3, 2, 4]
def baseStart_5940191 : Nat := 118140960795 + 5940191 * 2 ^ 59
def prefixEnd_5940191 : Nat := 4983230072969 + 3 ^ 40 * 5940191 * 2
def baseEnd_5940191 : Nat := 1016724387503957903031355

theorem tailTrace_5940191 : CollatzResearch.WordTrace tailWord_5940191 prefixEnd_5940191 1016724387503957903031355 := by
  unfold tailWord_5940191
  simp only [CollatzResearch.WordTrace]
  refine ⟨216656564822709985699132427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144437709881806657132754951 216656564822709985699132427)
  ·
    refine ⟨324984847234064978548698641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216656564822709985699132427 324984847234064978548698641)
    ·
      refine ⟨243738635425548733911523981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 324984847234064978548698641 243738635425548733911523981)
      ·
        refine ⟨91401988284580775216821493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 243738635425548733911523981 91401988284580775216821493)
        ·
          refine ⟨8568936401679447676577015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 91401988284580775216821493 8568936401679447676577015)
          ·
            refine ⟨12853404602519171514865523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8568936401679447676577015 12853404602519171514865523)
            ·
              refine ⟨19280106903778757272298285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12853404602519171514865523 19280106903778757272298285)
              ·
                refine ⟨7230040088917033977111857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19280106903778757272298285 7230040088917033977111857)
                ·
                  refine ⟨5422530066687775482833893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7230040088917033977111857 5422530066687775482833893)
                  ·
                    refine ⟨1016724387503957903031355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5422530066687775482833893 1016724387503957903031355)
                    ·
                      rfl

theorem cell23_5940191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 3, 2, 4].length) (baseStart_5940191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5940191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5940191 prefixEnd_5940191 := by exact prefixLift 5940191
  have htrace : WordTrace (prefixWord ++ tailWord_5940191) baseStart_5940191 baseEnd_5940191 := by
    simpa [prefixWord, tailWord_5940191, baseEnd_5940191] using wordTrace_append hprefix tailTrace_5940191
  have hstable : (prefixWord ++ tailWord_5940191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5940191).length < 2 ^ (prefixWord ++ tailWord_5940191).sum := by decide
  have hdescent : baseEnd_5940191 < baseStart_5940191 := by decide
  rcases family_descends (prefixWord ++ tailWord_5940191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5940226 : List Nat := [3, 4, 1, 3, 2, 1, 2, 2, 1, 1, 3]
def baseStart_5940226 : Nat := 118140960795 + 5940226 * 2 ^ 59
def prefixEnd_5940226 : Nat := 4983230072969 + 3 ^ 40 * 5940226 * 2
def baseEnd_5940226 : Nat := 3050191134334781072156405

theorem tailTrace_5940226 : CollatzResearch.WordTrace tailWord_5940226 prefixEnd_5940226 3050191134334781072156405 := by
  unfold tailWord_5940226
  simp only [CollatzResearch.WordTrace]
  refine ⟨54164460344395796669164133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144438560918388791117771021 54164460344395796669164133)
  ·
    refine ⟨10155836314574211875468275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54164460344395796669164133 10155836314574211875468275)
    ·
      refine ⟨15233754471861317813202413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10155836314574211875468275 15233754471861317813202413)
      ·
        refine ⟨5712657926947994179950905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15233754471861317813202413 5712657926947994179950905)
        ·
          refine ⟨4284493445210995634963179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5712657926947994179950905 4284493445210995634963179)
          ·
            refine ⟨6426740167816493452444769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4284493445210995634963179 6426740167816493452444769)
            ·
              refine ⟨4820055125862370089333577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6426740167816493452444769 4820055125862370089333577)
              ·
                refine ⟨3615041344396777567000183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4820055125862370089333577 3615041344396777567000183)
                ·
                  refine ⟨5422562016595166350500275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3615041344396777567000183 5422562016595166350500275)
                  ·
                    refine ⟨8133843024892749525750413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5422562016595166350500275 8133843024892749525750413)
                    ·
                      refine ⟨3050191134334781072156405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8133843024892749525750413 3050191134334781072156405)
                      ·
                        rfl

theorem cell23_5940226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_5940226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5940226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5940226 prefixEnd_5940226 := by exact prefixLift 5940226
  have htrace : WordTrace (prefixWord ++ tailWord_5940226) baseStart_5940226 baseEnd_5940226 := by
    simpa [prefixWord, tailWord_5940226, baseEnd_5940226] using wordTrace_append hprefix tailTrace_5940226
  have hstable : (prefixWord ++ tailWord_5940226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5940226).length < 2 ^ (prefixWord ++ tailWord_5940226).sum := by decide
  have hdescent : baseEnd_5940226 < baseStart_5940226 := by decide
  rcases family_descends (prefixWord ++ tailWord_5940226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5940232 : List Nat := [2, 1, 3, 2, 1, 5, 2, 2, 1, 2, 2]
def baseStart_5940232 : Nat := 118140960795 + 5940232 * 2 ^ 59
def prefixEnd_5940232 : Nat := 4983230072969 + 3 ^ 40 * 5940232 * 2
def baseEnd_5940232 : Nat := 3050194215218708048681377

theorem tailTrace_5940232 : CollatzResearch.WordTrace tailWord_5940232 prefixEnd_5940232 3050194215218708048681377 := by
  unfold tailWord_5940232
  simp only [CollatzResearch.WordTrace]
  refine ⟨108329030107780724850687475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144438706810374299800916633 108329030107780724850687475)
  ·
    refine ⟨162493545161671087276031213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108329030107780724850687475 162493545161671087276031213)
    ·
      refine ⟨60935079435626657728511705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162493545161671087276031213 60935079435626657728511705)
      ·
        refine ⟨45701309576719993296383779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60935079435626657728511705 45701309576719993296383779)
        ·
          refine ⟨68551964365079989944575669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45701309576719993296383779 68551964365079989944575669)
          ·
            refine ⟨6426746659226249057303969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68551964365079989944575669 6426746659226249057303969)
            ·
              refine ⟨4820059994419686792977977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6426746659226249057303969 4820059994419686792977977)
              ·
                refine ⟨3615044995814765094733483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4820059994419686792977977 3615044995814765094733483)
                ·
                  refine ⟨5422567493722147642100225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3615044995814765094733483 5422567493722147642100225)
                  ·
                    refine ⟨4066925620291610731575169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5422567493722147642100225 4066925620291610731575169)
                    ·
                      refine ⟨3050194215218708048681377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4066925620291610731575169 3050194215218708048681377)
                      ·
                        rfl

theorem cell23_5940232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 2, 2, 1, 2, 2].length) (baseStart_5940232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5940232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5940232 prefixEnd_5940232 := by exact prefixLift 5940232
  have htrace : WordTrace (prefixWord ++ tailWord_5940232) baseStart_5940232 baseEnd_5940232 := by
    simpa [prefixWord, tailWord_5940232, baseEnd_5940232] using wordTrace_append hprefix tailTrace_5940232
  have hstable : (prefixWord ++ tailWord_5940232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5940232).length < 2 ^ (prefixWord ++ tailWord_5940232).sum := by decide
  have hdescent : baseEnd_5940232 < baseStart_5940232 := by decide
  rcases family_descends (prefixWord ++ tailWord_5940232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5940267 : List Nat := [1, 1, 1, 1, 2, 1, 5, 2, 1, 4, 4]
def baseStart_5940267 : Nat := 118140960795 + 5940267 * 2 ^ 59
def prefixEnd_5940267 : Nat := 4983230072969 + 3 ^ 40 * 5940267 * 2
def baseEnd_5940267 : Nat := 3050212187041615411743715

theorem tailTrace_5940267 : CollatzResearch.WordTrace tailWord_5940267 prefixEnd_5940267 3050212187041615411743715 := by
  unfold tailWord_5940267
  simp only [CollatzResearch.WordTrace]
  refine ⟨216659336770434650678899055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144439557846956433785932703 216659336770434650678899055)
  ·
    refine ⟨324989005155651976018348583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216659336770434650678899055 324989005155651976018348583)
    ·
      refine ⟨487483507733477964027522875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324989005155651976018348583 487483507733477964027522875)
      ·
        refine ⟨731225261600216946041284313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 487483507733477964027522875 731225261600216946041284313)
        ·
          refine ⟨548418946200162709530963235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 731225261600216946041284313 548418946200162709530963235)
          ·
            refine ⟨822628419300244064296444853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 548418946200162709530963235 822628419300244064296444853)
            ·
              refine ⟨77121414309397881027791705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 822628419300244064296444853 77121414309397881027791705)
              ·
                refine ⟨57841060732048410770843779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77121414309397881027791705 57841060732048410770843779)
                ·
                  refine ⟨86761591098072616156265669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57841060732048410770843779 86761591098072616156265669)
                  ·
                    refine ⟨16267798330888615529299813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 86761591098072616156265669 16267798330888615529299813)
                    ·
                      refine ⟨3050212187041615411743715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16267798330888615529299813 3050212187041615411743715)
                      ·
                        rfl

theorem cell23_5940267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 4, 4].length) (baseStart_5940267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5940267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5940267 prefixEnd_5940267 := by exact prefixLift 5940267
  have htrace : WordTrace (prefixWord ++ tailWord_5940267) baseStart_5940267 baseEnd_5940267 := by
    simpa [prefixWord, tailWord_5940267, baseEnd_5940267] using wordTrace_append hprefix tailTrace_5940267
  have hstable : (prefixWord ++ tailWord_5940267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5940267).length < 2 ^ (prefixWord ++ tailWord_5940267).sum := by decide
  have hdescent : baseEnd_5940267 < baseStart_5940267 := by decide
  rcases family_descends (prefixWord ++ tailWord_5940267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5940277 : List Nat := [1, 3, 3, 1, 1, 1, 1, 1, 11]
def baseStart_5940277 : Nat := 118140960795 + 5940277 * 2 ^ 59
def prefixEnd_5940277 : Nat := 4983230072969 + 3 ^ 40 * 5940277 * 2
def baseEnd_5940277 : Nat := 338913035760906708068741

theorem tailTrace_5940277 : CollatzResearch.WordTrace tailWord_5940277 prefixEnd_5940277 338913035760906708068741 := by
  unfold tailWord_5940277
  simp only [CollatzResearch.WordTrace]
  refine ⟨216659701500398422386763085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144439801000265614924508723 216659701500398422386763085)
  ·
    refine ⟨81247388062649408395036157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216659701500398422386763085 81247388062649408395036157)
    ·
      refine ⟨30467770523493528148138559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81247388062649408395036157 30467770523493528148138559)
      ·
        refine ⟨45701655785240292222207839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30467770523493528148138559 45701655785240292222207839)
        ·
          refine ⟨68552483677860438333311759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45701655785240292222207839 68552483677860438333311759)
          ·
            refine ⟨102828725516790657499967639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68552483677860438333311759 102828725516790657499967639)
            ·
              refine ⟨154243088275185986249951459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102828725516790657499967639 154243088275185986249951459)
              ·
                refine ⟨231364632412778979374927189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154243088275185986249951459 231364632412778979374927189)
                ·
                  refine ⟨338913035760906708068741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 231364632412778979374927189 338913035760906708068741)
                  ·
                    rfl

theorem cell23_5940277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 11].length) (baseStart_5940277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5940277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5940277 prefixEnd_5940277 := by exact prefixLift 5940277
  have htrace : WordTrace (prefixWord ++ tailWord_5940277) baseStart_5940277 baseEnd_5940277 := by
    simpa [prefixWord, tailWord_5940277, baseEnd_5940277] using wordTrace_append hprefix tailTrace_5940277
  have hstable : (prefixWord ++ tailWord_5940277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5940277).length < 2 ^ (prefixWord ++ tailWord_5940277).sum := by decide
  have hdescent : baseEnd_5940277 < baseStart_5940277 := by decide
  rcases family_descends (prefixWord ++ tailWord_5940277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5940284 : List Nat := [2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 4]
def baseStart_5940284 : Nat := 118140960795 + 5940284 * 2 ^ 59
def prefixEnd_5940284 : Nat := 4983230072969 + 3 ^ 40 * 5940284 * 2
def baseEnd_5940284 : Nat := 3050220916212741845231137

theorem tailTrace_5940284 : CollatzResearch.WordTrace tailWord_5940284 prefixEnd_5940284 3050220916212741845231137 := by
  unfold tailWord_5940284
  simp only [CollatzResearch.WordTrace]
  refine ⟨108329978405686531291133953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144439971207582041721511937 108329978405686531291133953)
  ·
    refine ⟨81247483804264898468350465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108329978405686531291133953 81247483804264898468350465)
    ·
      refine ⟨60935612853198673851262849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81247483804264898468350465 60935612853198673851262849)
      ·
        refine ⟨45701709639899005388447137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60935612853198673851262849 45701709639899005388447137)
        ·
          refine ⟨34276282229924254041335353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45701709639899005388447137 34276282229924254041335353)
          ·
            refine ⟨25707211672443190531001515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34276282229924254041335353 25707211672443190531001515)
            ·
              refine ⟨38560817508664785796502273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25707211672443190531001515 38560817508664785796502273)
              ·
                refine ⟨28920613131498589347376705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38560817508664785796502273 28920613131498589347376705)
                ·
                  refine ⟨21690459848623942010532529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28920613131498589347376705 21690459848623942010532529)
                  ·
                    refine ⟨16267844886467956507899397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21690459848623942010532529 16267844886467956507899397)
                    ·
                      refine ⟨3050220916212741845231137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16267844886467956507899397 3050220916212741845231137)
                      ·
                        rfl

theorem cell23_5940284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_5940284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5940284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5940284 prefixEnd_5940284 := by exact prefixLift 5940284
  have htrace : WordTrace (prefixWord ++ tailWord_5940284) baseStart_5940284 baseEnd_5940284 := by
    simpa [prefixWord, tailWord_5940284, baseEnd_5940284] using wordTrace_append hprefix tailTrace_5940284
  have hstable : (prefixWord ++ tailWord_5940284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5940284).length < 2 ^ (prefixWord ++ tailWord_5940284).sum := by decide
  have hdescent : baseEnd_5940284 < baseStart_5940284 := by decide
  rcases family_descends (prefixWord ++ tailWord_5940284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5940301 : List Nat := [1, 6, 1, 1, 1, 2, 2, 1, 2, 2, 4]
def baseStart_5940301 : Nat := 118140960795 + 5940301 * 2 ^ 59
def prefixEnd_5940301 : Nat := 4983230072969 + 3 ^ 40 * 5940301 * 2
def baseEnd_5940301 : Nat := 3050229645383868278718559

theorem tailTrace_5940301 : CollatzResearch.WordTrace tailWord_5940301 prefixEnd_5940301 3050229645383868278718559 := by
  unfold tailWord_5940301
  simp only [CollatzResearch.WordTrace]
  refine ⟨216660576852311474485636757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144440384568207649657091171 216660576852311474485636757)
  ·
    refine ⟨10155964539952100366514223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 216660576852311474485636757 10155964539952100366514223)
    ·
      refine ⟨15233946809928150549771335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10155964539952100366514223 15233946809928150549771335)
      ·
        refine ⟨22850920214892225824657003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15233946809928150549771335 22850920214892225824657003)
        ·
          refine ⟨34276380322338338736985505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22850920214892225824657003 34276380322338338736985505)
          ·
            refine ⟨25707285241753754052739129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34276380322338338736985505 25707285241753754052739129)
            ·
              refine ⟨19280463931315315539554347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25707285241753754052739129 19280463931315315539554347)
              ·
                refine ⟨28920695896972973309331521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19280463931315315539554347 28920695896972973309331521)
                ·
                  refine ⟨21690521922729729981998641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28920695896972973309331521 21690521922729729981998641)
                  ·
                    refine ⟨16267891442047297486498981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21690521922729729981998641 16267891442047297486498981)
                    ·
                      refine ⟨3050229645383868278718559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16267891442047297486498981 3050229645383868278718559)
                      ·
                        rfl

theorem cell23_5940301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_5940301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5940301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5940301 prefixEnd_5940301 := by exact prefixLift 5940301
  have htrace : WordTrace (prefixWord ++ tailWord_5940301) baseStart_5940301 baseEnd_5940301 := by
    simpa [prefixWord, tailWord_5940301, baseEnd_5940301] using wordTrace_append hprefix tailTrace_5940301
  have hstable : (prefixWord ++ tailWord_5940301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5940301).length < 2 ^ (prefixWord ++ tailWord_5940301).sum := by decide
  have hdescent : baseEnd_5940301 < baseStart_5940301 := by decide
  rcases family_descends (prefixWord ++ tailWord_5940301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5940307 : List Nat := [1, 1, 1, 2, 1, 1, 2, 6, 1, 7]
def baseStart_5940307 : Nat := 118140960795 + 5940307 * 2 ^ 59
def prefixEnd_5940307 : Nat := 4983230072969 + 3 ^ 40 * 5940307 * 2
def baseEnd_5940307 : Nat := 1016744242089265085081177

theorem tailTrace_5940307 : CollatzResearch.WordTrace tailWord_5940307 prefixEnd_5940307 1016744242089265085081177 := by
  unfold tailWord_5940307
  simp only [CollatzResearch.WordTrace]
  refine ⟨216660795690289737510355175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144440530460193158340236783 216660795690289737510355175)
  ·
    refine ⟨324991193535434606265532763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216660795690289737510355175 324991193535434606265532763)
    ·
      refine ⟨487486790303151909398299145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324991193535434606265532763 487486790303151909398299145)
      ·
        refine ⟨365615092727363932048724359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 487486790303151909398299145 365615092727363932048724359)
        ·
          refine ⟨548422639091045898073086539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365615092727363932048724359 548422639091045898073086539)
          ·
            refine ⟨822633958636568847109629809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 548422639091045898073086539 822633958636568847109629809)
            ·
              refine ⟨616975468977426635332222357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 822633958636568847109629809 616975468977426635332222357)
              ·
                refine ⟨28920725108316873531197923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 616975468977426635332222357 28920725108316873531197923)
                ·
                  refine ⟨43381087662475310296796885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28920725108316873531197923 43381087662475310296796885)
                  ·
                    refine ⟨1016744242089265085081177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43381087662475310296796885 1016744242089265085081177)
                    ·
                      rfl

theorem cell23_5940307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 7].length) (baseStart_5940307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5940307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5940307 prefixEnd_5940307 := by exact prefixLift 5940307
  have htrace : WordTrace (prefixWord ++ tailWord_5940307) baseStart_5940307 baseEnd_5940307 := by
    simpa [prefixWord, tailWord_5940307, baseEnd_5940307] using wordTrace_append hprefix tailTrace_5940307
  have hstable : (prefixWord ++ tailWord_5940307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5940307).length < 2 ^ (prefixWord ++ tailWord_5940307).sum := by decide
  have hdescent : baseEnd_5940307 < baseStart_5940307 := by decide
  rcases family_descends (prefixWord ++ tailWord_5940307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5940324 : List Nat := [2, 3, 1, 1, 2, 1, 1, 5, 2, 5]
def baseStart_5940324 : Nat := 118140960795 + 5940324 * 2 ^ 59
def prefixEnd_5940324 : Nat := 4983230072969 + 3 ^ 40 * 5940324 * 2
def baseEnd_5940324 : Nat := 1016747151812973896243651

theorem tailTrace_5940324 : CollatzResearch.WordTrace tailWord_5940324 prefixEnd_5940324 1016747151812973896243651 := by
  unfold tailWord_5940324
  simp only [CollatzResearch.WordTrace]
  refine ⟨108330707865614074706862013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144440943820818766275816017 108330707865614074706862013)
  ·
    refine ⟨40624015449605278015073255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108330707865614074706862013 40624015449605278015073255)
    ·
      refine ⟨60936023174407917022609883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40624015449605278015073255 60936023174407917022609883)
      ·
        refine ⟨91404034761611875533914825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60936023174407917022609883 91404034761611875533914825)
        ·
          refine ⟨68553026071208906650436119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91404034761611875533914825 68553026071208906650436119)
          ·
            refine ⟨102829539106813359975654179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68553026071208906650436119 102829539106813359975654179)
            ·
              refine ⟨154244308660220039963481269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102829539106813359975654179 154244308660220039963481269)
              ·
                refine ⟨14460403936895628746576369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 154244308660220039963481269 14460403936895628746576369)
                ·
                  refine ⟨10845302952671721559932277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14460403936895628746576369 10845302952671721559932277)
                  ·
                    refine ⟨1016747151812973896243651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10845302952671721559932277 1016747151812973896243651)
                    ·
                      rfl

theorem cell23_5940324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 5, 2, 5].length) (baseStart_5940324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5940324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5940324 prefixEnd_5940324 := by exact prefixLift 5940324
  have htrace : WordTrace (prefixWord ++ tailWord_5940324) baseStart_5940324 baseEnd_5940324 := by
    simpa [prefixWord, tailWord_5940324, baseEnd_5940324] using wordTrace_append hprefix tailTrace_5940324
  have hstable : (prefixWord ++ tailWord_5940324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5940324).length < 2 ^ (prefixWord ++ tailWord_5940324).sum := by decide
  have hdescent : baseEnd_5940324 < baseStart_5940324 := by decide
  rcases family_descends (prefixWord ++ tailWord_5940324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5940344 : List Nat := [2, 1, 2, 1, 1, 1, 5, 1, 4, 1, 4]
def baseStart_5940344 : Nat := 118140960795 + 5940344 * 2 ^ 59
def prefixEnd_5940344 : Nat := 4983230072969 + 3 ^ 40 * 5940344 * 2
def baseEnd_5940344 : Nat := 3050251725052011610480861

theorem tailTrace_5940344 : CollatzResearch.WordTrace tailWord_5940344 prefixEnd_5940344 3050251725052011610480861 := by
  unfold tailWord_5940344
  simp only [CollatzResearch.WordTrace]
  refine ⟨108331072595577846414726043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144441430127437128552968057 108331072595577846414726043)
  ·
    refine ⟨162496608893366769622089065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108331072595577846414726043 162496608893366769622089065)
    ·
      refine ⟨121872456670025077216566799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162496608893366769622089065 121872456670025077216566799)
      ·
        refine ⟨182808685005037615824850199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121872456670025077216566799 182808685005037615824850199)
        ·
          refine ⟨274213027507556423737275299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182808685005037615824850199 274213027507556423737275299)
          ·
            refine ⟨411319541261334635605912949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274213027507556423737275299 411319541261334635605912949)
            ·
              refine ⟨38561206993250122088054339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 411319541261334635605912949 38561206993250122088054339)
              ·
                refine ⟨57841810489875183132081509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38561206993250122088054339 57841810489875183132081509)
                ·
                  refine ⟨10845339466851596837265283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57841810489875183132081509 10845339466851596837265283)
                  ·
                    refine ⟨16268009200277395255897925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10845339466851596837265283 16268009200277395255897925)
                    ·
                      refine ⟨3050251725052011610480861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16268009200277395255897925 3050251725052011610480861)
                      ·
                        rfl

theorem cell23_5940344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 4, 1, 4].length) (baseStart_5940344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5940344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5940344 prefixEnd_5940344 := by exact prefixLift 5940344
  have htrace : WordTrace (prefixWord ++ tailWord_5940344) baseStart_5940344 baseEnd_5940344 := by
    simpa [prefixWord, tailWord_5940344, baseEnd_5940344] using wordTrace_append hprefix tailTrace_5940344
  have hstable : (prefixWord ++ tailWord_5940344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5940344).length < 2 ^ (prefixWord ++ tailWord_5940344).sum := by decide
  have hdescent : baseEnd_5940344 < baseStart_5940344 := by decide
  rcases family_descends (prefixWord ++ tailWord_5940344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5940364 : List Nat := [2, 2, 1, 2, 1, 1, 1, 3, 3, 4, 3]
def baseStart_5940364 : Nat := 118140960795 + 5940364 * 2 ^ 59
def prefixEnd_5940364 : Nat := 4983230072969 + 3 ^ 40 * 5940364 * 2
def baseEnd_5940364 : Nat := 3050261994665101532230769

theorem tailTrace_5940364 : CollatzResearch.WordTrace tailWord_5940364 prefixEnd_5940364 3050261994665101532230769 := by
  unfold tailWord_5940364
  simp only [CollatzResearch.WordTrace]
  refine ⟨108331437325541618122590073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144441916434055490830120097 108331437325541618122590073)
  ·
    refine ⟨81248577994156213591942555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108331437325541618122590073 81248577994156213591942555)
    ·
      refine ⟨121872866991234320387913833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81248577994156213591942555 121872866991234320387913833)
      ·
        refine ⟨91404650243425740290935375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121872866991234320387913833 91404650243425740290935375)
        ·
          refine ⟨137106975365138610436403063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91404650243425740290935375 137106975365138610436403063)
          ·
            refine ⟨205660463047707915654604595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137106975365138610436403063 205660463047707915654604595)
            ·
              refine ⟨308490694571561873481906893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205660463047707915654604595 308490694571561873481906893)
              ·
                refine ⟨115684010464335702555715085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 308490694571561873481906893 115684010464335702555715085)
                ·
                  refine ⟨43381503924125888458393157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 115684010464335702555715085 43381503924125888458393157)
                  ·
                    refine ⟨8134031985773604085948717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43381503924125888458393157 8134031985773604085948717)
                    ·
                      refine ⟨3050261994665101532230769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8134031985773604085948717 3050261994665101532230769)
                      ·
                        rfl

theorem cell23_5940364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 3, 4, 3].length) (baseStart_5940364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5940364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5940364 prefixEnd_5940364 := by exact prefixLift 5940364
  have htrace : WordTrace (prefixWord ++ tailWord_5940364) baseStart_5940364 baseEnd_5940364 := by
    simpa [prefixWord, tailWord_5940364, baseEnd_5940364] using wordTrace_append hprefix tailTrace_5940364
  have hstable : (prefixWord ++ tailWord_5940364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5940364).length < 2 ^ (prefixWord ++ tailWord_5940364).sum := by decide
  have hdescent : baseEnd_5940364 < baseStart_5940364 := by decide
  rcases family_descends (prefixWord ++ tailWord_5940364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5940378 : List Nat := [3, 1, 1, 5, 1, 2, 2, 1, 2, 1, 4]
def baseStart_5940378 : Nat := 118140960795 + 5940378 * 2 ^ 59
def prefixEnd_5940378 : Nat := 4983230072969 + 3 ^ 40 * 5940378 * 2
def baseEnd_5940378 : Nat := 3050269183394264477455705

theorem tailTrace_5940378 : CollatzResearch.WordTrace tailWord_5940378 prefixEnd_5940378 3050269183394264477455705 := by
  unfold tailWord_5940378
  simp only [CollatzResearch.WordTrace]
  refine ⟨54165846318258129159047447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144442256848688344424126525 54165846318258129159047447)
  ·
    refine ⟨81248769477387193738571171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54165846318258129159047447 81248769477387193738571171)
    ·
      refine ⟨121873154216080790607856757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81248769477387193738571171 121873154216080790607856757)
      ·
        refine ⟨11425608207757574119486571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 121873154216080790607856757 11425608207757574119486571)
        ·
          refine ⟨17138412311636361179229857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11425608207757574119486571 17138412311636361179229857)
          ·
            refine ⟨12853809233727270884422393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17138412311636361179229857 12853809233727270884422393)
            ·
              refine ⟨9640356925295453163316795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12853809233727270884422393 9640356925295453163316795)
              ·
                refine ⟨14460535387943179744975193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9640356925295453163316795 14460535387943179744975193)
                ·
                  refine ⟨10845401540957384808731395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14460535387943179744975193 10845401540957384808731395)
                  ·
                    refine ⟨16268102311436077213097093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10845401540957384808731395 16268102311436077213097093)
                    ·
                      refine ⟨3050269183394264477455705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16268102311436077213097093 3050269183394264477455705)
                      ·
                        rfl

theorem cell23_5940378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_5940378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5940378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5940378 prefixEnd_5940378 := by exact prefixLift 5940378
  have htrace : WordTrace (prefixWord ++ tailWord_5940378) baseStart_5940378 baseEnd_5940378 := by
    simpa [prefixWord, tailWord_5940378, baseEnd_5940378] using wordTrace_append hprefix tailTrace_5940378
  have hstable : (prefixWord ++ tailWord_5940378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5940378).length < 2 ^ (prefixWord ++ tailWord_5940378).sum := by decide
  have hdescent : baseEnd_5940378 < baseStart_5940378 := by decide
  rcases family_descends (prefixWord ++ tailWord_5940378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5940401 : List Nat := [1, 2, 2, 5, 1, 1, 1, 4, 6]
def baseStart_5940401 : Nat := 118140960795 + 5940401 * 2 ^ 59
def prefixEnd_5940401 : Nat := 4983230072969 + 3 ^ 40 * 5940401 * 2
def baseEnd_5940401 : Nat := 338920110383257543052011

theorem tailTrace_5940401 : CollatzResearch.WordTrace tailWord_5940401 prefixEnd_5940401 338920110383257543052011 := by
  unfold tailWord_5940401
  simp only [CollatzResearch.WordTrace]
  refine ⟨216664224151949191564277057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144442816101299461042851371 216664224151949191564277057)
  ·
    refine ⟨162498168113961893673207793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216664224151949191564277057 162498168113961893673207793)
    ·
      refine ⟨121873626085471420254905845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162498168113961893673207793 121873626085471420254905845)
      ·
        refine ⟨11425652445512945648897423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 121873626085471420254905845 11425652445512945648897423)
        ·
          refine ⟨17138478668269418473346135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11425652445512945648897423 17138478668269418473346135)
          ·
            refine ⟨25707718002404127710019203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17138478668269418473346135 25707718002404127710019203)
            ·
              refine ⟨38561577003606191565028805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25707718002404127710019203 38561577003606191565028805)
              ·
                refine ⟨7230295688176160918442901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38561577003606191565028805 7230295688176160918442901)
                ·
                  refine ⟨338920110383257543052011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7230295688176160918442901 338920110383257543052011)
                  ·
                    rfl

theorem cell23_5940401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 4, 6].length) (baseStart_5940401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5940401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5940401 prefixEnd_5940401 := by exact prefixLift 5940401
  have htrace : WordTrace (prefixWord ++ tailWord_5940401) baseStart_5940401 baseEnd_5940401 := by
    simpa [prefixWord, tailWord_5940401, baseEnd_5940401] using wordTrace_append hprefix tailTrace_5940401
  have hstable : (prefixWord ++ tailWord_5940401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5940401).length < 2 ^ (prefixWord ++ tailWord_5940401).sum := by decide
  have hdescent : baseEnd_5940401 < baseStart_5940401 := by decide
  rcases family_descends (prefixWord ++ tailWord_5940401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5940421 : List Nat := [1, 3, 1, 1, 1, 1, 3, 4, 1, 5, 2]
def baseStart_5940421 : Nat := 118140960795 + 5940421 * 2 ^ 59
def prefixEnd_5940421 : Nat := 4983230072969 + 3 ^ 40 * 5940421 * 2
def baseEnd_5940421 : Nat := 3050291263062407809218007

theorem tailTrace_5940421 : CollatzResearch.WordTrace tailWord_5940421 prefixEnd_5940421 3050291263062407809218007 := by
  unfold tailWord_5940421
  simp only [CollatzResearch.WordTrace]
  refine ⟨216664953611876734980005117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144443302407917823320003411 216664953611876734980005117)
  ·
    refine ⟨81249357604453775617501919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216664953611876734980005117 81249357604453775617501919)
    ·
      refine ⟨121874036406680663426252879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81249357604453775617501919 121874036406680663426252879)
      ·
        refine ⟨182811054610020995139379319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121874036406680663426252879 182811054610020995139379319)
        ·
          refine ⟨274216581915031492709068979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182811054610020995139379319 274216581915031492709068979)
          ·
            refine ⟨411324872872547239063603469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274216581915031492709068979 411324872872547239063603469)
            ·
              refine ⟨154246827327205214648851301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 411324872872547239063603469 154246827327205214648851301)
              ·
                refine ⟨28921280123850977746659619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 154246827327205214648851301 28921280123850977746659619)
                ·
                  refine ⟨43381920185776466619989429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28921280123850977746659619 43381920185776466619989429)
                  ·
                    refine ⟨4067055017416543745624009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43381920185776466619989429 4067055017416543745624009)
                    ·
                      refine ⟨3050291263062407809218007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4067055017416543745624009 3050291263062407809218007)
                      ·
                        rfl

theorem cell23_5940421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 5, 2].length) (baseStart_5940421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5940421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5940421 prefixEnd_5940421 := by exact prefixLift 5940421
  have htrace : WordTrace (prefixWord ++ tailWord_5940421) baseStart_5940421 baseEnd_5940421 := by
    simpa [prefixWord, tailWord_5940421, baseEnd_5940421] using wordTrace_append hprefix tailTrace_5940421
  have hstable : (prefixWord ++ tailWord_5940421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5940421).length < 2 ^ (prefixWord ++ tailWord_5940421).sum := by decide
  have hdescent : baseEnd_5940421 < baseStart_5940421 := by decide
  rcases family_descends (prefixWord ++ tailWord_5940421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5940429 : List Nat := [1, 6, 2, 2, 2, 1, 1, 1, 2, 1, 4]
def baseStart_5940429 : Nat := 118140960795 + 5940429 * 2 ^ 59
def prefixEnd_5940429 : Nat := 4983230072969 + 3 ^ 40 * 5940429 * 2
def baseEnd_5940429 : Nat := 3050295370907643777917971

theorem tailTrace_5940429 : CollatzResearch.WordTrace tailWord_5940429 prefixEnd_5940429 3050295370907643777917971 := by
  unfold tailWord_5940429
  simp only [CollatzResearch.WordTrace]
  refine ⟨216665245395847752346296341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144443496930565168230864227 216665245395847752346296341)
  ·
    refine ⟨10156183377930363391232641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 216665245395847752346296341 10156183377930363391232641)
    ·
      refine ⟨7617137533447772543424481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10156183377930363391232641 7617137533447772543424481)
      ·
        refine ⟨5712853150085829407568361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7617137533447772543424481 5712853150085829407568361)
        ·
          refine ⟨4284639862564372055676271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5712853150085829407568361 4284639862564372055676271)
          ·
            refine ⟨6426959793846558083514407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4284639862564372055676271 6426959793846558083514407)
            ·
              refine ⟨9640439690769837125271611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6426959793846558083514407 9640439690769837125271611)
              ·
                refine ⟨14460659536154755687907417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9640439690769837125271611 14460659536154755687907417)
                ·
                  refine ⟨10845494652116066765930563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14460659536154755687907417 10845494652116066765930563)
                  ·
                    refine ⟨16268241978174100148895845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10845494652116066765930563 16268241978174100148895845)
                    ·
                      refine ⟨3050295370907643777917971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16268241978174100148895845 3050295370907643777917971)
                      ·
                        rfl

theorem cell23_5940429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_5940429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5940429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5940429 prefixEnd_5940429 := by exact prefixLift 5940429
  have htrace : WordTrace (prefixWord ++ tailWord_5940429) baseStart_5940429 baseEnd_5940429 := by
    simpa [prefixWord, tailWord_5940429, baseEnd_5940429] using wordTrace_append hprefix tailTrace_5940429
  have hstable : (prefixWord ++ tailWord_5940429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5940429).length < 2 ^ (prefixWord ++ tailWord_5940429).sum := by decide
  have hdescent : baseEnd_5940429 < baseStart_5940429 := by decide
  rcases family_descends (prefixWord ++ tailWord_5940429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5940448 : List Nat := [2, 1, 1, 3, 1, 4, 4, 1, 1, 5]
def baseStart_5940448 : Nat := 118140960795 + 5940448 * 2 ^ 59
def prefixEnd_5940448 : Nat := 4983230072969 + 3 ^ 40 * 5940448 * 2
def baseEnd_5940448 : Nat := 1016768375680026401193461

theorem tailTrace_5940448 : CollatzResearch.WordTrace tailWord_5940448 prefixEnd_5940448 1016768375680026401193461 := by
  unfold tailWord_5940448
  simp only [CollatzResearch.WordTrace]
  refine ⟨108332969191389459295618999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144443958921852612394158665 108332969191389459295618999)
  ·
    refine ⟨162499453787084188943428499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108332969191389459295618999 162499453787084188943428499)
    ·
      refine ⟨243749180680626283415142749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162499453787084188943428499 243749180680626283415142749)
      ·
        refine ⟨91405942755234856280678531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 243749180680626283415142749 91405942755234856280678531)
        ·
          refine ⟨137108914132852284421017797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91405942755234856280678531 137108914132852284421017797)
          ·
            refine ⟨25707921399909803328940837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 137108914132852284421017797 25707921399909803328940837)
            ·
              refine ⟨4820235262483088124176407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25707921399909803328940837 4820235262483088124176407)
              ·
                refine ⟨7230352893724632186264611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4820235262483088124176407 7230352893724632186264611)
                ·
                  refine ⟨10845529340586948279396917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7230352893724632186264611 10845529340586948279396917)
                  ·
                    refine ⟨1016768375680026401193461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10845529340586948279396917 1016768375680026401193461)
                    ·
                      rfl

theorem cell23_5940448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 4, 1, 1, 5].length) (baseStart_5940448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5940448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5940448 prefixEnd_5940448 := by exact prefixLift 5940448
  have htrace : WordTrace (prefixWord ++ tailWord_5940448) baseStart_5940448 baseEnd_5940448 := by
    simpa [prefixWord, tailWord_5940448, baseEnd_5940448] using wordTrace_append hprefix tailTrace_5940448
  have hstable : (prefixWord ++ tailWord_5940448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5940448).length < 2 ^ (prefixWord ++ tailWord_5940448).sum := by decide
  have hdescent : baseEnd_5940448 < baseStart_5940448 := by decide
  rcases family_descends (prefixWord ++ tailWord_5940448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5940464 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 4]
def baseStart_5940464 : Nat := 118140960795 + 5940464 * 2 ^ 59
def prefixEnd_5940464 : Nat := 4983230072969 + 3 ^ 40 * 5940464 * 2
def baseEnd_5940464 : Nat := 3050313342730551140980309

theorem tailTrace_5940464 : CollatzResearch.WordTrace tailWord_5940464 prefixEnd_5940464 3050313342730551140980309 := by
  unfold tailWord_5940464
  simp only [CollatzResearch.WordTrace]
  refine ⟨108333260975360476661910223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144444347967147302215880297 108333260975360476661910223)
  ·
    refine ⟨162499891463040714992865335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108333260975360476661910223 162499891463040714992865335)
    ·
      refine ⟨243749837194561072489298003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162499891463040714992865335 243749837194561072489298003)
      ·
        refine ⟨365624755791841608733947005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243749837194561072489298003 365624755791841608733947005)
        ·
          refine ⟨137109283421940603275230127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 365624755791841608733947005 137109283421940603275230127)
          ·
            refine ⟨205663925132910904912845191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137109283421940603275230127 205663925132910904912845191)
            ·
              refine ⟨308495887699366357369267787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205663925132910904912845191 308495887699366357369267787)
              ·
                refine ⟨462743831549049536053901681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 308495887699366357369267787 462743831549049536053901681)
                ·
                  refine ⟨347057873661787152040426261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 462743831549049536053901681 347057873661787152040426261)
                  ·
                    refine ⟨16268337827896272751894981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 347057873661787152040426261 16268337827896272751894981)
                    ·
                      refine ⟨3050313342730551140980309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16268337827896272751894981 3050313342730551140980309)
                      ·
                        rfl

theorem cell23_5940464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 4].length) (baseStart_5940464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5940464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5940464 prefixEnd_5940464 := by exact prefixLift 5940464
  have htrace : WordTrace (prefixWord ++ tailWord_5940464) baseStart_5940464 baseEnd_5940464 := by
    simpa [prefixWord, tailWord_5940464, baseEnd_5940464] using wordTrace_append hprefix tailTrace_5940464
  have hstable : (prefixWord ++ tailWord_5940464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5940464).length < 2 ^ (prefixWord ++ tailWord_5940464).sum := by decide
  have hdescent : baseEnd_5940464 < baseStart_5940464 := by decide
  rcases family_descends (prefixWord ++ tailWord_5940464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5940474 : List Nat := [3, 1, 1, 1, 1, 4, 2, 10]
def baseStart_5940474 : Nat := 118140960795 + 5940474 * 2 ^ 59
def prefixEnd_5940474 : Nat := 4983230072969 + 3 ^ 40 * 5940474 * 2
def baseEnd_5940474 : Nat := 112974758427299855624269

theorem tailTrace_5940474 : CollatzResearch.WordTrace tailWord_5940474 prefixEnd_5940474 112974758427299855624269 := by
  unfold tailWord_5940474
  simp only [CollatzResearch.WordTrace]
  refine ⟨54166721670171181257921119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144444591120456483354456317 54166721670171181257921119)
  ·
    refine ⟨81250082505256771886881679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54166721670171181257921119 81250082505256771886881679)
    ·
      refine ⟨121875123757885157830322519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81250082505256771886881679 121875123757885157830322519)
      ·
        refine ⟨182812685636827736745483779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121875123757885157830322519 182812685636827736745483779)
        ·
          refine ⟨274219028455241605118225669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182812685636827736745483779 274219028455241605118225669)
          ·
            refine ⟨51416067835357800959667313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 274219028455241605118225669 51416067835357800959667313)
            ·
              refine ⟨38562050876518350719750485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51416067835357800959667313 38562050876518350719750485)
              ·
                refine ⟨112974758427299855624269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 38562050876518350719750485 112974758427299855624269)
                ·
                  rfl

theorem cell23_5940474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 10].length) (baseStart_5940474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5940474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5940474 prefixEnd_5940474 := by exact prefixLift 5940474
  have htrace : WordTrace (prefixWord ++ tailWord_5940474) baseStart_5940474 baseEnd_5940474 := by
    simpa [prefixWord, tailWord_5940474, baseEnd_5940474] using wordTrace_append hprefix tailTrace_5940474
  have hstable : (prefixWord ++ tailWord_5940474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5940474).length < 2 ^ (prefixWord ++ tailWord_5940474).sum := by decide
  have hdescent : baseEnd_5940474 < baseStart_5940474 := by decide
  rcases family_descends (prefixWord ++ tailWord_5940474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5940478 : List Nat := [4, 2, 2, 1, 1, 2, 3, 1, 1, 6]
def baseStart_5940478 : Nat := 118140960795 + 5940478 * 2 ^ 59
def prefixEnd_5940478 : Nat := 4983230072969 + 3 ^ 40 * 5940478 * 2
def baseEnd_5940478 : Nat := 1016773510486571362068415

theorem tailTrace_5940478 : CollatzResearch.WordTrace tailWord_5940478 prefixEnd_5940478 1016773510486571362068415 := by
  unfold tailWord_5940478
  simp only [CollatzResearch.WordTrace]
  refine ⟨27083379071583779214353761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144444688381780155809886725 27083379071583779214353761)
  ·
    refine ⟨20312534303687834410765321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27083379071583779214353761 20312534303687834410765321)
    ·
      refine ⟨15234400727765875808073991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20312534303687834410765321 15234400727765875808073991)
      ·
        refine ⟨22851601091648813712110987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15234400727765875808073991 22851601091648813712110987)
        ·
          refine ⟨34277401637473220568166481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22851601091648813712110987 34277401637473220568166481)
          ·
            refine ⟨25708051228104915426124861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34277401637473220568166481 25708051228104915426124861)
            ·
              refine ⟨9640519210539343284796823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25708051228104915426124861 9640519210539343284796823)
              ·
                refine ⟨14460778815809014927195235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9640519210539343284796823 14460778815809014927195235)
                ·
                  refine ⟨21691168223713522390792853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14460778815809014927195235 21691168223713522390792853)
                  ·
                    refine ⟨1016773510486571362068415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21691168223713522390792853 1016773510486571362068415)
                    ·
                      rfl

theorem cell23_5940478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_5940478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5940478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5940478 prefixEnd_5940478 := by exact prefixLift 5940478
  have htrace : WordTrace (prefixWord ++ tailWord_5940478) baseStart_5940478 baseEnd_5940478 := by
    simpa [prefixWord, tailWord_5940478, baseEnd_5940478] using wordTrace_append hprefix tailTrace_5940478
  have hstable : (prefixWord ++ tailWord_5940478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5940478).length < 2 ^ (prefixWord ++ tailWord_5940478).sum := by decide
  have hdescent : baseEnd_5940478 < baseStart_5940478 := by decide
  rcases family_descends (prefixWord ++ tailWord_5940478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5940481 : List Nat := [1, 2, 4, 1, 1, 4, 1, 1, 1, 1, 6]
def baseStart_5940481 : Nat := 118140960795 + 5940481 * 2 ^ 59
def prefixEnd_5940481 : Nat := 4983230072969 + 3 ^ 40 * 5940481 * 2
def baseEnd_5940481 : Nat := 3050322071901677574467731

theorem tailTrace_5940481 : CollatzResearch.WordTrace tailWord_5940481 prefixEnd_5940481 3050322071901677574467731 := by
  unfold tailWord_5940481
  simp only [CollatzResearch.WordTrace]
  refine ⟨216667141991659365227189297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144444761327772910151459531 216667141991659365227189297)
  ·
    refine ⟨162500356493744523920391973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216667141991659365227189297 162500356493744523920391973)
    ·
      refine ⟨30468816842577098235073495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 162500356493744523920391973 30468816842577098235073495)
      ·
        refine ⟨45703225263865647352610243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30468816842577098235073495 45703225263865647352610243)
        ·
          refine ⟨68554837895798471028915365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45703225263865647352610243 68554837895798471028915365)
          ·
            refine ⟨12854032105462213317921631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68554837895798471028915365 12854032105462213317921631)
            ·
              refine ⟨19281048158193319976882447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12854032105462213317921631 19281048158193319976882447)
              ·
                refine ⟨28921572237289979965323671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19281048158193319976882447 28921572237289979965323671)
                ·
                  refine ⟨43382358355934969947985507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28921572237289979965323671 43382358355934969947985507)
                  ·
                    refine ⟨65073537533902454921978261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43382358355934969947985507 65073537533902454921978261)
                    ·
                      refine ⟨3050322071901677574467731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65073537533902454921978261 3050322071901677574467731)
                      ·
                        rfl

theorem cell23_5940481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_5940481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5940481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5940481 prefixEnd_5940481 := by exact prefixLift 5940481
  have htrace : WordTrace (prefixWord ++ tailWord_5940481) baseStart_5940481 baseEnd_5940481 := by
    simpa [prefixWord, tailWord_5940481, baseEnd_5940481] using wordTrace_append hprefix tailTrace_5940481
  have hstable : (prefixWord ++ tailWord_5940481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5940481).length < 2 ^ (prefixWord ++ tailWord_5940481).sum := by decide
  have hdescent : baseEnd_5940481 < baseStart_5940481 := by decide
  rcases family_descends (prefixWord ++ tailWord_5940481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5940491 : List Nat := [1, 1, 1, 1, 5, 3, 4, 7]
def baseStart_5940491 : Nat := 118140960795 + 5940491 * 2 ^ 59
def prefixEnd_5940491 : Nat := 4983230072969 + 3 ^ 40 * 5940491 * 2
def baseEnd_5940491 : Nat := 112975081729934167975655

theorem tailTrace_5940491 : CollatzResearch.WordTrace tailWord_5940491 prefixEnd_5940491 112975081729934167975655 := by
  unfold tailWord_5940491
  simp only [CollatzResearch.WordTrace]
  refine ⟨216667506721623136935053327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144445004481082091290035551 216667506721623136935053327)
  ·
    refine ⟨325001260082434705402579991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216667506721623136935053327 325001260082434705402579991)
    ·
      refine ⟨487501890123652058103869987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325001260082434705402579991 487501890123652058103869987)
      ·
        refine ⟨731252835185478087155804981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 487501890123652058103869987 731252835185478087155804981)
        ·
          refine ⟨68554953298638570670856717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 731252835185478087155804981 68554953298638570670856717)
          ·
            refine ⟨25708107486989464001571269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68554953298638570670856717 25708107486989464001571269)
            ·
              refine ⟨4820270153810524500294613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25708107486989464001571269 4820270153810524500294613)
              ·
                refine ⟨112975081729934167975655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4820270153810524500294613 112975081729934167975655)
                ·
                  rfl

theorem cell23_5940491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 4, 7].length) (baseStart_5940491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5940491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5940491 prefixEnd_5940491 := by exact prefixLift 5940491
  have htrace : WordTrace (prefixWord ++ tailWord_5940491) baseStart_5940491 baseEnd_5940491 := by
    simpa [prefixWord, tailWord_5940491, baseEnd_5940491] using wordTrace_append hprefix tailTrace_5940491
  have hstable : (prefixWord ++ tailWord_5940491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5940491).length < 2 ^ (prefixWord ++ tailWord_5940491).sum := by decide
  have hdescent : baseEnd_5940491 < baseStart_5940491 := by decide
  rcases family_descends (prefixWord ++ tailWord_5940491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5940501 : List Nat := [1, 3, 2, 1, 2, 1, 1, 3, 3, 3, 3]
def baseStart_5940501 : Nat := 118140960795 + 5940501 * 2 ^ 59
def prefixEnd_5940501 : Nat := 4983230072969 + 3 ^ 40 * 5940501 * 2
def baseEnd_5940501 : Nat := 3050332341514767496217639

theorem tailTrace_5940501 : CollatzResearch.WordTrace tailWord_5940501 prefixEnd_5940501 3050332341514767496217639 := by
  unfold tailWord_5940501
  simp only [CollatzResearch.WordTrace]
  refine ⟨216667871451586908642917357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144445247634391272428611571 216667871451586908642917357)
  ·
    refine ⟨81250451794345090741094009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216667871451586908642917357 81250451794345090741094009)
    ·
      refine ⟨60937838845758818055820507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81250451794345090741094009 60937838845758818055820507)
      ·
        refine ⟨91406758268638227083730761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60937838845758818055820507 91406758268638227083730761)
        ·
          refine ⟨68555068701478670312798071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91406758268638227083730761 68555068701478670312798071)
          ·
            refine ⟨102832603052218005469197107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68555068701478670312798071 102832603052218005469197107)
            ·
              refine ⟨154248904578327008203795661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102832603052218005469197107 154248904578327008203795661)
              ·
                refine ⟨57843339216872628076423373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 154248904578327008203795661 57843339216872628076423373)
                ·
                  refine ⟨21691252206327235528658765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57843339216872628076423373 21691252206327235528658765)
                  ·
                    refine ⟨8134219577372713323247037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21691252206327235528658765 8134219577372713323247037)
                    ·
                      refine ⟨3050332341514767496217639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8134219577372713323247037 3050332341514767496217639)
                      ·
                        rfl

theorem cell23_5940501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 3, 3, 3].length) (baseStart_5940501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5940501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5940501 prefixEnd_5940501 := by exact prefixLift 5940501
  have htrace : WordTrace (prefixWord ++ tailWord_5940501) baseStart_5940501 baseEnd_5940501 := by
    simpa [prefixWord, tailWord_5940501, baseEnd_5940501] using wordTrace_append hprefix tailTrace_5940501
  have hstable : (prefixWord ++ tailWord_5940501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5940501).length < 2 ^ (prefixWord ++ tailWord_5940501).sum := by decide
  have hdescent : baseEnd_5940501 < baseStart_5940501 := by decide
  rcases family_descends (prefixWord ++ tailWord_5940501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5940528 : List Nat := [2, 1, 1, 1, 2, 2, 4, 2, 3, 3, 2]
def baseStart_5940528 : Nat := 118140960795 + 5940528 * 2 ^ 59
def prefixEnd_5940528 : Nat := 4983230072969 + 3 ^ 40 * 5940528 * 2
def baseEnd_5940528 : Nat := 3050346205492438890580015

theorem tailTrace_5940528 : CollatzResearch.WordTrace tailWord_5940528 prefixEnd_5940528 3050346205492438890580015 := by
  unfold tailWord_5940528
  simp only [CollatzResearch.WordTrace]
  refine ⟨108334428111244546127075119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144445904148326061502766825 108334428111244546127075119)
  ·
    refine ⟨162501642166866819190612679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108334428111244546127075119 162501642166866819190612679)
    ·
      refine ⟨243752463250300228785919019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162501642166866819190612679 243752463250300228785919019)
      ·
        refine ⟨365628694875450343178878529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243752463250300228785919019 365628694875450343178878529)
        ·
          refine ⟨274221521156587757384158897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 365628694875450343178878529 274221521156587757384158897)
          ·
            refine ⟨205666140867440818038119173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 274221521156587757384158897 205666140867440818038119173)
            ·
              refine ⟨38562401412645153382147345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 205666140867440818038119173 38562401412645153382147345)
              ·
                refine ⟨28921801059483865036610509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38562401412645153382147345 28921801059483865036610509)
                ·
                  refine ⟨10845675397306449388728941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28921801059483865036610509 10845675397306449388728941)
                  ·
                    refine ⟨4067128273989918520773353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10845675397306449388728941 4067128273989918520773353)
                    ·
                      refine ⟨3050346205492438890580015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4067128273989918520773353 3050346205492438890580015)
                      ·
                        rfl

theorem cell23_5940528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 3, 3, 2].length) (baseStart_5940528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5940528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5940528 prefixEnd_5940528 := by exact prefixLift 5940528
  have htrace : WordTrace (prefixWord ++ tailWord_5940528) baseStart_5940528 baseEnd_5940528 := by
    simpa [prefixWord, tailWord_5940528, baseEnd_5940528] using wordTrace_append hprefix tailTrace_5940528
  have hstable : (prefixWord ++ tailWord_5940528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5940528).length < 2 ^ (prefixWord ++ tailWord_5940528).sum := by decide
  have hdescent : baseEnd_5940528 < baseStart_5940528 := by decide
  rcases family_descends (prefixWord ++ tailWord_5940528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5940561 : List Nat := [1, 2, 2, 1, 4, 1, 1, 3, 2, 1, 5]
def baseStart_5940561 : Nat := 118140960795 + 5940561 * 2 ^ 59
def prefixEnd_5940561 : Nat := 4983230072969 + 3 ^ 40 * 5940561 * 2
def baseEnd_5940561 : Nat := 3050363150354037261467363

theorem tailTrace_5940561 : CollatzResearch.WordTrace tailWord_5940561 prefixEnd_5940561 3050363150354037261467363 := by
  unfold tailWord_5940561
  simp only [CollatzResearch.WordTrace]
  refine ⟨216670059831369538890101537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144446706554246359260067691 216670059831369538890101537)
  ·
    refine ⟨162502544873527154167576153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216670059831369538890101537 162502544873527154167576153)
    ·
      refine ⟨121876908655145365625682115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162502544873527154167576153 121876908655145365625682115)
      ·
        refine ⟨182815362982718048438523173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121876908655145365625682115 182815362982718048438523173)
        ·
          refine ⟨34277880559259634082223095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 182815362982718048438523173 34277880559259634082223095)
          ·
            refine ⟨51416820838889451123334643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34277880559259634082223095 51416820838889451123334643)
            ·
              refine ⟨77125231258334176685001965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51416820838889451123334643 77125231258334176685001965)
              ·
                refine ⟨28921961721875316256875737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77125231258334176685001965 28921961721875316256875737)
                ·
                  refine ⟨21691471291406487192656803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28921961721875316256875737 21691471291406487192656803)
                  ·
                    refine ⟨32537206937109730788985205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21691471291406487192656803 32537206937109730788985205)
                    ·
                      refine ⟨3050363150354037261467363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32537206937109730788985205 3050363150354037261467363)
                      ·
                        rfl

theorem cell23_5940561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 2, 1, 5].length) (baseStart_5940561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5940561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5940561 prefixEnd_5940561 := by exact prefixLift 5940561
  have htrace : WordTrace (prefixWord ++ tailWord_5940561) baseStart_5940561 baseEnd_5940561 := by
    simpa [prefixWord, tailWord_5940561, baseEnd_5940561] using wordTrace_append hprefix tailTrace_5940561
  have hstable : (prefixWord ++ tailWord_5940561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5940561).length < 2 ^ (prefixWord ++ tailWord_5940561).sum := by decide
  have hdescent : baseEnd_5940561 < baseStart_5940561 := by decide
  rcases family_descends (prefixWord ++ tailWord_5940561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5940578 : List Nat := [3, 3, 2, 1, 1, 1, 1, 1, 1, 6, 3]
def baseStart_5940578 : Nat := 118140960795 + 5940578 * 2 ^ 59
def prefixEnd_5940578 : Nat := 4983230072969 + 3 ^ 40 * 5940578 * 2
def baseEnd_5940578 : Nat := 3050371879525163694954785

theorem tailTrace_5940578 : CollatzResearch.WordTrace tailWord_5940578 prefixEnd_5940578 3050371879525163694954785 := by
  unfold tailWord_5940578
  simp only [CollatzResearch.WordTrace]
  refine ⟨54167669968076987698367597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144447119914871967195646925 54167669968076987698367597)
  ·
    refine ⟨20312876238028870386887849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54167669968076987698367597 20312876238028870386887849)
    ·
      refine ⟨15234657178521652790165887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20312876238028870386887849 15234657178521652790165887)
      ·
        refine ⟨22851985767782479185248831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15234657178521652790165887 22851985767782479185248831)
        ·
          refine ⟨34277978651673718777873247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22851985767782479185248831 34277978651673718777873247)
          ·
            refine ⟨51416967977510578166809871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34277978651673718777873247 51416967977510578166809871)
            ·
              refine ⟨77125451966265867250214807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51416967977510578166809871 77125451966265867250214807)
              ·
                refine ⟨115688177949398800875322211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77125451966265867250214807 115688177949398800875322211)
                ·
                  refine ⟨173532266924098201312983317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115688177949398800875322211 173532266924098201312983317)
                  ·
                    refine ⟨8134325012067103186546093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 173532266924098201312983317 8134325012067103186546093)
                    ·
                      refine ⟨3050371879525163694954785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8134325012067103186546093 3050371879525163694954785)
                      ·
                        rfl

theorem cell23_5940578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_5940578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5940578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5940578 prefixEnd_5940578 := by exact prefixLift 5940578
  have htrace : WordTrace (prefixWord ++ tailWord_5940578) baseStart_5940578 baseEnd_5940578 := by
    simpa [prefixWord, tailWord_5940578, baseEnd_5940578] using wordTrace_append hprefix tailTrace_5940578
  have hstable : (prefixWord ++ tailWord_5940578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5940578).length < 2 ^ (prefixWord ++ tailWord_5940578).sum := by decide
  have hdescent : baseEnd_5940578 < baseStart_5940578 := by decide
  rcases family_descends (prefixWord ++ tailWord_5940578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5940581 : List Nat := [1, 3, 1, 3, 1, 2, 2, 3, 7]
def baseStart_5940581 : Nat := 118140960795 + 5940581 * 2 ^ 59
def prefixEnd_5940581 : Nat := 4983230072969 + 3 ^ 40 * 5940581 * 2
def baseEnd_5940581 : Nat := 338930379996347464801919

theorem tailTrace_5940581 : CollatzResearch.WordTrace tailWord_5940581 prefixEnd_5940581 338930379996347464801919 := by
  unfold tailWord_5940581
  simp only [CollatzResearch.WordTrace]
  refine ⟨216670789291297082305829597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144447192860864721537219731 216670789291297082305829597)
  ·
    refine ⟨81251545984236405864686099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216670789291297082305829597 81251545984236405864686099)
    ·
      refine ⟨121877318976354608797029149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81251545984236405864686099 121877318976354608797029149)
      ·
        refine ⟨45703994616132978298885931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121877318976354608797029149 45703994616132978298885931)
        ·
          refine ⟨68555991924199467448328897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45703994616132978298885931 68555991924199467448328897)
          ·
            refine ⟨51416993943149600586246673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68555991924199467448328897 51416993943149600586246673)
            ·
              refine ⟨38562745457362200439685005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51416993943149600586246673 38562745457362200439685005)
              ·
                refine ⟨14461029546510825164881877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38562745457362200439685005 14461029546510825164881877)
                ·
                  refine ⟨338930379996347464801919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14461029546510825164881877 338930379996347464801919)
                  ·
                    rfl

theorem cell23_5940581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 3, 7].length) (baseStart_5940581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5940581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5940581 prefixEnd_5940581 := by exact prefixLift 5940581
  have htrace : WordTrace (prefixWord ++ tailWord_5940581) baseStart_5940581 baseEnd_5940581 := by
    simpa [prefixWord, tailWord_5940581, baseEnd_5940581] using wordTrace_append hprefix tailTrace_5940581
  have hstable : (prefixWord ++ tailWord_5940581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5940581).length < 2 ^ (prefixWord ++ tailWord_5940581).sum := by decide
  have hdescent : baseEnd_5940581 < baseStart_5940581 := by decide
  rcases family_descends (prefixWord ++ tailWord_5940581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5940588 : List Nat := [2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 4]
def baseStart_5940588 : Nat := 118140960795 + 5940588 * 2 ^ 59
def prefixEnd_5940588 : Nat := 4983230072969 + 3 ^ 40 * 5940588 * 2
def baseEnd_5940588 : Nat := 3050377014331708655829739

theorem tailTrace_5940588 : CollatzResearch.WordTrace tailWord_5940588 prefixEnd_5940588 3050377014331708655829739 := by
  unfold tailWord_5940588
  simp only [CollatzResearch.WordTrace]
  refine ⟨108335522301135861250667209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144447363068181148334222945 108335522301135861250667209)
  ·
    refine ⟨81251641725851895938000407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108335522301135861250667209 81251641725851895938000407)
    ·
      refine ⟨121877462588777843907000611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81251641725851895938000407 121877462588777843907000611)
      ·
        refine ⟨182816193883166765860500917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121877462588777843907000611 182816193883166765860500917)
        ·
          refine ⟨17139018176546884299421961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 182816193883166765860500917 17139018176546884299421961)
          ·
            refine ⟨12854263632410163224566471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17139018176546884299421961 12854263632410163224566471)
            ·
              refine ⟨19281395448615244836849707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12854263632410163224566471 19281395448615244836849707)
              ·
                refine ⟨28922093172922867255274561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19281395448615244836849707 28922093172922867255274561)
                ·
                  refine ⟨21691569879692150441455921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28922093172922867255274561 21691569879692150441455921)
                  ·
                    refine ⟨16268677409769112831091941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21691569879692150441455921 16268677409769112831091941)
                    ·
                      refine ⟨3050377014331708655829739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16268677409769112831091941 3050377014331708655829739)
                      ·
                        rfl

theorem cell23_5940588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 4].length) (baseStart_5940588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5940588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5940588 prefixEnd_5940588 := by exact prefixLift 5940588
  have htrace : WordTrace (prefixWord ++ tailWord_5940588) baseStart_5940588 baseEnd_5940588 := by
    simpa [prefixWord, tailWord_5940588, baseEnd_5940588] using wordTrace_append hprefix tailTrace_5940588
  have hstable : (prefixWord ++ tailWord_5940588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5940588).length < 2 ^ (prefixWord ++ tailWord_5940588).sum := by decide
  have hdescent : baseEnd_5940588 < baseStart_5940588 := by decide
  rcases family_descends (prefixWord ++ tailWord_5940588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5940615 : List Nat := [1, 1, 4, 2, 2, 3, 2, 3, 5]
def baseStart_5940615 : Nat := 118140960795 + 5940615 * 2 ^ 59
def prefixEnd_5940615 : Nat := 4983230072969 + 3 ^ 40 * 5940615 * 2
def baseEnd_5940615 : Nat := 338932319812153338910235

theorem tailTrace_5940615 : CollatzResearch.WordTrace tailWord_5940615 prefixEnd_5940615 338932319812153338910235 := by
  unfold tailWord_5940615
  simp only [CollatzResearch.WordTrace]
  refine ⟨216672029373173906112567299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144448019582115937408378199 216672029373173906112567299)
  ·
    refine ⟨325008044059760859168850949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216672029373173906112567299 325008044059760859168850949)
    ·
      refine ⟨60939008261205161094159553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 325008044059760859168850949 60939008261205161094159553)
      ·
        refine ⟨45704256195903870820619665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60939008261205161094159553 45704256195903870820619665)
        ·
          refine ⟨34278192146927903115464749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45704256195903870820619665 34278192146927903115464749)
          ·
            refine ⟨12854322055097963668299281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34278192146927903115464749 12854322055097963668299281)
            ·
              refine ⟨9640741541323472751224461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12854322055097963668299281 9640741541323472751224461)
              ·
                refine ⟨3615278077996302281709173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9640741541323472751224461 3615278077996302281709173)
                ·
                  refine ⟨338932319812153338910235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3615278077996302281709173 338932319812153338910235)
                  ·
                    rfl

theorem cell23_5940615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 3, 5].length) (baseStart_5940615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5940615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5940615 prefixEnd_5940615 := by exact prefixLift 5940615
  have htrace : WordTrace (prefixWord ++ tailWord_5940615) baseStart_5940615 baseEnd_5940615 := by
    simpa [prefixWord, tailWord_5940615, baseEnd_5940615] using wordTrace_append hprefix tailTrace_5940615
  have hstable : (prefixWord ++ tailWord_5940615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5940615).length < 2 ^ (prefixWord ++ tailWord_5940615).sum := by decide
  have hdescent : baseEnd_5940615 < baseStart_5940615 := by decide
  rcases family_descends (prefixWord ++ tailWord_5940615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5940658 : List Nat := [3, 2, 1, 1, 1, 1, 2, 3, 5, 4]
def baseStart_5940658 : Nat := 118140960795 + 5940658 * 2 ^ 59
def prefixEnd_5940658 : Nat := 4983230072969 + 3 ^ 40 * 5940658 * 2
def baseEnd_5940658 : Nat := 1016804319325841127318139

theorem tailTrace_5940658 : CollatzResearch.WordTrace tailWord_5940658 prefixEnd_5940658 1016804319325841127318139 := by
  unfold tailWord_5940658
  simp only [CollatzResearch.WordTrace]
  refine ⟨54168399428004531114095657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144449065141345416304255085 54168399428004531114095657)
  ·
    refine ⟨40626299571003398335571743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54168399428004531114095657 40626299571003398335571743)
    ·
      refine ⟨60939449356505097503357615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40626299571003398335571743 60939449356505097503357615)
      ·
        refine ⟨91409174034757646255036423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60939449356505097503357615 91409174034757646255036423)
        ·
          refine ⟨137113761052136469382554635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91409174034757646255036423 137113761052136469382554635)
          ·
            refine ⟨205670641578204704073831953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137113761052136469382554635 205670641578204704073831953)
            ·
              refine ⟨154252981183653528055373965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 205670641578204704073831953 154252981183653528055373965)
              ·
                refine ⟨57844867943870073020765237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 154252981183653528055373965 57844867943870073020765237)
                ·
                  refine ⟨5422956369737819345696741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57844867943870073020765237 5422956369737819345696741)
                  ·
                    refine ⟨1016804319325841127318139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5422956369737819345696741 1016804319325841127318139)
                    ·
                      rfl

theorem cell23_5940658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 5, 4].length) (baseStart_5940658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5940658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5940658 prefixEnd_5940658 := by exact prefixLift 5940658
  have htrace : WordTrace (prefixWord ++ tailWord_5940658) baseStart_5940658 baseEnd_5940658 := by
    simpa [prefixWord, tailWord_5940658, baseEnd_5940658] using wordTrace_append hprefix tailTrace_5940658
  have hstable : (prefixWord ++ tailWord_5940658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5940658).length < 2 ^ (prefixWord ++ tailWord_5940658).sum := by decide
  have hdescent : baseEnd_5940658 < baseStart_5940658 := by decide
  rcases family_descends (prefixWord ++ tailWord_5940658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5940705 : List Nat := [1, 2, 3, 1, 2, 3, 4, 1, 6]
def baseStart_5940705 : Nat := 118140960795 + 5940705 * 2 ^ 59
def prefixEnd_5940705 : Nat := 4983230072969 + 3 ^ 40 * 5940705 * 2
def baseEnd_5940705 : Nat := 338937454618698299785189

theorem tailTrace_5940705 : CollatzResearch.WordTrace tailWord_5940705 prefixEnd_5940705 338937454618698299785189 := by
  unfold tailWord_5940705
  simp only [CollatzResearch.WordTrace]
  refine ⟨216675311942847851483343569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144450207961898567655562379 216675311942847851483343569)
  ·
    refine ⟨162506483957135888612507677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216675311942847851483343569 162506483957135888612507677)
    ·
      refine ⟨60939931483925958229690379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162506483957135888612507677 60939931483925958229690379)
      ·
        refine ⟨91409897225888937344535569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60939931483925958229690379 91409897225888937344535569)
        ·
          refine ⟨68557422919416703008401677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91409897225888937344535569 68557422919416703008401677)
          ·
            refine ⟨25709033594781263628150629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68557422919416703008401677 25709033594781263628150629)
            ·
              refine ⟨4820443799021486930278243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25709033594781263628150629 4820443799021486930278243)
              ·
                refine ⟨7230665698532230395417365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4820443799021486930278243 7230665698532230395417365)
                ·
                  refine ⟨338937454618698299785189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7230665698532230395417365 338937454618698299785189)
                  ·
                    rfl

theorem cell23_5940705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 4, 1, 6].length) (baseStart_5940705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5940705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5940705 prefixEnd_5940705 := by exact prefixLift 5940705
  have htrace : WordTrace (prefixWord ++ tailWord_5940705) baseStart_5940705 baseEnd_5940705 := by
    simpa [prefixWord, tailWord_5940705, baseEnd_5940705] using wordTrace_append hprefix tailTrace_5940705
  have hstable : (prefixWord ++ tailWord_5940705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5940705).length < 2 ^ (prefixWord ++ tailWord_5940705).sum := by decide
  have hdescent : baseEnd_5940705 < baseStart_5940705 := by decide
  rcases family_descends (prefixWord ++ tailWord_5940705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5940765 : List Nat := [1, 4, 2, 2, 1, 1, 4, 1, 1, 6]
def baseStart_5940765 : Nat := 118140960795 + 5940765 * 2 ^ 59
def prefixEnd_5940765 : Nat := 4983230072969 + 3 ^ 40 * 5940765 * 2
def baseEnd_5940765 : Nat := 1016822633469184821105475

theorem tailTrace_5940765 : CollatzResearch.WordTrace tailWord_5940765 prefixEnd_5940765 1016822633469184821105475 := by
  unfold tailWord_5940765
  simp only [CollatzResearch.WordTrace]
  refine ⟨216677500322630481730527749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144451666881753654487018499 216677500322630481730527749)
  ·
    refine ⟨40627031310493215324473953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 216677500322630481730527749 40627031310493215324473953)
    ·
      refine ⟨30470273482869911493355465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40627031310493215324473953 30470273482869911493355465)
      ·
        refine ⟨22852705112152433620016599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30470273482869911493355465 22852705112152433620016599)
        ·
          refine ⟨34279057668228650430024899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22852705112152433620016599 34279057668228650430024899)
          ·
            refine ⟨51418586502342975645037349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34279057668228650430024899 51418586502342975645037349)
            ·
              refine ⟨9640984969189307933444503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51418586502342975645037349 9640984969189307933444503)
              ·
                refine ⟨14461477453783961900166755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9640984969189307933444503 14461477453783961900166755)
                ·
                  refine ⟨21692216180675942850250133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14461477453783961900166755 21692216180675942850250133)
                  ·
                    refine ⟨1016822633469184821105475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21692216180675942850250133 1016822633469184821105475)
                    ·
                      rfl

theorem cell23_5940765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 1, 1, 6].length) (baseStart_5940765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5940765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5940765 prefixEnd_5940765 := by exact prefixLift 5940765
  have htrace : WordTrace (prefixWord ++ tailWord_5940765) baseStart_5940765 baseEnd_5940765 := by
    simpa [prefixWord, tailWord_5940765, baseEnd_5940765] using wordTrace_append hprefix tailTrace_5940765
  have hstable : (prefixWord ++ tailWord_5940765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5940765).length < 2 ^ (prefixWord ++ tailWord_5940765).sum := by decide
  have hdescent : baseEnd_5940765 < baseStart_5940765 := by decide
  rcases family_descends (prefixWord ++ tailWord_5940765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5940776 : List Nat := [2, 1, 5, 2, 2, 2, 1, 1, 2, 3, 2]
def baseStart_5940776 : Nat := 118140960795 + 5940776 * 2 ^ 59
def prefixEnd_5940776 : Nat := 4983230072969 + 3 ^ 40 * 5940776 * 2
def baseEnd_5940776 : Nat := 3050473548694753920278875

theorem tailTrace_5940776 : CollatzResearch.WordTrace tailWord_5940776 prefixEnd_5940776 3050473548694753920278875 := by
  unfold tailWord_5940776
  simp only [CollatzResearch.WordTrace]
  refine ⟨108338950762795315304589091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144451934350393753739452121 108338950762795315304589091)
  ·
    refine ⟨162508426144192972956883637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108338950762795315304589091 162508426144192972956883637)
    ·
      refine ⟨15235164951018091214707841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 162508426144192972956883637 15235164951018091214707841)
      ·
        refine ⟨11426373713263568411030881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15235164951018091214707841 11426373713263568411030881)
        ·
          refine ⟨8569780284947676308273161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11426373713263568411030881 8569780284947676308273161)
          ·
            refine ⟨6427335213710757231204871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8569780284947676308273161 6427335213710757231204871)
            ·
              refine ⟨9641002820566135846807307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6427335213710757231204871 9641002820566135846807307)
              ·
                refine ⟨14461504230849203770210961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9641002820566135846807307 14461504230849203770210961)
                ·
                  refine ⟨10846128173136902827658221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14461504230849203770210961 10846128173136902827658221)
                  ·
                    refine ⟨4067298064926338560371833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10846128173136902827658221 4067298064926338560371833)
                    ·
                      refine ⟨3050473548694753920278875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4067298064926338560371833 3050473548694753920278875)
                      ·
                        rfl

theorem cell23_5940776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_5940776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5940776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5940776 prefixEnd_5940776 := by exact prefixLift 5940776
  have htrace : WordTrace (prefixWord ++ tailWord_5940776) baseStart_5940776 baseEnd_5940776 := by
    simpa [prefixWord, tailWord_5940776, baseEnd_5940776] using wordTrace_append hprefix tailTrace_5940776
  have hstable : (prefixWord ++ tailWord_5940776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5940776).length < 2 ^ (prefixWord ++ tailWord_5940776).sum := by decide
  have hdescent : baseEnd_5940776 < baseStart_5940776 := by decide
  rcases family_descends (prefixWord ++ tailWord_5940776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5940789 : List Nat := [1, 3, 3, 1, 1, 5, 2, 1, 1, 1, 4]
def baseStart_5940789 : Nat := 118140960795 + 5940789 * 2 ^ 59
def prefixEnd_5940789 : Nat := 4983230072969 + 3 ^ 40 * 5940789 * 2
def baseEnd_5940789 : Nat := 3050480223943262369416315

theorem tailTrace_5940789 : CollatzResearch.WordTrace tailWord_5940789 prefixEnd_5940789 3050480223943262369416315 := by
  unfold tailWord_5940789
  simp only [CollatzResearch.WordTrace]
  refine ⟨216678375674543533829401421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144452250449695689219600947 216678375674543533829401421)
  ·
    refine ⟨81254390877953825186025533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216678375674543533829401421 81254390877953825186025533)
    ·
      refine ⟨30470396579232684444759575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81254390877953825186025533 30470396579232684444759575)
      ·
        refine ⟨45705594868849026667139363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30470396579232684444759575 45705594868849026667139363)
        ·
          refine ⟨68558392303273540000709045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45705594868849026667139363 68558392303273540000709045)
          ·
            refine ⟨6427349278431894375066473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68558392303273540000709045 6427349278431894375066473)
            ·
              refine ⟨4820511958823920781299855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6427349278431894375066473 4820511958823920781299855)
              ·
                refine ⟨7230767938235881171949783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4820511958823920781299855 7230767938235881171949783)
                ·
                  refine ⟨10846151907353821757924675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7230767938235881171949783 10846151907353821757924675)
                  ·
                    refine ⟨16269227861030732636887013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10846151907353821757924675 16269227861030732636887013)
                    ·
                      refine ⟨3050480223943262369416315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16269227861030732636887013 3050480223943262369416315)
                      ·
                        rfl

theorem cell23_5940789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 2, 1, 1, 1, 4].length) (baseStart_5940789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5940789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5940789 prefixEnd_5940789 := by exact prefixLift 5940789
  have htrace : WordTrace (prefixWord ++ tailWord_5940789) baseStart_5940789 baseEnd_5940789 := by
    simpa [prefixWord, tailWord_5940789, baseEnd_5940789] using wordTrace_append hprefix tailTrace_5940789
  have hstable : (prefixWord ++ tailWord_5940789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5940789).length < 2 ^ (prefixWord ++ tailWord_5940789).sum := by decide
  have hdescent : baseEnd_5940789 < baseStart_5940789 := by decide
  rcases family_descends (prefixWord ++ tailWord_5940789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5940792 : List Nat := [2, 1, 2, 1, 4, 3, 1, 3, 1, 2, 3]
def baseStart_5940792 : Nat := 118140960795 + 5940792 * 2 ^ 59
def prefixEnd_5940792 : Nat := 4983230072969 + 3 ^ 40 * 5940792 * 2
def baseEnd_5940792 : Nat := 3050481764385225857678801

theorem tailTrace_5940792 : CollatzResearch.WordTrace tailWord_5940792 prefixEnd_5940792 3050481764385225857678801 := by
  unfold tailWord_5940792
  simp only [CollatzResearch.WordTrace]
  refine ⟨108339242546766332670880315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144452323395688443561173753 108339242546766332670880315)
  ·
    refine ⟨162508863820149499006320473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108339242546766332670880315 162508863820149499006320473)
    ·
      refine ⟨121881647865112124254740355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162508863820149499006320473 121881647865112124254740355)
      ·
        refine ⟨182822471797668186382110533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121881647865112124254740355 182822471797668186382110533)
        ·
          refine ⟨34279213462062784946645725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 182822471797668186382110533 34279213462062784946645725)
          ·
            refine ⟨12854705048273544354992147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34279213462062784946645725 12854705048273544354992147)
            ·
              refine ⟨19282057572410316532488221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12854705048273544354992147 19282057572410316532488221)
              ·
                refine ⟨7230771589653868699683083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19282057572410316532488221 7230771589653868699683083)
                ·
                  refine ⟨10846157384480803049524625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7230771589653868699683083 10846157384480803049524625)
                  ·
                    refine ⟨8134618038360602287143469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10846157384480803049524625 8134618038360602287143469)
                    ·
                      refine ⟨3050481764385225857678801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8134618038360602287143469 3050481764385225857678801)
                      ·
                        rfl

theorem cell23_5940792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 3, 1, 2, 3].length) (baseStart_5940792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5940792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5940792 prefixEnd_5940792 := by exact prefixLift 5940792
  have htrace : WordTrace (prefixWord ++ tailWord_5940792) baseStart_5940792 baseEnd_5940792 := by
    simpa [prefixWord, tailWord_5940792, baseEnd_5940792] using wordTrace_append hprefix tailTrace_5940792
  have hstable : (prefixWord ++ tailWord_5940792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5940792).length < 2 ^ (prefixWord ++ tailWord_5940792).sum := by decide
  have hdescent : baseEnd_5940792 < baseStart_5940792 := by decide
  rcases family_descends (prefixWord ++ tailWord_5940792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5940858 : List Nat := [3, 1, 1, 1, 1, 1, 1, 3, 2, 3, 6]
def baseStart_5940858 : Nat := 118140960795 + 5940858 * 2 ^ 59
def prefixEnd_5940858 : Nat := 4983230072969 + 3 ^ 40 * 5940858 * 2
def baseEnd_5940858 : Nat := 3050515654108422599453497

theorem tailTrace_5940858 : CollatzResearch.WordTrace tailWord_5940858 prefixEnd_5940858 3050515654108422599453497 := by
  unfold tailWord_5940858
  simp only [CollatzResearch.WordTrace]
  refine ⟨54170223077823389653415807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144453928207529039075775485 54170223077823389653415807)
  ·
    refine ⟨81255334616735084480123711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54170223077823389653415807 81255334616735084480123711)
    ·
      refine ⟨121883001925102626720185567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81255334616735084480123711 121883001925102626720185567)
      ·
        refine ⟨182824502887653940080278351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121883001925102626720185567 182824502887653940080278351)
        ·
          refine ⟨274236754331480910120417527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182824502887653940080278351 274236754331480910120417527)
          ·
            refine ⟨411355131497221365180626291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274236754331480910120417527 411355131497221365180626291)
            ·
              refine ⟨617032697245832047770939437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 411355131497221365180626291 617032697245832047770939437)
              ·
                refine ⟨231387261467187017914102289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 617032697245832047770939437 231387261467187017914102289)
                ·
                  refine ⟨173540446100390263435576717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 231387261467187017914102289 173540446100390263435576717)
                  ·
                    refine ⟨65077667287646348788341269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 173540446100390263435576717 65077667287646348788341269)
                    ·
                      refine ⟨3050515654108422599453497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65077667287646348788341269 3050515654108422599453497)
                      ·
                        rfl

theorem cell23_5940858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 2, 3, 6].length) (baseStart_5940858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5940858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5940858 prefixEnd_5940858 := by exact prefixLift 5940858
  have htrace : WordTrace (prefixWord ++ tailWord_5940858) baseStart_5940858 baseEnd_5940858 := by
    simpa [prefixWord, tailWord_5940858, baseEnd_5940858] using wordTrace_append hprefix tailTrace_5940858
  have hstable : (prefixWord ++ tailWord_5940858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5940858).length < 2 ^ (prefixWord ++ tailWord_5940858).sum := by decide
  have hdescent : baseEnd_5940858 < baseStart_5940858 := by decide
  rcases family_descends (prefixWord ++ tailWord_5940858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5940915 : List Nat := [1, 1, 1, 2, 3, 3, 1, 4, 2, 5]
def baseStart_5940915 : Nat := 118140960795 + 5940915 * 2 ^ 59
def prefixEnd_5940915 : Nat := 4983230072969 + 3 ^ 40 * 5940915 * 2
def baseEnd_5940915 : Nat := 1016848307501909625480245

theorem tailTrace_5940915 : CollatzResearch.WordTrace tailWord_5940915 prefixEnd_5940915 1016848307501909625480245 := by
  unfold tailWord_5940915
  simp only [CollatzResearch.WordTrace]
  refine ⟨216682971272087057348488199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144455314181391371565658799 216682971272087057348488199)
  ·
    refine ⟨325024456908130586022732299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216682971272087057348488199 325024456908130586022732299)
    ·
      refine ⟨487536685362195879034098449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325024456908130586022732299 487536685362195879034098449)
      ·
        refine ⟨365652514021646909275573837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 487536685362195879034098449 365652514021646909275573837)
        ·
          refine ⟨137119692758117590978340189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 365652514021646909275573837 137119692758117590978340189)
          ·
            refine ⟨51419884784294096616877571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137119692758117590978340189 51419884784294096616877571)
            ·
              refine ⟨77129827176441144925316357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51419884784294096616877571 77129827176441144925316357)
              ·
                refine ⟨14461842595582714673496817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77129827176441144925316357 14461842595582714673496817)
                ·
                  refine ⟨10846381946687036005122613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14461842595582714673496817 10846381946687036005122613)
                  ·
                    refine ⟨1016848307501909625480245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10846381946687036005122613 1016848307501909625480245)
                    ·
                      rfl

theorem cell23_5940915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 4, 2, 5].length) (baseStart_5940915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5940915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5940915 prefixEnd_5940915 := by exact prefixLift 5940915
  have htrace : WordTrace (prefixWord ++ tailWord_5940915) baseStart_5940915 baseEnd_5940915 := by
    simpa [prefixWord, tailWord_5940915, baseEnd_5940915] using wordTrace_append hprefix tailTrace_5940915
  have hstable : (prefixWord ++ tailWord_5940915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5940915).length < 2 ^ (prefixWord ++ tailWord_5940915).sum := by decide
  have hdescent : baseEnd_5940915 < baseStart_5940915 := by decide
  rcases family_descends (prefixWord ++ tailWord_5940915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5940919 : List Nat := [1, 1, 3, 1, 5, 1, 4, 2, 5]
def baseStart_5940919 : Nat := 118140960795 + 5940919 * 2 ^ 59
def prefixEnd_5940919 : Nat := 4983230072969 + 3 ^ 40 * 5940919 * 2
def baseEnd_5940919 : Nat := 338949664047594095643413

theorem tailTrace_5940919 : CollatzResearch.WordTrace tailWord_5940919 prefixEnd_5940919 338949664047594095643413 := by
  unfold tailWord_5940919
  simp only [CollatzResearch.WordTrace]
  refine ⟨216683117164072566031633811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144455411442715044021089207 216683117164072566031633811)
  ·
    refine ⟨325024675746108849047450717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216683117164072566031633811 325024675746108849047450717)
    ·
      refine ⟨121884253404790818392794019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 325024675746108849047450717 121884253404790818392794019)
      ·
        refine ⟨182826380107186227589191029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121884253404790818392794019 182826380107186227589191029)
        ·
          refine ⟨17139973135048708836486659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 182826380107186227589191029 17139973135048708836486659)
          ·
            refine ⟨25709959702573063254729989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17139973135048708836486659 25709959702573063254729989)
            ·
              refine ⟨4820617444232449360261873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25709959702573063254729989 4820617444232449360261873)
              ·
                refine ⟨3615463083174337020196405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4820617444232449360261873 3615463083174337020196405)
                ·
                  refine ⟨338949664047594095643413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3615463083174337020196405 338949664047594095643413)
                  ·
                    rfl

theorem cell23_5940919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 4, 2, 5].length) (baseStart_5940919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5940919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5940919 prefixEnd_5940919 := by exact prefixLift 5940919
  have htrace : WordTrace (prefixWord ++ tailWord_5940919) baseStart_5940919 baseEnd_5940919 := by
    simpa [prefixWord, tailWord_5940919, baseEnd_5940919] using wordTrace_append hprefix tailTrace_5940919
  have hstable : (prefixWord ++ tailWord_5940919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5940919).length < 2 ^ (prefixWord ++ tailWord_5940919).sum := by decide
  have hdescent : baseEnd_5940919 < baseStart_5940919 := by decide
  rcases family_descends (prefixWord ++ tailWord_5940919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5940922 : List Nat := [3, 1, 1, 1, 2, 4, 1, 1, 2, 5, 2]
def baseStart_5940922 : Nat := 118140960795 + 5940922 * 2 ^ 59
def prefixEnd_5940922 : Nat := 4983230072969 + 3 ^ 40 * 5940922 * 2
def baseEnd_5940922 : Nat := 3050548516870310349053203

theorem tailTrace_5940922 : CollatzResearch.WordTrace tailWord_5940922 prefixEnd_5940922 3050548516870310349053203 := by
  unfold tailWord_5940922
  simp only [CollatzResearch.WordTrace]
  refine ⟨54170806645765424385998255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144455484388707798362662013 54170806645765424385998255)
  ·
    refine ⟨81256209968648136578997383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54170806645765424385998255 81256209968648136578997383)
    ·
      refine ⟨121884314952972204868496075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81256209968648136578997383 121884314952972204868496075)
      ·
        refine ⟨182826472429458307302744113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121884314952972204868496075 182826472429458307302744113)
        ·
          refine ⟨137119854322093730477058085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182826472429458307302744113 137119854322093730477058085)
          ·
            refine ⟨25709972685392574464448391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 137119854322093730477058085 25709972685392574464448391)
            ·
              refine ⟨38564959028088861696672587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25709972685392574464448391 38564959028088861696672587)
              ·
                refine ⟨57847438542133292545008881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38564959028088861696672587 57847438542133292545008881)
                ·
                  refine ⟨43385578906599969408756661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57847438542133292545008881 43385578906599969408756661)
                  ·
                    refine ⟨4067398022493747132070937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43385578906599969408756661 4067398022493747132070937)
                    ·
                      refine ⟨3050548516870310349053203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4067398022493747132070937 3050548516870310349053203)
                      ·
                        rfl

theorem cell23_5940922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 2, 5, 2].length) (baseStart_5940922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5940922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5940922 prefixEnd_5940922 := by exact prefixLift 5940922
  have htrace : WordTrace (prefixWord ++ tailWord_5940922) baseStart_5940922 baseEnd_5940922 := by
    simpa [prefixWord, tailWord_5940922, baseEnd_5940922] using wordTrace_append hprefix tailTrace_5940922
  have hstable : (prefixWord ++ tailWord_5940922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5940922).length < 2 ^ (prefixWord ++ tailWord_5940922).sum := by decide
  have hdescent : baseEnd_5940922 < baseStart_5940922 := by decide
  rcases family_descends (prefixWord ++ tailWord_5940922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5940925 : List Nat := [1, 4, 1, 2, 1, 2, 1, 3, 1, 2, 5]
def baseStart_5940925 : Nat := 118140960795 + 5940925 * 2 ^ 59
def prefixEnd_5940925 : Nat := 4983230072969 + 3 ^ 40 * 5940925 * 2
def baseEnd_5940925 : Nat := 3050550057312273837315689

theorem tailTrace_5940925 : CollatzResearch.WordTrace tailWord_5940925 prefixEnd_5940925 3050550057312273837315689 := by
  unfold tailWord_5940925
  simp only [CollatzResearch.WordTrace]
  refine ⟨216683336002050829056352229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144455557334700552704234819 216683336002050829056352229)
  ·
    refine ⟨40628125500384530448066043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 216683336002050829056352229 40628125500384530448066043)
    ·
      refine ⟨60942188250576795672099065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40628125500384530448066043 60942188250576795672099065)
      ·
        refine ⟨45706641187932596754074299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60942188250576795672099065 45706641187932596754074299)
        ·
          refine ⟨68559961781898895131111449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45706641187932596754074299 68559961781898895131111449)
          ·
            refine ⟨51419971336424171348333587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68559961781898895131111449 51419971336424171348333587)
            ·
              refine ⟨77129957004636257022500381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51419971336424171348333587 77129957004636257022500381)
              ·
                refine ⟨28923733876738596383437643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77129957004636257022500381 28923733876738596383437643)
                ·
                  refine ⟨43385600815107894575156465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28923733876738596383437643 43385600815107894575156465)
                  ·
                    refine ⟨32539200611330920931367349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43385600815107894575156465 32539200611330920931367349)
                    ·
                      refine ⟨3050550057312273837315689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32539200611330920931367349 3050550057312273837315689)
                      ·
                        rfl

theorem cell23_5940925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_5940925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5940925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5940925 prefixEnd_5940925 := by exact prefixLift 5940925
  have htrace : WordTrace (prefixWord ++ tailWord_5940925) baseStart_5940925 baseEnd_5940925 := by
    simpa [prefixWord, tailWord_5940925, baseEnd_5940925] using wordTrace_append hprefix tailTrace_5940925
  have hstable : (prefixWord ++ tailWord_5940925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5940925).length < 2 ^ (prefixWord ++ tailWord_5940925).sum := by decide
  have hdescent : baseEnd_5940925 < baseStart_5940925 := by decide
  rcases family_descends (prefixWord ++ tailWord_5940925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5940930 : List Nat := [3, 5, 1, 2, 1, 1, 2, 1, 1, 4, 2]
def baseStart_5940930 : Nat := 118140960795 + 5940930 * 2 ^ 59
def prefixEnd_5940930 : Nat := 4983230072969 + 3 ^ 40 * 5940930 * 2
def baseEnd_5940930 : Nat := 3050552624715546317753167

theorem tailTrace_5940930 : CollatzResearch.WordTrace tailWord_5940930 prefixEnd_5940930 3050552624715546317753167 := by
  unfold tailWord_5940930
  simp only [CollatzResearch.WordTrace]
  refine ⟨54170879591758178727571061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144455678911355143273522829 54170879591758178727571061)
  ·
    refine ⟨5078519961727329255709787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54170879591758178727571061 5078519961727329255709787)
    ·
      refine ⟨7617779942590993883564681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5078519961727329255709787 7617779942590993883564681)
      ·
        refine ⟨5713334956943245412673511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7617779942590993883564681 5713334956943245412673511)
        ·
          refine ⟨8570002435414868119010267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5713334956943245412673511 8570002435414868119010267)
          ·
            refine ⟨12855003653122302178515401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8570002435414868119010267 12855003653122302178515401)
            ·
              refine ⟨9641252739841726633886551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12855003653122302178515401 9641252739841726633886551)
              ·
                refine ⟨14461879109762589950829827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9641252739841726633886551 14461879109762589950829827)
                ·
                  refine ⟨21692818664643884926244741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14461879109762589950829827 21692818664643884926244741)
                  ·
                    refine ⟨4067403499620728423670889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21692818664643884926244741 4067403499620728423670889)
                    ·
                      refine ⟨3050552624715546317753167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4067403499620728423670889 3050552624715546317753167)
                      ·
                        rfl

theorem cell23_5940930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_5940930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5940930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5940930 prefixEnd_5940930 := by exact prefixLift 5940930
  have htrace : WordTrace (prefixWord ++ tailWord_5940930) baseStart_5940930 baseEnd_5940930 := by
    simpa [prefixWord, tailWord_5940930, baseEnd_5940930] using wordTrace_append hprefix tailTrace_5940930
  have hstable : (prefixWord ++ tailWord_5940930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5940930).length < 2 ^ (prefixWord ++ tailWord_5940930).sum := by decide
  have hdescent : baseEnd_5940930 < baseStart_5940930 := by decide
  rcases family_descends (prefixWord ++ tailWord_5940930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5940935 : List Nat := [1, 1, 4, 1, 1, 1, 4, 2, 1, 3, 4]
def baseStart_5940935 : Nat := 118140960795 + 5940935 * 2 ^ 59
def prefixEnd_5940935 : Nat := 4983230072969 + 3 ^ 40 * 5940935 * 2
def baseEnd_5940935 : Nat := 3050555192118818798190643

theorem tailTrace_5940935 : CollatzResearch.WordTrace tailWord_5940935 prefixEnd_5940935 3050555192118818798190643 := by
  unfold tailWord_5940935
  simp only [CollatzResearch.WordTrace]
  refine ⟨216683700732014600764216259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144455800488009733842810839 216683700732014600764216259)
  ·
    refine ⟨325025551098021901146324389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216683700732014600764216259 325025551098021901146324389)
    ·
      refine ⟨60942290830879106464935823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 325025551098021901146324389 60942290830879106464935823)
      ·
        refine ⟨91413436246318659697403735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60942290830879106464935823 91413436246318659697403735)
        ·
          refine ⟨137120154369477989546105603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91413436246318659697403735 137120154369477989546105603)
          ·
            refine ⟨205680231554216984319158405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137120154369477989546105603 205680231554216984319158405)
            ·
              refine ⟨38565043416415684559842201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 205680231554216984319158405 38565043416415684559842201)
              ·
                refine ⟨28923782562311763419881651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38565043416415684559842201 28923782562311763419881651)
                ·
                  refine ⟨43385673843467645129822477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28923782562311763419881651 43385673843467645129822477)
                  ·
                    refine ⟨16269627691300366923683429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43385673843467645129822477 16269627691300366923683429)
                    ·
                      refine ⟨3050555192118818798190643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16269627691300366923683429 3050555192118818798190643)
                      ·
                        rfl

theorem cell23_5940935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 3, 4].length) (baseStart_5940935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5940935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5940935 prefixEnd_5940935 := by exact prefixLift 5940935
  have htrace : WordTrace (prefixWord ++ tailWord_5940935) baseStart_5940935 baseEnd_5940935 := by
    simpa [prefixWord, tailWord_5940935, baseEnd_5940935] using wordTrace_append hprefix tailTrace_5940935
  have hstable : (prefixWord ++ tailWord_5940935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5940935).length < 2 ^ (prefixWord ++ tailWord_5940935).sum := by decide
  have hdescent : baseEnd_5940935 < baseStart_5940935 := by decide
  rcases family_descends (prefixWord ++ tailWord_5940935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5940952 : List Nat := [2, 1, 2, 2, 3, 1, 1, 2, 1, 6, 2]
def baseStart_5940952 : Nat := 118140960795 + 5940952 * 2 ^ 59
def prefixEnd_5940952 : Nat := 4983230072969 + 3 ^ 40 * 5940952 * 2
def baseEnd_5940952 : Nat := 3050563921289945231678065

theorem tailTrace_5940952 : CollatzResearch.WordTrace tailWord_5940952 prefixEnd_5940952 3050563921289945231678065 := by
  unfold tailWord_5940952
  simp only [CollatzResearch.WordTrace]
  refine ⟨108342160386476506333792555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144456213848635341778390073 108342160386476506333792555)
  ·
    refine ⟨162513240579714759500688833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108342160386476506333792555 162513240579714759500688833)
    ·
      refine ⟨121884930434786069625516625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162513240579714759500688833 121884930434786069625516625)
      ·
        refine ⟨91413697826089552219137469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121884930434786069625516625 91413697826089552219137469)
        ·
          refine ⟨34280136684783582082176551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91413697826089552219137469 34280136684783582082176551)
          ·
            refine ⟨51420205027175373123264827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34280136684783582082176551 51420205027175373123264827)
            ·
              refine ⟨77130307540763059684897241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51420205027175373123264827 77130307540763059684897241)
              ·
                refine ⟨57847730655572294763672931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77130307540763059684897241 57847730655572294763672931)
                ·
                  refine ⟨86771595983358442145509397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57847730655572294763672931 86771595983358442145509397)
                  ·
                    refine ⟨4067418561719926975570753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 86771595983358442145509397 4067418561719926975570753)
                    ·
                      refine ⟨3050563921289945231678065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4067418561719926975570753 3050563921289945231678065)
                      ·
                        rfl

theorem cell23_5940952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 1, 6, 2].length) (baseStart_5940952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5940952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5940952 prefixEnd_5940952 := by exact prefixLift 5940952
  have htrace : WordTrace (prefixWord ++ tailWord_5940952) baseStart_5940952 baseEnd_5940952 := by
    simpa [prefixWord, tailWord_5940952, baseEnd_5940952] using wordTrace_append hprefix tailTrace_5940952
  have hstable : (prefixWord ++ tailWord_5940952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5940952).length < 2 ^ (prefixWord ++ tailWord_5940952).sum := by decide
  have hdescent : baseEnd_5940952 < baseStart_5940952 := by decide
  rcases family_descends (prefixWord ++ tailWord_5940952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5940965 : List Nat := [1, 3, 1, 4, 1, 1, 1, 1, 1, 3, 6]
def baseStart_5940965 : Nat := 118140960795 + 5940965 * 2 ^ 59
def prefixEnd_5940965 : Nat := 4983230072969 + 3 ^ 40 * 5940965 * 2
def baseEnd_5940965 : Nat := 3050570596538453680815505

theorem tailTrace_5940965 : CollatzResearch.WordTrace tailWord_5940965 prefixEnd_5940965 3050570596538453680815505 := by
  unfold tailWord_5940965
  simp only [CollatzResearch.WordTrace]
  refine ⟨216684794921905915887808349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144456529947937277258538899 216684794921905915887808349)
  ·
    refine ⟨81256798095714718457928131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216684794921905915887808349 81256798095714718457928131)
    ·
      refine ⟨121885197143572077686892197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81256798095714718457928131 121885197143572077686892197)
      ·
        refine ⟨22853474464419764566292287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121885197143572077686892197 22853474464419764566292287)
        ·
          refine ⟨34280211696629646849438431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22853474464419764566292287 34280211696629646849438431)
          ·
            refine ⟨51420317544944470274157647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34280211696629646849438431 51420317544944470274157647)
            ·
              refine ⟨77130476317416705411236471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51420317544944470274157647 77130476317416705411236471)
              ·
                refine ⟨115695714476125058116854707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77130476317416705411236471 115695714476125058116854707)
                ·
                  refine ⟨173543571714187587175282061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115695714476125058116854707 173543571714187587175282061)
                  ·
                    refine ⟨65078839392820345190730773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 173543571714187587175282061 65078839392820345190730773)
                    ·
                      refine ⟨3050570596538453680815505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65078839392820345190730773 3050570596538453680815505)
                      ·
                        rfl

theorem cell23_5940965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_5940965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5940965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5940965 prefixEnd_5940965 := by exact prefixLift 5940965
  have htrace : WordTrace (prefixWord ++ tailWord_5940965) baseStart_5940965 baseEnd_5940965 := by
    simpa [prefixWord, tailWord_5940965, baseEnd_5940965] using wordTrace_append hprefix tailTrace_5940965
  have hstable : (prefixWord ++ tailWord_5940965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5940965).length < 2 ^ (prefixWord ++ tailWord_5940965).sum := by decide
  have hdescent : baseEnd_5940965 < baseStart_5940965 := by decide
  rcases family_descends (prefixWord ++ tailWord_5940965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5940972 : List Nat := [2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 3]
def baseStart_5940972 : Nat := 118140960795 + 5940972 * 2 ^ 59
def prefixEnd_5940972 : Nat := 4983230072969 + 3 ^ 40 * 5940972 * 2
def baseEnd_5940972 : Nat := 3050574190903035153427973

theorem tailTrace_5940972 : CollatzResearch.WordTrace tailWord_5940972 prefixEnd_5940972 3050574190903035153427973 := by
  unfold tailWord_5940972
  simp only [CollatzResearch.WordTrace]
  refine ⟨108342525116440278041656585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144456700155253704055542113 108342525116440278041656585)
  ·
    refine ⟨81256893837330208531242439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108342525116440278041656585 81256893837330208531242439)
    ·
      refine ⟨121885340755995312796863659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81256893837330208531242439 121885340755995312796863659)
      ·
        refine ⟨182828011133992969195295489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121885340755995312796863659 182828011133992969195295489)
        ·
          refine ⟨137121008350494726896471617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182828011133992969195295489 137121008350494726896471617)
          ·
            refine ⟨102840756262871045172353713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137121008350494726896471617 102840756262871045172353713)
            ·
              refine ⟨77130567197153283879265285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102840756262871045172353713 77130567197153283879265285)
              ·
                refine ⟨14461981349466240727362241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77130567197153283879265285 14461981349466240727362241)
                ·
                  refine ⟨10846486012099680545521681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14461981349466240727362241 10846486012099680545521681)
                  ·
                    refine ⟨8134864509074760409141261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10846486012099680545521681 8134864509074760409141261)
                    ·
                      refine ⟨3050574190903035153427973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8134864509074760409141261 3050574190903035153427973)
                      ·
                        rfl

theorem cell23_5940972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 3].length) (baseStart_5940972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5940972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5940972 prefixEnd_5940972 := by exact prefixLift 5940972
  have htrace : WordTrace (prefixWord ++ tailWord_5940972) baseStart_5940972 baseEnd_5940972 := by
    simpa [prefixWord, tailWord_5940972, baseEnd_5940972] using wordTrace_append hprefix tailTrace_5940972
  have hstable : (prefixWord ++ tailWord_5940972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5940972).length < 2 ^ (prefixWord ++ tailWord_5940972).sum := by decide
  have hdescent : baseEnd_5940972 < baseStart_5940972 := by decide
  rcases family_descends (prefixWord ++ tailWord_5940972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5940975 : List Nat := [1, 1, 2, 1, 5, 1, 3, 1, 8]
def baseStart_5940975 : Nat := 118140960795 + 5940975 * 2 ^ 59
def prefixEnd_5940975 : Nat := 4983230072969 + 3 ^ 40 * 5940975 * 2
def baseEnd_5940975 : Nat := 338952859038333182410051

theorem tailTrace_5940975 : CollatzResearch.WordTrace tailWord_5940975 prefixEnd_5940975 338952859038333182410051 := by
  unfold tailWord_5940975
  simp only [CollatzResearch.WordTrace]
  refine ⟨216685159651869687595672379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144456773101246458397114919 216685159651869687595672379)
  ·
    refine ⟨325027739477804531393508569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216685159651869687595672379 325027739477804531393508569)
    ·
      refine ⟨243770804608353398545131427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 325027739477804531393508569 243770804608353398545131427)
      ·
        refine ⟨365656206912530097817697141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243770804608353398545131427 365656206912530097817697141)
        ·
          refine ⟨34280269398049696670409107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 365656206912530097817697141 34280269398049696670409107)
          ·
            refine ⟨51420404097074545005613661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34280269398049696670409107 51420404097074545005613661)
            ·
              refine ⟨19282651536402954377105123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51420404097074545005613661 19282651536402954377105123)
              ·
                refine ⟨28923977304604431565657685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19282651536402954377105123 28923977304604431565657685)
                ·
                  refine ⟨338952859038333182410051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28923977304604431565657685 338952859038333182410051)
                  ·
                    rfl

theorem cell23_5940975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 8].length) (baseStart_5940975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5940975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5940975 prefixEnd_5940975 := by exact prefixLift 5940975
  have htrace : WordTrace (prefixWord ++ tailWord_5940975) baseStart_5940975 baseEnd_5940975 := by
    simpa [prefixWord, tailWord_5940975, baseEnd_5940975] using wordTrace_append hprefix tailTrace_5940975
  have hstable : (prefixWord ++ tailWord_5940975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5940975).length < 2 ^ (prefixWord ++ tailWord_5940975).sum := by decide
  have hdescent : baseEnd_5940975 < baseStart_5940975 := by decide
  rcases family_descends (prefixWord ++ tailWord_5940975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5940979 : List Nat := [1, 1, 1, 2, 2, 3, 4, 4, 1, 4]
def baseStart_5940979 : Nat := 118140960795 + 5940979 * 2 ^ 59
def prefixEnd_5940979 : Nat := 4983230072969 + 3 ^ 40 * 5940979 * 2
def baseEnd_5940979 : Nat := 1016859261755872208680147

theorem tailTrace_5940979 : CollatzResearch.WordTrace tailWord_5940979 prefixEnd_5940979 1016859261755872208680147 := by
  unfold tailWord_5940979
  simp only [CollatzResearch.WordTrace]
  refine ⟨216685305543855196278817991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144456870362570130852545327 216685305543855196278817991)
  ·
    refine ⟨325027958315782794418226987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216685305543855196278817991 325027958315782794418226987)
    ·
      refine ⟨487541937473674191627340481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325027958315782794418226987 487541937473674191627340481)
      ·
        refine ⟨365656453105255643720505361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 487541937473674191627340481 365656453105255643720505361)
        ·
          refine ⟨274242339828941732790379021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 365656453105255643720505361 274242339828941732790379021)
          ·
            refine ⟨102840877435853149796392133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 274242339828941732790379021 102840877435853149796392133)
            ·
              refine ⟨19282664519222465586823525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102840877435853149796392133 19282664519222465586823525)
              ·
                refine ⟨3615499597354212297529411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19282664519222465586823525 3615499597354212297529411)
                ·
                  refine ⟨5423249396031318446294117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3615499597354212297529411 5423249396031318446294117)
                  ·
                    refine ⟨1016859261755872208680147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5423249396031318446294117 1016859261755872208680147)
                    ·
                      rfl

theorem cell23_5940979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 4, 1, 4].length) (baseStart_5940979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5940979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5940979 prefixEnd_5940979 := by exact prefixLift 5940979
  have htrace : WordTrace (prefixWord ++ tailWord_5940979) baseStart_5940979 baseEnd_5940979 := by
    simpa [prefixWord, tailWord_5940979, baseEnd_5940979] using wordTrace_append hprefix tailTrace_5940979
  have hstable : (prefixWord ++ tailWord_5940979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5940979).length < 2 ^ (prefixWord ++ tailWord_5940979).sum := by decide
  have hdescent : baseEnd_5940979 < baseStart_5940979 := by decide
  rcases family_descends (prefixWord ++ tailWord_5940979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5941029 : List Nat := [1, 3, 1, 2, 3, 2, 1, 1, 4, 3, 2]
def baseStart_5941029 : Nat := 118140960795 + 5941029 * 2 ^ 59
def prefixEnd_5941029 : Nat := 4983230072969 + 3 ^ 40 * 5941029 * 2
def baseEnd_5941029 : Nat := 3050603459300341430415211

theorem tailTrace_5941029 : CollatzResearch.WordTrace tailWord_5941029 prefixEnd_5941029 3050603459300341430415211 := by
  unfold tailWord_5941029
  simp only [CollatzResearch.WordTrace]
  refine ⟨216687129193674054818138141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144458086129116036545425427 216687129193674054818138141)
  ·
    refine ⟨81257673447627770556801803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216687129193674054818138141 81257673447627770556801803)
    ·
      refine ⟨121886510171441655835202705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81257673447627770556801803 121886510171441655835202705)
      ·
        refine ⟨91414882628581241876402029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121886510171441655835202705 91414882628581241876402029)
        ·
          refine ⟨34280580985717965703650761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91414882628581241876402029 34280580985717965703650761)
          ·
            refine ⟨25710435739288474277738071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34280580985717965703650761 25710435739288474277738071)
            ·
              refine ⟨38565653608932711416607107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25710435739288474277738071 38565653608932711416607107)
              ·
                refine ⟨57848480413399067124910661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38565653608932711416607107 57848480413399067124910661)
                ·
                  refine ⟨10846590077512325085920749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57848480413399067124910661 10846590077512325085920749)
                  ·
                    refine ⟨4067471279067121907220281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10846590077512325085920749 4067471279067121907220281)
                    ·
                      refine ⟨3050603459300341430415211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4067471279067121907220281 3050603459300341430415211)
                      ·
                        rfl

theorem cell23_5941029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 4, 3, 2].length) (baseStart_5941029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5941029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5941029 prefixEnd_5941029 := by exact prefixLift 5941029
  have htrace : WordTrace (prefixWord ++ tailWord_5941029) baseStart_5941029 baseEnd_5941029 := by
    simpa [prefixWord, tailWord_5941029, baseEnd_5941029] using wordTrace_append hprefix tailTrace_5941029
  have hstable : (prefixWord ++ tailWord_5941029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5941029).length < 2 ^ (prefixWord ++ tailWord_5941029).sum := by decide
  have hdescent : baseEnd_5941029 < baseStart_5941029 := by decide
  rcases family_descends (prefixWord ++ tailWord_5941029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5941036 : List Nat := [2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 3]
def baseStart_5941036 : Nat := 118140960795 + 5941036 * 2 ^ 59
def prefixEnd_5941036 : Nat := 4983230072969 + 3 ^ 40 * 5941036 * 2
def baseEnd_5941036 : Nat := 3050607053664922903027679

theorem tailTrace_5941036 : CollatzResearch.WordTrace tailWord_5941036 prefixEnd_5941036 3050607053664922903027679 := by
  unfold tailWord_5941036
  simp only [CollatzResearch.WordTrace]
  refine ⟨108343692252324347506821481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144458256336432463342428641 108343692252324347506821481)
  ·
    refine ⟨81257769189243260630116111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108343692252324347506821481 81257769189243260630116111)
    ·
      refine ⟨121886653783864890945174167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81257769189243260630116111 121886653783864890945174167)
      ·
        refine ⟨182829980675797336417761251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121886653783864890945174167 182829980675797336417761251)
        ·
          refine ⟨274244971013696004626641877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182829980675797336417761251 274244971013696004626641877)
          ·
            refine ⟨6427616508133500108436919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 274244971013696004626641877 6427616508133500108436919)
            ·
              refine ⟨9641424762200250162655379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6427616508133500108436919 9641424762200250162655379)
              ·
                refine ⟨14462137143300375243983069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9641424762200250162655379 14462137143300375243983069)
                ·
                  refine ⟨5423301428737640716493651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14462137143300375243983069 5423301428737640716493651)
                  ·
                    refine ⟨8134952143106461074740477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5423301428737640716493651 8134952143106461074740477)
                    ·
                      refine ⟨3050607053664922903027679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8134952143106461074740477 3050607053664922903027679)
                      ·
                        rfl

theorem cell23_5941036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 3].length) (baseStart_5941036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5941036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5941036 prefixEnd_5941036 := by exact prefixLift 5941036
  have htrace : WordTrace (prefixWord ++ tailWord_5941036) baseStart_5941036 baseEnd_5941036 := by
    simpa [prefixWord, tailWord_5941036, baseEnd_5941036] using wordTrace_append hprefix tailTrace_5941036
  have hstable : (prefixWord ++ tailWord_5941036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5941036).length < 2 ^ (prefixWord ++ tailWord_5941036).sum := by decide
  have hdescent : baseEnd_5941036 < baseStart_5941036 := by decide
  rcases family_descends (prefixWord ++ tailWord_5941036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5941059 : List Nat := [1, 1, 1, 3, 1, 5, 3, 2, 1, 1, 4]
def baseStart_5941059 : Nat := 118140960795 + 5941059 * 2 ^ 59
def prefixEnd_5941059 : Nat := 4983230072969 + 3 ^ 40 * 5941059 * 2
def baseEnd_5941059 : Nat := 3050618863719976313040073

theorem tailTrace_5941059 : CollatzResearch.WordTrace tailWord_5941059 prefixEnd_5941059 3050618863719976313040073 := by
  unfold tailWord_5941059
  simp only [CollatzResearch.WordTrace]
  refine ⟨216688223383565369941730231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144458815589043579961153487 216688223383565369941730231)
  ·
    refine ⟨325032335075348054912595347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216688223383565369941730231 325032335075348054912595347)
    ·
      refine ⟨487548502613022082368893021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325032335075348054912595347 487548502613022082368893021)
      ·
        refine ⟨182830688479883280888334883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 487548502613022082368893021 182830688479883280888334883)
        ·
          refine ⟨274246032719824921332502325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182830688479883280888334883 274246032719824921332502325)
          ·
            refine ⟨25710565567483586374922093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 274246032719824921332502325 25710565567483586374922093)
            ·
              refine ⟨9641462087806344890595785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25710565567483586374922093 9641462087806344890595785)
              ·
                refine ⟨7231096565854758667946839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9641462087806344890595785 7231096565854758667946839)
                ·
                  refine ⟨10846644848782138001920259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7231096565854758667946839 10846644848782138001920259)
                  ·
                    refine ⟨16269967273173207002880389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10846644848782138001920259 16269967273173207002880389)
                    ·
                      refine ⟨3050618863719976313040073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16269967273173207002880389 3050618863719976313040073)
                      ·
                        rfl

theorem cell23_5941059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 2, 1, 1, 4].length) (baseStart_5941059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5941059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5941059 prefixEnd_5941059 := by exact prefixLift 5941059
  have htrace : WordTrace (prefixWord ++ tailWord_5941059) baseStart_5941059 baseEnd_5941059 := by
    simpa [prefixWord, tailWord_5941059, baseEnd_5941059] using wordTrace_append hprefix tailTrace_5941059
  have hstable : (prefixWord ++ tailWord_5941059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5941059).length < 2 ^ (prefixWord ++ tailWord_5941059).sum := by decide
  have hdescent : baseEnd_5941059 < baseStart_5941059 := by decide
  rcases family_descends (prefixWord ++ tailWord_5941059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5941065 : List Nat := [1, 2, 1, 1, 2, 4, 1, 11]
def baseStart_5941065 : Nat := 118140960795 + 5941065 * 2 ^ 59
def prefixEnd_5941065 : Nat := 4983230072969 + 3 ^ 40 * 5941065 * 2
def baseEnd_5941065 : Nat := 112985997948292714428335

theorem tailTrace_5941065 : CollatzResearch.WordTrace tailWord_5941065 prefixEnd_5941065 112985997948292714428335 := by
  unfold tailWord_5941065
  simp only [CollatzResearch.WordTrace]
  refine ⟨216688442221543632966448649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144458961481029088644299099 216688442221543632966448649)
  ·
    refine ⟨162516331666157724724836487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216688442221543632966448649 162516331666157724724836487)
    ·
      refine ⟨243774497499236587087254731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162516331666157724724836487 243774497499236587087254731)
      ·
        refine ⟨365661746248854880630882097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243774497499236587087254731 365661746248854880630882097)
        ·
          refine ⟨274246309686641160473161573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 365661746248854880630882097 274246309686641160473161573)
          ·
            refine ⟨51421183066245217588717795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 274246309686641160473161573 51421183066245217588717795)
            ·
              refine ⟨77131774599367826383076693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51421183066245217588717795 77131774599367826383076693)
              ·
                refine ⟨112985997948292714428335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 77131774599367826383076693 112985997948292714428335)
                ·
                  rfl

theorem cell23_5941065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 11].length) (baseStart_5941065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5941065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5941065 prefixEnd_5941065 := by exact prefixLift 5941065
  have htrace : WordTrace (prefixWord ++ tailWord_5941065) baseStart_5941065 baseEnd_5941065 := by
    simpa [prefixWord, tailWord_5941065, baseEnd_5941065] using wordTrace_append hprefix tailTrace_5941065
  have hstable : (prefixWord ++ tailWord_5941065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5941065).length < 2 ^ (prefixWord ++ tailWord_5941065).sum := by decide
  have hdescent : baseEnd_5941065 < baseStart_5941065 := by decide
  rcases family_descends (prefixWord ++ tailWord_5941065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5941069 : List Nat := [1, 6, 1, 2, 1, 1, 1, 1, 3, 6]
def baseStart_5941069 : Nat := 118140960795 + 5941069 * 2 ^ 59
def prefixEnd_5941069 : Nat := 4983230072969 + 3 ^ 40 * 5941069 * 2
def baseEnd_5941069 : Nat := 1016874666175507091305009

theorem tailTrace_5941069 : CollatzResearch.WordTrace tailWord_5941069 prefixEnd_5941069 1016874666175507091305009 := by
  unfold tailWord_5941069
  simp only [CollatzResearch.WordTrace]
  refine ⟨216688588113529141649594261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144459058742352761099729507 216688588113529141649594261)
  ·
    refine ⟨10157277567821678514824731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 216688588113529141649594261 10157277567821678514824731)
    ·
      refine ⟨15235916351732517772237097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10157277567821678514824731 15235916351732517772237097)
      ·
        refine ⟨11426937263799388329177823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15235916351732517772237097 11426937263799388329177823)
        ·
          refine ⟨17140405895699082493766735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11426937263799388329177823 17140405895699082493766735)
          ·
            refine ⟨25710608843548623740650103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17140405895699082493766735 25710608843548623740650103)
            ·
              refine ⟨38565913265322935610975155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25710608843548623740650103 38565913265322935610975155)
              ·
                refine ⟨57848869897984403416462733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38565913265322935610975155 57848869897984403416462733)
                ·
                  refine ⟨21693326211744151281173525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57848869897984403416462733 21693326211744151281173525)
                  ·
                    refine ⟨1016874666175507091305009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21693326211744151281173525 1016874666175507091305009)
                    ·
                      rfl

theorem cell23_5941069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_5941069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5941069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5941069 prefixEnd_5941069 := by exact prefixLift 5941069
  have htrace : WordTrace (prefixWord ++ tailWord_5941069) baseStart_5941069 baseEnd_5941069 := by
    simpa [prefixWord, tailWord_5941069, baseEnd_5941069] using wordTrace_append hprefix tailTrace_5941069
  have hstable : (prefixWord ++ tailWord_5941069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5941069).length < 2 ^ (prefixWord ++ tailWord_5941069).sum := by decide
  have hdescent : baseEnd_5941069 < baseStart_5941069 := by decide
  rcases family_descends (prefixWord ++ tailWord_5941069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5941110 : List Nat := [5, 1, 1, 3, 2, 1, 1, 2, 3, 2, 2]
def baseStart_5941110 : Nat := 118140960795 + 5941110 * 2 ^ 59
def prefixEnd_5941110 : Nat := 4983230072969 + 3 ^ 40 * 5941110 * 2
def baseEnd_5941110 : Nat := 3050645051233355613502339

theorem tailTrace_5941110 : CollatzResearch.WordTrace tailWord_5941110 prefixEnd_5941110 3050645051233355613502339 := by
  unfold tailWord_5941110
  simp only [CollatzResearch.WordTrace]
  refine ⟨13543130219148787853239799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 144460055670920403767891189 13543130219148787853239799)
  ·
    refine ⟨20314695328723181779859699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13543130219148787853239799 20314695328723181779859699)
    ·
      refine ⟨30472042993084772669789549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20314695328723181779859699 30472042993084772669789549)
      ·
        refine ⟨11427016122406789751171081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30472042993084772669789549 11427016122406789751171081)
        ·
          refine ⟨8570262091805092313378311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11427016122406789751171081 8570262091805092313378311)
          ·
            refine ⟨12855393137707638470067467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8570262091805092313378311 12855393137707638470067467)
            ·
              refine ⟨19283089706561457705101201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12855393137707638470067467 19283089706561457705101201)
              ·
                refine ⟨14462317279921093278825901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19283089706561457705101201 14462317279921093278825901)
                ·
                  refine ⟨5423368979970409979559713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14462317279921093278825901 5423368979970409979559713)
                  ·
                    refine ⟨4067526734977807484669785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5423368979970409979559713 4067526734977807484669785)
                    ·
                      refine ⟨3050645051233355613502339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4067526734977807484669785 3050645051233355613502339)
                      ·
                        rfl

theorem cell23_5941110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_5941110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5941110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5941110 prefixEnd_5941110 := by exact prefixLift 5941110
  have htrace : WordTrace (prefixWord ++ tailWord_5941110) baseStart_5941110 baseEnd_5941110 := by
    simpa [prefixWord, tailWord_5941110, baseEnd_5941110] using wordTrace_append hprefix tailTrace_5941110
  have hstable : (prefixWord ++ tailWord_5941110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5941110).length < 2 ^ (prefixWord ++ tailWord_5941110).sum := by decide
  have hdescent : baseEnd_5941110 < baseStart_5941110 := by decide
  rcases family_descends (prefixWord ++ tailWord_5941110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5941130 : List Nat := [3, 1, 2, 4, 2, 2, 2, 1, 1, 2, 3]
def baseStart_5941130 : Nat := 118140960795 + 5941130 * 2 ^ 59
def prefixEnd_5941130 : Nat := 4983230072969 + 3 ^ 40 * 5941130 * 2
def baseEnd_5941130 : Nat := 3050655320846445535252247

theorem tailTrace_5941130 : CollatzResearch.WordTrace tailWord_5941130 prefixEnd_5941130 3050655320846445535252247 := by
  unfold tailWord_5941130
  simp only [CollatzResearch.WordTrace]
  refine ⟨54172703241577037266891211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144460541977538766045043229 54172703241577037266891211)
  ·
    refine ⟨81259054862365555900336817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54172703241577037266891211 81259054862365555900336817)
    ·
      refine ⟨60944291146774166925252613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81259054862365555900336817 60944291146774166925252613)
      ·
        refine ⟨11427054590020156298484865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60944291146774166925252613 11427054590020156298484865)
        ·
          refine ⟨8570290942515117223863649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11427054590020156298484865 8570290942515117223863649)
          ·
            refine ⟨6427718206886337917897737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8570290942515117223863649 6427718206886337917897737)
            ·
              refine ⟨4820788655164753438423303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6427718206886337917897737 4820788655164753438423303)
              ·
                refine ⟨7231182982747130157634955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4820788655164753438423303 7231182982747130157634955)
                ·
                  refine ⟨10846774474120695236452433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7231182982747130157634955 10846774474120695236452433)
                  ·
                    refine ⟨8135080855590521427339325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10846774474120695236452433 8135080855590521427339325)
                    ·
                      refine ⟨3050655320846445535252247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8135080855590521427339325 3050655320846445535252247)
                      ·
                        rfl

theorem cell23_5941130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_5941130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5941130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5941130 prefixEnd_5941130 := by exact prefixLift 5941130
  have htrace : WordTrace (prefixWord ++ tailWord_5941130) baseStart_5941130 baseEnd_5941130 := by
    simpa [prefixWord, tailWord_5941130, baseEnd_5941130] using wordTrace_append hprefix tailTrace_5941130
  have hstable : (prefixWord ++ tailWord_5941130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5941130).length < 2 ^ (prefixWord ++ tailWord_5941130).sum := by decide
  have hdescent : baseEnd_5941130 < baseStart_5941130 := by decide
  rcases family_descends (prefixWord ++ tailWord_5941130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5941143 : List Nat := [1, 1, 3, 3, 1, 5, 1, 2, 2, 1, 3]
def baseStart_5941143 : Nat := 118140960795 + 5941143 * 2 ^ 59
def prefixEnd_5941143 : Nat := 4983230072969 + 3 ^ 40 * 5941143 * 2
def baseEnd_5941143 : Nat := 3050661996094953984389687

theorem tailTrace_5941143 : CollatzResearch.WordTrace tailWord_5941143 prefixEnd_5941143 3050661996094953984389687 := by
  unfold tailWord_5941143
  simp only [CollatzResearch.WordTrace]
  refine ⟨216691287115261052287788083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144460858076840701525192055 216691287115261052287788083)
  ·
    refine ⟨325036930672891578431682125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216691287115261052287788083 325036930672891578431682125)
    ·
      refine ⟨121888849002334341911880797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 325036930672891578431682125 121888849002334341911880797)
      ·
        refine ⟨45708318375875378216955299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121888849002334341911880797 45708318375875378216955299)
        ·
          refine ⟨68562477563813067325432949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45708318375875378216955299 68562477563813067325432949)
          ·
            refine ⟨6427732271607475061759339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68562477563813067325432949 6427732271607475061759339)
            ·
              refine ⟨9641598407411212592639009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6427732271607475061759339 9641598407411212592639009)
              ·
                refine ⟨7231198805558409444479257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9641598407411212592639009 7231198805558409444479257)
                ·
                  refine ⟨5423399104168807083359443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7231198805558409444479257 5423399104168807083359443)
                  ·
                    refine ⟨8135098656253210625039165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5423399104168807083359443 8135098656253210625039165)
                    ·
                      refine ⟨3050661996094953984389687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8135098656253210625039165 3050661996094953984389687)
                      ·
                        rfl

theorem cell23_5941143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 2, 2, 1, 3].length) (baseStart_5941143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5941143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5941143 prefixEnd_5941143 := by exact prefixLift 5941143
  have htrace : WordTrace (prefixWord ++ tailWord_5941143) baseStart_5941143 baseEnd_5941143 := by
    simpa [prefixWord, tailWord_5941143, baseEnd_5941143] using wordTrace_append hprefix tailTrace_5941143
  have hstable : (prefixWord ++ tailWord_5941143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5941143).length < 2 ^ (prefixWord ++ tailWord_5941143).sum := by decide
  have hdescent : baseEnd_5941143 < baseStart_5941143 := by decide
  rcases family_descends (prefixWord ++ tailWord_5941143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5941152 : List Nat := [2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 5]
def baseStart_5941152 : Nat := 118140960795 + 5941152 * 2 ^ 59
def prefixEnd_5941152 : Nat := 4983230072969 + 3 ^ 40 * 5941152 * 2
def baseEnd_5941152 : Nat := 3050666617420844449177145

theorem tailTrace_5941152 : CollatzResearch.WordTrace tailWord_5941152 prefixEnd_5941152 3050666617420844449177145 := by
  unfold tailWord_5941152
  simp only [CollatzResearch.WordTrace]
  refine ⟨108345807686114223412432855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144461076914818964549910473 108345807686114223412432855)
  ·
    refine ⟨162518711529171335118649283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108345807686114223412432855 162518711529171335118649283)
    ·
      refine ⟨243778067293757002677973925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162518711529171335118649283 243778067293757002677973925)
      ·
        refine ⟨45708387617579438002120111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 243778067293757002677973925 45708387617579438002120111)
        ·
          refine ⟨68562581426369157003180167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45708387617579438002120111 68562581426369157003180167)
          ·
            refine ⟨102843872139553735504770251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68562581426369157003180167 102843872139553735504770251)
            ·
              refine ⟨154265808209330603257155377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102843872139553735504770251 154265808209330603257155377)
              ·
                refine ⟨115699356156997952442866533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154265808209330603257155377 115699356156997952442866533)
                ·
                  refine ⟨21693629279437116083037475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 115699356156997952442866533 21693629279437116083037475)
                  ·
                    refine ⟨32540443919155674124556213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21693629279437116083037475 32540443919155674124556213)
                    ·
                      refine ⟨3050666617420844449177145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32540443919155674124556213 3050666617420844449177145)
                      ·
                        rfl

theorem cell23_5941152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_5941152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5941152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5941152 prefixEnd_5941152 := by exact prefixLift 5941152
  have htrace : WordTrace (prefixWord ++ tailWord_5941152) baseStart_5941152 baseEnd_5941152 := by
    simpa [prefixWord, tailWord_5941152, baseEnd_5941152] using wordTrace_append hprefix tailTrace_5941152
  have hstable : (prefixWord ++ tailWord_5941152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5941152).length < 2 ^ (prefixWord ++ tailWord_5941152).sum := by decide
  have hdescent : baseEnd_5941152 < baseStart_5941152 := by decide
  rcases family_descends (prefixWord ++ tailWord_5941152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5941159 : List Nat := [1, 1, 6, 1, 2, 1, 2, 1, 2, 6]
def baseStart_5941159 : Nat := 118140960795 + 5941159 * 2 ^ 59
def prefixEnd_5941159 : Nat := 4983230072969 + 3 ^ 40 * 5941159 * 2
def baseEnd_5941159 : Nat := 1016890070595141973929871

theorem tailTrace_5941159 : CollatzResearch.WordTrace tailWord_5941159 prefixEnd_5941159 1016890070595141973929871 := by
  unfold tailWord_5941159
  simp only [CollatzResearch.WordTrace]
  refine ⟨216691870683203087020370531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144461247122135391346913687 216691870683203087020370531)
  ·
    refine ⟨325037806024804630530555797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216691870683203087020370531 325037806024804630530555797)
    ·
      refine ⟨15236147157412717056119803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 325037806024804630530555797 15236147157412717056119803)
      ·
        refine ⟨22854220736119075584179705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15236147157412717056119803 22854220736119075584179705)
        ·
          refine ⟨17140665552089306688134779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22854220736119075584179705 17140665552089306688134779)
          ·
            refine ⟨25710998328133960032202169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17140665552089306688134779 25710998328133960032202169)
            ·
              refine ⟨19283248746100470024151627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25710998328133960032202169 19283248746100470024151627)
              ·
                refine ⟨28924873119150705036227441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19283248746100470024151627 28924873119150705036227441)
                ·
                  refine ⟨21693654839363028777170581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28924873119150705036227441 21693654839363028777170581)
                  ·
                    refine ⟨1016890070595141973929871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21693654839363028777170581 1016890070595141973929871)
                    ·
                      rfl

theorem cell23_5941159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_5941159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5941159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5941159 prefixEnd_5941159 := by exact prefixLift 5941159
  have htrace : WordTrace (prefixWord ++ tailWord_5941159) baseStart_5941159 baseEnd_5941159 := by
    simpa [prefixWord, tailWord_5941159, baseEnd_5941159] using wordTrace_append hprefix tailTrace_5941159
  have hstable : (prefixWord ++ tailWord_5941159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5941159).length < 2 ^ (prefixWord ++ tailWord_5941159).sum := by decide
  have hdescent : baseEnd_5941159 < baseStart_5941159 := by decide
  rcases family_descends (prefixWord ++ tailWord_5941159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5941160 : List Nat := [2, 1, 6, 2, 1, 2, 1, 1, 1, 3, 3]
def baseStart_5941160 : Nat := 118140960795 + 5941160 * 2 ^ 59
def prefixEnd_5941160 : Nat := 4983230072969 + 3 ^ 40 * 5941160 * 2
def baseEnd_5941160 : Nat := 3050670725266080417877109

theorem tailTrace_5941160 : CollatzResearch.WordTrace tailWord_5941160 prefixEnd_5941160 3050670725266080417877109 := by
  unfold tailWord_5941160
  simp only [CollatzResearch.WordTrace]
  refine ⟨108345953578099732095578467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144461271437466309460771289 108345953578099732095578467)
  ·
    refine ⟨162518930367149598143367701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108345953578099732095578467 162518930367149598143367701)
    ·
      refine ⟨7618074860960137412970361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 162518930367149598143367701 7618074860960137412970361)
      ·
        refine ⟨5713556145720103059727771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7618074860960137412970361 5713556145720103059727771)
        ·
          refine ⟨8570334218580154589591657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5713556145720103059727771 8570334218580154589591657)
          ·
            refine ⟨6427750663935115942193743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8570334218580154589591657 6427750663935115942193743)
            ·
              refine ⟨9641625995902673913290615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6427750663935115942193743 9641625995902673913290615)
              ·
                refine ⟨14462438993854010869935923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9641625995902673913290615 14462438993854010869935923)
                ·
                  refine ⟨21693658490781016304903885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14462438993854010869935923 21693658490781016304903885)
                  ·
                    refine ⟨8135121934042881114338957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21693658490781016304903885 8135121934042881114338957)
                    ·
                      refine ⟨3050670725266080417877109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8135121934042881114338957 3050670725266080417877109)
                      ·
                        rfl

theorem cell23_5941160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_5941160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5941160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5941160 prefixEnd_5941160 := by exact prefixLift 5941160
  have htrace : WordTrace (prefixWord ++ tailWord_5941160) baseStart_5941160 baseEnd_5941160 := by
    simpa [prefixWord, tailWord_5941160, baseEnd_5941160] using wordTrace_append hprefix tailTrace_5941160
  have hstable : (prefixWord ++ tailWord_5941160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5941160).length < 2 ^ (prefixWord ++ tailWord_5941160).sum := by decide
  have hdescent : baseEnd_5941160 < baseStart_5941160 := by decide
  rcases family_descends (prefixWord ++ tailWord_5941160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5941189 : List Nat := [1, 3, 1, 1, 1, 1, 1, 9, 5]
def baseStart_5941189 : Nat := 118140960795 + 5941189 * 2 ^ 59
def prefixEnd_5941189 : Nat := 4983230072969 + 3 ^ 40 * 5941189 * 2
def baseEnd_5941189 : Nat := 338965068467228978268275

theorem tailTrace_5941189 : CollatzResearch.WordTrace tailWord_5941189 prefixEnd_5941189 338965068467228978268275 := by
  unfold tailWord_5941189
  simp only [CollatzResearch.WordTrace]
  refine ⟨216692964873094402143962621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144461976582062934762641747 216692964873094402143962621)
  ·
    refine ⟨81259861827410400803985983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216692964873094402143962621 81259861827410400803985983)
    ·
      refine ⟨121889792741115601205978975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81259861827410400803985983 121889792741115601205978975)
      ·
        refine ⟨182834689111673401808968463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121889792741115601205978975 182834689111673401808968463)
        ·
          refine ⟨274252033667510102713452695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182834689111673401808968463 274252033667510102713452695)
          ·
            refine ⟨411378050501265154070179043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274252033667510102713452695 411378050501265154070179043)
            ·
              refine ⟨617067075751897731105268565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 411378050501265154070179043 617067075751897731105268565)
              ·
                refine ⟨3615627396983775768194933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 617067075751897731105268565 3615627396983775768194933)
                ·
                  refine ⟨338965068467228978268275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3615627396983775768194933 338965068467228978268275)
                  ·
                    rfl

theorem cell23_5941189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 9, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 9, 5].length) (baseStart_5941189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5941189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5941189 prefixEnd_5941189 := by exact prefixLift 5941189
  have htrace : WordTrace (prefixWord ++ tailWord_5941189) baseStart_5941189 baseEnd_5941189 := by
    simpa [prefixWord, tailWord_5941189, baseEnd_5941189] using wordTrace_append hprefix tailTrace_5941189
  have hstable : (prefixWord ++ tailWord_5941189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5941189).length < 2 ^ (prefixWord ++ tailWord_5941189).sum := by decide
  have hdescent : baseEnd_5941189 < baseStart_5941189 := by decide
  rcases family_descends (prefixWord ++ tailWord_5941189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5941232 : List Nat := [2, 1, 1, 1, 3, 2, 2, 1, 2, 8]
def baseStart_5941232 : Nat := 118140960795 + 5941232 * 2 ^ 59
def prefixEnd_5941232 : Nat := 4983230072969 + 3 ^ 40 * 5941232 * 2
def baseEnd_5941232 : Nat := 1016902565291068045392259

theorem tailTrace_5941232 : CollatzResearch.WordTrace tailWord_5941232 prefixEnd_5941232 1016902565291068045392259 := by
  unfold tailWord_5941232
  simp only [CollatzResearch.WordTrace]
  refine ⟨108347266605969310243888975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144463022141292413658518633 108347266605969310243888975)
  ·
    refine ⟨162520899908953965365833463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108347266605969310243888975 162520899908953965365833463)
    ·
      refine ⟨243781349863430948048750195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162520899908953965365833463 243781349863430948048750195)
      ·
        refine ⟨365672024795146422073125293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243781349863430948048750195 365672024795146422073125293)
        ·
          refine ⟨137127009298179908277421985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 365672024795146422073125293 137127009298179908277421985)
          ·
            refine ⟨102845256973634931208066489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137127009298179908277421985 102845256973634931208066489)
            ·
              refine ⟨77133942730226198406049867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102845256973634931208066489 77133942730226198406049867)
              ·
                refine ⟨115700914095339297609074801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77133942730226198406049867 115700914095339297609074801)
                ·
                  refine ⟨86775685571504473206806101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115700914095339297609074801 86775685571504473206806101)
                  ·
                    refine ⟨1016902565291068045392259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 86775685571504473206806101 1016902565291068045392259)
                    ·
                      rfl

theorem cell23_5941232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 2, 8].length) (baseStart_5941232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5941232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5941232 prefixEnd_5941232 := by exact prefixLift 5941232
  have htrace : WordTrace (prefixWord ++ tailWord_5941232) baseStart_5941232 baseEnd_5941232 := by
    simpa [prefixWord, tailWord_5941232, baseEnd_5941232] using wordTrace_append hprefix tailTrace_5941232
  have hstable : (prefixWord ++ tailWord_5941232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5941232).length < 2 ^ (prefixWord ++ tailWord_5941232).sum := by decide
  have hdescent : baseEnd_5941232 < baseStart_5941232 := by decide
  rcases family_descends (prefixWord ++ tailWord_5941232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5941242 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 1, 2, 9]
def baseStart_5941242 : Nat := 118140960795 + 5941242 * 2 ^ 59
def prefixEnd_5941242 : Nat := 4983230072969 + 3 ^ 40 * 5941242 * 2
def baseEnd_5941242 : Nat := 3050712830679749097051731

theorem tailTrace_5941242 : CollatzResearch.WordTrace tailWord_5941242 prefixEnd_5941242 3050712830679749097051731 := by
  unfold tailWord_5941242
  simp only [CollatzResearch.WordTrace]
  refine ⟨54173724485475598048910495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144463265294601594797094653 54173724485475598048910495)
  ·
    refine ⟨81260586728213397073365743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54173724485475598048910495 81260586728213397073365743)
    ·
      refine ⟨121890880092320095610048615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81260586728213397073365743 121890880092320095610048615)
      ·
        refine ⟨182836320138480143415072923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121890880092320095610048615 182836320138480143415072923)
        ·
          refine ⟨274254480207720215122609385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182836320138480143415072923 274254480207720215122609385)
          ·
            refine ⟨205690860155790161341957039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 274254480207720215122609385 205690860155790161341957039)
            ·
              refine ⟨308536290233685242012935559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205690860155790161341957039 308536290233685242012935559)
              ·
                refine ⟨462804435350527863019403339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 308536290233685242012935559 462804435350527863019403339)
                ·
                  refine ⟨694206653025791794529105009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 462804435350527863019403339 694206653025791794529105009)
                  ·
                    refine ⟨520654989769343845896828757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 694206653025791794529105009 520654989769343845896828757)
                    ·
                      refine ⟨3050712830679749097051731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 520654989769343845896828757 3050712830679749097051731)
                      ·
                        rfl

theorem cell23_5941242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 1, 2, 9].length) (baseStart_5941242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5941242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5941242 prefixEnd_5941242 := by exact prefixLift 5941242
  have htrace : WordTrace (prefixWord ++ tailWord_5941242) baseStart_5941242 baseEnd_5941242 := by
    simpa [prefixWord, tailWord_5941242, baseEnd_5941242] using wordTrace_append hprefix tailTrace_5941242
  have hstable : (prefixWord ++ tailWord_5941242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5941242).length < 2 ^ (prefixWord ++ tailWord_5941242).sum := by decide
  have hdescent : baseEnd_5941242 < baseStart_5941242 := by decide
  rcases family_descends (prefixWord ++ tailWord_5941242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5941246 : List Nat := [4, 2, 2, 2, 1, 1, 1, 2, 1, 2, 5]
def baseStart_5941246 : Nat := 118140960795 + 5941246 * 2 ^ 59
def prefixEnd_5941246 : Nat := 4983230072969 + 3 ^ 40 * 5941246 * 2
def baseEnd_5941246 : Nat := 3050714884602367081401713

theorem tailTrace_5941246 : CollatzResearch.WordTrace tailWord_5941246 prefixEnd_5941246 3050714884602367081401713 := by
  unfold tailWord_5941246
  simp only [CollatzResearch.WordTrace]
  refine ⟨27086880479235987609848449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144463362555925267252525061 27086880479235987609848449)
  ·
    refine ⟨20315160359426990707386337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27086880479235987609848449 20315160359426990707386337)
    ·
      refine ⟨15236370269570243030539753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20315160359426990707386337 15236370269570243030539753)
      ·
        refine ⟨11427277702177682272904815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15236370269570243030539753 11427277702177682272904815)
        ·
          refine ⟨17140916553266523409357223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11427277702177682272904815 17140916553266523409357223)
          ·
            refine ⟨25711374829899785114035835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17140916553266523409357223 25711374829899785114035835)
            ·
              refine ⟨38567062244849677671053753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25711374829899785114035835 38567062244849677671053753)
              ·
                refine ⟨28925296683637258253290315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38567062244849677671053753 28925296683637258253290315)
                ·
                  refine ⟨43387945025455887379935473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28925296683637258253290315 43387945025455887379935473)
                  ·
                    refine ⟨32540958769091915534951605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43387945025455887379935473 32540958769091915534951605)
                    ·
                      refine ⟨3050714884602367081401713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32540958769091915534951605 3050714884602367081401713)
                      ·
                        rfl

theorem cell23_5941246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_5941246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5941246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5941246 prefixEnd_5941246 := by exact prefixLift 5941246
  have htrace : WordTrace (prefixWord ++ tailWord_5941246) baseStart_5941246 baseEnd_5941246 := by
    simpa [prefixWord, tailWord_5941246, baseEnd_5941246] using wordTrace_append hprefix tailTrace_5941246
  have hstable : (prefixWord ++ tailWord_5941246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5941246).length < 2 ^ (prefixWord ++ tailWord_5941246).sum := by decide
  have hdescent : baseEnd_5941246 < baseStart_5941246 := by decide
  rcases family_descends (prefixWord ++ tailWord_5941246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5941256 : List Nat := [2, 1, 3, 2, 1, 2, 2, 2, 2, 4, 2]
def baseStart_5941256 : Nat := 118140960795 + 5941256 * 2 ^ 59
def prefixEnd_5941256 : Nat := 4983230072969 + 3 ^ 40 * 5941256 * 2
def baseEnd_5941256 : Nat := 3050720019408912042276667

theorem tailTrace_5941256 : CollatzResearch.WordTrace tailWord_5941256 prefixEnd_5941256 3050720019408912042276667 := by
  unfold tailWord_5941256
  simp only [CollatzResearch.WordTrace]
  refine ⟨108347704281925836293325811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144463605709234448391101081 108347704281925836293325811)
  ·
    refine ⟨162521556422888754439988717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108347704281925836293325811 162521556422888754439988717)
    ·
      refine ⟨60945583658583282914995769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162521556422888754439988717 60945583658583282914995769)
      ·
        refine ⟨45709187743937462186246827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60945583658583282914995769 45709187743937462186246827)
        ·
          refine ⟨68563781615906193279370241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45709187743937462186246827 68563781615906193279370241)
          ·
            refine ⟨51422836211929644959527681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68563781615906193279370241 51422836211929644959527681)
            ·
              refine ⟨38567127158947233719645761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51422836211929644959527681 38567127158947233719645761)
              ·
                refine ⟨28925345369210425289734321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38567127158947233719645761 28925345369210425289734321)
                ·
                  refine ⟨21694009026907818967300741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28925345369210425289734321 21694009026907818967300741)
                  ·
                    refine ⟨4067626692545216056368889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21694009026907818967300741 4067626692545216056368889)
                    ·
                      refine ⟨3050720019408912042276667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4067626692545216056368889 3050720019408912042276667)
                      ·
                        rfl

theorem cell23_5941256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 2, 4, 2].length) (baseStart_5941256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5941256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5941256 prefixEnd_5941256 := by exact prefixLift 5941256
  have htrace : WordTrace (prefixWord ++ tailWord_5941256) baseStart_5941256 baseEnd_5941256 := by
    simpa [prefixWord, tailWord_5941256, baseEnd_5941256] using wordTrace_append hprefix tailTrace_5941256
  have hstable : (prefixWord ++ tailWord_5941256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5941256).length < 2 ^ (prefixWord ++ tailWord_5941256).sum := by decide
  have hdescent : baseEnd_5941256 < baseStart_5941256 := by decide
  rcases family_descends (prefixWord ++ tailWord_5941256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5941279 : List Nat := [1, 1, 2, 4, 1, 2, 1, 5, 6]
def baseStart_5941279 : Nat := 118140960795 + 5941279 * 2 ^ 59
def prefixEnd_5941279 : Nat := 4983230072969 + 3 ^ 40 * 5941279 * 2
def baseEnd_5941279 : Nat := 338970203273773939143229

theorem tailTrace_5941279 : CollatzResearch.WordTrace tailWord_5941279 prefixEnd_5941279 338970203273773939143229 := by
  unfold tailWord_5941279
  simp only [CollatzResearch.WordTrace]
  refine ⟨216696247442768347514738891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144464164961845565009825927 216696247442768347514738891)
  ·
    refine ⟨325044371164152521272108337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216696247442768347514738891 325044371164152521272108337)
    ·
      refine ⟨243783278373114390954081253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 325044371164152521272108337 243783278373114390954081253)
      ·
        refine ⟨45709364694958948303890235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 243783278373114390954081253 45709364694958948303890235)
        ·
          refine ⟨68564047042438422455835353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45709364694958948303890235 68564047042438422455835353)
          ·
            refine ⟨51423035281828816841876515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68564047042438422455835353 51423035281828816841876515)
            ·
              refine ⟨77134552922743225262814773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51423035281828816841876515 77134552922743225262814773)
              ·
                refine ⟨7231364336507177368388885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77134552922743225262814773 7231364336507177368388885)
                ·
                  refine ⟨338970203273773939143229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7231364336507177368388885 338970203273773939143229)
                  ·
                    rfl

theorem cell23_5941279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 5, 6].length) (baseStart_5941279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5941279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5941279 prefixEnd_5941279 := by exact prefixLift 5941279
  have htrace : WordTrace (prefixWord ++ tailWord_5941279) baseStart_5941279 baseEnd_5941279 := by
    simpa [prefixWord, tailWord_5941279, baseEnd_5941279] using wordTrace_append hprefix tailTrace_5941279
  have hstable : (prefixWord ++ tailWord_5941279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5941279).length < 2 ^ (prefixWord ++ tailWord_5941279).sum := by decide
  have hdescent : baseEnd_5941279 < baseStart_5941279 := by decide
  rcases family_descends (prefixWord ++ tailWord_5941279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5941306 : List Nat := [3, 1, 1, 1, 3, 1, 1, 1, 7, 1, 3]
def baseStart_5941306 : Nat := 118140960795 + 5941306 * 2 ^ 59
def prefixEnd_5941306 : Nat := 4983230072969 + 3 ^ 40 * 5941306 * 2
def baseEnd_5941306 : Nat := 3050745693441636846651437

theorem tailTrace_5941306 : CollatzResearch.WordTrace tailWord_5941306 prefixEnd_5941306 3050745693441636846651437 := by
  unfold tailWord_5941306
  simp only [CollatzResearch.WordTrace]
  refine ⟨54174308053417632781492943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144464821475780354083981181 54174308053417632781492943)
  ·
    refine ⟨81261462080126449172239415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54174308053417632781492943 81261462080126449172239415)
    ·
      refine ⟨121892193120189673758359123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81261462080126449172239415 121892193120189673758359123)
      ·
        refine ⟨182838289680284510637538685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121892193120189673758359123 182838289680284510637538685)
        ·
          refine ⟨68564358630106691489077007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182838289680284510637538685 68564358630106691489077007)
          ·
            refine ⟨102846537945160037233615511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68564358630106691489077007 102846537945160037233615511)
            ·
              refine ⟨154269806917740055850423267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102846537945160037233615511 154269806917740055850423267)
              ·
                refine ⟨231404710376610083775634901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154269806917740055850423267 231404710376610083775634901)
                ·
                  refine ⟨5423547899451798838491443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 231404710376610083775634901 5423547899451798838491443)
                  ·
                    refine ⟨8135321849177698257737165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5423547899451798838491443 8135321849177698257737165)
                    ·
                      refine ⟨3050745693441636846651437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8135321849177698257737165 3050745693441636846651437)
                      ·
                        rfl

theorem cell23_5941306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 7, 1, 3].length) (baseStart_5941306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5941306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5941306 prefixEnd_5941306 := by exact prefixLift 5941306
  have htrace : WordTrace (prefixWord ++ tailWord_5941306) baseStart_5941306 baseEnd_5941306 := by
    simpa [prefixWord, tailWord_5941306, baseEnd_5941306] using wordTrace_append hprefix tailTrace_5941306
  have hstable : (prefixWord ++ tailWord_5941306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5941306).length < 2 ^ (prefixWord ++ tailWord_5941306).sum := by decide
  have hdescent : baseEnd_5941306 < baseStart_5941306 := by decide
  rcases family_descends (prefixWord ++ tailWord_5941306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5941313 : List Nat := [1, 2, 5, 1, 2, 3, 1, 2, 6]
def baseStart_5941313 : Nat := 118140960795 + 5941313 * 2 ^ 59
def prefixEnd_5941313 : Nat := 4983230072969 + 3 ^ 40 * 5941313 * 2
def baseEnd_5941313 : Nat := 338972143089579813251545

theorem tailTrace_5941313 : CollatzResearch.WordTrace tailWord_5941313 prefixEnd_5941313 338972143089579813251545 := by
  unfold tailWord_5941313
  simp only [CollatzResearch.WordTrace]
  refine ⟨216697487524645171321476593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144464991683096780880984395 216697487524645171321476593)
  ·
    refine ⟨162523115643483878491107445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216697487524645171321476593 162523115643483878491107445)
    ·
      refine ⟨15236542091576613608541323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 162523115643483878491107445 15236542091576613608541323)
      ·
        refine ⟨22854813137364920412811985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15236542091576613608541323 22854813137364920412811985)
        ·
          refine ⟨17141109853023690309608989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22854813137364920412811985 17141109853023690309608989)
          ·
            refine ⟨6427916194883883866103371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17141109853023690309608989 6427916194883883866103371)
            ·
              refine ⟨9641874292325825799155057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6427916194883883866103371 9641874292325825799155057)
              ·
                refine ⟨7231405719244369349366293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9641874292325825799155057 7231405719244369349366293)
                ·
                  refine ⟨338972143089579813251545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7231405719244369349366293 338972143089579813251545)
                  ·
                    rfl

theorem cell23_5941313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 2, 6].length) (baseStart_5941313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5941313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5941313 prefixEnd_5941313 := by exact prefixLift 5941313
  have htrace : WordTrace (prefixWord ++ tailWord_5941313) baseStart_5941313 baseEnd_5941313 := by
    simpa [prefixWord, tailWord_5941313, baseEnd_5941313] using wordTrace_append hprefix tailTrace_5941313
  have hstable : (prefixWord ++ tailWord_5941313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5941313).length < 2 ^ (prefixWord ++ tailWord_5941313).sum := by decide
  have hdescent : baseEnd_5941313 < baseStart_5941313 := by decide
  rcases family_descends (prefixWord ++ tailWord_5941313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5941356 : List Nat := [2, 2, 1, 1, 3, 3, 1, 2, 4, 4]
def baseStart_5941356 : Nat := 118140960795 + 5941356 * 2 ^ 59
def prefixEnd_5941356 : Nat := 4983230072969 + 3 ^ 40 * 5941356 * 2
def baseEnd_5941356 : Nat := 1016923789158120550342069

theorem tailTrace_5941356 : CollatzResearch.WordTrace tailWord_5941356 prefixEnd_5941356 1016923789158120550342069 := by
  unfold tailWord_5941356
  simp only [CollatzResearch.WordTrace]
  refine ⟨108349527931744694832645961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144466037242326259776861281 108349527931744694832645961)
  ·
    refine ⟨81262145948808521124484471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108349527931744694832645961 81262145948808521124484471)
    ·
      refine ⟨121893218923212781686726707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81262145948808521124484471 121893218923212781686726707)
      ·
        refine ⟨182839828384819172530090061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121893218923212781686726707 182839828384819172530090061)
        ·
          refine ⟨68564935644307189698783773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182839828384819172530090061 68564935644307189698783773)
          ·
            refine ⟨25711850866615196137043915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68564935644307189698783773 25711850866615196137043915)
            ·
              refine ⟨38567776299922794205565873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25711850866615196137043915 38567776299922794205565873)
              ·
                refine ⟨28925832224942095654174405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38567776299922794205565873 28925832224942095654174405)
                ·
                  refine ⟨5423593542176642935157701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28925832224942095654174405 5423593542176642935157701)
                  ·
                    refine ⟨1016923789158120550342069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5423593542176642935157701 1016923789158120550342069)
                    ·
                      rfl

theorem cell23_5941356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 4].length) (baseStart_5941356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5941356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5941356 prefixEnd_5941356 := by exact prefixLift 5941356
  have htrace : WordTrace (prefixWord ++ tailWord_5941356) baseStart_5941356 baseEnd_5941356 := by
    simpa [prefixWord, tailWord_5941356, baseEnd_5941356] using wordTrace_append hprefix tailTrace_5941356
  have hstable : (prefixWord ++ tailWord_5941356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5941356).length < 2 ^ (prefixWord ++ tailWord_5941356).sum := by decide
  have hdescent : baseEnd_5941356 < baseStart_5941356 := by decide
  rcases family_descends (prefixWord ++ tailWord_5941356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5941369 : List Nat := [1, 2, 1, 3, 4, 1, 11]
def baseStart_5941369 : Nat := 118140960795 + 5941369 * 2 ^ 59
def prefixEnd_5941369 : Nat := 4983230072969 + 3 ^ 40 * 5941369 * 2
def baseEnd_5941369 : Nat := 37663926453368766668687

theorem tailTrace_5941369 : CollatzResearch.WordTrace tailWord_5941369 prefixEnd_5941369 37663926453368766668687 := by
  unfold tailWord_5941369
  simp only [CollatzResearch.WordTrace]
  refine ⟨216699530012442292885515161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144466353341628195257010107 216699530012442292885515161)
  ·
    refine ⟨162524647509331719664136371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216699530012442292885515161 162524647509331719664136371)
    ·
      refine ⟨243786971263997579496204557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162524647509331719664136371 243786971263997579496204557)
      ·
        refine ⟨91420114223999092311076709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 243786971263997579496204557 91420114223999092311076709)
        ·
          refine ⟨17141271416999829808326883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91420114223999092311076709 17141271416999829808326883)
          ·
            refine ⟨25711907125499744712490325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17141271416999829808326883 25711907125499744712490325)
            ·
              refine ⟨37663926453368766668687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 25711907125499744712490325 37663926453368766668687)
              ·
                rfl

theorem cell23_5941369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 11].length) (baseStart_5941369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5941369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5941369 prefixEnd_5941369 := by exact prefixLift 5941369
  have htrace : WordTrace (prefixWord ++ tailWord_5941369) baseStart_5941369 baseEnd_5941369 := by
    simpa [prefixWord, tailWord_5941369, baseEnd_5941369] using wordTrace_append hprefix tailTrace_5941369
  have hstable : (prefixWord ++ tailWord_5941369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5941369).length < 2 ^ (prefixWord ++ tailWord_5941369).sum := by decide
  have hdescent : baseEnd_5941369 < baseStart_5941369 := by decide
  rcases family_descends (prefixWord ++ tailWord_5941369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5941386 : List Nat := [3, 1, 2, 3, 1, 3, 2, 8]
def baseStart_5941386 : Nat := 118140960795 + 5941386 * 2 ^ 59
def prefixEnd_5941386 : Nat := 4983230072969 + 3 ^ 40 * 5941386 * 2
def baseEnd_5941386 : Nat := 112992102662740612357447

theorem tailTrace_5941386 : CollatzResearch.WordTrace tailWord_5941386 prefixEnd_5941386 112992102662740612357447 := by
  unfold tailWord_5941386
  simp only [CollatzResearch.WordTrace]
  refine ⟨54175037513345176197221003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144466766702253803192589341 54175037513345176197221003)
  ·
    refine ⟨81262556270017764295831505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54175037513345176197221003 81262556270017764295831505)
    ·
      refine ⟨60946917202513323221873629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81262556270017764295831505 60946917202513323221873629)
      ·
        refine ⟨22855093950942496208202611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60946917202513323221873629 22855093950942496208202611)
        ·
          refine ⟨34282640926413744312303917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22855093950942496208202611 34282640926413744312303917)
          ·
            refine ⟨12855990347405154117113969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34282640926413744312303917 12855990347405154117113969)
            ·
              refine ⟨9641992760553865587835477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12855990347405154117113969 9641992760553865587835477)
              ·
                refine ⟨112992102662740612357447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9641992760553865587835477 112992102662740612357447)
                ·
                  rfl

theorem cell23_5941386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 8].length) (baseStart_5941386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5941386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5941386 prefixEnd_5941386 := by exact prefixLift 5941386
  have htrace : WordTrace (prefixWord ++ tailWord_5941386) baseStart_5941386 baseEnd_5941386 := by
    simpa [prefixWord, tailWord_5941386, baseEnd_5941386] using wordTrace_append hprefix tailTrace_5941386
  have hstable : (prefixWord ++ tailWord_5941386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5941386).length < 2 ^ (prefixWord ++ tailWord_5941386).sum := by decide
  have hdescent : baseEnd_5941386 < baseStart_5941386 := by decide
  rcases family_descends (prefixWord ++ tailWord_5941386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5941390 : List Nat := [4, 1, 1, 3, 3, 1, 1, 3, 2, 4]
def baseStart_5941390 : Nat := 118140960795 + 5941390 * 2 ^ 59
def prefixEnd_5941390 : Nat := 4983230072969 + 3 ^ 40 * 5941390 * 2
def baseEnd_5941390 : Nat := 1016929608605538172667017

theorem tailTrace_5941390 : CollatzResearch.WordTrace tailWord_5941390 prefixEnd_5941390 1016929608605538172667017 := by
  unfold tailWord_5941390
  simp only [CollatzResearch.WordTrace]
  refine ⟨27087536993170776684003703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144466863963577475648019749 27087536993170776684003703)
  ·
    refine ⟨40631305489756165026005555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27087536993170776684003703 40631305489756165026005555)
    ·
      refine ⟨60946958234634247539008333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40631305489756165026005555 60946958234634247539008333)
      ·
        refine ⟨22855109337987842827128125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60946958234634247539008333 22855109337987842827128125)
        ·
          refine ⟨8570666001745441060173047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22855109337987842827128125 8570666001745441060173047)
          ·
            refine ⟨12855999002618161590259571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8570666001745441060173047 12855999002618161590259571)
            ·
              refine ⟨19283998503927242385389357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12855999002618161590259571 19283998503927242385389357)
              ·
                refine ⟨7231499438972715894521009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19283998503927242385389357 7231499438972715894521009)
                ·
                  refine ⟨5423624579229536920890757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7231499438972715894521009 5423624579229536920890757)
                  ·
                    refine ⟨1016929608605538172667017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5423624579229536920890757 1016929608605538172667017)
                    ·
                      rfl

theorem cell23_5941390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 3, 2, 4].length) (baseStart_5941390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5941390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5941390 prefixEnd_5941390 := by exact prefixLift 5941390
  have htrace : WordTrace (prefixWord ++ tailWord_5941390) baseStart_5941390 baseEnd_5941390 := by
    simpa [prefixWord, tailWord_5941390, baseEnd_5941390] using wordTrace_append hprefix tailTrace_5941390
  have hstable : (prefixWord ++ tailWord_5941390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5941390).length < 2 ^ (prefixWord ++ tailWord_5941390).sum := by decide
  have hdescent : baseEnd_5941390 < baseStart_5941390 := by decide
  rcases family_descends (prefixWord ++ tailWord_5941390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5941487 : List Nat := [1, 1, 2, 1, 6, 1, 3, 2, 2, 2, 2]
def baseStart_5941487 : Nat := 118140960795 + 5941487 * 2 ^ 59
def prefixEnd_5941487 : Nat := 4983230072969 + 3 ^ 40 * 5941487 * 2
def baseEnd_5941487 : Nat := 3050838633440100638488105

theorem tailTrace_5941487 : CollatzResearch.WordTrace tailWord_5941487 prefixEnd_5941487 3050838633440100638488105 := by
  unfold tailWord_5941487
  simp only [CollatzResearch.WordTrace]
  refine ⟨216703833826014799038310715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144469222550676532692207143 216703833826014799038310715)
  ·
    refine ⟨325055750739022198557466073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216703833826014799038310715 325055750739022198557466073)
    ·
      refine ⟨243791813054266648918099555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 325055750739022198557466073 243791813054266648918099555)
      ·
        refine ⟨365687719581399973377149333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243791813054266648918099555 365687719581399973377149333)
        ·
          refine ⟨17141611855378123752053875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 365687719581399973377149333 17141611855378123752053875)
          ·
            refine ⟨25712417783067185628080813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17141611855378123752053875 25712417783067185628080813)
            ·
              refine ⟨9642156668650194610530305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25712417783067185628080813 9642156668650194610530305)
              ·
                refine ⟨7231617501487645957897729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9642156668650194610530305 7231617501487645957897729)
                ·
                  refine ⟨5423713126115734468423297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7231617501487645957897729 5423713126115734468423297)
                  ·
                    refine ⟨4067784844586800851317473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5423713126115734468423297 4067784844586800851317473)
                    ·
                      refine ⟨3050838633440100638488105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4067784844586800851317473 3050838633440100638488105)
                      ·
                        rfl

theorem cell23_5941487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 2, 2, 2, 2].length) (baseStart_5941487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5941487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5941487 prefixEnd_5941487 := by exact prefixLift 5941487
  have htrace : WordTrace (prefixWord ++ tailWord_5941487) baseStart_5941487 baseEnd_5941487 := by
    simpa [prefixWord, tailWord_5941487, baseEnd_5941487] using wordTrace_append hprefix tailTrace_5941487
  have hstable : (prefixWord ++ tailWord_5941487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5941487).length < 2 ^ (prefixWord ++ tailWord_5941487).sum := by decide
  have hdescent : baseEnd_5941487 < baseStart_5941487 := by decide
  rcases family_descends (prefixWord ++ tailWord_5941487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5941580 : List Nat := [2, 2, 1, 3, 2, 1, 4, 1, 2, 2, 3]
def baseStart_5941580 : Nat := 118140960795 + 5941580 * 2 ^ 59
def prefixEnd_5941580 : Nat := 4983230072969 + 3 ^ 40 * 5941580 * 2
def baseEnd_5941580 : Nat := 3050886387140968774625177

theorem tailTrace_5941580 : CollatzResearch.WordTrace tailWord_5941580 prefixEnd_5941580 3050886387140968774625177 := by
  unfold tailWord_5941580
  simp only [CollatzResearch.WordTrace]
  refine ⟨108353612907338937960723097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144471483876451917280964129 108353612907338937960723097)
  ·
    refine ⟨81265209680504203470542323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108353612907338937960723097 81265209680504203470542323)
    ·
      refine ⟨121897814520756305205813485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81265209680504203470542323 121897814520756305205813485)
      ·
        refine ⟨45711680445283614452180057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121897814520756305205813485 45711680445283614452180057)
        ·
          refine ⟨34283760333962710839135043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45711680445283614452180057 34283760333962710839135043)
          ·
            refine ⟨51425640500944066258702565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34283760333962710839135043 51425640500944066258702565)
            ·
              refine ⟨9642307593927012423506731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51425640500944066258702565 9642307593927012423506731)
              ·
                refine ⟨14463461390890518635260097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9642307593927012423506731 14463461390890518635260097)
                ·
                  refine ⟨10847596043167888976445073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14463461390890518635260097 10847596043167888976445073)
                  ·
                    refine ⟨8135697032375916732333805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10847596043167888976445073 8135697032375916732333805)
                    ·
                      refine ⟨3050886387140968774625177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8135697032375916732333805 3050886387140968774625177)
                      ·
                        rfl

theorem cell23_5941580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 1, 2, 2, 3].length) (baseStart_5941580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5941580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5941580 prefixEnd_5941580 := by exact prefixLift 5941580
  have htrace : WordTrace (prefixWord ++ tailWord_5941580) baseStart_5941580 baseEnd_5941580 := by
    simpa [prefixWord, tailWord_5941580, baseEnd_5941580] using wordTrace_append hprefix tailTrace_5941580
  have hstable : (prefixWord ++ tailWord_5941580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5941580).length < 2 ^ (prefixWord ++ tailWord_5941580).sum := by decide
  have hdescent : baseEnd_5941580 < baseStart_5941580 := by decide
  rcases family_descends (prefixWord ++ tailWord_5941580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5941600 : List Nat := [2, 1, 1, 3, 5, 1, 2, 2, 6]
def baseStart_5941600 : Nat := 118140960795 + 5941600 * 2 ^ 59
def prefixEnd_5941600 : Nat := 4983230072969 + 3 ^ 40 * 5941600 * 2
def baseEnd_5941600 : Nat := 338988517417117632930565

theorem tailTrace_5941600 : CollatzResearch.WordTrace tailWord_5941600 prefixEnd_5941600 338988517417117632930565 := by
  unfold tailWord_5941600
  simp only [CollatzResearch.WordTrace]
  refine ⟨108353977637302709668587127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144471970183070279558116169 108353977637302709668587127)
  ·
    refine ⟨162530966455954064502880691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108353977637302709668587127 162530966455954064502880691)
    ·
      refine ⟨243796449683931096754321037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162530966455954064502880691 243796449683931096754321037)
      ·
        refine ⟨91423668631474161282870389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 243796449683931096754321037 91423668631474161282870389)
        ·
          refine ⟨8570968934200702620269099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 91423668631474161282870389 8570968934200702620269099)
          ·
            refine ⟨12856453401301053930403649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8570968934200702620269099 12856453401301053930403649)
            ·
              refine ⟨9642340050975790447802737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12856453401301053930403649 9642340050975790447802737)
              ·
                refine ⟨7231755038231842835852053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9642340050975790447802737 7231755038231842835852053)
                ·
                  refine ⟨338988517417117632930565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7231755038231842835852053 338988517417117632930565)
                  ·
                    rfl

theorem cell23_5941600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 2, 6].length) (baseStart_5941600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5941600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5941600 prefixEnd_5941600 := by exact prefixLift 5941600
  have htrace : WordTrace (prefixWord ++ tailWord_5941600) baseStart_5941600 baseEnd_5941600 := by
    simpa [prefixWord, tailWord_5941600, baseEnd_5941600] using wordTrace_append hprefix tailTrace_5941600
  have hstable : (prefixWord ++ tailWord_5941600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5941600).length < 2 ^ (prefixWord ++ tailWord_5941600).sum := by decide
  have hdescent : baseEnd_5941600 < baseStart_5941600 := by decide
  rcases family_descends (prefixWord ++ tailWord_5941600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5941613 : List Nat := [1, 5, 1, 1, 1, 2, 1, 1, 5, 5]
def baseStart_5941613 : Nat := 118140960795 + 5941613 * 2 ^ 59
def prefixEnd_5941613 : Nat := 4983230072969 + 3 ^ 40 * 5941613 * 2
def baseEnd_5941613 : Nat := 1016967777334189048504175

theorem tailTrace_5941613 : CollatzResearch.WordTrace tailWord_5941613 prefixEnd_5941613 1016967777334189048504175 := by
  unfold tailWord_5941613
  simp only [CollatzResearch.WordTrace]
  refine ⟨216708429423558322557397493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144472286282372215038264995 216708429423558322557397493)
  ·
    refine ⟨20316415258458592739756015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 216708429423558322557397493 20316415258458592739756015)
    ·
      refine ⟨30474622887687889109634023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20316415258458592739756015 30474622887687889109634023)
      ·
        refine ⟨45711934331531833664451035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30474622887687889109634023 45711934331531833664451035)
        ·
          refine ⟨68567901497297750496676553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45711934331531833664451035 68567901497297750496676553)
          ·
            refine ⟨51425926122973312872507415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68567901497297750496676553 51425926122973312872507415)
            ·
              refine ⟨77138889184459969308761123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51425926122973312872507415 77138889184459969308761123)
              ·
                refine ⟨115708333776689953963141685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77138889184459969308761123 115708333776689953963141685)
                ·
                  refine ⟨10847656291564683184044533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 115708333776689953963141685 10847656291564683184044533)
                  ·
                    refine ⟨1016967777334189048504175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10847656291564683184044533 1016967777334189048504175)
                    ·
                      rfl

theorem cell23_5941613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_5941613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5941613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5941613 prefixEnd_5941613 := by exact prefixLift 5941613
  have htrace : WordTrace (prefixWord ++ tailWord_5941613) baseStart_5941613 baseEnd_5941613 := by
    simpa [prefixWord, tailWord_5941613, baseEnd_5941613] using wordTrace_append hprefix tailTrace_5941613
  have hstable : (prefixWord ++ tailWord_5941613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5941613).length < 2 ^ (prefixWord ++ tailWord_5941613).sum := by decide
  have hdescent : baseEnd_5941613 < baseStart_5941613 := by decide
  rcases family_descends (prefixWord ++ tailWord_5941613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5941643 : List Nat := [1, 1, 1, 1, 4, 4, 2, 2, 1, 6]
def baseStart_5941643 : Nat := 118140960795 + 5941643 * 2 ^ 59
def prefixEnd_5941643 : Nat := 4983230072969 + 3 ^ 40 * 5941643 * 2
def baseEnd_5941643 : Nat := 1016972912140734009379129

theorem tailTrace_5941643 : CollatzResearch.WordTrace tailWord_5941643 prefixEnd_5941643 1016972912140734009379129 := by
  unfold tailWord_5941643
  simp only [CollatzResearch.WordTrace]
  refine ⟨216709523613449637680989583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144473015742299758453993055 216709523613449637680989583)
  ·
    refine ⟨325064285420174456521484375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216709523613449637680989583 325064285420174456521484375)
    ·
      refine ⟨487596428130261684782226563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325064285420174456521484375 487596428130261684782226563)
      ·
        refine ⟨731394642195392527173339845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 487596428130261684782226563 731394642195392527173339845)
        ·
          refine ⟨137136495411636098845001221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 731394642195392527173339845 137136495411636098845001221)
          ·
            refine ⟨25713092889681768533437729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 137136495411636098845001221 25713092889681768533437729)
            ·
              refine ⟨19284819667261326400078297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25713092889681768533437729 19284819667261326400078297)
              ·
                refine ⟨14463614750445994800058723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19284819667261326400078297 14463614750445994800058723)
                ·
                  refine ⟨21695422125668992200088085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14463614750445994800058723 21695422125668992200088085)
                  ·
                    refine ⟨1016972912140734009379129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21695422125668992200088085 1016972912140734009379129)
                    ·
                      rfl

theorem cell23_5941643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 2, 1, 6].length) (baseStart_5941643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5941643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5941643 prefixEnd_5941643 := by exact prefixLift 5941643
  have htrace : WordTrace (prefixWord ++ tailWord_5941643) baseStart_5941643 baseEnd_5941643 := by
    simpa [prefixWord, tailWord_5941643, baseEnd_5941643] using wordTrace_append hprefix tailTrace_5941643
  have hstable : (prefixWord ++ tailWord_5941643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5941643).length < 2 ^ (prefixWord ++ tailWord_5941643).sum := by decide
  have hdescent : baseEnd_5941643 < baseStart_5941643 := by decide
  rcases family_descends (prefixWord ++ tailWord_5941643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5941644 : List Nat := [2, 2, 1, 2, 1, 5, 2, 3, 1, 1, 3]
def baseStart_5941644 : Nat := 118140960795 + 5941644 * 2 ^ 59
def prefixEnd_5941644 : Nat := 4983230072969 + 3 ^ 40 * 5941644 * 2
def baseEnd_5941644 : Nat := 3050919249902856524224883

theorem tailTrace_5941644 : CollatzResearch.WordTrace tailWord_5941644 prefixEnd_5941644 3050919249902856524224883 := by
  unfold tailWord_5941644
  simp only [CollatzResearch.WordTrace]
  refine ⟨108354780043223007425887993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144473040057630676567850657 108354780043223007425887993)
  ·
    refine ⟨81266085032417255569415995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108354780043223007425887993 81266085032417255569415995)
    ·
      refine ⟨121899127548625883354123993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81266085032417255569415995 121899127548625883354123993)
      ·
        refine ⟨91424345661469412515592995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121899127548625883354123993 91424345661469412515592995)
        ·
          refine ⟨137136518492204118773389493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91424345661469412515592995 137136518492204118773389493)
          ·
            refine ⟨12856548608644136135005265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 137136518492204118773389493 12856548608644136135005265)
            ·
              refine ⟨9642411456483102101253949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12856548608644136135005265 9642411456483102101253949)
              ·
                refine ⟨3615904296181163287970231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9642411456483102101253949 3615904296181163287970231)
                ·
                  refine ⟨5423856444271744931955347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3615904296181163287970231 5423856444271744931955347)
                  ·
                    refine ⟨8135784666407617397933021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5423856444271744931955347 8135784666407617397933021)
                    ·
                      refine ⟨3050919249902856524224883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8135784666407617397933021 3050919249902856524224883)
                      ·
                        rfl

theorem cell23_5941644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 3, 1, 1, 3].length) (baseStart_5941644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5941644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5941644 prefixEnd_5941644 := by exact prefixLift 5941644
  have htrace : WordTrace (prefixWord ++ tailWord_5941644) baseStart_5941644 baseEnd_5941644 := by
    simpa [prefixWord, tailWord_5941644, baseEnd_5941644] using wordTrace_append hprefix tailTrace_5941644
  have hstable : (prefixWord ++ tailWord_5941644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5941644).length < 2 ^ (prefixWord ++ tailWord_5941644).sum := by decide
  have hdescent : baseEnd_5941644 < baseStart_5941644 := by decide
  rcases family_descends (prefixWord ++ tailWord_5941644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5941653 : List Nat := [1, 3, 2, 1, 1, 2, 1, 5, 1, 1, 5]
def baseStart_5941653 : Nat := 118140960795 + 5941653 * 2 ^ 59
def prefixEnd_5941653 : Nat := 4983230072969 + 3 ^ 40 * 5941653 * 2
def baseEnd_5941653 : Nat := 3050923871228746989012341

theorem tailTrace_5941653 : CollatzResearch.WordTrace tailWord_5941653 prefixEnd_5941653 3050923871228746989012341 := by
  unfold tailWord_5941653
  simp only [CollatzResearch.WordTrace]
  refine ⟨216709888343413409388853613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144473258895608939592569075 216709888343413409388853613)
  ·
    refine ⟨81266208128780028520820105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216709888343413409388853613 81266208128780028520820105)
    ·
      refine ⟨60949656096585021390615079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81266208128780028520820105 60949656096585021390615079)
      ·
        refine ⟨91424484144877532085922619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60949656096585021390615079 91424484144877532085922619)
        ·
          refine ⟨137136726217316298128883929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91424484144877532085922619 137136726217316298128883929)
          ·
            refine ⟨102852544662987223596662947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137136726217316298128883929 102852544662987223596662947)
            ·
              refine ⟨154278816994480835394994421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102852544662987223596662947 154278816994480835394994421)
              ·
                refine ⟨14463639093232578318280727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 154278816994480835394994421 14463639093232578318280727)
                ·
                  refine ⟨21695458639848867477421091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14463639093232578318280727 21695458639848867477421091)
                  ·
                    refine ⟨32543187959773301216131637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21695458639848867477421091 32543187959773301216131637)
                    ·
                      refine ⟨3050923871228746989012341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32543187959773301216131637 3050923871228746989012341)
                      ·
                        rfl

theorem cell23_5941653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 5, 1, 1, 5].length) (baseStart_5941653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5941653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5941653 prefixEnd_5941653 := by exact prefixLift 5941653
  have htrace : WordTrace (prefixWord ++ tailWord_5941653) baseStart_5941653 baseEnd_5941653 := by
    simpa [prefixWord, tailWord_5941653, baseEnd_5941653] using wordTrace_append hprefix tailTrace_5941653
  have hstable : (prefixWord ++ tailWord_5941653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5941653).length < 2 ^ (prefixWord ++ tailWord_5941653).sum := by decide
  have hdescent : baseEnd_5941653 < baseStart_5941653 := by decide
  rcases family_descends (prefixWord ++ tailWord_5941653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5941663 : List Nat := [1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 6]
def baseStart_5941663 : Nat := 118140960795 + 5941663 * 2 ^ 59
def prefixEnd_5941663 : Nat := 4983230072969 + 3 ^ 40 * 5941663 * 2
def baseEnd_5941663 : Nat := 3050929006035291949887295

theorem tailTrace_5941663 : CollatzResearch.WordTrace tailWord_5941663 prefixEnd_5941663 3050929006035291949887295 := by
  unfold tailWord_5941663
  simp only [CollatzResearch.WordTrace]
  refine ⟨216710253073377181096717643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144473502048918120731145095 216710253073377181096717643)
  ·
    refine ⟨325065379610065771645076465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216710253073377181096717643 325065379610065771645076465)
    ·
      refine ⟨243799034707549328733807349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 325065379610065771645076465 243799034707549328733807349)
      ·
        refine ⟨22856159503832749568794439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 243799034707549328733807349 22856159503832749568794439)
        ·
          refine ⟨34284239255749124353191659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22856159503832749568794439 34284239255749124353191659)
          ·
            refine ⟨51426358883623686529787489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34284239255749124353191659 51426358883623686529787489)
            ·
              refine ⟨38569769162717764897340617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51426358883623686529787489 38569769162717764897340617)
              ·
                refine ⟨28927326872038323673005463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38569769162717764897340617 28927326872038323673005463)
                ·
                  refine ⟨43390990308057485509508195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28927326872038323673005463 43390990308057485509508195)
                  ·
                    refine ⟨65086485462086228264262293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43390990308057485509508195 65086485462086228264262293)
                    ·
                      refine ⟨3050929006035291949887295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65086485462086228264262293 3050929006035291949887295)
                      ·
                        rfl

theorem cell23_5941663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_5941663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5941663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5941663 prefixEnd_5941663 := by exact prefixLift 5941663
  have htrace : WordTrace (prefixWord ++ tailWord_5941663) baseStart_5941663 baseEnd_5941663 := by
    simpa [prefixWord, tailWord_5941663, baseEnd_5941663] using wordTrace_append hprefix tailTrace_5941663
  have hstable : (prefixWord ++ tailWord_5941663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5941663).length < 2 ^ (prefixWord ++ tailWord_5941663).sum := by decide
  have hdescent : baseEnd_5941663 < baseStart_5941663 := by decide
  rcases family_descends (prefixWord ++ tailWord_5941663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5941667 : List Nat := [1, 1, 1, 4, 1, 4, 1, 3, 3, 2, 2]
def baseStart_5941667 : Nat := 118140960795 + 5941667 * 2 ^ 59
def prefixEnd_5941667 : Nat := 4983230072969 + 3 ^ 40 * 5941667 * 2
def baseEnd_5941667 : Nat := 3050931059957909934237277

theorem tailTrace_5941667 : CollatzResearch.WordTrace tailWord_5941667 prefixEnd_5941667 3050931059957909934237277 := by
  unfold tailWord_5941667
  simp only [CollatzResearch.WordTrace]
  refine ⟨216710398965362689779863255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144473599310241793186575503 216710398965362689779863255)
  ·
    refine ⟨325065598448044034669794883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216710398965362689779863255 325065598448044034669794883)
    ·
      refine ⟨487598397672066052004692325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325065598448044034669794883 487598397672066052004692325)
      ·
        refine ⟨91424699563512384750879811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 487598397672066052004692325 91424699563512384750879811)
        ·
          refine ⟨137137049345268577126319717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91424699563512384750879811 137137049345268577126319717)
          ·
            refine ⟨25713196752237858211184947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 137137049345268577126319717 25713196752237858211184947)
            ·
              refine ⟨38569795128356787316777421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25713196752237858211184947 38569795128356787316777421)
              ·
                refine ⟨14463673173133795243791533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38569795128356787316777421 14463673173133795243791533)
                ·
                  refine ⟨5423877439925173216421825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14463673173133795243791533 5423877439925173216421825)
                  ·
                    refine ⟨4067908079943879912316369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5423877439925173216421825 4067908079943879912316369)
                    ·
                      refine ⟨3050931059957909934237277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4067908079943879912316369 3050931059957909934237277)
                      ·
                        rfl

theorem cell23_5941667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 3, 3, 2, 2].length) (baseStart_5941667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5941667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5941667 prefixEnd_5941667 := by exact prefixLift 5941667
  have htrace : WordTrace (prefixWord ++ tailWord_5941667) baseStart_5941667 baseEnd_5941667 := by
    simpa [prefixWord, tailWord_5941667, baseEnd_5941667] using wordTrace_append hprefix tailTrace_5941667
  have hstable : (prefixWord ++ tailWord_5941667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5941667).length < 2 ^ (prefixWord ++ tailWord_5941667).sum := by decide
  have hdescent : baseEnd_5941667 < baseStart_5941667 := by decide
  rcases family_descends (prefixWord ++ tailWord_5941667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5941687 : List Nat := [1, 1, 3, 1, 3, 4, 2, 2, 1, 2, 3]
def baseStart_5941687 : Nat := 118140960795 + 5941687 * 2 ^ 59
def prefixEnd_5941687 : Nat := 4983230072969 + 3 ^ 40 * 5941687 * 2
def baseEnd_5941687 : Nat := 3050941329570999855987185

theorem tailTrace_5941687 : CollatzResearch.WordTrace tailWord_5941687 prefixEnd_5941687 3050941329570999855987185 := by
  unfold tailWord_5941687
  simp only [CollatzResearch.WordTrace]
  refine ⟨216711128425290233195591315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144474085616860155463727543 216711128425290233195591315)
  ·
    refine ⟨325066692637935349793386973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216711128425290233195591315 325066692637935349793386973)
    ·
      refine ⟨121900009739225756172520115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 325066692637935349793386973 121900009739225756172520115)
      ·
        refine ⟨182850014608838634258780173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121900009739225756172520115 182850014608838634258780173)
        ·
          refine ⟨68568755478314487847042565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182850014608838634258780173 68568755478314487847042565)
          ·
            refine ⟨12856641652183966471320481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68568755478314487847042565 12856641652183966471320481)
            ·
              refine ⟨9642481239137974853490361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12856641652183966471320481 9642481239137974853490361)
              ·
                refine ⟨7231860929353481140117771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9642481239137974853490361 7231860929353481140117771)
                ·
                  refine ⟨10847791394030221710176657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7231860929353481140117771 10847791394030221710176657)
                  ·
                    refine ⟨8135843545522666282632493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10847791394030221710176657 8135843545522666282632493)
                    ·
                      refine ⟨3050941329570999855987185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8135843545522666282632493 3050941329570999855987185)
                      ·
                        rfl

theorem cell23_5941687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 2, 1, 2, 3].length) (baseStart_5941687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5941687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5941687 prefixEnd_5941687 := by exact prefixLift 5941687
  have htrace : WordTrace (prefixWord ++ tailWord_5941687) baseStart_5941687 baseEnd_5941687 := by
    simpa [prefixWord, tailWord_5941687, baseEnd_5941687] using wordTrace_append hprefix tailTrace_5941687
  have hstable : (prefixWord ++ tailWord_5941687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5941687).length < 2 ^ (prefixWord ++ tailWord_5941687).sum := by decide
  have hdescent : baseEnd_5941687 < baseStart_5941687 := by decide
  rcases family_descends (prefixWord ++ tailWord_5941687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5941717 : List Nat := [1, 3, 2, 3, 1, 2, 2, 1, 4, 1, 3]
def baseStart_5941717 : Nat := 118140960795 + 5941717 * 2 ^ 59
def prefixEnd_5941717 : Nat := 4983230072969 + 3 ^ 40 * 5941717 * 2
def baseEnd_5941717 : Nat := 3050956733990634738612047

theorem tailTrace_5941717 : CollatzResearch.WordTrace tailWord_5941717 prefixEnd_5941717 3050956733990634738612047 := by
  unfold tailWord_5941717
  simp only [CollatzResearch.WordTrace]
  refine ⟨216712222615181548319183405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144474815076787698879455603 216712222615181548319183405)
  ·
    refine ⟨81267083480693080619693777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216712222615181548319183405 81267083480693080619693777)
    ·
      refine ⟨60950312610519810464770333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81267083480693080619693777 60950312610519810464770333)
      ·
        refine ⟨22856367228944928924288875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60950312610519810464770333 22856367228944928924288875)
        ·
          refine ⟨34284550843417393386433313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22856367228944928924288875 34284550843417393386433313)
          ·
            refine ⟨25713413132563045039824985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34284550843417393386433313 25713413132563045039824985)
            ·
              refine ⟨19285059849422283779868739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25713413132563045039824985 19285059849422283779868739)
              ·
                refine ⟨28927589774133425669803109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19285059849422283779868739 28927589774133425669803109)
                ·
                  refine ⟨5423923082650017313088083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28927589774133425669803109 5423923082650017313088083)
                  ·
                    refine ⟨8135884623975025969632125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5423923082650017313088083 8135884623975025969632125)
                    ·
                      refine ⟨3050956733990634738612047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8135884623975025969632125 3050956733990634738612047)
                      ·
                        rfl

theorem cell23_5941717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_5941717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5941717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5941717 prefixEnd_5941717 := by exact prefixLift 5941717
  have htrace : WordTrace (prefixWord ++ tailWord_5941717) baseStart_5941717 baseEnd_5941717 := by
    simpa [prefixWord, tailWord_5941717, baseEnd_5941717] using wordTrace_append hprefix tailTrace_5941717
  have hstable : (prefixWord ++ tailWord_5941717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5941717).length < 2 ^ (prefixWord ++ tailWord_5941717).sum := by decide
  have hdescent : baseEnd_5941717 < baseStart_5941717 := by decide
  rcases family_descends (prefixWord ++ tailWord_5941717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5941757 : List Nat := [1, 4, 1, 1, 1, 3, 3, 2, 1, 4, 2]
def baseStart_5941757 : Nat := 118140960795 + 5941757 * 2 ^ 59
def prefixEnd_5941757 : Nat := 4983230072969 + 3 ^ 40 * 5941757 * 2
def baseEnd_5941757 : Nat := 3050977273216814582111863

theorem tailTrace_5941757 : CollatzResearch.WordTrace tailWord_5941757 prefixEnd_5941757 3050977273216814582111863 := by
  unfold tailWord_5941757
  simp only [CollatzResearch.WordTrace]
  refine ⟨216713681535036635150639525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144475787690024423433759683 216713681535036635150639525)
  ·
    refine ⟨40633815287819369090744911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 216713681535036635150639525 40633815287819369090744911)
    ·
      refine ⟨60950722931729053636117367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40633815287819369090744911 60950722931729053636117367)
      ·
        refine ⟨91426084397593580454176051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60950722931729053636117367 91426084397593580454176051)
        ·
          refine ⟨137139126596390370681264077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91426084397593580454176051 137139126596390370681264077)
          ·
            refine ⟨51427172473646389005474029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137139126596390370681264077 51427172473646389005474029)
            ·
              refine ⟨19285189677617395877052761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51427172473646389005474029 19285189677617395877052761)
              ·
                refine ⟨14463892258213046907789571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19285189677617395877052761 14463892258213046907789571)
                ·
                  refine ⟨21695838387319570361684357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14463892258213046907789571 21695838387319570361684357)
                  ·
                    refine ⟨4067969697622419442815817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21695838387319570361684357 4067969697622419442815817)
                    ·
                      refine ⟨3050977273216814582111863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4067969697622419442815817 3050977273216814582111863)
                      ·
                        rfl

theorem cell23_5941757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 2, 1, 4, 2].length) (baseStart_5941757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5941757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5941757 prefixEnd_5941757 := by exact prefixLift 5941757
  have htrace : WordTrace (prefixWord ++ tailWord_5941757) baseStart_5941757 baseEnd_5941757 := by
    simpa [prefixWord, tailWord_5941757, baseEnd_5941757] using wordTrace_append hprefix tailTrace_5941757
  have hstable : (prefixWord ++ tailWord_5941757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5941757).length < 2 ^ (prefixWord ++ tailWord_5941757).sum := by decide
  have hdescent : baseEnd_5941757 < baseStart_5941757 := by decide
  rcases family_descends (prefixWord ++ tailWord_5941757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5941761 : List Nat := [1, 2, 4, 1, 3, 2, 3, 1, 1, 3, 2]
def baseStart_5941761 : Nat := 118140960795 + 5941761 * 2 ^ 59
def prefixEnd_5941761 : Nat := 4983230072969 + 3 ^ 40 * 5941761 * 2
def baseEnd_5941761 : Nat := 3050979327139432566461845

theorem tailTrace_5941761 : CollatzResearch.WordTrace tailWord_5941761 prefixEnd_5941761 3050979327139432566461845 := by
  unfold tailWord_5941761
  simp only [CollatzResearch.WordTrace]
  refine ⟨216713827427022143833785137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144475884951348095889190091 216713827427022143833785137)
  ·
    refine ⟨162535370570266607875338853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216713827427022143833785137 162535370570266607875338853)
    ·
      refine ⟨30475381981924988976626035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 162535370570266607875338853 30475381981924988976626035)
      ·
        refine ⟨45713072972887483464939053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30475381981924988976626035 45713072972887483464939053)
        ·
          refine ⟨17142402364832806299352145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45713072972887483464939053 17142402364832806299352145)
          ·
            refine ⟨12856801773624604724514109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17142402364832806299352145 12856801773624604724514109)
            ·
              refine ⟨4821300665109226771692791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12856801773624604724514109 4821300665109226771692791)
              ·
                refine ⟨7231950997663840157539187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4821300665109226771692791 7231950997663840157539187)
                ·
                  refine ⟨10847926496495760236308781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7231950997663840157539187 10847926496495760236308781)
                  ·
                    refine ⟨4067972436185910088615793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10847926496495760236308781 4067972436185910088615793)
                    ·
                      refine ⟨3050979327139432566461845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4067972436185910088615793 3050979327139432566461845)
                      ·
                        rfl

theorem cell23_5941761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 3, 1, 1, 3, 2].length) (baseStart_5941761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5941761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5941761 prefixEnd_5941761 := by exact prefixLift 5941761
  have htrace : WordTrace (prefixWord ++ tailWord_5941761) baseStart_5941761 baseEnd_5941761 := by
    simpa [prefixWord, tailWord_5941761, baseEnd_5941761] using wordTrace_append hprefix tailTrace_5941761
  have hstable : (prefixWord ++ tailWord_5941761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5941761).length < 2 ^ (prefixWord ++ tailWord_5941761).sum := by decide
  have hdescent : baseEnd_5941761 < baseStart_5941761 := by decide
  rcases family_descends (prefixWord ++ tailWord_5941761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5941770 : List Nat := [3, 1, 2, 2, 2, 1, 2, 2, 2, 2, 4]
def baseStart_5941770 : Nat := 118140960795 + 5941770 * 2 ^ 59
def prefixEnd_5941770 : Nat := 4983230072969 + 3 ^ 40 * 5941770 * 2
def baseEnd_5941770 : Nat := 3050983948465323031249303

theorem tailTrace_5941770 : CollatzResearch.WordTrace tailWord_5941770 prefixEnd_5941770 3050983948465323031249303 := by
  unfold tailWord_5941770
  simp only [CollatzResearch.WordTrace]
  refine ⟨54178538920997384592715691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144476103789326358913908509 54178538920997384592715691)
  ·
    refine ⟨81267808381496076889073537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54178538920997384592715691 81267808381496076889073537)
    ·
      refine ⟨60950856286122057666805153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81267808381496076889073537 60950856286122057666805153)
      ·
        refine ⟨45713142214591543250103865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60950856286122057666805153 45713142214591543250103865)
        ·
          refine ⟨34284856660943657437577899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45713142214591543250103865 34284856660943657437577899)
          ·
            refine ⟨51427284991415486156366849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34284856660943657437577899 51427284991415486156366849)
            ·
              refine ⟨38570463743561614617275137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51427284991415486156366849 38570463743561614617275137)
              ·
                refine ⟨28927847807671210962956353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38570463743561614617275137 28927847807671210962956353)
                ·
                  refine ⟨21695885855753408222217265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28927847807671210962956353 21695885855753408222217265)
                  ·
                    refine ⟨16271914391815056166662949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21695885855753408222217265 16271914391815056166662949)
                    ·
                      refine ⟨3050983948465323031249303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16271914391815056166662949 3050983948465323031249303)
                      ·
                        rfl

theorem cell23_5941770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_5941770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5941770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5941770 prefixEnd_5941770 := by exact prefixLift 5941770
  have htrace : WordTrace (prefixWord ++ tailWord_5941770) baseStart_5941770 baseEnd_5941770 := by
    simpa [prefixWord, tailWord_5941770, baseEnd_5941770] using wordTrace_append hprefix tailTrace_5941770
  have hstable : (prefixWord ++ tailWord_5941770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5941770).length < 2 ^ (prefixWord ++ tailWord_5941770).sum := by decide
  have hdescent : baseEnd_5941770 < baseStart_5941770 := by decide
  rcases family_descends (prefixWord ++ tailWord_5941770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5941803 : List Nat := [1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 7]
def baseStart_5941803 : Nat := 118140960795 + 5941803 * 2 ^ 59
def prefixEnd_5941803 : Nat := 4983230072969 + 3 ^ 40 * 5941803 * 2
def baseEnd_5941803 : Nat := 3051000893326921402136651

theorem tailTrace_5941803 : CollatzResearch.WordTrace tailWord_5941803 prefixEnd_5941803 3051000893326921402136651 := by
  unfold tailWord_5941803
  simp only [CollatzResearch.WordTrace]
  refine ⟨216715359292869985006814063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144476906195246656671209375 216715359292869985006814063)
  ·
    refine ⟨325073038939304977510221095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216715359292869985006814063 325073038939304977510221095)
    ·
      refine ⟨487609558408957466265331643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325073038939304977510221095 487609558408957466265331643)
      ·
        refine ⟨731414337613436199397997465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 487609558408957466265331643 731414337613436199397997465)
        ·
          refine ⟨548560753210077149548498099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 731414337613436199397997465 548560753210077149548498099)
          ·
            refine ⟨822841129815115724322747149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 548560753210077149548498099 822841129815115724322747149)
            ·
              refine ⟨308565423680668396621030181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 822841129815115724322747149 308565423680668396621030181)
              ·
                refine ⟨57856016940125324366443159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 308565423680668396621030181 57856016940125324366443159)
                ·
                  refine ⟨86784025410187986549664739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57856016940125324366443159 86784025410187986549664739)
                  ·
                    refine ⟨130176038115281979824497109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 86784025410187986549664739 130176038115281979824497109)
                    ·
                      refine ⟨3051000893326921402136651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 130176038115281979824497109 3051000893326921402136651)
                      ·
                        rfl

theorem cell23_5941803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 7].length) (baseStart_5941803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5941803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5941803 prefixEnd_5941803 := by exact prefixLift 5941803
  have htrace : WordTrace (prefixWord ++ tailWord_5941803) baseStart_5941803 baseEnd_5941803 := by
    simpa [prefixWord, tailWord_5941803, baseEnd_5941803] using wordTrace_append hprefix tailTrace_5941803
  have hstable : (prefixWord ++ tailWord_5941803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5941803).length < 2 ^ (prefixWord ++ tailWord_5941803).sum := by decide
  have hdescent : baseEnd_5941803 < baseStart_5941803 := by decide
  rcases family_descends (prefixWord ++ tailWord_5941803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5941812 : List Nat := [2, 5, 1, 3, 2, 1, 2, 1, 1, 3, 2]
def baseStart_5941812 : Nat := 118140960795 + 5941812 * 2 ^ 59
def prefixEnd_5941812 : Nat := 4983230072969 + 3 ^ 40 * 5941812 * 2
def baseEnd_5941812 : Nat := 3051005514652811866924111

theorem tailTrace_5941812 : CollatzResearch.WordTrace tailWord_5941812 prefixEnd_5941812 3051005514652811866924111 := by
  unfold tailWord_5941812
  simp only [CollatzResearch.WordTrace]
  refine ⟨108357843774918689771945845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144477125033224919695927793 108357843774918689771945845)
  ·
    refine ⟨10158547853898627166119923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 108357843774918689771945845 10158547853898627166119923)
    ·
      refine ⟨15237821780847940749179885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10158547853898627166119923 15237821780847940749179885)
      ·
        refine ⟨5714183167817977780942457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15237821780847940749179885 5714183167817977780942457)
        ·
          refine ⟨4285637375863483335706843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5714183167817977780942457 4285637375863483335706843)
          ·
            refine ⟨6428456063795225003560265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4285637375863483335706843 6428456063795225003560265)
            ·
              refine ⟨4821342047846418752670199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6428456063795225003560265 4821342047846418752670199)
              ·
                refine ⟨7232013071769628129005299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4821342047846418752670199 7232013071769628129005299)
                ·
                  refine ⟨10848019607654442193507949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7232013071769628129005299 10848019607654442193507949)
                  ·
                    refine ⟨4068007352870415822565481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10848019607654442193507949 4068007352870415822565481)
                    ·
                      refine ⟨3051005514652811866924111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4068007352870415822565481 3051005514652811866924111)
                      ·
                        rfl

theorem cell23_5941812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_5941812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5941812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5941812 prefixEnd_5941812 := by exact prefixLift 5941812
  have htrace : WordTrace (prefixWord ++ tailWord_5941812) baseStart_5941812 baseEnd_5941812 := by
    simpa [prefixWord, tailWord_5941812, baseEnd_5941812] using wordTrace_append hprefix tailTrace_5941812
  have hstable : (prefixWord ++ tailWord_5941812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5941812).length < 2 ^ (prefixWord ++ tailWord_5941812).sum := by decide
  have hdescent : baseEnd_5941812 < baseStart_5941812 := by decide
  rcases family_descends (prefixWord ++ tailWord_5941812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5941814 : List Nat := [5, 1, 2, 1, 2, 1, 1, 5, 5]
def baseStart_5941814 : Nat := 118140960795 + 5941814 * 2 ^ 59
def prefixEnd_5941814 : Nat := 4983230072969 + 3 ^ 40 * 5941814 * 2
def baseEnd_5941814 : Nat := 339000726846013428788789

theorem tailTrace_5941814 : CollatzResearch.WordTrace tailWord_5941814 prefixEnd_5941814 339000726846013428788789 := by
  unfold tailWord_5941814
  simp only [CollatzResearch.WordTrace]
  refine ⟨13544735030989383367841531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 144477173663886755923642997 13544735030989383367841531)
  ·
    refine ⟨20317102546484075051762297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13544735030989383367841531 20317102546484075051762297)
    ·
      refine ⟨15237826909863056288821723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20317102546484075051762297 15237826909863056288821723)
      ·
        refine ⟨22856740364794584433232585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15237826909863056288821723 22856740364794584433232585)
        ·
          refine ⟨17142555273595938324924439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22856740364794584433232585 17142555273595938324924439)
          ·
            refine ⟨25713832910393907487386659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17142555273595938324924439 25713832910393907487386659)
            ·
              refine ⟨38570749365590861231079989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25713832910393907487386659 38570749365590861231079989)
              ·
                refine ⟨3616007753024143240413749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38570749365590861231079989 3616007753024143240413749)
                ·
                  refine ⟨339000726846013428788789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3616007753024143240413749 339000726846013428788789)
                  ·
                    rfl

theorem cell23_5941814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 5, 5].length) (baseStart_5941814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5941814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5941814 prefixEnd_5941814 := by exact prefixLift 5941814
  have htrace : WordTrace (prefixWord ++ tailWord_5941814) baseStart_5941814 baseEnd_5941814 := by
    simpa [prefixWord, tailWord_5941814, baseEnd_5941814] using wordTrace_append hprefix tailTrace_5941814
  have hstable : (prefixWord ++ tailWord_5941814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5941814).length < 2 ^ (prefixWord ++ tailWord_5941814).sum := by decide
  have hdescent : baseEnd_5941814 < baseStart_5941814 := by decide
  rcases family_descends (prefixWord ++ tailWord_5941814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5941847 : List Nat := [1, 1, 3, 2, 2, 2, 1, 3, 2, 4, 2]
def baseStart_5941847 : Nat := 118140960795 + 5941847 * 2 ^ 59
def prefixEnd_5941847 : Nat := 4983230072969 + 3 ^ 40 * 5941847 * 2
def baseEnd_5941847 : Nat := 3051023486475719229986449

theorem tailTrace_5941847 : CollatzResearch.WordTrace tailWord_5941847 prefixEnd_5941847 3051023486475719229986449 := by
  unfold tailWord_5941847
  simp only [CollatzResearch.WordTrace]
  refine ⟨216716964104710580521415795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144477976069807053680943863 216716964104710580521415795)
  ·
    refine ⟨325075446157065870782123693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216716964104710580521415795 325075446157065870782123693)
    ·
      refine ⟨121903292308899701543296385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 325075446157065870782123693 121903292308899701543296385)
      ·
        refine ⟨91427469231674776157472289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121903292308899701543296385 91427469231674776157472289)
        ·
          refine ⟨68570601923756082118104217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91427469231674776157472289 68570601923756082118104217)
          ·
            refine ⟨51427951442817061588578163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68570601923756082118104217 51427951442817061588578163)
            ·
              refine ⟨77141927164225592382867245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51427951442817061588578163 77141927164225592382867245)
              ·
                refine ⟨28928222686584597143575217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77141927164225592382867245 28928222686584597143575217)
                ·
                  refine ⟨21696167014938447857681413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28928222686584597143575217 21696167014938447857681413)
                  ·
                    refine ⟨4068031315300958973315265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21696167014938447857681413 4068031315300958973315265)
                    ·
                      refine ⟨3051023486475719229986449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4068031315300958973315265 3051023486475719229986449)
                      ·
                        rfl

theorem cell23_5941847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 2, 4, 2].length) (baseStart_5941847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5941847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5941847 prefixEnd_5941847 := by exact prefixLift 5941847
  have htrace : WordTrace (prefixWord ++ tailWord_5941847) baseStart_5941847 baseEnd_5941847 := by
    simpa [prefixWord, tailWord_5941847, baseEnd_5941847] using wordTrace_append hprefix tailTrace_5941847
  have hstable : (prefixWord ++ tailWord_5941847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5941847).length < 2 ^ (prefixWord ++ tailWord_5941847).sum := by decide
  have hdescent : baseEnd_5941847 < baseStart_5941847 := by decide
  rcases family_descends (prefixWord ++ tailWord_5941847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5941857 : List Nat := [1, 2, 3, 1, 1, 4, 2, 2, 3, 4]
def baseStart_5941857 : Nat := 118140960795 + 5941857 * 2 ^ 59
def prefixEnd_5941857 : Nat := 4983230072969 + 3 ^ 40 * 5941857 * 2
def baseEnd_5941857 : Nat := 1017009540427421396953801

theorem tailTrace_5941857 : CollatzResearch.WordTrace tailWord_5941857 prefixEnd_5941857 1017009540427421396953801 := by
  unfold tailWord_5941857
  simp only [CollatzResearch.WordTrace]
  refine ⟨216717328834674352229279825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144478219223116234819519883 216717328834674352229279825)
  ·
    refine ⟨162537996626005764171959869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216717328834674352229279825 162537996626005764171959869)
    ·
      refine ⟨60951748734752161564484951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162537996626005764171959869 60951748734752161564484951)
      ·
        refine ⟨91427623102128242346727427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60951748734752161564484951 91427623102128242346727427)
        ·
          refine ⟨137141434653192363520091141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91427623102128242346727427 137141434653192363520091141)
          ·
            refine ⟨25714018997473568160017089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 137141434653192363520091141 25714018997473568160017089)
            ·
              refine ⟨19285514248105176120012817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25714018997473568160017089 19285514248105176120012817)
              ·
                refine ⟨14464135686078882090009613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19285514248105176120012817 14464135686078882090009613)
                ·
                  refine ⟨5424050882279580783753605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14464135686078882090009613 5424050882279580783753605)
                  ·
                    refine ⟨1017009540427421396953801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5424050882279580783753605 1017009540427421396953801)
                    ·
                      rfl

theorem cell23_5941857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 2, 3, 4].length) (baseStart_5941857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5941857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5941857 prefixEnd_5941857 := by exact prefixLift 5941857
  have htrace : WordTrace (prefixWord ++ tailWord_5941857) baseStart_5941857 baseEnd_5941857 := by
    simpa [prefixWord, tailWord_5941857, baseEnd_5941857] using wordTrace_append hprefix tailTrace_5941857
  have hstable : (prefixWord ++ tailWord_5941857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5941857).length < 2 ^ (prefixWord ++ tailWord_5941857).sum := by decide
  have hdescent : baseEnd_5941857 < baseStart_5941857 := by decide
  rcases family_descends (prefixWord ++ tailWord_5941857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5941860 : List Nat := [2, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4]
def baseStart_5941860 : Nat := 118140960795 + 5941860 * 2 ^ 59
def prefixEnd_5941860 : Nat := 4983230072969 + 3 ^ 40 * 5941860 * 2
def baseEnd_5941860 : Nat := 3051030161724227679123889

theorem tailTrace_5941860 : CollatzResearch.WordTrace tailWord_5941860 prefixEnd_5941860 3051030161724227679123889 := by
  unfold tailWord_5941860
  simp only [CollatzResearch.WordTrace]
  refine ⟨108358719126831741870819517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144478292169108989161092689 108358719126831741870819517)
  ·
    refine ⟨40634519672561903201557319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108358719126831741870819517 40634519672561903201557319)
    ·
      refine ⟨60951779508842854802335979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40634519672561903201557319 60951779508842854802335979)
      ·
        refine ⟨91427669263264282203503969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60951779508842854802335979 91427669263264282203503969)
        ·
          refine ⟨68570751947448211652627977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91427669263264282203503969 68570751947448211652627977)
          ·
            refine ⟨51428063960586158739470983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68570751947448211652627977 51428063960586158739470983)
            ·
              refine ⟨77142095940879238109206475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51428063960586158739470983 77142095940879238109206475)
              ·
                refine ⟨115713143911318857163809713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77142095940879238109206475 115713143911318857163809713)
                ·
                  refine ⟨86784857933489142872857285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115713143911318857163809713 86784857933489142872857285)
                  ·
                    refine ⟨16272160862529214288660741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 86784857933489142872857285 16272160862529214288660741)
                    ·
                      refine ⟨3051030161724227679123889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16272160862529214288660741 3051030161724227679123889)
                      ·
                        rfl

theorem cell23_5941860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4].length) (baseStart_5941860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5941860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5941860 prefixEnd_5941860 := by exact prefixLift 5941860
  have htrace : WordTrace (prefixWord ++ tailWord_5941860) baseStart_5941860 baseEnd_5941860 := by
    simpa [prefixWord, tailWord_5941860, baseEnd_5941860] using wordTrace_append hprefix tailTrace_5941860
  have hstable : (prefixWord ++ tailWord_5941860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5941860).length < 2 ^ (prefixWord ++ tailWord_5941860).sum := by decide
  have hdescent : baseEnd_5941860 < baseStart_5941860 := by decide
  rcases family_descends (prefixWord ++ tailWord_5941860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5941880 : List Nat := [2, 1, 2, 1, 1, 1, 2, 2, 1, 7, 3]
def baseStart_5941880 : Nat := 118140960795 + 5941880 * 2 ^ 59
def prefixEnd_5941880 : Nat := 4983230072969 + 3 ^ 40 * 5941880 * 2
def baseEnd_5941880 : Nat := 3051040431337317600873797

theorem tailTrace_5941880 : CollatzResearch.WordTrace tailWord_5941880 prefixEnd_5941880 3051040431337317600873797 := by
  unfold tailWord_5941880
  simp only [CollatzResearch.WordTrace]
  refine ⟨108359083856795513578683547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144478778475727351438244729 108359083856795513578683547)
  ·
    refine ⟨162538625785193270368025321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108359083856795513578683547 162538625785193270368025321)
    ·
      refine ⟨121903969338894952776018991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162538625785193270368025321 121903969338894952776018991)
      ·
        refine ⟨182855954008342429164028487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121903969338894952776018991 182855954008342429164028487)
        ·
          refine ⟨274283931012513643746042731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182855954008342429164028487 274283931012513643746042731)
          ·
            refine ⟨411425896518770465619064097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274283931012513643746042731 411425896518770465619064097)
            ·
              refine ⟨308569422389077849214298073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 411425896518770465619064097 308569422389077849214298073)
              ·
                refine ⟨231427066791808386910723555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 308569422389077849214298073 231427066791808386910723555)
                ·
                  refine ⟨347140600187712580366085333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 231427066791808386910723555 347140600187712580366085333)
                  ·
                    refine ⟨8136107816899513602330125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 347140600187712580366085333 8136107816899513602330125)
                    ·
                      refine ⟨3051040431337317600873797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8136107816899513602330125 3051040431337317600873797)
                      ·
                        rfl

theorem cell23_5941880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 1, 7, 3].length) (baseStart_5941880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5941880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5941880 prefixEnd_5941880 := by exact prefixLift 5941880
  have htrace : WordTrace (prefixWord ++ tailWord_5941880) baseStart_5941880 baseEnd_5941880 := by
    simpa [prefixWord, tailWord_5941880, baseEnd_5941880] using wordTrace_append hprefix tailTrace_5941880
  have hstable : (prefixWord ++ tailWord_5941880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5941880).length < 2 ^ (prefixWord ++ tailWord_5941880).sum := by decide
  have hdescent : baseEnd_5941880 < baseStart_5941880 := by decide
  rcases family_descends (prefixWord ++ tailWord_5941880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5941941 : List Nat := [1, 3, 3, 3, 1, 1, 2, 2, 2, 3, 2]
def baseStart_5941941 : Nat := 118140960795 + 5941941 * 2 ^ 59
def prefixEnd_5941941 : Nat := 4983230072969 + 3 ^ 40 * 5941941 * 2
def baseEnd_5941941 : Nat := 3051071753657241862211017

theorem tailTrace_5941941 : CollatzResearch.WordTrace tailWord_5941941 prefixEnd_5941941 3051071753657241862211017 := by
  unfold tailWord_5941941
  simp only [CollatzResearch.WordTrace]
  refine ⟨216720392566370034575337677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144480261710913356383558451 216720392566370034575337677)
  ·
    refine ⟨81270147212388762965751629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216720392566370034575337677 81270147212388762965751629)
    ·
      refine ⟨30476305204645786112156861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81270147212388762965751629 30476305204645786112156861)
      ·
        refine ⟨11428614451742169792058823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30476305204645786112156861 11428614451742169792058823)
        ·
          refine ⟨17142921677613254688088235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11428614451742169792058823 17142921677613254688088235)
          ·
            refine ⟨25714382516419882032132353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17142921677613254688088235 25714382516419882032132353)
            ·
              refine ⟨19285786887314911524099265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25714382516419882032132353 19285786887314911524099265)
              ·
                refine ⟨14464340165486183643074449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19285786887314911524099265 14464340165486183643074449)
                ·
                  refine ⟨10848255124114637732305837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14464340165486183643074449 10848255124114637732305837)
                  ·
                    refine ⟨4068095671542989149614689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10848255124114637732305837 4068095671542989149614689)
                    ·
                      refine ⟨3051071753657241862211017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4068095671542989149614689 3051071753657241862211017)
                      ·
                        rfl

theorem cell23_5941941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_5941941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5941941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5941941 prefixEnd_5941941 := by exact prefixLift 5941941
  have htrace : WordTrace (prefixWord ++ tailWord_5941941) baseStart_5941941 baseEnd_5941941 := by
    simpa [prefixWord, tailWord_5941941, baseEnd_5941941] using wordTrace_append hprefix tailTrace_5941941
  have hstable : (prefixWord ++ tailWord_5941941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5941941).length < 2 ^ (prefixWord ++ tailWord_5941941).sum := by decide
  have hdescent : baseEnd_5941941 < baseStart_5941941 := by decide
  rcases family_descends (prefixWord ++ tailWord_5941941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5941942 : List Nat := [5, 1, 3, 1, 2, 2, 2, 2, 1, 4]
def baseStart_5941942 : Nat := 118140960795 + 5941942 * 2 ^ 59
def prefixEnd_5941942 : Nat := 4983230072969 + 3 ^ 40 * 5941942 * 2
def baseEnd_5941942 : Nat := 1017024089045965452766171

theorem tailTrace_5941942 : CollatzResearch.WordTrace tailWord_5941942 prefixEnd_5941942 1017024089045965452766171 := by
  unfold tailWord_5941942
  simp only [CollatzResearch.WordTrace]
  refine ⟨13545026814960400734132755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 144480286026244274497416053 13545026814960400734132755)
  ·
    refine ⟨20317540222440601101199133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13545026814960400734132755 20317540222440601101199133)
    ·
      refine ⟨7619077583415225412949675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20317540222440601101199133 7619077583415225412949675)
      ·
        refine ⟨11428616375122838119424513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7619077583415225412949675 11428616375122838119424513)
        ·
          refine ⟨8571462281342128589568385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11428616375122838119424513 8571462281342128589568385)
          ·
            refine ⟨6428596711006596442176289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8571462281342128589568385 6428596711006596442176289)
            ·
              refine ⟨4821447533254947331632217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6428596711006596442176289 4821447533254947331632217)
              ·
                refine ⟨3616085649941210498724163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4821447533254947331632217 3616085649941210498724163)
                ·
                  refine ⟨5424128474911815748086245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3616085649941210498724163 5424128474911815748086245)
                  ·
                    refine ⟨1017024089045965452766171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5424128474911815748086245 1017024089045965452766171)
                    ·
                      rfl

theorem cell23_5941942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_5941942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5941942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5941942 prefixEnd_5941942 := by exact prefixLift 5941942
  have htrace : WordTrace (prefixWord ++ tailWord_5941942) baseStart_5941942 baseEnd_5941942 := by
    simpa [prefixWord, tailWord_5941942, baseEnd_5941942] using wordTrace_append hprefix tailTrace_5941942
  have hstable : (prefixWord ++ tailWord_5941942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5941942).length < 2 ^ (prefixWord ++ tailWord_5941942).sum := by decide
  have hdescent : baseEnd_5941942 < baseStart_5941942 := by decide
  rcases family_descends (prefixWord ++ tailWord_5941942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5941964 : List Nat := [2, 2, 1, 5, 1, 2, 2, 1, 1, 6]
def baseStart_5941964 : Nat := 118140960795 + 5941964 * 2 ^ 59
def prefixEnd_5941964 : Nat := 4983230072969 + 3 ^ 40 * 5941964 * 2
def baseEnd_5941964 : Nat := 1017027854570765090741137

theorem tailTrace_5941964 : CollatzResearch.WordTrace tailWord_5941964 prefixEnd_5941964 1017027854570765090741137 := by
  unfold tailWord_5941964
  simp only [CollatzResearch.WordTrace]
  refine ⟨108360615722643354751712473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144480820963524473002283297 108360615722643354751712473)
  ·
    refine ⟨81270461791982516063784355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108360615722643354751712473 81270461791982516063784355)
    ·
      refine ⟨121905692687973774095676533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81270461791982516063784355 121905692687973774095676533)
      ·
        refine ⟨11428658689497541321469675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 121905692687973774095676533 11428658689497541321469675)
        ·
          refine ⟨17142988034246311982204513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11428658689497541321469675 17142988034246311982204513)
          ·
            refine ⟨12857241025684733986653385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17142988034246311982204513 12857241025684733986653385)
            ·
              refine ⟨9642930769263550489990039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12857241025684733986653385 9642930769263550489990039)
              ·
                refine ⟨14464396153895325734985059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9642930769263550489990039 14464396153895325734985059)
                ·
                  refine ⟨21696594230842988602477589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14464396153895325734985059 21696594230842988602477589)
                  ·
                    refine ⟨1017027854570765090741137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21696594230842988602477589 1017027854570765090741137)
                    ·
                      rfl

theorem cell23_5941964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 1, 1, 6].length) (baseStart_5941964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5941964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5941964 prefixEnd_5941964 := by exact prefixLift 5941964
  have htrace : WordTrace (prefixWord ++ tailWord_5941964) baseStart_5941964 baseEnd_5941964 := by
    simpa [prefixWord, tailWord_5941964, baseEnd_5941964] using wordTrace_append hprefix tailTrace_5941964
  have hstable : (prefixWord ++ tailWord_5941964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5941964).length < 2 ^ (prefixWord ++ tailWord_5941964).sum := by decide
  have hdescent : baseEnd_5941964 < baseStart_5941964 := by decide
  rcases family_descends (prefixWord ++ tailWord_5941964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5941977 : List Nat := [1, 2, 1, 2, 3, 2, 5, 7]
def baseStart_5941977 : Nat := 118140960795 + 5941977 * 2 ^ 59
def prefixEnd_5941977 : Nat := 4983230072969 + 3 ^ 40 * 5941977 * 2
def baseEnd_5941977 : Nat := 113003342183733471161513

theorem tailTrace_5941977 : CollatzResearch.WordTrace tailWord_5941977 prefixEnd_5941977 113003342183733471161513 := by
  unfold tailWord_5941977
  simp only [CollatzResearch.WordTrace]
  refine ⟨216721705594239612723648185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144481137062826408482432123 216721705594239612723648185)
  ·
    refine ⟨162541279195679709542736139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216721705594239612723648185 162541279195679709542736139)
    ·
      refine ⟨243811918793519564314104209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162541279195679709542736139 243811918793519564314104209)
      ·
        refine ⟨182858939095139673235578157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243811918793519564314104209 182858939095139673235578157)
        ·
          refine ⟨68572102160677377463341809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182858939095139673235578157 68572102160677377463341809)
          ·
            refine ⟨51429076620508033097506357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68572102160677377463341809 51429076620508033097506357)
            ·
              refine ⟨4821475933172628102891221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51429076620508033097506357 4821475933172628102891221)
              ·
                refine ⟨113003342183733471161513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4821475933172628102891221 113003342183733471161513)
                ·
                  rfl

theorem cell23_5941977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 5, 7].length) (baseStart_5941977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5941977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5941977 prefixEnd_5941977 := by exact prefixLift 5941977
  have htrace : WordTrace (prefixWord ++ tailWord_5941977) baseStart_5941977 baseEnd_5941977 := by
    simpa [prefixWord, tailWord_5941977, baseEnd_5941977] using wordTrace_append hprefix tailTrace_5941977
  have hstable : (prefixWord ++ tailWord_5941977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5941977).length < 2 ^ (prefixWord ++ tailWord_5941977).sum := by decide
  have hdescent : baseEnd_5941977 < baseStart_5941977 := by decide
  rcases family_descends (prefixWord ++ tailWord_5941977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5941988 : List Nat := [2, 3, 1, 1, 1, 4, 1, 5, 1, 2, 2]
def baseStart_5941988 : Nat := 118140960795 + 5941988 * 2 ^ 59
def prefixEnd_5941988 : Nat := 4983230072969 + 3 ^ 40 * 5941988 * 2
def baseEnd_5941988 : Nat := 3051095887248003178323301

theorem tailTrace_5941988 : CollatzResearch.WordTrace tailWord_5941988 prefixEnd_5941988 3051095887248003178323301 := by
  unfold tailWord_5941988
  simp only [CollatzResearch.WordTrace]
  refine ⟨108361053398599880801149309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144481404531466507734865745 108361053398599880801149309)
  ·
    refine ⟨40635395024474955300430991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108361053398599880801149309 40635395024474955300430991)
    ·
      refine ⟨60953092536712432950646487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40635395024474955300430991 60953092536712432950646487)
      ·
        refine ⟨91429638805068649425969731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60953092536712432950646487 91429638805068649425969731)
        ·
          refine ⟨137144458207602974138954597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91429638805068649425969731 137144458207602974138954597)
          ·
            refine ⟨25714585913925557651053987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 137144458207602974138954597 25714585913925557651053987)
            ·
              refine ⟨38571878870888336476580981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25714585913925557651053987 38571878870888336476580981)
              ·
                refine ⟨3616113644145781544679467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38571878870888336476580981 3616113644145781544679467)
                ·
                  refine ⟨5424170466218672317019201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3616113644145781544679467 5424170466218672317019201)
                  ·
                    refine ⟨4068127849664004237764401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5424170466218672317019201 4068127849664004237764401)
                    ·
                      refine ⟨3051095887248003178323301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4068127849664004237764401 3051095887248003178323301)
                      ·
                        rfl

theorem cell23_5941988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 5, 1, 2, 2].length) (baseStart_5941988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5941988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5941988 prefixEnd_5941988 := by exact prefixLift 5941988
  have htrace : WordTrace (prefixWord ++ tailWord_5941988) baseStart_5941988 baseEnd_5941988 := by
    simpa [prefixWord, tailWord_5941988, baseEnd_5941988] using wordTrace_append hprefix tailTrace_5941988
  have hstable : (prefixWord ++ tailWord_5941988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5941988).length < 2 ^ (prefixWord ++ tailWord_5941988).sum := by decide
  have hdescent : baseEnd_5941988 < baseStart_5941988 := by decide
  rcases family_descends (prefixWord ++ tailWord_5941988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5942031 : List Nat := [1, 1, 2, 1, 1, 1, 8, 2, 1, 3, 2]
def baseStart_5942031 : Nat := 118140960795 + 5942031 * 2 ^ 59
def prefixEnd_5942031 : Nat := 4983230072969 + 3 ^ 40 * 5942031 * 2
def baseEnd_5942031 : Nat := 3051117966916146510085603

theorem tailTrace_5942031 : CollatzResearch.WordTrace tailWord_5942031 prefixEnd_5942031 3051117966916146510085603 := by
  unfold tailWord_5942031
  simp only [CollatzResearch.WordTrace]
  refine ⟨216723675136043979946113947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144482450090695986630742631 216723675136043979946113947)
  ·
    refine ⟨325085512704065969919170921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216723675136043979946113947 325085512704065969919170921)
    ·
      refine ⟨243814134528049477439378191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 325085512704065969919170921 243814134528049477439378191)
      ·
        refine ⟨365721201792074216159067287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243814134528049477439378191 365721201792074216159067287)
        ·
          refine ⟨548581802688111324238600931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365721201792074216159067287 548581802688111324238600931)
          ·
            refine ⟨822872704032166986357901397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 548581802688111324238600931 822872704032166986357901397)
            ·
              refine ⟨9643039500376956871381657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 822872704032166986357901397 9643039500376956871381657)
              ·
                refine ⟨7232279625282717653536243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9643039500376956871381657 7232279625282717653536243)
                ·
                  refine ⟨10848419437924076480304365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7232279625282717653536243 10848419437924076480304365)
                  ·
                    refine ⟨4068157289221528680114137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10848419437924076480304365 4068157289221528680114137)
                    ·
                      refine ⟨3051117966916146510085603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4068157289221528680114137 3051117966916146510085603)
                      ·
                        rfl

theorem cell23_5942031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 2, 1, 3, 2].length) (baseStart_5942031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5942031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5942031 prefixEnd_5942031 := by exact prefixLift 5942031
  have htrace : WordTrace (prefixWord ++ tailWord_5942031) baseStart_5942031 baseEnd_5942031 := by
    simpa [prefixWord, tailWord_5942031, baseEnd_5942031] using wordTrace_append hprefix tailTrace_5942031
  have hstable : (prefixWord ++ tailWord_5942031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5942031).length < 2 ^ (prefixWord ++ tailWord_5942031).sum := by decide
  have hdescent : baseEnd_5942031 < baseStart_5942031 := by decide
  rcases family_descends (prefixWord ++ tailWord_5942031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5942047 : List Nat := [1, 1, 2, 4, 2, 2, 1, 1, 1, 3, 5]
def baseStart_5942047 : Nat := 118140960795 + 5942047 * 2 ^ 59
def prefixEnd_5942047 : Nat := 4983230072969 + 3 ^ 40 * 5942047 * 2
def baseEnd_5942047 : Nat := 3051126182606618447485529

theorem tailTrace_5942047 : CollatzResearch.WordTrace tailWord_5942047 prefixEnd_5942047 3051126182606618447485529 := by
  unfold tailWord_5942047
  simp only [CollatzResearch.WordTrace]
  refine ⟨216724258703986014678696395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144482839135990676452464263 216724258703986014678696395)
  ·
    refine ⟨325086388055979022018044593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216724258703986014678696395 325086388055979022018044593)
    ·
      refine ⟨243814791041984266513533445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 325086388055979022018044593 243814791041984266513533445)
      ·
        refine ⟨45715273320372049971287521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 243814791041984266513533445 45715273320372049971287521)
        ·
          refine ⟨34286454990279037478465641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45715273320372049971287521 34286454990279037478465641)
          ·
            refine ⟨25714841242709278108849231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34286454990279037478465641 25714841242709278108849231)
            ·
              refine ⟨38572261864063917163273847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25714841242709278108849231 38572261864063917163273847)
              ·
                refine ⟨57858392796095875744910771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38572261864063917163273847 57858392796095875744910771)
                ·
                  refine ⟨86787589194143813617366157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57858392796095875744910771 86787589194143813617366157)
                  ·
                    refine ⟨32545345947803930106512309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 86787589194143813617366157 32545345947803930106512309)
                    ·
                      refine ⟨3051126182606618447485529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32545345947803930106512309 3051126182606618447485529)
                      ·
                        rfl

theorem cell23_5942047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_5942047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5942047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5942047 prefixEnd_5942047 := by exact prefixLift 5942047
  have htrace : WordTrace (prefixWord ++ tailWord_5942047) baseStart_5942047 baseEnd_5942047 := by
    simpa [prefixWord, tailWord_5942047, baseEnd_5942047] using wordTrace_append hprefix tailTrace_5942047
  have hstable : (prefixWord ++ tailWord_5942047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5942047).length < 2 ^ (prefixWord ++ tailWord_5942047).sum := by decide
  have hdescent : baseEnd_5942047 < baseStart_5942047 := by decide
  rcases family_descends (prefixWord ++ tailWord_5942047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5942104 : List Nat := [2, 1, 2, 2, 1, 1, 1, 2, 4, 5, 2]
def baseStart_5942104 : Nat := 118140960795 + 5942104 * 2 ^ 59
def prefixEnd_5942104 : Nat := 4983230072969 + 3 ^ 40 * 5942104 * 2
def baseEnd_5942104 : Nat := 3051155451003924724472767

theorem tailTrace_5942104 : CollatzResearch.WordTrace tailWord_5942104 prefixEnd_5942104 3051155451003924724472767 := by
  unfold tailWord_5942104
  simp only [CollatzResearch.WordTrace]
  refine ⟨108363168832389756706760683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144484225109853008942347577 108363168832389756706760683)
  ·
    refine ⟨162544753248584635060141025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108363168832389756706760683 162544753248584635060141025)
    ·
      refine ⟨121908564936438476295105769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162544753248584635060141025 121908564936438476295105769)
      ·
        refine ⟨91431423702328857221329327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121908564936438476295105769 91431423702328857221329327)
        ·
          refine ⟨137147135553493285831993991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91431423702328857221329327 137147135553493285831993991)
          ·
            refine ⟨205720703330239928747990987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137147135553493285831993991 205720703330239928747990987)
            ·
              refine ⟨308581054995359893121986481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205720703330239928747990987 308581054995359893121986481)
              ·
                refine ⟨231435791246519919841489861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 308581054995359893121986481 231435791246519919841489861)
                ·
                  refine ⟨43394210858722484970279349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 231435791246519919841489861 43394210858722484970279349)
                  ·
                    refine ⟨4068207268005232965963689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43394210858722484970279349 4068207268005232965963689)
                    ·
                      refine ⟨3051155451003924724472767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4068207268005232965963689 3051155451003924724472767)
                      ·
                        rfl

theorem cell23_5942104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 4, 5, 2].length) (baseStart_5942104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5942104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5942104 prefixEnd_5942104 := by exact prefixLift 5942104
  have htrace : WordTrace (prefixWord ++ tailWord_5942104) baseStart_5942104 baseEnd_5942104 := by
    simpa [prefixWord, tailWord_5942104, baseEnd_5942104] using wordTrace_append hprefix tailTrace_5942104
  have hstable : (prefixWord ++ tailWord_5942104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5942104).length < 2 ^ (prefixWord ++ tailWord_5942104).sum := by decide
  have hdescent : baseEnd_5942104 < baseStart_5942104 := by decide
  rcases family_descends (prefixWord ++ tailWord_5942104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5942151 : List Nat := [1, 1, 4, 2, 3, 1, 3, 1, 2, 1, 4]
def baseStart_5942151 : Nat := 118140960795 + 5942151 * 2 ^ 59
def prefixEnd_5942151 : Nat := 4983230072969 + 3 ^ 40 * 5942151 * 2
def baseEnd_5942151 : Nat := 3051179584594686040585051

theorem tailTrace_5942151 : CollatzResearch.WordTrace tailWord_5942151 prefixEnd_5942151 3051179584594686040585051 := by
  unfold tailWord_5942151
  simp only [CollatzResearch.WordTrace]
  refine ⟨216728051895609240440482307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144485367930406160293654871 216728051895609240440482307)
  ·
    refine ⟨325092077843413860660723461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216728051895609240440482307 325092077843413860660723461)
    ·
      refine ⟨60954764595640098873885649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 325092077843413860660723461 60954764595640098873885649)
      ·
        refine ⟨45716073446730074155414237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60954764595640098873885649 45716073446730074155414237)
        ·
          refine ⟨17143527542523777808280339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45716073446730074155414237 17143527542523777808280339)
          ·
            refine ⟨25715291313785666712420509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17143527542523777808280339 25715291313785666712420509)
            ·
              refine ⟨9643234242669625017157691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25715291313785666712420509 9643234242669625017157691)
              ·
                refine ⟨14464851364004437525736537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9643234242669625017157691 14464851364004437525736537)
                ·
                  refine ⟨10848638523003328144302403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14464851364004437525736537 10848638523003328144302403)
                  ·
                    refine ⟨16272957784504992216453605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10848638523003328144302403 16272957784504992216453605)
                    ·
                      refine ⟨3051179584594686040585051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16272957784504992216453605 3051179584594686040585051)
                      ·
                        rfl

theorem cell23_5942151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 1, 2, 1, 4].length) (baseStart_5942151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5942151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5942151 prefixEnd_5942151 := by exact prefixLift 5942151
  have htrace : WordTrace (prefixWord ++ tailWord_5942151) baseStart_5942151 baseEnd_5942151 := by
    simpa [prefixWord, tailWord_5942151, baseEnd_5942151] using wordTrace_append hprefix tailTrace_5942151
  have hstable : (prefixWord ++ tailWord_5942151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5942151).length < 2 ^ (prefixWord ++ tailWord_5942151).sum := by decide
  have hdescent : baseEnd_5942151 < baseStart_5942151 := by decide
  rcases family_descends (prefixWord ++ tailWord_5942151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5942164 : List Nat := [2, 4, 2, 1, 1, 1, 1, 1, 1, 3, 6]
def baseStart_5942164 : Nat := 118140960795 + 5942164 * 2 ^ 59
def prefixEnd_5942164 : Nat := 4983230072969 + 3 ^ 40 * 5942164 * 2
def baseEnd_5942164 : Nat := 3051186259843194489722491

theorem tailTrace_5942164 : CollatzResearch.WordTrace tailWord_5942164 prefixEnd_5942164 3051186259843194489722491 := by
  unfold tailWord_5942164
  simp only [CollatzResearch.WordTrace]
  refine ⟨108364263022281071830352773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144485684029708095773803697 108364263022281071830352773)
  ·
    refine ⟨20318299316677700968191145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108364263022281071830352773 20318299316677700968191145)
    ·
      refine ⟨15238724487508275726143359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20318299316677700968191145 15238724487508275726143359)
      ·
        refine ⟨22858086731262413589215039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15238724487508275726143359 22858086731262413589215039)
        ·
          refine ⟨34287130096893620383822559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22858086731262413589215039 34287130096893620383822559)
          ·
            refine ⟨51430695145340430575733839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34287130096893620383822559 51430695145340430575733839)
            ·
              refine ⟨77146042718010645863600759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51430695145340430575733839 77146042718010645863600759)
              ·
                refine ⟨115719064077015968795401139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77146042718010645863600759 115719064077015968795401139)
                ·
                  refine ⟨173578596115523953193101709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115719064077015968795401139 173578596115523953193101709)
                  ·
                    refine ⟨65091973543321482447413141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 173578596115523953193101709 65091973543321482447413141)
                    ·
                      refine ⟨3051186259843194489722491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65091973543321482447413141 3051186259843194489722491)
                      ·
                        rfl

theorem cell23_5942164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_5942164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5942164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5942164 prefixEnd_5942164 := by exact prefixLift 5942164
  have htrace : WordTrace (prefixWord ++ tailWord_5942164) baseStart_5942164 baseEnd_5942164 := by
    simpa [prefixWord, tailWord_5942164, baseEnd_5942164] using wordTrace_append hprefix tailTrace_5942164
  have hstable : (prefixWord ++ tailWord_5942164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5942164).length < 2 ^ (prefixWord ++ tailWord_5942164).sum := by decide
  have hdescent : baseEnd_5942164 < baseStart_5942164 := by decide
  rcases family_descends (prefixWord ++ tailWord_5942164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5942178 : List Nat := [3, 3, 1, 2, 2, 2, 2, 1, 3, 4]
def baseStart_5942178 : Nat := 118140960795 + 5942178 * 2 ^ 59
def prefixEnd_5942178 : Nat := 4983230072969 + 3 ^ 40 * 5942178 * 2
def baseEnd_5942178 : Nat := 1017064482857452478315809

theorem tailTrace_5942178 : CollatzResearch.WordTrace tailWord_5942178 prefixEnd_5942178 1017064482857452478315809 := by
  unfold tailWord_5942178
  simp only [CollatzResearch.WordTrace]
  refine ⟨54182259166627856012928797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144486024444340949367810125 54182259166627856012928797)
  ·
    refine ⟨20318347187485446004848299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54182259166627856012928797 20318347187485446004848299)
    ·
      refine ⟨30477520781228169007272449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20318347187485446004848299 30477520781228169007272449)
      ·
        refine ⟨22858140585921126755454337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30477520781228169007272449 22858140585921126755454337)
        ·
          refine ⟨17143605439440845066590753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22858140585921126755454337 17143605439440845066590753)
          ·
            refine ⟨12857704079580633799943065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17143605439440845066590753 12857704079580633799943065)
            ·
              refine ⟨9643278059685475349957299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12857704079580633799943065 9643278059685475349957299)
              ·
                refine ⟨14464917089528213024935949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9643278059685475349957299 14464917089528213024935949)
                ·
                  refine ⟨5424343908573079884350981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14464917089528213024935949 5424343908573079884350981)
                  ·
                    refine ⟨1017064482857452478315809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5424343908573079884350981 1017064482857452478315809)
                    ·
                      rfl

theorem cell23_5942178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 1, 3, 4].length) (baseStart_5942178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5942178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5942178 prefixEnd_5942178 := by exact prefixLift 5942178
  have htrace : WordTrace (prefixWord ++ tailWord_5942178) baseStart_5942178 baseEnd_5942178 := by
    simpa [prefixWord, tailWord_5942178, baseEnd_5942178] using wordTrace_append hprefix tailTrace_5942178
  have hstable : (prefixWord ++ tailWord_5942178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5942178).length < 2 ^ (prefixWord ++ tailWord_5942178).sum := by decide
  have hdescent : baseEnd_5942178 < baseStart_5942178 := by decide
  rcases family_descends (prefixWord ++ tailWord_5942178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5942224 : List Nat := [2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 4]
def baseStart_5942224 : Nat := 118140960795 + 5942224 * 2 ^ 59
def prefixEnd_5942224 : Nat := 4983230072969 + 3 ^ 40 * 5942224 * 2
def baseEnd_5942224 : Nat := 3051217068682464254972215

theorem tailTrace_5942224 : CollatzResearch.WordTrace tailWord_5942224 prefixEnd_5942224 3051217068682464254972215 := by
  unfold tailWord_5942224
  simp only [CollatzResearch.WordTrace]
  refine ⟨108365357212172386953944863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144487142949563182605259817 108365357212172386953944863)
  ·
    refine ⟨162548035818258580430917295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108365357212172386953944863 162548035818258580430917295)
    ·
      refine ⟨243822053727387870646375943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162548035818258580430917295 243822053727387870646375943)
      ·
        refine ⟨365733080591081805969563915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243822053727387870646375943 365733080591081805969563915)
        ·
          refine ⟨548599620886622708954345873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365733080591081805969563915 548599620886622708954345873)
          ·
            refine ⟨411449715664967031715759405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 548599620886622708954345873 411449715664967031715759405)
            ·
              refine ⟨154293643374362636893409777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 411449715664967031715759405 154293643374362636893409777)
              ·
                refine ⟨115720232530771977670057333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154293643374362636893409777 115720232530771977670057333)
                ·
                  refine ⟨10848771799759872906567875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 115720232530771977670057333 10848771799759872906567875)
                  ·
                    refine ⟨16273157699639809359851813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10848771799759872906567875 16273157699639809359851813)
                    ·
                      refine ⟨3051217068682464254972215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16273157699639809359851813 3051217068682464254972215)
                      ·
                        rfl

theorem cell23_5942224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 4].length) (baseStart_5942224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5942224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5942224 prefixEnd_5942224 := by exact prefixLift 5942224
  have htrace : WordTrace (prefixWord ++ tailWord_5942224) baseStart_5942224 baseEnd_5942224 := by
    simpa [prefixWord, tailWord_5942224, baseEnd_5942224] using wordTrace_append hprefix tailTrace_5942224
  have hstable : (prefixWord ++ tailWord_5942224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5942224).length < 2 ^ (prefixWord ++ tailWord_5942224).sum := by decide
  have hdescent : baseEnd_5942224 < baseStart_5942224 := by decide
  rcases family_descends (prefixWord ++ tailWord_5942224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5942228 : List Nat := [2, 4, 1, 2, 1, 2, 1, 1, 4, 3, 2]
def baseStart_5942228 : Nat := 118140960795 + 5942228 * 2 ^ 59
def prefixEnd_5942228 : Nat := 4983230072969 + 3 ^ 40 * 5942228 * 2
def baseEnd_5942228 : Nat := 3051219122605082239322197

theorem tailTrace_5942228 : CollatzResearch.WordTrace tailWord_5942228 prefixEnd_5942228 3051219122605082239322197 := by
  unfold tailWord_5942228
  simp only [CollatzResearch.WordTrace]
  refine ⟨108365430158165141295517669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144487240210886855060690225 108365430158165141295517669)
  ·
    refine ⟨20318518154655963992909563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108365430158165141295517669 20318518154655963992909563)
    ·
      refine ⟨30477777231983945989364345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20318518154655963992909563 30477777231983945989364345)
      ·
        refine ⟨22858332923987959492023259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30477777231983945989364345 22858332923987959492023259)
        ·
          refine ⟨34287499385981939238034889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22858332923987959492023259 34287499385981939238034889)
          ·
            refine ⟨25715624539486454428526167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34287499385981939238034889 25715624539486454428526167)
            ·
              refine ⟨38573436809229681642789251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25715624539486454428526167 38573436809229681642789251)
              ·
                refine ⟨57860155213844522464183877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38573436809229681642789251 57860155213844522464183877)
                ·
                  refine ⟨10848779102595847962034477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57860155213844522464183877 10848779102595847962034477)
                  ·
                    refine ⟨4068292163473442985762929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10848779102595847962034477 4068292163473442985762929)
                    ·
                      refine ⟨3051219122605082239322197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4068292163473442985762929 3051219122605082239322197)
                      ·
                        rfl

theorem cell23_5942228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 4, 3, 2].length) (baseStart_5942228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5942228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5942228 prefixEnd_5942228 := by exact prefixLift 5942228
  have htrace : WordTrace (prefixWord ++ tailWord_5942228) baseStart_5942228 baseEnd_5942228 := by
    simpa [prefixWord, tailWord_5942228, baseEnd_5942228] using wordTrace_append hprefix tailTrace_5942228
  have hstable : (prefixWord ++ tailWord_5942228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5942228).length < 2 ^ (prefixWord ++ tailWord_5942228).sum := by decide
  have hdescent : baseEnd_5942228 < baseStart_5942228 := by decide
  rcases family_descends (prefixWord ++ tailWord_5942228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5942244 : List Nat := [2, 3, 1, 1, 1, 1, 2, 3, 3, 1, 5]
def baseStart_5942244 : Nat := 118140960795 + 5942244 * 2 ^ 59
def prefixEnd_5942244 : Nat := 4983230072969 + 3 ^ 40 * 5942244 * 2
def baseEnd_5942244 : Nat := 3051227338295554176722123

theorem tailTrace_5942244 : CollatzResearch.WordTrace tailWord_5942244 prefixEnd_5942244 3051227338295554176722123 := by
  unfold tailWord_5942244
  simp only [CollatzResearch.WordTrace]
  refine ⟨108365721942136158661808893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144487629256181544882411857 108365721942136158661808893)
  ·
    refine ⟨40637145728301059498178335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108365721942136158661808893 40637145728301059498178335)
    ·
      refine ⟨60955718592451589247267503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40637145728301059498178335 60955718592451589247267503)
      ·
        refine ⟨91433577888677383870901255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60955718592451589247267503 91433577888677383870901255)
        ·
          refine ⟨137150366833016075806351883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91433577888677383870901255 137150366833016075806351883)
          ·
            refine ⟨205725550249524113709527825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137150366833016075806351883 205725550249524113709527825)
            ·
              refine ⟨154294162687143085282145869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 205725550249524113709527825 154294162687143085282145869)
              ·
                refine ⟨57860311007678656980804701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 154294162687143085282145869 57860311007678656980804701)
                ·
                  refine ⟨21697616627879496367801763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57860311007678656980804701 21697616627879496367801763)
                  ·
                    refine ⟨32546424941819244551702645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21697616627879496367801763 32546424941819244551702645)
                    ·
                      refine ⟨3051227338295554176722123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32546424941819244551702645 3051227338295554176722123)
                      ·
                        rfl

theorem cell23_5942244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 3, 1, 5].length) (baseStart_5942244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5942244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5942244 prefixEnd_5942244 := by exact prefixLift 5942244
  have htrace : WordTrace (prefixWord ++ tailWord_5942244) baseStart_5942244 baseEnd_5942244 := by
    simpa [prefixWord, tailWord_5942244, baseEnd_5942244] using wordTrace_append hprefix tailTrace_5942244
  have hstable : (prefixWord ++ tailWord_5942244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5942244).length < 2 ^ (prefixWord ++ tailWord_5942244).sum := by decide
  have hdescent : baseEnd_5942244 < baseStart_5942244 := by decide
  rcases family_descends (prefixWord ++ tailWord_5942244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5942308 : List Nat := [2, 3, 1, 4, 1, 1, 1, 3, 1, 3, 3]
def baseStart_5942308 : Nat := 118140960795 + 5942308 * 2 ^ 59
def prefixEnd_5942308 : Nat := 4983230072969 + 3 ^ 40 * 5942308 * 2
def baseEnd_5942308 : Nat := 3051260201057441926321829

theorem tailTrace_5942308 : CollatzResearch.WordTrace tailWord_5942308 prefixEnd_5942308 3051260201057441926321829 := by
  unfold tailWord_5942308
  simp only [CollatzResearch.WordTrace]
  refine ⟨108366889078020228126973789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144489185437360304169298385 108366889078020228126973789)
  ·
    refine ⟨40637583404257585547615171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108366889078020228126973789 40637583404257585547615171)
    ·
      refine ⟨60956375106386378321422757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40637583404257585547615171 60956375106386378321422757)
      ·
        refine ⟨11429320332447445935266767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60956375106386378321422757 11429320332447445935266767)
        ·
          refine ⟨17143980498671168902900151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11429320332447445935266767 17143980498671168902900151)
          ·
            refine ⟨25715970748006753354350227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17143980498671168902900151 25715970748006753354350227)
            ·
              refine ⟨38573956122010130031525341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25715970748006753354350227 38573956122010130031525341)
              ·
                refine ⟨14465233545753798761822003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38573956122010130031525341 14465233545753798761822003)
                ·
                  refine ⟨21697850318630698142733005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14465233545753798761822003 21697850318630698142733005)
                  ·
                    refine ⟨8136693869486511803524877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21697850318630698142733005 8136693869486511803524877)
                    ·
                      refine ⟨3051260201057441926321829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8136693869486511803524877 3051260201057441926321829)
                      ·
                        rfl

theorem cell23_5942308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_5942308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5942308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5942308 prefixEnd_5942308 := by exact prefixLift 5942308
  have htrace : WordTrace (prefixWord ++ tailWord_5942308) baseStart_5942308 baseEnd_5942308 := by
    simpa [prefixWord, tailWord_5942308, baseEnd_5942308] using wordTrace_append hprefix tailTrace_5942308
  have hstable : (prefixWord ++ tailWord_5942308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5942308).length < 2 ^ (prefixWord ++ tailWord_5942308).sum := by decide
  have hdescent : baseEnd_5942308 < baseStart_5942308 := by decide
  rcases family_descends (prefixWord ++ tailWord_5942308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5942342 : List Nat := [6, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3]
def baseStart_5942342 : Nat := 118140960795 + 5942342 * 2 ^ 59
def prefixEnd_5942342 : Nat := 4983230072969 + 3 ^ 40 * 5942342 * 2
def baseEnd_5942342 : Nat := 3051277659399694793296673

theorem tailTrace_5942342 : CollatzResearch.WordTrace tailWord_5942342 prefixEnd_5942342 3051277659399694793296673 := by
  unfold tailWord_5942342
  simp only [CollatzResearch.WordTrace]
  refine ⟨6772969319934915001896415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 144490012158611520040456853 6772969319934915001896415)
  ·
    refine ⟨10159453979902372502844623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6772969319934915001896415 10159453979902372502844623)
    ·
      refine ⟨15239180969853558754266935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10159453979902372502844623 15239180969853558754266935)
      ·
        refine ⟨22858771454780338131400403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15239180969853558754266935 22858771454780338131400403)
        ·
          refine ⟨34288157182170507197100605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22858771454780338131400403 34288157182170507197100605)
          ·
            refine ⟨12858058943313940198912727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34288157182170507197100605 12858058943313940198912727)
            ·
              refine ⟨19287088414970910298369091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12858058943313940198912727 19287088414970910298369091)
              ·
                refine ⟨28930632622456365447553637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19287088414970910298369091 28930632622456365447553637)
                ·
                  refine ⟨5424493616710568521416307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28930632622456365447553637 5424493616710568521416307)
                  ·
                    refine ⟨8136740425065852782124461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5424493616710568521416307 8136740425065852782124461)
                    ·
                      refine ⟨3051277659399694793296673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8136740425065852782124461 3051277659399694793296673)
                      ·
                        rfl

theorem cell23_5942342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_5942342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5942342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5942342 prefixEnd_5942342 := by exact prefixLift 5942342
  have htrace : WordTrace (prefixWord ++ tailWord_5942342) baseStart_5942342 baseEnd_5942342 := by
    simpa [prefixWord, tailWord_5942342, baseEnd_5942342] using wordTrace_append hprefix tailTrace_5942342
  have hstable : (prefixWord ++ tailWord_5942342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5942342).length < 2 ^ (prefixWord ++ tailWord_5942342).sum := by decide
  have hdescent : baseEnd_5942342 < baseStart_5942342 := by decide
  rcases family_descends (prefixWord ++ tailWord_5942342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5942405 : List Nat := [1, 3, 1, 1, 7, 1, 1, 1, 7]
def baseStart_5942405 : Nat := 118140960795 + 5942405 * 2 ^ 59
def prefixEnd_5942405 : Nat := 4983230072969 + 3 ^ 40 * 5942405 * 2
def baseEnd_5942405 : Nat := 339034445408992005200987

theorem tailTrace_5942405 : CollatzResearch.WordTrace tailWord_5942405 prefixEnd_5942405 339034445408992005200987 := by
  unfold tailWord_5942405
  simp only [CollatzResearch.WordTrace]
  refine ⟨216737316036689041820228669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144491544024459361213485779 216737316036689041820228669)
  ·
    refine ⟨81276493513758390682585751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216737316036689041820228669 81276493513758390682585751)
    ·
      refine ⟨121914740270637586023878627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81276493513758390682585751 121914740270637586023878627)
      ·
        refine ⟨182872110405956379035817941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121914740270637586023878627 182872110405956379035817941)
        ·
          refine ⟨4286065087639602633651983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 182872110405956379035817941 4286065087639602633651983)
          ·
            refine ⟨6429097631459403950477975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4286065087639602633651983 6429097631459403950477975)
            ·
              refine ⟨9643646447189105925716963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6429097631459403950477975 9643646447189105925716963)
              ·
                refine ⟨14465469670783658888575445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9643646447189105925716963 14465469670783658888575445)
                ·
                  refine ⟨339034445408992005200987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14465469670783658888575445 339034445408992005200987)
                  ·
                    rfl

theorem cell23_5942405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 1, 7].length) (baseStart_5942405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5942405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5942405 prefixEnd_5942405 := by exact prefixLift 5942405
  have htrace : WordTrace (prefixWord ++ tailWord_5942405) baseStart_5942405 baseEnd_5942405 := by
    simpa [prefixWord, tailWord_5942405, baseEnd_5942405] using wordTrace_append hprefix tailTrace_5942405
  have hstable : (prefixWord ++ tailWord_5942405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5942405).length < 2 ^ (prefixWord ++ tailWord_5942405).sum := by decide
  have hdescent : baseEnd_5942405 < baseStart_5942405 := by decide
  rcases family_descends (prefixWord ++ tailWord_5942405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5942421 : List Nat := [1, 3, 2, 1, 1, 1, 2, 4, 1, 3, 4]
def baseStart_5942421 : Nat := 118140960795 + 5942421 * 2 ^ 59
def prefixEnd_5942421 : Nat := 4983230072969 + 3 ^ 40 * 5942421 * 2
def baseEnd_5942421 : Nat := 3051318224371399984208809

theorem tailTrace_5942421 : CollatzResearch.WordTrace tailWord_5942421 prefixEnd_5942421 3051318224371399984208809 := by
  unfold tailWord_5942421
  simp only [CollatzResearch.WordTrace]
  refine ⟨216737899604631076552811117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144491933069754051035207411 216737899604631076552811117)
  ·
    refine ⟨81276712351736653707304169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216737899604631076552811117 81276712351736653707304169)
    ·
      refine ⟨60957534263802490280478127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81276712351736653707304169 60957534263802490280478127)
      ·
        refine ⟨91436301395703735420717191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60957534263802490280478127 91436301395703735420717191)
        ·
          refine ⟨137154452093555603131075787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91436301395703735420717191 137154452093555603131075787)
          ·
            refine ⟨205731678140333404696613681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137154452093555603131075787 205731678140333404696613681)
            ·
              refine ⟨154298758605250053522460261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 205731678140333404696613681 154298758605250053522460261)
              ·
                refine ⟨28931017238484385035461299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 154298758605250053522460261 28931017238484385035461299)
                ·
                  refine ⟨43396525857726577553191949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28931017238484385035461299 43396525857726577553191949)
                  ·
                    refine ⟨16273697196647466582446981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43396525857726577553191949 16273697196647466582446981)
                    ·
                      refine ⟨3051318224371399984208809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16273697196647466582446981 3051318224371399984208809)
                      ·
                        rfl

theorem cell23_5942421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 3, 4].length) (baseStart_5942421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5942421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5942421 prefixEnd_5942421 := by exact prefixLift 5942421
  have htrace : WordTrace (prefixWord ++ tailWord_5942421) baseStart_5942421 baseEnd_5942421 := by
    simpa [prefixWord, tailWord_5942421, baseEnd_5942421] using wordTrace_append hprefix tailTrace_5942421
  have hstable : (prefixWord ++ tailWord_5942421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5942421).length < 2 ^ (prefixWord ++ tailWord_5942421).sum := by decide
  have hdescent : baseEnd_5942421 < baseStart_5942421 := by decide
  rcases family_descends (prefixWord ++ tailWord_5942421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5942461 : List Nat := [1, 4, 1, 2, 1, 1, 2, 3, 8]
def baseStart_5942461 : Nat := 118140960795 + 5942461 * 2 ^ 59
def prefixEnd_5942461 : Nat := 4983230072969 + 3 ^ 40 * 5942461 * 2
def baseEnd_5942461 : Nat := 339037640399731091967625

theorem tailTrace_5942461 : CollatzResearch.WordTrace tailWord_5942461 prefixEnd_5942461 339037640399731091967625 := by
  unfold tailWord_5942461
  simp only [CollatzResearch.WordTrace]
  refine ⟨216739358524486163384267237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144492905682990775589511491 216739358524486163384267237)
  ·
    refine ⟨40638629723341155634550107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 216739358524486163384267237 40638629723341155634550107)
    ·
      refine ⟨60957944585011733451825161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40638629723341155634550107 60957944585011733451825161)
      ·
        refine ⟨45718458438758800088868871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60957944585011733451825161 45718458438758800088868871)
        ·
          refine ⟨68577687658138200133303307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45718458438758800088868871 68577687658138200133303307)
          ·
            refine ⟨102866531487207300199954961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68577687658138200133303307 102866531487207300199954961)
            ·
              refine ⟨77149898615405475149966221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102866531487207300199954961 77149898615405475149966221)
              ·
                refine ⟨28931211980777053181237333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77149898615405475149966221 28931211980777053181237333)
                ·
                  refine ⟨339037640399731091967625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28931211980777053181237333 339037640399731091967625)
                  ·
                    rfl

theorem cell23_5942461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 8].length) (baseStart_5942461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5942461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5942461 prefixEnd_5942461 := by exact prefixLift 5942461
  have htrace : WordTrace (prefixWord ++ tailWord_5942461) baseStart_5942461 baseEnd_5942461 := by
    simpa [prefixWord, tailWord_5942461, baseEnd_5942461] using wordTrace_append hprefix tailTrace_5942461
  have hstable : (prefixWord ++ tailWord_5942461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5942461).length < 2 ^ (prefixWord ++ tailWord_5942461).sum := by decide
  have hdescent : baseEnd_5942461 < baseStart_5942461 := by decide
  rcases family_descends (prefixWord ++ tailWord_5942461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5942491 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 7, 5]
def baseStart_5942491 : Nat := 118140960795 + 5942491 * 2 ^ 59
def prefixEnd_5942491 : Nat := 4983230072969 + 3 ^ 40 * 5942491 * 2
def baseEnd_5942491 : Nat := 1017118056005738236777829

theorem tailTrace_5942491 : CollatzResearch.WordTrace tailWord_5942491 prefixEnd_5942491 1017118056005738236777829 := by
  unfold tailWord_5942491
  simp only [CollatzResearch.WordTrace]
  refine ⟨216740452714377478507859327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144493635142918319005239551 216740452714377478507859327)
  ·
    refine ⟨325110679071566217761788991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216740452714377478507859327 325110679071566217761788991)
    ·
      refine ⟨487666018607349326642683487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325110679071566217761788991 487666018607349326642683487)
      ·
        refine ⟨731499027911023989964025231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 487666018607349326642683487 731499027911023989964025231)
        ·
          refine ⟨1097248541866535984946037847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 731499027911023989964025231 1097248541866535984946037847)
          ·
            refine ⟨1645872812799803977419056771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1097248541866535984946037847 1645872812799803977419056771)
            ·
              refine ⟨2468809219199705966128585157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1645872812799803977419056771 2468809219199705966128585157)
              ·
                refine ⟨462901728599944868649109717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2468809219199705966128585157 462901728599944868649109717)
                ·
                  refine ⟨10849259264061207858963509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 462901728599944868649109717 10849259264061207858963509)
                  ·
                    refine ⟨1017118056005738236777829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10849259264061207858963509 1017118056005738236777829)
                    ·
                      rfl

theorem cell23_5942491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 7, 5].length) (baseStart_5942491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5942491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5942491 prefixEnd_5942491 := by exact prefixLift 5942491
  have htrace : WordTrace (prefixWord ++ tailWord_5942491) baseStart_5942491 baseEnd_5942491 := by
    simpa [prefixWord, tailWord_5942491, baseEnd_5942491] using wordTrace_append hprefix tailTrace_5942491
  have hstable : (prefixWord ++ tailWord_5942491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5942491).length < 2 ^ (prefixWord ++ tailWord_5942491).sum := by decide
  have hdescent : baseEnd_5942491 < baseStart_5942491 := by decide
  rcases family_descends (prefixWord ++ tailWord_5942491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5942516 : List Nat := [2, 6, 1, 2, 1, 1, 2, 1, 3, 4]
def baseStart_5942516 : Nat := 118140960795 + 5942516 * 2 ^ 59
def prefixEnd_5942516 : Nat := 4983230072969 + 3 ^ 40 * 5942516 * 2
def baseEnd_5942516 : Nat := 1017122335011192370840291

theorem tailTrace_5942516 : CollatzResearch.WordTrace tailWord_5942516 prefixEnd_5942516 1017122335011192370840291 := by
  unfold tailWord_5942516
  simp only [CollatzResearch.WordTrace]
  refine ⟨108370682269643453888759701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144494243026191271851679601 108370682269643453888759701)
  ·
    refine ⟨5079875731389536901035611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 108370682269643453888759701 5079875731389536901035611)
    ·
      refine ⟨7619813597084305351553417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5079875731389536901035611 7619813597084305351553417)
      ·
        refine ⟨5714860197813229013665063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7619813597084305351553417 5714860197813229013665063)
        ·
          refine ⟨8572290296719843520497595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5714860197813229013665063 8572290296719843520497595)
          ·
            refine ⟨12858435445079765280746393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8572290296719843520497595 12858435445079765280746393)
            ·
              refine ⟨9643826583809823960559795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12858435445079765280746393 9643826583809823960559795)
              ·
                refine ⟨14465739875714735940839693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9643826583809823960559795 14465739875714735940839693)
                ·
                  refine ⟨5424652453393025977814885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14465739875714735940839693 5424652453393025977814885)
                  ·
                    refine ⟨1017122335011192370840291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5424652453393025977814885 1017122335011192370840291)
                    ·
                      rfl

theorem cell23_5942516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_5942516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5942516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5942516 prefixEnd_5942516 := by exact prefixLift 5942516
  have htrace : WordTrace (prefixWord ++ tailWord_5942516) baseStart_5942516 baseEnd_5942516 := by
    simpa [prefixWord, tailWord_5942516, baseEnd_5942516] using wordTrace_append hprefix tailTrace_5942516
  have hstable : (prefixWord ++ tailWord_5942516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5942516).length < 2 ^ (prefixWord ++ tailWord_5942516).sum := by decide
  have hdescent : baseEnd_5942516 < baseStart_5942516 := by decide
  rcases family_descends (prefixWord ++ tailWord_5942516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5942522 : List Nat := [3, 1, 1, 1, 1, 4, 1, 6, 1, 1, 3]
def baseStart_5942522 : Nat := 118140960795 + 5942522 * 2 ^ 59
def prefixEnd_5942522 : Nat := 4983230072969 + 3 ^ 40 * 5942522 * 2
def baseEnd_5942522 : Nat := 3051370085917504089045845

theorem tailTrace_5942522 : CollatzResearch.WordTrace tailWord_5942522 prefixEnd_5942522 3051370085917504089045845 := by
  unfold tailWord_5942522
  simp only [CollatzResearch.WordTrace]
  refine ⟨54185395844316292700559455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144494388918176780534825213 54185395844316292700559455)
  ·
    refine ⟨81278093766474439050839183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54185395844316292700559455 81278093766474439050839183)
    ·
      refine ⟨121917140649711658576258775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81278093766474439050839183 121917140649711658576258775)
      ·
        refine ⟨182875710974567487864388163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121917140649711658576258775 182875710974567487864388163)
        ·
          refine ⟨274313566461851231796582245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182875710974567487864388163 274313566461851231796582245)
          ·
            refine ⟨51433793711597105961859171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 274313566461851231796582245 51433793711597105961859171)
            ·
              refine ⟨77150690567395658942788757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51433793711597105961859171 77150690567395658942788757)
              ·
                refine ⟨3616438620346671512943223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 77150690567395658942788757 3616438620346671512943223)
                ·
                  refine ⟨5424657930520007269414835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3616438620346671512943223 5424657930520007269414835)
                  ·
                    refine ⟨8136986895780010904122253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5424657930520007269414835 8136986895780010904122253)
                    ·
                      refine ⟨3051370085917504089045845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8136986895780010904122253 3051370085917504089045845)
                      ·
                        rfl

theorem cell23_5942522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 6, 1, 1, 3].length) (baseStart_5942522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5942522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5942522 prefixEnd_5942522 := by exact prefixLift 5942522
  have htrace : WordTrace (prefixWord ++ tailWord_5942522) baseStart_5942522 baseEnd_5942522 := by
    simpa [prefixWord, tailWord_5942522, baseEnd_5942522] using wordTrace_append hprefix tailTrace_5942522
  have hstable : (prefixWord ++ tailWord_5942522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5942522).length < 2 ^ (prefixWord ++ tailWord_5942522).sum := by decide
  have hdescent : baseEnd_5942522 < baseStart_5942522 := by decide
  rcases family_descends (prefixWord ++ tailWord_5942522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5942545 : List Nat := [1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 4]
def baseStart_5942545 : Nat := 118140960795 + 5942545 * 2 ^ 59
def prefixEnd_5942545 : Nat := 4983230072969 + 3 ^ 40 * 5942545 * 2
def baseEnd_5942545 : Nat := 3051381895972557499058239

theorem tailTrace_5942545 : CollatzResearch.WordTrace tailWord_5942545 prefixEnd_5942545 3051381895972557499058239 := by
  unfold tailWord_5942545
  simp only [CollatzResearch.WordTrace]
  refine ⟨216742422256181845730325089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144494948170787897153550059 216742422256181845730325089)
  ·
    refine ⟨162556816692136384297743817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216742422256181845730325089 162556816692136384297743817)
    ·
      refine ⟨121917612519102288223307863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162556816692136384297743817 121917612519102288223307863)
      ·
        refine ⟨182876418778653432334961795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121917612519102288223307863 182876418778653432334961795)
        ·
          refine ⟨274314628167980148502442693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182876418778653432334961795 274314628167980148502442693)
          ·
            refine ⟨51433992781496277844208005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 274314628167980148502442693 51433992781496277844208005)
            ·
              refine ⟨9643873646530552095789001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51433992781496277844208005 9643873646530552095789001)
              ·
                refine ⟨7232905234897914071841751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9643873646530552095789001 7232905234897914071841751)
                ·
                  refine ⟨10849357852346871107762627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7232905234897914071841751 10849357852346871107762627)
                  ·
                    refine ⟨16274036778520306661643941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10849357852346871107762627 16274036778520306661643941)
                    ·
                      refine ⟨3051381895972557499058239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16274036778520306661643941 3051381895972557499058239)
                      ·
                        rfl

theorem cell23_5942545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 4].length) (baseStart_5942545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5942545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5942545 prefixEnd_5942545 := by exact prefixLift 5942545
  have htrace : WordTrace (prefixWord ++ tailWord_5942545) baseStart_5942545 baseEnd_5942545 := by
    simpa [prefixWord, tailWord_5942545, baseEnd_5942545] using wordTrace_append hprefix tailTrace_5942545
  have hstable : (prefixWord ++ tailWord_5942545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5942545).length < 2 ^ (prefixWord ++ tailWord_5942545).sum := by decide
  have hdescent : baseEnd_5942545 < baseStart_5942545 := by decide
  rcases family_descends (prefixWord ++ tailWord_5942545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5942565 : List Nat := [1, 3, 1, 2, 4, 2, 2, 1, 1, 1, 5]
def baseStart_5942565 : Nat := 118140960795 + 5942565 * 2 ^ 59
def prefixEnd_5942565 : Nat := 4983230072969 + 3 ^ 40 * 5942565 * 2
def baseEnd_5942565 : Nat := 3051392165585647420808147

theorem tailTrace_5942565 : CollatzResearch.WordTrace tailWord_5942565 prefixEnd_5942565 3051392165585647420808147 := by
  unfold tailWord_5942565
  simp only [CollatzResearch.WordTrace]
  refine ⟨216743151716109389146053149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144495434477406259430702099 216743151716109389146053149)
  ·
    refine ⟨81278681893541020929769931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216743151716109389146053149 81278681893541020929769931)
    ·
      refine ⟨121918022840311531394654897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81278681893541020929769931 121918022840311531394654897)
      ·
        refine ⟨91438517130233648545991173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121918022840311531394654897 91438517130233648545991173)
        ·
          refine ⟨17144721961918809102373345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91438517130233648545991173 17144721961918809102373345)
          ·
            refine ⟨12858541471439106826780009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17144721961918809102373345 12858541471439106826780009)
            ·
              refine ⟨9643906103579330120085007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12858541471439106826780009 9643906103579330120085007)
              ·
                refine ⟨14465859155368995180127511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9643906103579330120085007 14465859155368995180127511)
                ·
                  refine ⟨21698788733053492770191267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14465859155368995180127511 21698788733053492770191267)
                  ·
                    refine ⟨32548183099580239155286901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21698788733053492770191267 32548183099580239155286901)
                    ·
                      refine ⟨3051392165585647420808147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32548183099580239155286901 3051392165585647420808147)
                      ·
                        rfl

theorem cell23_5942565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 1, 1, 1, 5].length) (baseStart_5942565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5942565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5942565 prefixEnd_5942565 := by exact prefixLift 5942565
  have htrace : WordTrace (prefixWord ++ tailWord_5942565) baseStart_5942565 baseEnd_5942565 := by
    simpa [prefixWord, tailWord_5942565, baseEnd_5942565] using wordTrace_append hprefix tailTrace_5942565
  have hstable : (prefixWord ++ tailWord_5942565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5942565).length < 2 ^ (prefixWord ++ tailWord_5942565).sum := by decide
  have hdescent : baseEnd_5942565 < baseStart_5942565 := by decide
  rcases family_descends (prefixWord ++ tailWord_5942565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5942568 : List Nat := [2, 1, 5, 1, 2, 1, 11]
def baseStart_5942568 : Nat := 118140960795 + 5942568 * 2 ^ 59
def prefixEnd_5942568 : Nat := 4983230072969 + 3 ^ 40 * 5942568 * 2
def baseEnd_5942568 : Nat := 37671527234908776655193

theorem tailTrace_5942568 : CollatzResearch.WordTrace tailWord_5942568 prefixEnd_5942568 37671527234908776655193 := by
  unfold tailWord_5942568
  simp only [CollatzResearch.WordTrace]
  refine ⟨108371630567549260329206179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144495507423399013772274905 108371630567549260329206179)
  ·
    refine ⟨162557445851323890493809269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108371630567549260329206179 162557445851323890493809269)
    ·
      refine ⟨15239760548561614733794619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 162557445851323890493809269 15239760548561614733794619)
      ·
        refine ⟨22859640822842422100691929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15239760548561614733794619 22859640822842422100691929)
        ·
          refine ⟨17144730617131816575518947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22859640822842422100691929 17144730617131816575518947)
          ·
            refine ⟨25717095925697724863278421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17144730617131816575518947 25717095925697724863278421)
            ·
              refine ⟨37671527234908776655193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 25717095925697724863278421 37671527234908776655193)
              ·
                rfl

theorem cell23_5942568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 11].length) (baseStart_5942568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5942568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5942568 prefixEnd_5942568 := by exact prefixLift 5942568
  have htrace : WordTrace (prefixWord ++ tailWord_5942568) baseStart_5942568 baseEnd_5942568 := by
    simpa [prefixWord, tailWord_5942568, baseEnd_5942568] using wordTrace_append hprefix tailTrace_5942568
  have hstable : (prefixWord ++ tailWord_5942568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5942568).length < 2 ^ (prefixWord ++ tailWord_5942568).sum := by decide
  have hdescent : baseEnd_5942568 < baseStart_5942568 := by decide
  rcases family_descends (prefixWord ++ tailWord_5942568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5942571 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 8]
def baseStart_5942571 : Nat := 118140960795 + 5942571 * 2 ^ 59
def prefixEnd_5942571 : Nat := 4983230072969 + 3 ^ 40 * 5942571 * 2
def baseEnd_5942571 : Nat := 3051395246469574397333119

theorem tailTrace_5942571 : CollatzResearch.WordTrace tailWord_5942571 prefixEnd_5942571 3051395246469574397333119 := by
  unfold tailWord_5942571
  simp only [CollatzResearch.WordTrace]
  refine ⟨216743370554087652170771567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144495580369391768113847711 216743370554087652170771567)
  ·
    refine ⟨325115055831131478256157351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216743370554087652170771567 325115055831131478256157351)
    ·
      refine ⟨487672583746697217384236027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325115055831131478256157351 487672583746697217384236027)
      ·
        refine ⟨731508875620045826076354041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 487672583746697217384236027 731508875620045826076354041)
        ·
          refine ⟨548631656715034369557265531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 731508875620045826076354041 548631656715034369557265531)
          ·
            refine ⟨822947485072551554335898297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 548631656715034369557265531 822947485072551554335898297)
            ·
              refine ⟨617210613804413665751923723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 822947485072551554335898297 617210613804413665751923723)
              ·
                refine ⟨925815920706620498627885585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 617210613804413665751923723 925815920706620498627885585)
                ·
                  refine ⟨694361940529965373970914189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 925815920706620498627885585 694361940529965373970914189)
                  ·
                    refine ⟨260385727698737015239092821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 694361940529965373970914189 260385727698737015239092821)
                    ·
                      refine ⟨3051395246469574397333119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 260385727698737015239092821 3051395246469574397333119)
                      ·
                        rfl

theorem cell23_5942571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 8].length) (baseStart_5942571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5942571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5942571 prefixEnd_5942571 := by exact prefixLift 5942571
  have htrace : WordTrace (prefixWord ++ tailWord_5942571) baseStart_5942571 baseEnd_5942571 := by
    simpa [prefixWord, tailWord_5942571, baseEnd_5942571] using wordTrace_append hprefix tailTrace_5942571
  have hstable : (prefixWord ++ tailWord_5942571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5942571).length < 2 ^ (prefixWord ++ tailWord_5942571).sum := by decide
  have hdescent : baseEnd_5942571 < baseStart_5942571 := by decide
  rcases family_descends (prefixWord ++ tailWord_5942571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5942573 : List Nat := [1, 5, 3, 1, 1, 2, 3, 2, 1, 1, 3]
def baseStart_5942573 : Nat := 118140960795 + 5942573 * 2 ^ 59
def prefixEnd_5942573 : Nat := 4983230072969 + 3 ^ 40 * 5942573 * 2
def baseEnd_5942573 : Nat := 3051396273430883389508111

theorem tailTrace_5942573 : CollatzResearch.WordTrace tailWord_5942573 prefixEnd_5942573 3051396273430883389508111 := by
  unfold tailWord_5942573
  simp only [CollatzResearch.WordTrace]
  refine ⟨216743443500080406512344373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144495629000053604341562915 216743443500080406512344373)
  ·
    refine ⟨20319697828132538110532285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 216743443500080406512344373 20319697828132538110532285)
    ·
      refine ⟨7619886685549701791449607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20319697828132538110532285 7619886685549701791449607)
      ·
        refine ⟨11429830028324552687174411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7619886685549701791449607 11429830028324552687174411)
        ·
          refine ⟨17144745042486829030761617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11429830028324552687174411 17144745042486829030761617)
          ·
            refine ⟨12858558781865121773071213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17144745042486829030761617 12858558781865121773071213)
            ·
              refine ⟨4821959543199420664901705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12858558781865121773071213 4821959543199420664901705)
              ·
                refine ⟨3616469657399565498676279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4821959543199420664901705 3616469657399565498676279)
                ·
                  refine ⟨5424704486099348248014419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3616469657399565498676279 5424704486099348248014419)
                  ·
                    refine ⟨8137056729149022372021629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5424704486099348248014419 8137056729149022372021629)
                    ·
                      refine ⟨3051396273430883389508111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8137056729149022372021629 3051396273430883389508111)
                      ·
                        rfl

theorem cell23_5942573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_5942573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5942573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5942573 prefixEnd_5942573 := by exact prefixLift 5942573
  have htrace : WordTrace (prefixWord ++ tailWord_5942573) baseStart_5942573 baseEnd_5942573 := by
    simpa [prefixWord, tailWord_5942573, baseEnd_5942573] using wordTrace_append hprefix tailTrace_5942573
  have hstable : (prefixWord ++ tailWord_5942573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5942573).length < 2 ^ (prefixWord ++ tailWord_5942573).sum := by decide
  have hdescent : baseEnd_5942573 < baseStart_5942573 := by decide
  rcases family_descends (prefixWord ++ tailWord_5942573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5942579 : List Nat := [1, 1, 1, 2, 5, 4, 1, 1, 3, 2, 2]
def baseStart_5942579 : Nat := 118140960795 + 5942579 * 2 ^ 59
def prefixEnd_5942579 : Nat := 4983230072969 + 3 ^ 40 * 5942579 * 2
def baseEnd_5942579 : Nat := 3051399354314810366033083

theorem tailTrace_5942579 : CollatzResearch.WordTrace tailWord_5942579 prefixEnd_5942579 3051399354314810366033083 := by
  unfold tailWord_5942579
  simp only [CollatzResearch.WordTrace]
  refine ⟨216743662338058669537062791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144495774892039113024708527 216743662338058669537062791)
  ·
    refine ⟨325115493507088004305594187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216743662338058669537062791 325115493507088004305594187)
    ·
      refine ⟨487673240260632006458391281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325115493507088004305594187 487673240260632006458391281)
      ·
        refine ⟨365754930195474004843793461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 487673240260632006458391281 365754930195474004843793461)
        ·
          refine ⟨34289524705825687954105637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 365754930195474004843793461 34289524705825687954105637)
          ·
            refine ⟨6429285882342316491394807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34289524705825687954105637 6429285882342316491394807)
            ·
              refine ⟨9643928823513474737092211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6429285882342316491394807 9643928823513474737092211)
              ·
                refine ⟨14465893235270212105638317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9643928823513474737092211 14465893235270212105638317)
                ·
                  refine ⟨5424709963226329539614369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14465893235270212105638317 5424709963226329539614369)
                  ·
                    refine ⟨4068532472419747154710777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5424709963226329539614369 4068532472419747154710777)
                    ·
                      refine ⟨3051399354314810366033083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4068532472419747154710777 3051399354314810366033083)
                      ·
                        rfl

theorem cell23_5942579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 1, 3, 2, 2].length) (baseStart_5942579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5942579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5942579 prefixEnd_5942579 := by exact prefixLift 5942579
  have htrace : WordTrace (prefixWord ++ tailWord_5942579) baseStart_5942579 baseEnd_5942579 := by
    simpa [prefixWord, tailWord_5942579, baseEnd_5942579] using wordTrace_append hprefix tailTrace_5942579
  have hstable : (prefixWord ++ tailWord_5942579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5942579).length < 2 ^ (prefixWord ++ tailWord_5942579).sum := by decide
  have hdescent : baseEnd_5942579 < baseStart_5942579 := by decide
  rcases family_descends (prefixWord ++ tailWord_5942579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5942585 : List Nat := [1, 2, 1, 6, 2, 1, 2, 8]
def baseStart_5942585 : Nat := 118140960795 + 5942585 * 2 ^ 59
def prefixEnd_5942585 : Nat := 4983230072969 + 3 ^ 40 * 5942585 * 2
def baseEnd_5942585 : Nat := 113014905007360642316965

theorem tailTrace_5942585 : CollatzResearch.WordTrace tailWord_5942585 prefixEnd_5942585 113014905007360642316965 := by
  unfold tailWord_5942585
  simp only [CollatzResearch.WordTrace]
  refine ⟨216743881176036932561781209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144495920784024621707854139 216743881176036932561781209)
  ·
    refine ⟨162557910882027699421335907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216743881176036932561781209 162557910882027699421335907)
    ·
      refine ⟨243836866323041549132003861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162557910882027699421335907 243836866323041549132003861)
      ·
        refine ⟨11429853108892572615562681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 243836866323041549132003861 11429853108892572615562681)
        ·
          refine ⟨8572389831669429461672011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11429853108892572615562681 8572389831669429461672011)
          ·
            refine ⟨12858584747504144192508017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8572389831669429461672011 12858584747504144192508017)
            ·
              refine ⟨9643938560628108144381013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12858584747504144192508017 9643938560628108144381013)
              ·
                refine ⟨113014905007360642316965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9643938560628108144381013 113014905007360642316965)
                ·
                  rfl

theorem cell23_5942585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 8].length) (baseStart_5942585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5942585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5942585 prefixEnd_5942585 := by exact prefixLift 5942585
  have htrace : WordTrace (prefixWord ++ tailWord_5942585) baseStart_5942585 baseEnd_5942585 := by
    simpa [prefixWord, tailWord_5942585, baseEnd_5942585] using wordTrace_append hprefix tailTrace_5942585
  have hstable : (prefixWord ++ tailWord_5942585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5942585).length < 2 ^ (prefixWord ++ tailWord_5942585).sum := by decide
  have hdescent : baseEnd_5942585 < baseStart_5942585 := by decide
  rcases family_descends (prefixWord ++ tailWord_5942585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5942589 : List Nat := [1, 4, 1, 5, 1, 1, 1, 3, 2, 4]
def baseStart_5942589 : Nat := 118140960795 + 5942589 * 2 ^ 59
def prefixEnd_5942589 : Nat := 4983230072969 + 3 ^ 40 * 5942589 * 2
def baseEnd_5942589 : Nat := 1017134829707118442302679

theorem tailTrace_5942589 : CollatzResearch.WordTrace tailWord_5942589 prefixEnd_5942589 1017134829707118442302679 := by
  unfold tailWord_5942589
  simp only [CollatzResearch.WordTrace]
  refine ⟨216744027068022441244926821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144496018045348294163284547 216744027068022441244926821)
  ·
    refine ⟨40639505075254207733423779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 216744027068022441244926821 40639505075254207733423779)
    ·
      refine ⟨60959257612881311600135669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40639505075254207733423779 60959257612881311600135669)
      ·
        refine ⟨5714930401207622962512719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60959257612881311600135669 5714930401207622962512719)
        ·
          refine ⟨8572395601811434443769079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5714930401207622962512719 8572395601811434443769079)
          ·
            refine ⟨12858593402717151665653619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8572395601811434443769079 12858593402717151665653619)
            ·
              refine ⟨19287890104075727498480429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12858593402717151665653619 19287890104075727498480429)
              ·
                refine ⟨7232958789028397811930161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19287890104075727498480429 7232958789028397811930161)
                ·
                  refine ⟨5424719091771298358947621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7232958789028397811930161 5424719091771298358947621)
                  ·
                    refine ⟨1017134829707118442302679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5424719091771298358947621 1017134829707118442302679)
                    ·
                      rfl

theorem cell23_5942589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 3, 2, 4].length) (baseStart_5942589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5942589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5942589 prefixEnd_5942589 := by exact prefixLift 5942589
  have htrace : WordTrace (prefixWord ++ tailWord_5942589) baseStart_5942589 baseEnd_5942589 := by
    simpa [prefixWord, tailWord_5942589, baseEnd_5942589] using wordTrace_append hprefix tailTrace_5942589
  have hstable : (prefixWord ++ tailWord_5942589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5942589).length < 2 ^ (prefixWord ++ tailWord_5942589).sum := by decide
  have hdescent : baseEnd_5942589 < baseStart_5942589 := by decide
  rcases family_descends (prefixWord ++ tailWord_5942589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5942652 : List Nat := [2, 2, 2, 1, 1, 1, 6, 1, 1, 4, 2]
def baseStart_5942652 : Nat := 118140960795 + 5942652 * 2 ^ 59
def prefixEnd_5942652 : Nat := 4983230072969 + 3 ^ 40 * 5942652 * 2
def baseEnd_5942652 : Nat := 3051436838402588580420247

theorem tailTrace_5942652 : CollatzResearch.WordTrace tailWord_5942652 prefixEnd_5942652 3051436838402588580420247 := by
  unfold tailWord_5942652
  simp only [CollatzResearch.WordTrace]
  refine ⟨108373162433397101502235105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144497549911196135336313473 108373162433397101502235105)
  ·
    refine ⟨81279871825047826126676329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108373162433397101502235105 81279871825047826126676329)
    ·
      refine ⟨60959903868785869595007247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81279871825047826126676329 60959903868785869595007247)
      ·
        refine ⟨91439855803178804392510871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60959903868785869595007247 91439855803178804392510871)
        ·
          refine ⟨137159783704768206588766307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91439855803178804392510871 137159783704768206588766307)
          ·
            refine ⟨205739675557152309883149461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137159783704768206588766307 205739675557152309883149461)
            ·
              refine ⟨9644047291741514525772631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 205739675557152309883149461 9644047291741514525772631)
              ·
                refine ⟨14466070937612271788658947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9644047291741514525772631 14466070937612271788658947)
                ·
                  refine ⟨21699106406418407682988421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14466070937612271788658947 21699106406418407682988421)
                  ·
                    refine ⟨4068582451203451440560329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21699106406418407682988421 4068582451203451440560329)
                    ·
                      refine ⟨3051436838402588580420247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4068582451203451440560329 3051436838402588580420247)
                      ·
                        rfl

theorem cell23_5942652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 1, 1, 4, 2].length) (baseStart_5942652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5942652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5942652 prefixEnd_5942652 := by exact prefixLift 5942652
  have htrace : WordTrace (prefixWord ++ tailWord_5942652) baseStart_5942652 baseEnd_5942652 := by
    simpa [prefixWord, tailWord_5942652, baseEnd_5942652] using wordTrace_append hprefix tailTrace_5942652
  have hstable : (prefixWord ++ tailWord_5942652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5942652).length < 2 ^ (prefixWord ++ tailWord_5942652).sum := by decide
  have hdescent : baseEnd_5942652 < baseStart_5942652 := by decide
  rcases family_descends (prefixWord ++ tailWord_5942652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5942735 : List Nat := [1, 1, 2, 1, 1, 4, 2, 2, 5, 4]
def baseStart_5942735 : Nat := 118140960795 + 5942735 * 2 ^ 59
def prefixEnd_5942735 : Nat := 4983230072969 + 3 ^ 40 * 5942735 * 2
def baseEnd_5942735 : Nat := 1017159819098970585227455

theorem tailTrace_5942735 : CollatzResearch.WordTrace tailWord_5942735 prefixEnd_5942735 1017159819098970585227455 := by
  unfold tailWord_5942735
  simp only [CollatzResearch.WordTrace]
  refine ⟨216749352125493508179741659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144499568083662338786494439 216749352125493508179741659)
  ·
    refine ⟨325124028188240262269612489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216749352125493508179741659 325124028188240262269612489)
    ·
      refine ⟨243843021141180196702209367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 325124028188240262269612489 243843021141180196702209367)
      ·
        refine ⟨365764531711770295053314051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243843021141180196702209367 365764531711770295053314051)
        ·
          refine ⟨548646797567655442579971077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365764531711770295053314051 548646797567655442579971077)
          ·
            refine ⟨102871274543935395483744577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 548646797567655442579971077 102871274543935395483744577)
            ·
              refine ⟨77153455907951546612808433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102871274543935395483744577 77153455907951546612808433)
              ·
                refine ⟨57865091930963659959606325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77153455907951546612808433 57865091930963659959606325)
                ·
                  refine ⟨5424852368527843121213093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57865091930963659959606325 5424852368527843121213093)
                  ·
                    refine ⟨1017159819098970585227455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5424852368527843121213093 1017159819098970585227455)
                    ·
                      rfl

theorem cell23_5942735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 5, 4].length) (baseStart_5942735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5942735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5942735 prefixEnd_5942735 := by exact prefixLift 5942735
  have htrace : WordTrace (prefixWord ++ tailWord_5942735) baseStart_5942735 baseEnd_5942735 := by
    simpa [prefixWord, tailWord_5942735, baseEnd_5942735] using wordTrace_append hprefix tailTrace_5942735
  have hstable : (prefixWord ++ tailWord_5942735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5942735).length < 2 ^ (prefixWord ++ tailWord_5942735).sum := by decide
  have hdescent : baseEnd_5942735 < baseStart_5942735 := by decide
  rcases family_descends (prefixWord ++ tailWord_5942735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5942832 : List Nat := [2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 4]
def baseStart_5942832 : Nat := 118140960795 + 5942832 * 2 ^ 59
def prefixEnd_5942832 : Nat := 4983230072969 + 3 ^ 40 * 5942832 * 2
def baseEnd_5942832 : Nat := 3051529264920397876169419

theorem tailTrace_5942832 : CollatzResearch.WordTrace tailWord_5942832 prefixEnd_5942832 3051529264920397876169419 := by
  unfold tailWord_5942832
  simp only [CollatzResearch.WordTrace]
  refine ⟨108376445003071046873011375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144501926670761395830681833 108376445003071046873011375)
  ·
    refine ⟨162564667504606570309517063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108376445003071046873011375 162564667504606570309517063)
    ·
      refine ⟨243847001256909855464275595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162564667504606570309517063 243847001256909855464275595)
      ·
        refine ⟨365770501885364783196413393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243847001256909855464275595 365770501885364783196413393)
        ·
          refine ⟨274327876414023587397310045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 365770501885364783196413393 274327876414023587397310045)
          ·
            refine ⟨102872953655258845273991267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 274327876414023587397310045 102872953655258845273991267)
            ·
              refine ⟨154309430482888267910986901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102872953655258845273991267 154309430482888267910986901)
              ·
                refine ⟨7233254553885387558327511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 154309430482888267910986901 7233254553885387558327511)
                ·
                  refine ⟨10849881830828081337491267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7233254553885387558327511 10849881830828081337491267)
                  ·
                    refine ⟨16274822746242122006236901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10849881830828081337491267 16274822746242122006236901)
                    ·
                      refine ⟨3051529264920397876169419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16274822746242122006236901 3051529264920397876169419)
                      ·
                        rfl

theorem cell23_5942832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 4].length) (baseStart_5942832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5942832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5942832 prefixEnd_5942832 := by exact prefixLift 5942832
  have htrace : WordTrace (prefixWord ++ tailWord_5942832) baseStart_5942832 baseEnd_5942832 := by
    simpa [prefixWord, tailWord_5942832, baseEnd_5942832] using wordTrace_append hprefix tailTrace_5942832
  have hstable : (prefixWord ++ tailWord_5942832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5942832).length < 2 ^ (prefixWord ++ tailWord_5942832).sum := by decide
  have hdescent : baseEnd_5942832 < baseStart_5942832 := by decide
  rcases family_descends (prefixWord ++ tailWord_5942832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5942842 : List Nat := [3, 1, 1, 1, 3, 2, 2, 2, 4, 4]
def baseStart_5942842 : Nat := 118140960795 + 5942842 * 2 ^ 59
def prefixEnd_5942842 : Nat := 4983230072969 + 3 ^ 40 * 5942842 * 2
def baseEnd_5942842 : Nat := 1017178133242314279014791

theorem tailTrace_5942842 : CollatzResearch.WordTrace tailWord_5942842 prefixEnd_5942842 1017178133242314279014791 := by
  unfold tailWord_5942842
  simp only [CollatzResearch.WordTrace]
  refine ⟨54188313684026466363471695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144502169824070576969257853 54188313684026466363471695)
  ·
    refine ⟨81282470526039699545207543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54188313684026466363471695 81282470526039699545207543)
    ·
      refine ⟨121923705789059549317811315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81282470526039699545207543 121923705789059549317811315)
      ·
        refine ⟨182885558683589323976716973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121923705789059549317811315 182885558683589323976716973)
        ·
          refine ⟨68582084506345996491268865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182885558683589323976716973 68582084506345996491268865)
          ·
            refine ⟨51436563379759497368451649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68582084506345996491268865 51436563379759497368451649)
            ·
              refine ⟨38577422534819623026338737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51436563379759497368451649 38577422534819623026338737)
              ·
                refine ⟨28933066901114717269754053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38577422534819623026338737 28933066901114717269754053)
                ·
                  refine ⟨5424950043959009488078885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28933066901114717269754053 5424950043959009488078885)
                  ·
                    refine ⟨1017178133242314279014791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5424950043959009488078885 1017178133242314279014791)
                    ·
                      rfl

theorem cell23_5942842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 4, 4].length) (baseStart_5942842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5942842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5942842 prefixEnd_5942842 := by exact prefixLift 5942842
  have htrace : WordTrace (prefixWord ++ tailWord_5942842) baseStart_5942842 baseEnd_5942842 := by
    simpa [prefixWord, tailWord_5942842, baseEnd_5942842] using wordTrace_append hprefix tailTrace_5942842
  have hstable : (prefixWord ++ tailWord_5942842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5942842).length < 2 ^ (prefixWord ++ tailWord_5942842).sum := by decide
  have hdescent : baseEnd_5942842 < baseStart_5942842 := by decide
  rcases family_descends (prefixWord ++ tailWord_5942842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5942849 : List Nat := [1, 2, 5, 1, 1, 1, 3, 3, 1, 1, 4]
def baseStart_5942849 : Nat := 118140960795 + 5942849 * 2 ^ 59
def prefixEnd_5942849 : Nat := 4983230072969 + 3 ^ 40 * 5942849 * 2
def baseEnd_5942849 : Nat := 3051537994091524309656841

theorem tailTrace_5942849 : CollatzResearch.WordTrace tailWord_5942849 prefixEnd_5942849 3051537994091524309656841 := by
  unfold tailWord_5942849
  simp only [CollatzResearch.WordTrace]
  refine ⟨216753510047080505649391601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144502340031387003766261067 216753510047080505649391601)
  ·
    refine ⟨162565132535310379237043701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216753510047080505649391601 162565132535310379237043701)
    ·
      refine ⟨15240481175185348053472847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 162565132535310379237043701 15240481175185348053472847)
      ·
        refine ⟨22860721762778022080209271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15240481175185348053472847 22860721762778022080209271)
        ·
          refine ⟨34291082644167033120313907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22860721762778022080209271 34291082644167033120313907)
          ·
            refine ⟨51436623966250549680470861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34291082644167033120313907 51436623966250549680470861)
            ·
              refine ⟨19288733987343956130176573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51436623966250549680470861 19288733987343956130176573)
              ·
                refine ⟨7233275245253983548816215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19288733987343956130176573 7233275245253983548816215)
                ·
                  refine ⟨10849912867880975323224323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7233275245253983548816215 10849912867880975323224323)
                  ·
                    refine ⟨16274869301821462984836485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10849912867880975323224323 16274869301821462984836485)
                    ·
                      refine ⟨3051537994091524309656841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16274869301821462984836485 3051537994091524309656841)
                      ·
                        rfl

theorem cell23_5942849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_5942849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5942849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5942849 prefixEnd_5942849 := by exact prefixLift 5942849
  have htrace : WordTrace (prefixWord ++ tailWord_5942849) baseStart_5942849 baseEnd_5942849 := by
    simpa [prefixWord, tailWord_5942849, baseEnd_5942849] using wordTrace_append hprefix tailTrace_5942849
  have hstable : (prefixWord ++ tailWord_5942849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5942849).length < 2 ^ (prefixWord ++ tailWord_5942849).sum := by decide
  have hdescent : baseEnd_5942849 < baseStart_5942849 := by decide
  rcases family_descends (prefixWord ++ tailWord_5942849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5942866 : List Nat := [3, 2, 2, 1, 2, 2, 1, 3, 3, 2, 2]
def baseStart_5942866 : Nat := 118140960795 + 5942866 * 2 ^ 59
def prefixEnd_5942866 : Nat := 4983230072969 + 3 ^ 40 * 5942866 * 2
def baseEnd_5942866 : Nat := 3051546723262650743144263

theorem tailTrace_5942866 : CollatzResearch.WordTrace tailWord_5942866 prefixEnd_5942866 3051546723262650743144263 := by
  unfold tailWord_5942866
  simp only [CollatzResearch.WordTrace]
  refine ⟨54188532522004729388190113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144502753392012611701840301 54188532522004729388190113)
  ·
    refine ⟨40641399391503547041142585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54188532522004729388190113 40641399391503547041142585)
    ·
      refine ⟨30481049543627660280856939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40641399391503547041142585 30481049543627660280856939)
      ·
        refine ⟨45721574315441490421285409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30481049543627660280856939 45721574315441490421285409)
        ·
          refine ⟨34291180736581117815964057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45721574315441490421285409 34291180736581117815964057)
          ·
            refine ⟨25718385552435838361973043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34291180736581117815964057 25718385552435838361973043)
            ·
              refine ⟨38577578328653757542959565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25718385552435838361973043 38577578328653757542959565)
              ·
                refine ⟨14466591873245159078609837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38577578328653757542959565 14466591873245159078609837)
                ·
                  refine ⟨5424971952466934654478689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14466591873245159078609837 5424971952466934654478689)
                  ·
                    refine ⟨4068728964350200990859017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5424971952466934654478689 4068728964350200990859017)
                    ·
                      refine ⟨3051546723262650743144263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4068728964350200990859017 3051546723262650743144263)
                      ·
                        rfl

theorem cell23_5942866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 3, 3, 2, 2].length) (baseStart_5942866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5942866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5942866 prefixEnd_5942866 := by exact prefixLift 5942866
  have htrace : WordTrace (prefixWord ++ tailWord_5942866) baseStart_5942866 baseEnd_5942866 := by
    simpa [prefixWord, tailWord_5942866, baseEnd_5942866] using wordTrace_append hprefix tailTrace_5942866
  have hstable : (prefixWord ++ tailWord_5942866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5942866).length < 2 ^ (prefixWord ++ tailWord_5942866).sum := by decide
  have hdescent : baseEnd_5942866 < baseStart_5942866 := by decide
  rcases family_descends (prefixWord ++ tailWord_5942866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5942943 : List Nat := [1, 1, 2, 7, 1, 1, 1, 1, 3, 3, 2]
def baseStart_5942943 : Nat := 118140960795 + 5942943 * 2 ^ 59
def prefixEnd_5942943 : Nat := 4983230072969 + 3 ^ 40 * 5942943 * 2
def baseEnd_5942943 : Nat := 3051586261273046941881409

theorem tailTrace_5942943 : CollatzResearch.WordTrace tailWord_5942943 prefixEnd_5942943 3051586261273046941881409 := by
  unfold tailWord_5942943
  simp only [CollatzResearch.WordTrace]
  refine ⟨216756938508739959703313483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144504625672493306468875655 216756938508739959703313483)
  ·
    refine ⟨325135407763109939554970225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216756938508739959703313483 325135407763109939554970225)
    ·
      refine ⟨243851555822332454666227669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 325135407763109939554970225 243851555822332454666227669)
      ·
        refine ⟨5715270839585916906239711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 243851555822332454666227669 5715270839585916906239711)
        ·
          refine ⟨8572906259378875359359567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5715270839585916906239711 8572906259378875359359567)
          ·
            refine ⟨12859359389068313039039351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8572906259378875359359567 12859359389068313039039351)
            ·
              refine ⟨19289039083602469558559027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12859359389068313039039351 19289039083602469558559027)
              ·
                refine ⟨28933558625403704337838541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19289039083602469558559027 28933558625403704337838541)
                ·
                  refine ⟨10850084484526389126689453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28933558625403704337838541 10850084484526389126689453)
                  ·
                    refine ⟨4068781681697395922508545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10850084484526389126689453 4068781681697395922508545)
                    ·
                      refine ⟨3051586261273046941881409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4068781681697395922508545 3051586261273046941881409)
                      ·
                        rfl

theorem cell23_5942943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_5942943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5942943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5942943 prefixEnd_5942943 := by exact prefixLift 5942943
  have htrace : WordTrace (prefixWord ++ tailWord_5942943) baseStart_5942943 baseEnd_5942943 := by
    simpa [prefixWord, tailWord_5942943, baseEnd_5942943] using wordTrace_append hprefix tailTrace_5942943
  have hstable : (prefixWord ++ tailWord_5942943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5942943).length < 2 ^ (prefixWord ++ tailWord_5942943).sum := by decide
  have hdescent : baseEnd_5942943 < baseStart_5942943 := by decide
  rcases family_descends (prefixWord ++ tailWord_5942943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5942973 : List Nat := [1, 4, 1, 2, 1, 2, 4, 2, 2, 2, 2]
def baseStart_5942973 : Nat := 118140960795 + 5942973 * 2 ^ 59
def prefixEnd_5942973 : Nat := 4983230072969 + 3 ^ 40 * 5942973 * 2
def baseEnd_5942973 : Nat := 3051601665692681824506271

theorem tailTrace_5942973 : CollatzResearch.WordTrace tailWord_5942973 prefixEnd_5942973 3051601665692681824506271 := by
  unfold tailWord_5942973
  simp only [CollatzResearch.WordTrace]
  refine ⟨216758032698631274826905573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144505355132420849884603715 216758032698631274826905573)
  ·
    refine ⟨40642131130993364030044795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 216758032698631274826905573 40642131130993364030044795)
    ·
      refine ⟨60963196696490046045067193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40642131130993364030044795 60963196696490046045067193)
      ·
        refine ⟨45722397522367534533800395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60963196696490046045067193 45722397522367534533800395)
        ·
          refine ⟨68583596283551301800700593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45722397522367534533800395 68583596283551301800700593)
          ·
            refine ⟨51437697212663476350525445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68583596283551301800700593 51437697212663476350525445)
            ·
              refine ⟨9644568227374401815723521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51437697212663476350525445 9644568227374401815723521)
              ·
                refine ⟨7233426170530801361792641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9644568227374401815723521 7233426170530801361792641)
                ·
                  refine ⟨5425069627898101021344481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7233426170530801361792641 5425069627898101021344481)
                  ·
                    refine ⟨4068802220923575766008361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5425069627898101021344481 4068802220923575766008361)
                    ·
                      refine ⟨3051601665692681824506271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4068802220923575766008361 3051601665692681824506271)
                      ·
                        rfl

theorem cell23_5942973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 2, 2, 2, 2].length) (baseStart_5942973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5942973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5942973 prefixEnd_5942973 := by exact prefixLift 5942973
  have htrace : WordTrace (prefixWord ++ tailWord_5942973) baseStart_5942973 baseEnd_5942973 := by
    simpa [prefixWord, tailWord_5942973, baseEnd_5942973] using wordTrace_append hprefix tailTrace_5942973
  have hstable : (prefixWord ++ tailWord_5942973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5942973).length < 2 ^ (prefixWord ++ tailWord_5942973).sum := by decide
  have hdescent : baseEnd_5942973 < baseStart_5942973 := by decide
  rcases family_descends (prefixWord ++ tailWord_5942973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5942999 : List Nat := [1, 1, 3, 2, 1, 3, 1, 2, 2, 5, 2]
def baseStart_5942999 : Nat := 118140960795 + 5942999 * 2 ^ 59
def prefixEnd_5942999 : Nat := 4983230072969 + 3 ^ 40 * 5942999 * 2
def baseEnd_5942999 : Nat := 3051615016189698722781151

theorem tailTrace_5942999 : CollatzResearch.WordTrace tailWord_5942999 prefixEnd_5942999 3051615016189698722781151 := by
  unfold tailWord_5942999
  simp only [CollatzResearch.WordTrace]
  refine ⟨216758980996537081267352051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144505987331024720844901367 216758980996537081267352051)
  ·
    refine ⟨325138471494805621901028077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216758980996537081267352051 325138471494805621901028077)
    ·
      refine ⟨121926926810552108212885529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 325138471494805621901028077 121926926810552108212885529)
      ·
        refine ⟨91445195107914081159664147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121926926810552108212885529 91445195107914081159664147)
        ·
          refine ⟨137167792661871121739496221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91445195107914081159664147 137167792661871121739496221)
          ·
            refine ⟨51437922248201670652311083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137167792661871121739496221 51437922248201670652311083)
            ·
              refine ⟨77156883372302505978466625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51437922248201670652311083 77156883372302505978466625)
              ·
                refine ⟨57867662529226879483849969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77156883372302505978466625 57867662529226879483849969)
                ·
                  refine ⟨43400746896920159612887477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57867662529226879483849969 43400746896920159612887477)
                  ·
                    refine ⟨4068820021586264963708201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43400746896920159612887477 4068820021586264963708201)
                    ·
                      refine ⟨3051615016189698722781151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4068820021586264963708201 3051615016189698722781151)
                      ·
                        rfl

theorem cell23_5942999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 5, 2].length) (baseStart_5942999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5942999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5942999 prefixEnd_5942999 := by exact prefixLift 5942999
  have htrace : WordTrace (prefixWord ++ tailWord_5942999) baseStart_5942999 baseEnd_5942999 := by
    simpa [prefixWord, tailWord_5942999, baseEnd_5942999] using wordTrace_append hprefix tailTrace_5942999
  have hstable : (prefixWord ++ tailWord_5942999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5942999).length < 2 ^ (prefixWord ++ tailWord_5942999).sum := by decide
  have hdescent : baseEnd_5942999 < baseStart_5942999 := by decide
  rcases family_descends (prefixWord ++ tailWord_5942999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5943009 : List Nat := [1, 2, 3, 1, 5, 1, 1, 1, 1, 7]
def baseStart_5943009 : Nat := 118140960795 + 5943009 * 2 ^ 59
def prefixEnd_5943009 : Nat := 4983230072969 + 3 ^ 40 * 5943009 * 2
def baseEnd_5943009 : Nat := 1017206716998747894552035

theorem tailTrace_5943009 : CollatzResearch.WordTrace tailWord_5943009 prefixEnd_5943009 1017206716998747894552035 := by
  unfold tailWord_5943009
  simp only [CollatzResearch.WordTrace]
  refine ⟨216759345726500852975216081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144506230484333901983477387 216759345726500852975216081)
  ·
    refine ⟨162569509294875639731412061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216759345726500852975216081 162569509294875639731412061)
    ·
      refine ⟨60963565985578364899279523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162569509294875639731412061 60963565985578364899279523)
      ·
        refine ⟨91445348978367547348919285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60963565985578364899279523 91445348978367547348919285)
        ·
          refine ⟨8573001466721957563961183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 91445348978367547348919285 8573001466721957563961183)
          ·
            refine ⟨12859502200082936345941775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8573001466721957563961183 12859502200082936345941775)
            ·
              refine ⟨19289253300124404518912663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12859502200082936345941775 19289253300124404518912663)
              ·
                refine ⟨28933879950186606778368995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19289253300124404518912663 28933879950186606778368995)
                ·
                  refine ⟨43400819925279910167553493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28933879950186606778368995 43400819925279910167553493)
                  ·
                    refine ⟨1017206716998747894552035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43400819925279910167553493 1017206716998747894552035)
                    ·
                      rfl

theorem cell23_5943009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 7].length) (baseStart_5943009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5943009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5943009 prefixEnd_5943009 := by exact prefixLift 5943009
  have htrace : WordTrace (prefixWord ++ tailWord_5943009) baseStart_5943009 baseEnd_5943009 := by
    simpa [prefixWord, tailWord_5943009, baseEnd_5943009] using wordTrace_append hprefix tailTrace_5943009
  have hstable : (prefixWord ++ tailWord_5943009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5943009).length < 2 ^ (prefixWord ++ tailWord_5943009).sum := by decide
  have hdescent : baseEnd_5943009 < baseStart_5943009 := by decide
  rcases family_descends (prefixWord ++ tailWord_5943009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5943039 : List Nat := [1, 1, 2, 2, 1, 3, 3, 3, 3, 4]
def baseStart_5943039 : Nat := 118140960795 + 5943039 * 2 ^ 59
def prefixEnd_5943039 : Nat := 4983230072969 + 3 ^ 40 * 5943039 * 2
def baseEnd_5943039 : Nat := 1017211851805292855426989

theorem tailTrace_5943039 : CollatzResearch.WordTrace tailWord_5943039 prefixEnd_5943039 1017211851805292855426989 := by
  unfold tailWord_5943039
  simp only [CollatzResearch.WordTrace]
  refine ⟨216760439916392168098808171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144506959944261445399205447 216760439916392168098808171)
  ·
    refine ⟨325140659874588252148212257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216760439916392168098808171 325140659874588252148212257)
    ·
      refine ⟨243855494905941189111159193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 325140659874588252148212257 243855494905941189111159193)
      ·
        refine ⟨182891621179455891833369395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243855494905941189111159193 182891621179455891833369395)
        ·
          refine ⟨274337431769183837750054093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182891621179455891833369395 274337431769183837750054093)
          ·
            refine ⟨102876536913443939156270285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 274337431769183837750054093 102876536913443939156270285)
            ·
              refine ⟨38578701342541477183601357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102876536913443939156270285 38578701342541477183601357)
              ·
                refine ⟨14467013003453053943850509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38578701342541477183601357 14467013003453053943850509)
                ·
                  refine ⟨5425129876294895228943941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14467013003453053943850509 5425129876294895228943941)
                  ·
                    refine ⟨1017211851805292855426989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5425129876294895228943941 1017211851805292855426989)
                    ·
                      rfl

theorem cell23_5943039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 3, 3, 4].length) (baseStart_5943039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5943039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5943039 prefixEnd_5943039 := by exact prefixLift 5943039
  have htrace : WordTrace (prefixWord ++ tailWord_5943039) baseStart_5943039 baseEnd_5943039 := by
    simpa [prefixWord, tailWord_5943039, baseEnd_5943039] using wordTrace_append hprefix tailTrace_5943039
  have hstable : (prefixWord ++ tailWord_5943039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5943039).length < 2 ^ (prefixWord ++ tailWord_5943039).sum := by decide
  have hdescent : baseEnd_5943039 < baseStart_5943039 := by decide
  rcases family_descends (prefixWord ++ tailWord_5943039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5943073 : List Nat := [1, 2, 3, 2, 1, 3, 3, 3, 1, 4]
def baseStart_5943073 : Nat := 118140960795 + 5943073 * 2 ^ 59
def prefixEnd_5943073 : Nat := 4983230072969 + 3 ^ 40 * 5943073 * 2
def baseEnd_5943073 : Nat := 1017217671252710477751937

theorem tailTrace_5943073 : CollatzResearch.WordTrace tailWord_5943073 prefixEnd_5943073 1017217671252710477751937 := by
  unfold tailWord_5943073
  simp only [CollatzResearch.WordTrace]
  refine ⟨216761679998268991905545873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144507786665512661270363915 216761679998268991905545873)
  ·
    refine ⟨162571259998701743929159405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216761679998268991905545873 162571259998701743929159405)
    ·
      refine ⟨60964222499513153973434777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162571259998701743929159405 60964222499513153973434777)
      ·
        refine ⟨45723166874634865480076083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60964222499513153973434777 45723166874634865480076083)
        ·
          refine ⟨68584750311952298220114125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45723166874634865480076083 68584750311952298220114125)
          ·
            refine ⟨25719281366982111832542797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68584750311952298220114125 25719281366982111832542797)
            ·
              refine ⟨9644730512618291937203549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25719281366982111832542797 9644730512618291937203549)
              ·
                refine ⟨3616773942231859476451331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9644730512618291937203549 3616773942231859476451331)
                ·
                  refine ⟨5425160913347789214676997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3616773942231859476451331 5425160913347789214676997)
                  ·
                    refine ⟨1017217671252710477751937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5425160913347789214676997 1017217671252710477751937)
                    ·
                      rfl

theorem cell23_5943073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 3, 1, 4].length) (baseStart_5943073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5943073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5943073 prefixEnd_5943073 := by exact prefixLift 5943073
  have htrace : WordTrace (prefixWord ++ tailWord_5943073) baseStart_5943073 baseEnd_5943073 := by
    simpa [prefixWord, tailWord_5943073, baseEnd_5943073] using wordTrace_append hprefix tailTrace_5943073
  have hstable : (prefixWord ++ tailWord_5943073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5943073).length < 2 ^ (prefixWord ++ tailWord_5943073).sum := by decide
  have hdescent : baseEnd_5943073 < baseStart_5943073 := by decide
  rcases family_descends (prefixWord ++ tailWord_5943073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5943090 : List Nat := [3, 2, 1, 1, 3, 3, 3, 2, 1, 4]
def baseStart_5943090 : Nat := 118140960795 + 5943090 * 2 ^ 59
def prefixEnd_5943090 : Nat := 4983230072969 + 3 ^ 40 * 5943090 * 2
def baseEnd_5943090 : Nat := 1017220580976419288914411

theorem tailTrace_5943090 : CollatzResearch.WordTrace tailWord_5943090 prefixEnd_5943090 1017220580976419288914411 := by
  unfold tailWord_5943090
  simp only [CollatzResearch.WordTrace]
  refine ⟨54190575009801850952228681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144508200026138269205943149 54190575009801850952228681)
  ·
    refine ⟨40642931257351388214171511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54190575009801850952228681 40642931257351388214171511)
    ·
      refine ⟨60964396886027082321257267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40642931257351388214171511 60964396886027082321257267)
      ·
        refine ⟨91446595329040623481885901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60964396886027082321257267 91446595329040623481885901)
        ·
          refine ⟨34292473248390233805707213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91446595329040623481885901 34292473248390233805707213)
          ·
            refine ⟨12859677468146337677140205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34292473248390233805707213 12859677468146337677140205)
            ·
              refine ⟨4822379050554876628927577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12859677468146337677140205 4822379050554876628927577)
              ·
                refine ⟨3616784287916157471695683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4822379050554876628927577 3616784287916157471695683)
                ·
                  refine ⟨5425176431874236207543525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3616784287916157471695683 5425176431874236207543525)
                  ·
                    refine ⟨1017220580976419288914411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5425176431874236207543525 1017220580976419288914411)
                    ·
                      rfl

theorem cell23_5943090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 3, 2, 1, 4].length) (baseStart_5943090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5943090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5943090 prefixEnd_5943090 := by exact prefixLift 5943090
  have htrace : WordTrace (prefixWord ++ tailWord_5943090) baseStart_5943090 baseEnd_5943090 := by
    simpa [prefixWord, tailWord_5943090, baseEnd_5943090] using wordTrace_append hprefix tailTrace_5943090
  have hstable : (prefixWord ++ tailWord_5943090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5943090).length < 2 ^ (prefixWord ++ tailWord_5943090).sum := by decide
  have hdescent : baseEnd_5943090 < baseStart_5943090 := by decide
  rcases family_descends (prefixWord ++ tailWord_5943090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5943103 : List Nat := [1, 1, 2, 2, 6, 2, 2, 1, 6]
def baseStart_5943103 : Nat := 118140960795 + 5943103 * 2 ^ 59
def prefixEnd_5943103 : Nat := 4983230072969 + 3 ^ 40 * 5943103 * 2
def baseEnd_5943103 : Nat := 339074268686418479542297

theorem tailTrace_5943103 : CollatzResearch.WordTrace tailWord_5943103 prefixEnd_5943103 339074268686418479542297 := by
  unfold tailWord_5943103
  simp only [CollatzResearch.WordTrace]
  refine ⟨216762774188160307029137963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144508516125440204686091975 216762774188160307029137963)
  ·
    refine ⟨325144161282240460543706945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216762774188160307029137963 325144161282240460543706945)
    ·
      refine ⟨243858120961680345407780209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 325144161282240460543706945 243858120961680345407780209)
      ·
        refine ⟨182893590721260259055835157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243858120961680345407780209 182893590721260259055835157)
        ·
          refine ⟨8573137065059074643242273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 182893590721260259055835157 8573137065059074643242273)
          ·
            refine ⟨6429852798794305982431705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8573137065059074643242273 6429852798794305982431705)
            ·
              refine ⟨4822389599095729486823779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6429852798794305982431705 4822389599095729486823779)
              ·
                refine ⟨7233584398643594230235669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4822389599095729486823779 7233584398643594230235669)
                ·
                  refine ⟨339074268686418479542297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7233584398643594230235669 339074268686418479542297)
                  ·
                    rfl

theorem cell23_5943103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 2, 1, 6].length) (baseStart_5943103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5943103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5943103 prefixEnd_5943103 := by exact prefixLift 5943103
  have htrace : WordTrace (prefixWord ++ tailWord_5943103) baseStart_5943103 baseEnd_5943103 := by
    simpa [prefixWord, tailWord_5943103, baseEnd_5943103] using wordTrace_append hprefix tailTrace_5943103
  have hstable : (prefixWord ++ tailWord_5943103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5943103).length < 2 ^ (prefixWord ++ tailWord_5943103).sum := by decide
  have hdescent : baseEnd_5943103 < baseStart_5943103 := by decide
  rcases family_descends (prefixWord ++ tailWord_5943103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5943116 : List Nat := [2, 2, 1, 3, 4, 1, 1, 1, 3, 5]
def baseStart_5943116 : Nat := 118140960795 + 5943116 * 2 ^ 59
def prefixEnd_5943116 : Nat := 4983230072969 + 3 ^ 40 * 5943116 * 2
def baseEnd_5943116 : Nat := 1017225031142091588339371

theorem tailTrace_5943116 : CollatzResearch.WordTrace tailWord_5943116 prefixEnd_5943116 1017225031142091588339371 := by
  unfold tailWord_5943116
  simp only [CollatzResearch.WordTrace]
  refine ⟨108381624168556605124680601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144508832224742140166240801 108381624168556605124680601)
  ·
    refine ⟨81286218126417453843510451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108381624168556605124680601 81286218126417453843510451)
    ·
      refine ⟨121929327189626180765265677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81286218126417453843510451 121929327189626180765265677)
      ·
        refine ⟨45723497696109817786974629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121929327189626180765265677 45723497696109817786974629)
        ·
          refine ⟨8573155818020590835057743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45723497696109817786974629 8573155818020590835057743)
          ·
            refine ⟨12859733727030886252586615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8573155818020590835057743 12859733727030886252586615)
            ·
              refine ⟨19289600590546329378879923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12859733727030886252586615 19289600590546329378879923)
              ·
                refine ⟨28934400885819494068319885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19289600590546329378879923 28934400885819494068319885)
                ·
                  refine ⟨10850400332182310275619957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28934400885819494068319885 10850400332182310275619957)
                  ·
                    refine ⟨1017225031142091588339371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10850400332182310275619957 1017225031142091588339371)
                    ·
                      rfl

theorem cell23_5943116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 3, 5].length) (baseStart_5943116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5943116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5943116 prefixEnd_5943116 := by exact prefixLift 5943116
  have htrace : WordTrace (prefixWord ++ tailWord_5943116) baseStart_5943116 baseEnd_5943116 := by
    simpa [prefixWord, tailWord_5943116, baseEnd_5943116] using wordTrace_append hprefix tailTrace_5943116
  have hstable : (prefixWord ++ tailWord_5943116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5943116).length < 2 ^ (prefixWord ++ tailWord_5943116).sum := by decide
  have hdescent : baseEnd_5943116 < baseStart_5943116 := by decide
  rcases family_descends (prefixWord ++ tailWord_5943116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5943129 : List Nat := [1, 2, 1, 2, 2, 3, 3, 2, 1, 6]
def baseStart_5943129 : Nat := 118140960795 + 5943129 * 2 ^ 59
def prefixEnd_5943129 : Nat := 4983230072969 + 3 ^ 40 * 5943129 * 2
def baseEnd_5943129 : Nat := 1017227256224927738051851

theorem tailTrace_5943129 : CollatzResearch.WordTrace tailWord_5943129 prefixEnd_5943129 1017227256224927738051851 := by
  unfold tailWord_5943129
  simp only [CollatzResearch.WordTrace]
  refine ⟨216763722486066113469584441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144509148324044075646389627 216763722486066113469584441)
  ·
    refine ⟨162572791864549585102188331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216763722486066113469584441 162572791864549585102188331)
    ·
      refine ⟨243859187796824377653282497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162572791864549585102188331 243859187796824377653282497)
      ·
        refine ⟨182894390847618283239961873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243859187796824377653282497 182894390847618283239961873)
        ·
          refine ⟨137170793135713712429971405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182894390847618283239961873 137170793135713712429971405)
          ·
            refine ⟨51439047425892642161239277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137170793135713712429971405 51439047425892642161239277)
            ·
              refine ⟨19289642784709740810464729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51439047425892642161239277 19289642784709740810464729)
              ·
                refine ⟨14467232088532305607848547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19289642784709740810464729 14467232088532305607848547)
                ·
                  refine ⟨21700848132798458411772821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14467232088532305607848547 21700848132798458411772821)
                  ·
                    refine ⟨1017227256224927738051851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21700848132798458411772821 1017227256224927738051851)
                    ·
                      rfl

theorem cell23_5943129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 2, 1, 6].length) (baseStart_5943129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5943129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5943129 prefixEnd_5943129 := by exact prefixLift 5943129
  have htrace : WordTrace (prefixWord ++ tailWord_5943129) baseStart_5943129 baseEnd_5943129 := by
    simpa [prefixWord, tailWord_5943129, baseEnd_5943129] using wordTrace_append hprefix tailTrace_5943129
  have hstable : (prefixWord ++ tailWord_5943129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5943129).length < 2 ^ (prefixWord ++ tailWord_5943129).sum := by decide
  have hdescent : baseEnd_5943129 < baseStart_5943129 := by decide
  rcases family_descends (prefixWord ++ tailWord_5943129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5943149 : List Nat := [1, 5, 1, 1, 1, 1, 2, 1, 3, 1, 6]
def baseStart_5943149 : Nat := 118140960795 + 5943149 * 2 ^ 59
def prefixEnd_5943149 : Nat := 4983230072969 + 3 ^ 40 * 5943149 * 2
def baseEnd_5943149 : Nat := 3051692038287873135905461

theorem tailTrace_5943149 : CollatzResearch.WordTrace tailWord_5943149 prefixEnd_5943149 3051692038287873135905461 := by
  unfold tailWord_5943149
  simp only [CollatzResearch.WordTrace]
  refine ⟨216764451945993656885312501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144509634630662437923541667 216764451945993656885312501)
  ·
    refine ⟨20321667369936905332998047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 216764451945993656885312501 20321667369936905332998047)
    ·
      refine ⟨30482501054905357999497071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20321667369936905332998047 30482501054905357999497071)
      ·
        refine ⟨45723751582358036999245607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30482501054905357999497071 45723751582358036999245607)
        ·
          refine ⟨68585627373537055498868411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45723751582358036999245607 68585627373537055498868411)
          ·
            refine ⟨102878441060305583248302617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68585627373537055498868411 102878441060305583248302617)
            ·
              refine ⟨77158830795229187436226963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102878441060305583248302617 77158830795229187436226963)
              ·
                refine ⟨115738246192843781154340445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77158830795229187436226963 115738246192843781154340445)
                ·
                  refine ⟨43401842322316417932877667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 115738246192843781154340445 43401842322316417932877667)
                  ·
                    refine ⟨65102763483474626899316501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43401842322316417932877667 65102763483474626899316501)
                    ·
                      refine ⟨3051692038287873135905461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65102763483474626899316501 3051692038287873135905461)
                      ·
                        rfl

theorem cell23_5943149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_5943149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5943149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5943149 prefixEnd_5943149 := by exact prefixLift 5943149
  have htrace : WordTrace (prefixWord ++ tailWord_5943149) baseStart_5943149 baseEnd_5943149 := by
    simpa [prefixWord, tailWord_5943149, baseEnd_5943149] using wordTrace_append hprefix tailTrace_5943149
  have hstable : (prefixWord ++ tailWord_5943149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5943149).length < 2 ^ (prefixWord ++ tailWord_5943149).sum := by decide
  have hdescent : baseEnd_5943149 < baseStart_5943149 := by decide
  rcases family_descends (prefixWord ++ tailWord_5943149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5943153 : List Nat := [1, 2, 2, 2, 1, 3, 2, 3, 3, 2, 2]
def baseStart_5943153 : Nat := 118140960795 + 5943153 * 2 ^ 59
def prefixEnd_5943153 : Nat := 4983230072969 + 3 ^ 40 * 5943153 * 2
def baseEnd_5943153 : Nat := 3051694092210491120255443

theorem tailTrace_5943153 : CollatzResearch.WordTrace tailWord_5943153 prefixEnd_5943153 3051694092210491120255443 := by
  unfold tailWord_5943153
  simp only [CollatzResearch.WordTrace]
  refine ⟨216764597837979165568458113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144509731891986110378972075 216764597837979165568458113)
  ·
    refine ⟨162573448378484374176343585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216764597837979165568458113 162573448378484374176343585)
    ·
      refine ⟨121930086283863280632257689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162573448378484374176343585 121930086283863280632257689)
      ·
        refine ⟨91447564712897460474193267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121930086283863280632257689 91447564712897460474193267)
        ·
          refine ⟨137171347069346190711289901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91447564712897460474193267 137171347069346190711289901)
          ·
            refine ⟨51439255151004821516733713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137171347069346190711289901 51439255151004821516733713)
            ·
              refine ⟨38579441363253616137550285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51439255151004821516733713 38579441363253616137550285)
              ·
                refine ⟨14467290511220106051581357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38579441363253616137550285 14467290511220106051581357)
                ·
                  refine ⟨5425233941707539769343009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14467290511220106051581357 5425233941707539769343009)
                  ·
                    refine ⟨4068925456280654827007257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5425233941707539769343009 4068925456280654827007257)
                    ·
                      refine ⟨3051694092210491120255443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4068925456280654827007257 3051694092210491120255443)
                      ·
                        rfl

theorem cell23_5943153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 3, 3, 2, 2].length) (baseStart_5943153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5943153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5943153 prefixEnd_5943153 := by exact prefixLift 5943153
  have htrace : WordTrace (prefixWord ++ tailWord_5943153) baseStart_5943153 baseEnd_5943153 := by
    simpa [prefixWord, tailWord_5943153, baseEnd_5943153] using wordTrace_append hprefix tailTrace_5943153
  have hstable : (prefixWord ++ tailWord_5943153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5943153).length < 2 ^ (prefixWord ++ tailWord_5943153).sum := by decide
  have hdescent : baseEnd_5943153 < baseStart_5943153 := by decide
  rcases family_descends (prefixWord ++ tailWord_5943153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5943209 : List Nat := [1, 2, 1, 1, 1, 1, 4, 3, 2, 3, 4]
def baseStart_5943209 : Nat := 118140960795 + 5943209 * 2 ^ 59
def prefixEnd_5943209 : Nat := 4983230072969 + 3 ^ 40 * 5943209 * 2
def baseEnd_5943209 : Nat := 3051722847127142901155185

theorem tailTrace_5943209 : CollatzResearch.WordTrace tailWord_5943209 prefixEnd_5943209 3051722847127142901155185 := by
  unfold tailWord_5943209
  simp only [CollatzResearch.WordTrace]
  refine ⟨216766640325776287132496681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144511093550517524754997787 216766640325776287132496681)
  ·
    refine ⟨162574980244332215349372511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216766640325776287132496681 162574980244332215349372511)
    ·
      refine ⟨243862470366498323024058767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162574980244332215349372511 243862470366498323024058767)
      ·
        refine ⟨365793705549747484536088151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243862470366498323024058767 365793705549747484536088151)
        ·
          refine ⟨548690558324621226804132227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365793705549747484536088151 548690558324621226804132227)
          ·
            refine ⟨823035837486931840206198341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 548690558324621226804132227 823035837486931840206198341)
            ·
              refine ⟨154319219528799720038662189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 823035837486931840206198341 154319219528799720038662189)
              ·
                refine ⟨57869707323299895014498321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 154319219528799720038662189 57869707323299895014498321)
                ·
                  refine ⟨43402280492474921260873741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57869707323299895014498321 43402280492474921260873741)
                  ·
                    refine ⟨16275855184678095472827653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43402280492474921260873741 16275855184678095472827653)
                    ·
                      refine ⟨3051722847127142901155185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16275855184678095472827653 3051722847127142901155185)
                      ·
                        rfl

theorem cell23_5943209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 3, 4].length) (baseStart_5943209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5943209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5943209 prefixEnd_5943209 := by exact prefixLift 5943209
  have htrace : WordTrace (prefixWord ++ tailWord_5943209) baseStart_5943209 baseEnd_5943209 := by
    simpa [prefixWord, tailWord_5943209, baseEnd_5943209] using wordTrace_append hprefix tailTrace_5943209
  have hstable : (prefixWord ++ tailWord_5943209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5943209).length < 2 ^ (prefixWord ++ tailWord_5943209).sum := by decide
  have hdescent : baseEnd_5943209 < baseStart_5943209 := by decide
  rcases family_descends (prefixWord ++ tailWord_5943209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5943214 : List Nat := [4, 1, 5, 1, 2, 1, 1, 1, 1, 6]
def baseStart_5943214 : Nat := 118140960795 + 5943214 * 2 ^ 59
def prefixEnd_5943214 : Nat := 4983230072969 + 3 ^ 40 * 5943214 * 2
def baseEnd_5943214 : Nat := 1017241804843471793864221

theorem tailTrace_5943214 : CollatzResearch.WordTrace tailWord_5943214 prefixEnd_5943214 1017241804843471793864221 := by
  unfold tailWord_5943214
  simp only [CollatzResearch.WordTrace]
  refine ⟨27095852836344771623303587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144511215127172115324285797 27095852836344771623303587)
  ·
    refine ⟨40643779254517157434955381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27095852836344771623303587 40643779254517157434955381)
    ·
      refine ⟨3810354305110983509527067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40643779254517157434955381 3810354305110983509527067)
      ·
        refine ⟨5715531457666475264290601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3810354305110983509527067 5715531457666475264290601)
        ·
          refine ⟨4286648593249856448217951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5715531457666475264290601 4286648593249856448217951)
          ·
            refine ⟨6429972889874784672326927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4286648593249856448217951 6429972889874784672326927)
            ·
              refine ⟨9644959334812177008490391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6429972889874784672326927 9644959334812177008490391)
              ·
                refine ⟨14467439002218265512735587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9644959334812177008490391 14467439002218265512735587)
                ·
                  refine ⟨21701158503327398269103381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14467439002218265512735587 21701158503327398269103381)
                  ·
                    refine ⟨1017241804843471793864221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21701158503327398269103381 1017241804843471793864221)
                    ·
                      rfl

theorem cell23_5943214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_5943214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5943214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5943214 prefixEnd_5943214 := by exact prefixLift 5943214
  have htrace : WordTrace (prefixWord ++ tailWord_5943214) baseStart_5943214 baseEnd_5943214 := by
    simpa [prefixWord, tailWord_5943214, baseEnd_5943214] using wordTrace_append hprefix tailTrace_5943214
  have hstable : (prefixWord ++ tailWord_5943214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5943214).length < 2 ^ (prefixWord ++ tailWord_5943214).sum := by decide
  have hdescent : baseEnd_5943214 < baseStart_5943214 := by decide
  rcases family_descends (prefixWord ++ tailWord_5943214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5943219 : List Nat := [1, 1, 1, 2, 3, 1, 3, 3, 2, 6]
def baseStart_5943219 : Nat := 118140960795 + 5943219 * 2 ^ 59
def prefixEnd_5943219 : Nat := 4983230072969 + 3 ^ 40 * 5943219 * 2
def baseEnd_5943219 : Nat := 1017242660644562620676713

theorem tailTrace_5943219 : CollatzResearch.WordTrace tailWord_5943219 prefixEnd_5943219 1017242660644562620676713 := by
  unfold tailWord_5943219
  simp only [CollatzResearch.WordTrace]
  refine ⟨216767005055740058840360711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144511336703826705893573807 216767005055740058840360711)
  ·
    refine ⟨325150507583610088260541067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216767005055740058840360711 325150507583610088260541067)
    ·
      refine ⟨487725761375415132390811601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325150507583610088260541067 487725761375415132390811601)
      ·
        refine ⟨365794321031561349293108701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 487725761375415132390811601 365794321031561349293108701)
        ·
          refine ⟨137172870386835505984915763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 365794321031561349293108701 137172870386835505984915763)
          ·
            refine ⟨205759305580253258977373645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137172870386835505984915763 205759305580253258977373645)
            ·
              refine ⟨77159739592594972116515117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 205759305580253258977373645 77159739592594972116515117)
              ·
                refine ⟨28934902347223114543693169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77159739592594972116515117 28934902347223114543693169)
                ·
                  refine ⟨21701176760417335907769877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28934902347223114543693169 21701176760417335907769877)
                  ·
                    refine ⟨1017242660644562620676713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21701176760417335907769877 1017242660644562620676713)
                    ·
                      rfl

theorem cell23_5943219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 2, 6].length) (baseStart_5943219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5943219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5943219 prefixEnd_5943219 := by exact prefixLift 5943219
  have htrace : WordTrace (prefixWord ++ tailWord_5943219) baseStart_5943219 baseEnd_5943219 := by
    simpa [prefixWord, tailWord_5943219, baseEnd_5943219] using wordTrace_append hprefix tailTrace_5943219
  have hstable : (prefixWord ++ tailWord_5943219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5943219).length < 2 ^ (prefixWord ++ tailWord_5943219).sum := by decide
  have hdescent : baseEnd_5943219 < baseStart_5943219 := by decide
  rcases family_descends (prefixWord ++ tailWord_5943219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5943230 : List Nat := [4, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2]
def baseStart_5943230 : Nat := 118140960795 + 5943230 * 2 ^ 59
def prefixEnd_5943230 : Nat := 4983230072969 + 3 ^ 40 * 5943230 * 2
def baseEnd_5943230 : Nat := 3051733630220887318992589

theorem tailTrace_5943230 : CollatzResearch.WordTrace tailWord_5943230 prefixEnd_5943230 3051733630220887318992589 := by
  unfold tailWord_5943230
  simp only [CollatzResearch.WordTrace]
  refine ⟨27095925782337525964876393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144511604172466805146007429 27095925782337525964876393)
  ·
    refine ⟨20321944336753144473657295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27095925782337525964876393 20321944336753144473657295)
    ·
      refine ⟨30482916505129716710485943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20321944336753144473657295 30482916505129716710485943)
      ·
        refine ⟨45724374757694575065728915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30482916505129716710485943 45724374757694575065728915)
        ·
          refine ⟨68586562136541862598593373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45724374757694575065728915 68586562136541862598593373)
          ·
            refine ⟨25719960801203198474472515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68586562136541862598593373 25719960801203198474472515)
            ·
              refine ⟨38579941201804797711708773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25719960801203198474472515 38579941201804797711708773)
              ·
                refine ⟨7233738975338399570945395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38579941201804797711708773 7233738975338399570945395)
                ·
                  refine ⟨10850608463007599356418093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7233738975338399570945395 10850608463007599356418093)
                  ·
                    refine ⟨4068978173627849758656785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10850608463007599356418093 4068978173627849758656785)
                    ·
                      refine ⟨3051733630220887318992589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4068978173627849758656785 3051733630220887318992589)
                      ·
                        rfl

theorem cell23_5943230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2].length) (baseStart_5943230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5943230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5943230 prefixEnd_5943230 := by exact prefixLift 5943230
  have htrace : WordTrace (prefixWord ++ tailWord_5943230) baseStart_5943230 baseEnd_5943230 := by
    simpa [prefixWord, tailWord_5943230, baseEnd_5943230] using wordTrace_append hprefix tailTrace_5943230
  have hstable : (prefixWord ++ tailWord_5943230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5943230).length < 2 ^ (prefixWord ++ tailWord_5943230).sum := by decide
  have hdescent : baseEnd_5943230 < baseStart_5943230 := by decide
  rcases family_descends (prefixWord ++ tailWord_5943230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5943243 : List Nat := [1, 1, 1, 1, 3, 4, 1, 1, 6, 2, 2]
def baseStart_5943243 : Nat := 118140960795 + 5943243 * 2 ^ 59
def prefixEnd_5943243 : Nat := 4983230072969 + 3 ^ 40 * 5943243 * 2
def baseEnd_5943243 : Nat := 3051740305469395768130029

theorem tailTrace_5943243 : CollatzResearch.WordTrace tailWord_5943243 prefixEnd_5943243 3051740305469395768130029 := by
  unfold tailWord_5943243
  simp only [CollatzResearch.WordTrace]
  refine ⟨216767880407653110939234383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144511920271768740626156255 216767880407653110939234383)
  ·
    refine ⟨325151820611479666408851575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216767880407653110939234383 325151820611479666408851575)
    ·
      refine ⟨487727730917219499613277363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325151820611479666408851575 487727730917219499613277363)
      ·
        refine ⟨731591596375829249419916045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 487727730917219499613277363 731591596375829249419916045)
        ·
          refine ⟨274346848640935968532468517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 731591596375829249419916045 274346848640935968532468517)
          ·
            refine ⟨51440034120175494099837847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 274346848640935968532468517 51440034120175494099837847)
            ·
              refine ⟨77160051180263241149756771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51440034120175494099837847 77160051180263241149756771)
              ·
                refine ⟨115740076770394861724635157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77160051180263241149756771 115740076770394861724635157)
                ·
                  refine ⟨5425316098612259143342273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 115740076770394861724635157 5425316098612259143342273)
                  ·
                    refine ⟨4068987073959194357506705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5425316098612259143342273 4068987073959194357506705)
                    ·
                      refine ⟨3051740305469395768130029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4068987073959194357506705 3051740305469395768130029)
                      ·
                        rfl

theorem cell23_5943243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 6, 2, 2].length) (baseStart_5943243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5943243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5943243 prefixEnd_5943243 := by exact prefixLift 5943243
  have htrace : WordTrace (prefixWord ++ tailWord_5943243) baseStart_5943243 baseEnd_5943243 := by
    simpa [prefixWord, tailWord_5943243, baseEnd_5943243] using wordTrace_append hprefix tailTrace_5943243
  have hstable : (prefixWord ++ tailWord_5943243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5943243).length < 2 ^ (prefixWord ++ tailWord_5943243).sum := by decide
  have hdescent : baseEnd_5943243 < baseStart_5943243 := by decide
  rcases family_descends (prefixWord ++ tailWord_5943243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5943246 : List Nat := [4, 1, 1, 1, 2, 2, 3, 1, 2, 1, 5]
def baseStart_5943246 : Nat := 118140960795 + 5943246 * 2 ^ 59
def prefixEnd_5943246 : Nat := 4983230072969 + 3 ^ 40 * 5943246 * 2
def baseEnd_5943246 : Nat := 3051741845911359256392515

theorem tailTrace_5943246 : CollatzResearch.WordTrace tailWord_5943246 prefixEnd_5943246 3051741845911359256392515 := by
  unfold tailWord_5943246
  simp only [CollatzResearch.WordTrace]
  refine ⟨27095998728330280306449199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144511993217761494967729061 27095998728330280306449199)
  ·
    refine ⟨40643998092495420459673799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27095998728330280306449199 40643998092495420459673799)
    ·
      refine ⟨60965997138743130689510699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40643998092495420459673799 60965997138743130689510699)
      ·
        refine ⟨91448995708114696034266049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60965997138743130689510699 91448995708114696034266049)
        ·
          refine ⟨68586746781086022025699537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91448995708114696034266049 68586746781086022025699537)
          ·
            refine ⟨51440060085814516519274653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68586746781086022025699537 51440060085814516519274653)
            ·
              refine ⟨19290022532180443694727995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51440060085814516519274653 19290022532180443694727995)
              ·
                refine ⟨28935033798270665542091993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19290022532180443694727995 28935033798270665542091993)
                ·
                  refine ⟨21701275348702999156568995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28935033798270665542091993 21701275348702999156568995)
                  ·
                    refine ⟨32551913023054498734853493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21701275348702999156568995 32551913023054498734853493)
                    ·
                      refine ⟨3051741845911359256392515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32551913023054498734853493 3051741845911359256392515)
                      ·
                        rfl

theorem cell23_5943246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 2, 1, 5].length) (baseStart_5943246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5943246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5943246 prefixEnd_5943246 := by exact prefixLift 5943246
  have htrace : WordTrace (prefixWord ++ tailWord_5943246) baseStart_5943246 baseEnd_5943246 := by
    simpa [prefixWord, tailWord_5943246, baseEnd_5943246] using wordTrace_append hprefix tailTrace_5943246
  have hstable : (prefixWord ++ tailWord_5943246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5943246).length < 2 ^ (prefixWord ++ tailWord_5943246).sum := by decide
  have hdescent : baseEnd_5943246 < baseStart_5943246 := by decide
  rcases family_descends (prefixWord ++ tailWord_5943246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5943276 : List Nat := [2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 3]
def baseStart_5943276 : Nat := 118140960795 + 5943276 * 2 ^ 59
def prefixEnd_5943276 : Nat := 4983230072969 + 3 ^ 40 * 5943276 * 2
def baseEnd_5943276 : Nat := 3051757250330994139017377

theorem tailTrace_5943276 : CollatzResearch.WordTrace tailWord_5943276 prefixEnd_5943276 3051757250330994139017377 := by
  unfold tailWord_5943276
  simp only [CollatzResearch.WordTrace]
  refine ⟨108384542008266778787592841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144512722677689038383457121 108384542008266778787592841)
  ·
    refine ⟨81288406506200084090694631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108384542008266778787592841 81288406506200084090694631)
    ·
      refine ⟨121932609759300126136041947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81288406506200084090694631 121932609759300126136041947)
      ·
        refine ⟨182898914638950189204062921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121932609759300126136041947 182898914638950189204062921)
        ·
          refine ⟨137174185979212641903047191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182898914638950189204062921 137174185979212641903047191)
          ·
            refine ⟨205761278968818962854570787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137174185979212641903047191 205761278968818962854570787)
            ·
              refine ⟨308641918453228444281856181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205761278968818962854570787 308641918453228444281856181)
              ·
                refine ⟨28935179854990166651424017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 308641918453228444281856181 28935179854990166651424017)
                ·
                  refine ⟨21701384891242624988568013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28935179854990166651424017 21701384891242624988568013)
                  ·
                    refine ⟨8138019334215984370713005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21701384891242624988568013 8138019334215984370713005)
                    ·
                      refine ⟨3051757250330994139017377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8138019334215984370713005 3051757250330994139017377)
                      ·
                        rfl

theorem cell23_5943276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 3].length) (baseStart_5943276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5943276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5943276 prefixEnd_5943276 := by exact prefixLift 5943276
  have htrace : WordTrace (prefixWord ++ tailWord_5943276) baseStart_5943276 baseEnd_5943276 := by
    simpa [prefixWord, tailWord_5943276, baseEnd_5943276] using wordTrace_append hprefix tailTrace_5943276
  have hstable : (prefixWord ++ tailWord_5943276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5943276).length < 2 ^ (prefixWord ++ tailWord_5943276).sum := by decide
  have hdescent : baseEnd_5943276 < baseStart_5943276 := by decide
  rcases family_descends (prefixWord ++ tailWord_5943276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5943317 : List Nat := [1, 3, 2, 1, 5, 2, 2, 2, 5]
def baseStart_5943317 : Nat := 118140960795 + 5943317 * 2 ^ 59
def prefixEnd_5943317 : Nat := 4983230072969 + 3 ^ 40 * 5943317 * 2
def baseEnd_5943317 : Nat := 339086478115314275400521

theorem tailTrace_5943317 : CollatzResearch.WordTrace tailWord_5943317 prefixEnd_5943317 339086478115314275400521 := by
  unfold tailWord_5943317
  simp only [CollatzResearch.WordTrace]
  refine ⟨216770579409385021577428205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144513719606256681051618803 216770579409385021577428205)
  ·
    refine ⟨81288967278519383091535577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216770579409385021577428205 81288967278519383091535577)
    ·
      refine ⟨60966725458889537318651683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81288967278519383091535577 60966725458889537318651683)
      ·
        refine ⟨91450088188334305977977525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60966725458889537318651683 91450088188334305977977525)
        ·
          refine ⟨8573445767656341185435393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 91450088188334305977977525 8573445767656341185435393)
          ·
            refine ⟨6430084325742255889076545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8573445767656341185435393 6430084325742255889076545)
            ·
              refine ⟨4822563244306691916807409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6430084325742255889076545 4822563244306691916807409)
              ·
                refine ⟨3616922433230018937605557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4822563244306691916807409 3616922433230018937605557)
                ·
                  refine ⟨339086478115314275400521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3616922433230018937605557 339086478115314275400521)
                  ·
                    rfl

theorem cell23_5943317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 2, 2, 5].length) (baseStart_5943317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5943317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5943317 prefixEnd_5943317 := by exact prefixLift 5943317
  have htrace : WordTrace (prefixWord ++ tailWord_5943317) baseStart_5943317 baseEnd_5943317 := by
    simpa [prefixWord, tailWord_5943317, baseEnd_5943317] using wordTrace_append hprefix tailTrace_5943317
  have hstable : (prefixWord ++ tailWord_5943317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5943317).length < 2 ^ (prefixWord ++ tailWord_5943317).sum := by decide
  have hdescent : baseEnd_5943317 < baseStart_5943317 := by decide
  rcases family_descends (prefixWord ++ tailWord_5943317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5943333 : List Nat := [1, 3, 1, 2, 2, 3, 1, 1, 1, 6, 2]
def baseStart_5943333 : Nat := 118140960795 + 5943333 * 2 ^ 59
def prefixEnd_5943333 : Nat := 4983230072969 + 3 ^ 40 * 5943333 * 2
def baseEnd_5943333 : Nat := 3051786518728300416004615

theorem tailTrace_5943333 : CollatzResearch.WordTrace tailWord_5943333 prefixEnd_5943333 3051786518728300416004615 := by
  unfold tailWord_5943333
  simp only [CollatzResearch.WordTrace]
  refine ⟨216771162977327056310010653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144514108651551370873340435 216771162977327056310010653)
  ·
    refine ⟨81289186116497646116253995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216771162977327056310010653 81289186116497646116253995)
    ·
      refine ⟨121933779174746469174380993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81289186116497646116253995 121933779174746469174380993)
      ·
        refine ⟨91450334381059851880785745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121933779174746469174380993 91450334381059851880785745)
        ·
          refine ⟨68587750785794888910589309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91450334381059851880785745 68587750785794888910589309)
          ·
            refine ⟨25720406544673083341470991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68587750785794888910589309 25720406544673083341470991)
            ·
              refine ⟨38580609817009625012206487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25720406544673083341470991 38580609817009625012206487)
              ·
                refine ⟨57870914725514437518309731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38580609817009625012206487 57870914725514437518309731)
                ·
                  refine ⟨86806372088271656277464597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57870914725514437518309731 86806372088271656277464597)
                  ·
                    refine ⟨4069048691637733888006153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 86806372088271656277464597 4069048691637733888006153)
                    ·
                      refine ⟨3051786518728300416004615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4069048691637733888006153 3051786518728300416004615)
                      ·
                        rfl

theorem cell23_5943333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 6, 2].length) (baseStart_5943333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5943333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5943333 prefixEnd_5943333 := by exact prefixLift 5943333
  have htrace : WordTrace (prefixWord ++ tailWord_5943333) baseStart_5943333 baseEnd_5943333 := by
    simpa [prefixWord, tailWord_5943333, baseEnd_5943333] using wordTrace_append hprefix tailTrace_5943333
  have hstable : (prefixWord ++ tailWord_5943333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5943333).length < 2 ^ (prefixWord ++ tailWord_5943333).sum := by decide
  have hdescent : baseEnd_5943333 < baseStart_5943333 := by decide
  rcases family_descends (prefixWord ++ tailWord_5943333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5943350 : List Nat := [5, 1, 2, 1, 1, 1, 1, 2, 1, 6, 2]
def baseStart_5943350 : Nat := 118140960795 + 5943350 * 2 ^ 59
def prefixEnd_5943350 : Nat := 4983230072969 + 3 ^ 40 * 5943350 * 2
def baseEnd_5943350 : Nat := 3051795247899426849492037

theorem tailTrace_5943350 : CollatzResearch.WordTrace tailWord_5943350 prefixEnd_5943350 3051795247899426849492037 := by
  unfold tailWord_5943350
  simp only [CollatzResearch.WordTrace]
  refine ⟨13548236438641591763336219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 144514522012176978808919669 13548236438641591763336219)
  ·
    refine ⟨20322354657962387645004329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13548236438641591763336219 20322354657962387645004329)
    ·
      refine ⟨15241765993471790733753247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20322354657962387645004329 15241765993471790733753247)
      ·
        refine ⟨22862648990207686100629871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15241765993471790733753247 22862648990207686100629871)
        ·
          refine ⟨34293973485311529150944807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22862648990207686100629871 34293973485311529150944807)
          ·
            refine ⟨51440960227967293726417211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34293973485311529150944807 51440960227967293726417211)
            ·
              refine ⟨77161440341950940589625817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51440960227967293726417211 77161440341950940589625817)
              ·
                refine ⟨57871080256463205442219363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77161440341950940589625817 57871080256463205442219363)
                ·
                  refine ⟨86806620384694808163329045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57871080256463205442219363 86806620384694808163329045)
                  ·
                    refine ⟨4069060330532569132656049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 86806620384694808163329045 4069060330532569132656049)
                    ·
                      refine ⟨3051795247899426849492037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4069060330532569132656049 3051795247899426849492037)
                      ·
                        rfl

theorem cell23_5943350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 1, 6, 2].length) (baseStart_5943350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5943350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5943350 prefixEnd_5943350 := by exact prefixLift 5943350
  have htrace : WordTrace (prefixWord ++ tailWord_5943350) baseStart_5943350 baseEnd_5943350 := by
    simpa [prefixWord, tailWord_5943350, baseEnd_5943350] using wordTrace_append hprefix tailTrace_5943350
  have hstable : (prefixWord ++ tailWord_5943350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5943350).length < 2 ^ (prefixWord ++ tailWord_5943350).sum := by decide
  have hdescent : baseEnd_5943350 < baseStart_5943350 := by decide
  rcases family_descends (prefixWord ++ tailWord_5943350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5943356 : List Nat := [2, 2, 2, 2, 2, 1, 2, 2, 8]
def baseStart_5943356 : Nat := 118140960795 + 5943356 * 2 ^ 59
def prefixEnd_5943356 : Nat := 4983230072969 + 3 ^ 40 * 5943356 * 2
def baseEnd_5943356 : Nat := 339088703198150425113001

theorem tailTrace_5943356 : CollatzResearch.WordTrace tailWord_5943356 prefixEnd_5943356 339088703198150425113001 := by
  unfold tailWord_5943356
  simp only [CollatzResearch.WordTrace]
  refine ⟨108386000928121865619048961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144514667904162487492065281 108386000928121865619048961)
  ·
    refine ⟨81289500696091399214286721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108386000928121865619048961 81289500696091399214286721)
    ·
      refine ⟨60967125522068549410715041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81289500696091399214286721 60967125522068549410715041)
      ·
        refine ⟨45725344141551412058036281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60967125522068549410715041 45725344141551412058036281)
        ·
          refine ⟨34294008106163559043527211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45725344141551412058036281 34294008106163559043527211)
          ·
            refine ⟨51441012159245338565290817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34294008106163559043527211 51441012159245338565290817)
            ·
              refine ⟨38580759119434003923968113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51441012159245338565290817 38580759119434003923968113)
              ·
                refine ⟨28935569339575502942976085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38580759119434003923968113 28935569339575502942976085)
                ·
                  refine ⟨339088703198150425113001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28935569339575502942976085 339088703198150425113001)
                  ·
                    rfl

theorem cell23_5943356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 8].length) (baseStart_5943356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5943356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5943356 prefixEnd_5943356 := by exact prefixLift 5943356
  have htrace : WordTrace (prefixWord ++ tailWord_5943356) baseStart_5943356 baseEnd_5943356 := by
    simpa [prefixWord, tailWord_5943356, baseEnd_5943356] using wordTrace_append hprefix tailTrace_5943356
  have hstable : (prefixWord ++ tailWord_5943356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5943356).length < 2 ^ (prefixWord ++ tailWord_5943356).sum := by decide
  have hdescent : baseEnd_5943356 < baseStart_5943356 := by decide
  rcases family_descends (prefixWord ++ tailWord_5943356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5943360 : List Nat := [2, 1, 1, 2, 2, 4, 1, 5, 1, 4]
def baseStart_5943360 : Nat := 118140960795 + 5943360 * 2 ^ 59
def prefixEnd_5943360 : Nat := 4983230072969 + 3 ^ 40 * 5943360 * 2
def baseEnd_5943360 : Nat := 1017266794235323936788997

theorem tailTrace_5943360 : CollatzResearch.WordTrace tailWord_5943360 prefixEnd_5943360 1017266794235323936788997 := by
  unfold tailWord_5943360
  simp only [CollatzResearch.WordTrace]
  refine ⟨108386073874114619960621767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144514765165486159947495689 108386073874114619960621767)
  ·
    refine ⟨162579110811171929940932651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108386073874114619960621767 162579110811171929940932651)
    ·
      refine ⟨243868666216757894911398977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162579110811171929940932651 243868666216757894911398977)
      ·
        refine ⟨182901499662568421183549233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243868666216757894911398977 182901499662568421183549233)
        ·
          refine ⟨137176124746926315887661925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182901499662568421183549233 137176124746926315887661925)
          ·
            refine ⟨25720523390048684228936611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 137176124746926315887661925 25720523390048684228936611)
            ·
              refine ⟨38580785085073026343404917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25720523390048684228936611 38580785085073026343404917)
              ·
                refine ⟨3616948601725596219694211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38580785085073026343404917 3616948601725596219694211)
                ·
                  refine ⟨5425422902588394329541317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3616948601725596219694211 5425422902588394329541317)
                  ·
                    refine ⟨1017266794235323936788997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5425422902588394329541317 1017266794235323936788997)
                    ·
                      rfl

theorem cell23_5943360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 5, 1, 4].length) (baseStart_5943360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5943360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5943360 prefixEnd_5943360 := by exact prefixLift 5943360
  have htrace : WordTrace (prefixWord ++ tailWord_5943360) baseStart_5943360 baseEnd_5943360 := by
    simpa [prefixWord, tailWord_5943360, baseEnd_5943360] using wordTrace_append hprefix tailTrace_5943360
  have hstable : (prefixWord ++ tailWord_5943360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5943360).length < 2 ^ (prefixWord ++ tailWord_5943360).sum := by decide
  have hdescent : baseEnd_5943360 < baseStart_5943360 := by decide
  rcases family_descends (prefixWord ++ tailWord_5943360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5943373 : List Nat := [1, 6, 1, 1, 1, 1, 3, 1, 8]
def baseStart_5943373 : Nat := 118140960795 + 5943373 * 2 ^ 59
def prefixEnd_5943373 : Nat := 4983230072969 + 3 ^ 40 * 5943373 * 2
def baseEnd_5943373 : Nat := 339089673106053362167159

theorem tailTrace_5943373 : CollatzResearch.WordTrace tailWord_5943373 prefixEnd_5943373 339089673106053362167159 := by
  unfold tailWord_5943373
  simp only [CollatzResearch.WordTrace]
  refine ⟨216772621897182143141466773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144515081264788095427644515 216772621897182143141466773)
  ·
    refine ⟨10161216651430412959756255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 216772621897182143141466773 10161216651430412959756255)
    ·
      refine ⟨15241824977145619439634383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10161216651430412959756255 15241824977145619439634383)
      ·
        refine ⟨22862737465718429159451575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15241824977145619439634383 22862737465718429159451575)
        ·
          refine ⟨34294106198577643739177363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22862737465718429159451575 34294106198577643739177363)
          ·
            refine ⟨51441159297866465608766045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34294106198577643739177363 51441159297866465608766045)
            ·
              refine ⟨19290434736699924603287267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51441159297866465608766045 19290434736699924603287267)
              ·
                refine ⟨28935652105049886904930901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19290434736699924603287267 28935652105049886904930901)
                ·
                  refine ⟨339089673106053362167159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28935652105049886904930901 339089673106053362167159)
                  ·
                    rfl

theorem cell23_5943373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_5943373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5943373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5943373 prefixEnd_5943373 := by exact prefixLift 5943373
  have htrace : WordTrace (prefixWord ++ tailWord_5943373) baseStart_5943373 baseEnd_5943373 := by
    simpa [prefixWord, tailWord_5943373, baseEnd_5943373] using wordTrace_append hprefix tailTrace_5943373
  have hstable : (prefixWord ++ tailWord_5943373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5943373).length < 2 ^ (prefixWord ++ tailWord_5943373).sum := by decide
  have hdescent : baseEnd_5943373 < baseStart_5943373 := by decide
  rcases family_descends (prefixWord ++ tailWord_5943373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5943396 : List Nat := [2, 3, 1, 1, 2, 1, 2, 1, 2, 1, 7]
def baseStart_5943396 : Nat := 118140960795 + 5943396 * 2 ^ 59
def prefixEnd_5943396 : Nat := 4983230072969 + 3 ^ 40 * 5943396 * 2
def baseEnd_5943396 : Nat := 3051818868009533669516825

theorem tailTrace_5943396 : CollatzResearch.WordTrace tailWord_5943396 prefixEnd_5943396 3051818868009533669516825 := by
  unfold tailWord_5943396
  simp only [CollatzResearch.WordTrace]
  refine ⟨108386730388049409034777021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144515640517399212046369361 108386730388049409034777021)
  ·
    refine ⟨40645023895518528388041383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108386730388049409034777021 40645023895518528388041383)
    ·
      refine ⟨60967535843277792582062075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40645023895518528388041383 60967535843277792582062075)
      ·
        refine ⟨91451303764916688873093113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60967535843277792582062075 91451303764916688873093113)
        ·
          refine ⟨68588477823687516654819835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91451303764916688873093113 68588477823687516654819835)
          ·
            refine ⟨102882716735531274982229753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68588477823687516654819835 102882716735531274982229753)
            ·
              refine ⟨77162037551648456236672315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102882716735531274982229753 77162037551648456236672315)
              ·
                refine ⟨115743056327472684355008473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77162037551648456236672315 115743056327472684355008473)
                ·
                  refine ⟨86807292245604513266256355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115743056327472684355008473 86807292245604513266256355)
                  ·
                    refine ⟨130210938368406769899384533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 86807292245604513266256355 130210938368406769899384533)
                    ·
                      refine ⟨3051818868009533669516825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 130210938368406769899384533 3051818868009533669516825)
                      ·
                        rfl

theorem cell23_5943396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_5943396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5943396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5943396 prefixEnd_5943396 := by exact prefixLift 5943396
  have htrace : WordTrace (prefixWord ++ tailWord_5943396) baseStart_5943396 baseEnd_5943396 := by
    simpa [prefixWord, tailWord_5943396, baseEnd_5943396] using wordTrace_append hprefix tailTrace_5943396
  have hstable : (prefixWord ++ tailWord_5943396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5943396).length < 2 ^ (prefixWord ++ tailWord_5943396).sum := by decide
  have hdescent : baseEnd_5943396 < baseStart_5943396 := by decide
  rcases family_descends (prefixWord ++ tailWord_5943396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5943410 : List Nat := [3, 2, 1, 2, 2, 2, 2, 1, 1, 5, 2]
def baseStart_5943410 : Nat := 118140960795 + 5943410 * 2 ^ 59
def prefixEnd_5943410 : Nat := 4983230072969 + 3 ^ 40 * 5943410 * 2
def baseEnd_5943410 : Nat := 3051826056738696614741761

theorem tailTrace_5943410 : CollatzResearch.WordTrace tailWord_5943410 prefixEnd_5943410 3051826056738696614741761 := by
  unfold tailWord_5943410
  simp only [CollatzResearch.WordTrace]
  refine ⟨54193492849512024615140921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144515980932032065640375789 54193492849512024615140921)
  ·
    refine ⟨40645119637134018461355691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54193492849512024615140921 40645119637134018461355691)
    ·
      refine ⟨60967679455701027692033537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40645119637134018461355691 60967679455701027692033537)
      ·
        refine ⟨45725759591775770769025153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60967679455701027692033537 45725759591775770769025153)
        ·
          refine ⟨34294319693831828076768865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45725759591775770769025153 34294319693831828076768865)
          ·
            refine ⟨25720739770373871057576649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34294319693831828076768865 25720739770373871057576649)
            ·
              refine ⟨19290554827780403293182487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25720739770373871057576649 19290554827780403293182487)
              ·
                refine ⟨28935832241670604939773731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19290554827780403293182487 28935832241670604939773731)
                ·
                  refine ⟨43403748362505907409660597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28935832241670604939773731 43403748362505907409660597)
                  ·
                    refine ⟨4069101408984928819655681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43403748362505907409660597 4069101408984928819655681)
                    ·
                      refine ⟨3051826056738696614741761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4069101408984928819655681 3051826056738696614741761)
                      ·
                        rfl

theorem cell23_5943410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 1, 5, 2].length) (baseStart_5943410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5943410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5943410 prefixEnd_5943410 := by exact prefixLift 5943410
  have htrace : WordTrace (prefixWord ++ tailWord_5943410) baseStart_5943410 baseEnd_5943410 := by
    simpa [prefixWord, tailWord_5943410, baseEnd_5943410] using wordTrace_append hprefix tailTrace_5943410
  have hstable : (prefixWord ++ tailWord_5943410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5943410).length < 2 ^ (prefixWord ++ tailWord_5943410).sum := by decide
  have hdescent : baseEnd_5943410 < baseStart_5943410 := by decide
  rcases family_descends (prefixWord ++ tailWord_5943410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5943416 : List Nat := [2, 1, 2, 1, 1, 1, 3, 3, 3, 6]
def baseStart_5943416 : Nat := 118140960795 + 5943416 * 2 ^ 59
def prefixEnd_5943416 : Nat := 4983230072969 + 3 ^ 40 * 5943416 * 2
def baseEnd_5943416 : Nat := 1017276379207541197088911

theorem tailTrace_5943416 : CollatzResearch.WordTrace tailWord_5943416 prefixEnd_5943416 1017276379207541197088911 := by
  unfold tailWord_5943416
  simp only [CollatzResearch.WordTrace]
  refine ⟨108387095118013180742641051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144516126824017574323521401 108387095118013180742641051)
  ·
    refine ⟨162580642677019771113961577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108387095118013180742641051 162580642677019771113961577)
    ·
      refine ⟨121935482007764828335471183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162580642677019771113961577 121935482007764828335471183)
      ·
        refine ⟨182903223011647242503206775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121935482007764828335471183 182903223011647242503206775)
        ·
          refine ⟨274354834517470863754810163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182903223011647242503206775 274354834517470863754810163)
          ·
            refine ⟨411532251776206295632215245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274354834517470863754810163 411532251776206295632215245)
            ·
              refine ⟨154324594416077360862080717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 411532251776206295632215245 154324594416077360862080717)
              ·
                refine ⟨57871722906029010323280269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 154324594416077360862080717 57871722906029010323280269)
                ·
                  refine ⟨21701896089760878871230101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57871722906029010323280269 21701896089760878871230101)
                  ·
                    refine ⟨1017276379207541197088911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21701896089760878871230101 1017276379207541197088911)
                    ·
                      rfl

theorem cell23_5943416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 3, 6].length) (baseStart_5943416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5943416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5943416 prefixEnd_5943416 := by exact prefixLift 5943416
  have htrace : WordTrace (prefixWord ++ tailWord_5943416) baseStart_5943416 baseEnd_5943416 := by
    simpa [prefixWord, tailWord_5943416, baseEnd_5943416] using wordTrace_append hprefix tailTrace_5943416
  have hstable : (prefixWord ++ tailWord_5943416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5943416).length < 2 ^ (prefixWord ++ tailWord_5943416).sum := by decide
  have hdescent : baseEnd_5943416 < baseStart_5943416 := by decide
  rcases family_descends (prefixWord ++ tailWord_5943416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5943433 : List Nat := [1, 2, 1, 1, 4, 2, 1, 3, 4, 4]
def baseStart_5943433 : Nat := 118140960795 + 5943433 * 2 ^ 59
def prefixEnd_5943433 : Nat := 4983230072969 + 3 ^ 40 * 5943433 * 2
def baseEnd_5943433 : Nat := 1017279288931250008251385

theorem tailTrace_5943433 : CollatzResearch.WordTrace tailWord_5943433 prefixEnd_5943433 1017279288931250008251385 := by
  unfold tailWord_5943433
  simp only [CollatzResearch.WordTrace]
  refine ⟨216774810276964773388650953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144516540184643182259100635 216774810276964773388650953)
  ·
    refine ⟨162581107707723580041488215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216774810276964773388650953 162581107707723580041488215)
    ·
      refine ⟨243871661561585370062232323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162581107707723580041488215 243871661561585370062232323)
      ·
        refine ⟨365807492342378055093348485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243871661561585370062232323 365807492342378055093348485)
        ·
          refine ⟨68588904814195885330002841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 365807492342378055093348485 68588904814195885330002841)
          ·
            refine ⟨51441678610646913997502131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68588904814195885330002841 51441678610646913997502131)
            ·
              refine ⟨77162517915970370996253197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51441678610646913997502131 77162517915970370996253197)
              ·
                refine ⟨28935944218488889123594949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77162517915970370996253197 28935944218488889123594949)
                ·
                  refine ⟨5425489540966666710674053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28935944218488889123594949 5425489540966666710674053)
                  ·
                    refine ⟨1017279288931250008251385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5425489540966666710674053 1017279288931250008251385)
                    ·
                      rfl

theorem cell23_5943433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 4, 4].length) (baseStart_5943433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5943433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5943433 prefixEnd_5943433 := by exact prefixLift 5943433
  have htrace : WordTrace (prefixWord ++ tailWord_5943433) baseStart_5943433 baseEnd_5943433 := by
    simpa [prefixWord, tailWord_5943433, baseEnd_5943433] using wordTrace_append hprefix tailTrace_5943433
  have hstable : (prefixWord ++ tailWord_5943433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5943433).length < 2 ^ (prefixWord ++ tailWord_5943433).sum := by decide
  have hdescent : baseEnd_5943433 < baseStart_5943433 := by decide
  rcases family_descends (prefixWord ++ tailWord_5943433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5943443 : List Nat := [1, 1, 1, 2, 1, 2, 3, 4, 3, 2, 3]
def baseStart_5943443 : Nat := 118140960795 + 5943443 * 2 ^ 59
def prefixEnd_5943443 : Nat := 4983230072969 + 3 ^ 40 * 5943443 * 2
def baseEnd_5943443 : Nat := 3051843001600294985629109

theorem tailTrace_5943443 : CollatzResearch.WordTrace tailWord_5943443 prefixEnd_5943443 3051843001600294985629109 := by
  unfold tailWord_5943443
  simp only [CollatzResearch.WordTrace]
  refine ⟨216775175006928545096514983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144516783337952363397676655 216775175006928545096514983)
  ·
    refine ⟨325162762510392817644772475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216775175006928545096514983 325162762510392817644772475)
    ·
      refine ⟨487744143765589226467158713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325162762510392817644772475 487744143765589226467158713)
      ·
        refine ⟨365808107824191919850369035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 487744143765589226467158713 365808107824191919850369035)
        ·
          refine ⟨548712161736287879775553553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365808107824191919850369035 548712161736287879775553553)
          ·
            refine ⟨411534121302215909831665165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 548712161736287879775553553 411534121302215909831665165)
            ·
              refine ⟨154325295488330966186874437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 411534121302215909831665165 154325295488330966186874437)
              ·
                refine ⟨28935992904062056160038957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 154325295488330966186874437 28935992904062056160038957)
                ·
                  refine ⟨10850997339023271060014609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28935992904062056160038957 10850997339023271060014609)
                  ·
                    refine ⟨8138248004267453295010957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10850997339023271060014609 8138248004267453295010957)
                    ·
                      refine ⟨3051843001600294985629109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8138248004267453295010957 3051843001600294985629109)
                      ·
                        rfl

theorem cell23_5943443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 3, 2, 3].length) (baseStart_5943443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5943443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5943443 prefixEnd_5943443 := by exact prefixLift 5943443
  have htrace : WordTrace (prefixWord ++ tailWord_5943443) baseStart_5943443 baseEnd_5943443 := by
    simpa [prefixWord, tailWord_5943443, baseEnd_5943443] using wordTrace_append hprefix tailTrace_5943443
  have hstable : (prefixWord ++ tailWord_5943443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5943443).length < 2 ^ (prefixWord ++ tailWord_5943443).sum := by decide
  have hdescent : baseEnd_5943443 < baseStart_5943443 := by decide
  rcases family_descends (prefixWord ++ tailWord_5943443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5943453 : List Nat := [1, 4, 2, 1, 1, 3, 2, 1, 1, 1, 6]
def baseStart_5943453 : Nat := 118140960795 + 5943453 * 2 ^ 59
def prefixEnd_5943453 : Nat := 4983230072969 + 3 ^ 40 * 5943453 * 2
def baseEnd_5943453 : Nat := 3051848136406839946504063

theorem tailTrace_5943453 : CollatzResearch.WordTrace tailWord_5943453 prefixEnd_5943453 3051848136406839946504063 := by
  unfold tailWord_5943453
  simp only [CollatzResearch.WordTrace]
  refine ⟨216775539736892316804379013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144517026491261544536252675 216775539736892316804379013)
  ·
    refine ⟨40645413700667309400821065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 216775539736892316804379013 40645413700667309400821065)
    ·
      refine ⟨30484060275500482050615799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40645413700667309400821065 30484060275500482050615799)
      ·
        refine ⟨45726090413250723075923699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30484060275500482050615799 45726090413250723075923699)
        ·
          refine ⟨68589135619876084613885549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45726090413250723075923699 68589135619876084613885549)
          ·
            refine ⟨25720925857453531730207081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68589135619876084613885549 25720925857453531730207081)
            ·
              refine ⟨19290694393090148797655311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25720925857453531730207081 19290694393090148797655311)
              ·
                refine ⟨28936041589635223196482967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19290694393090148797655311 28936041589635223196482967)
                ·
                  refine ⟨43404062384452834794724451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28936041589635223196482967 43404062384452834794724451)
                  ·
                    refine ⟨65106093576679252192086677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43404062384452834794724451 65106093576679252192086677)
                    ·
                      refine ⟨3051848136406839946504063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65106093576679252192086677 3051848136406839946504063)
                      ·
                        rfl

theorem cell23_5943453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_5943453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5943453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5943453 prefixEnd_5943453 := by exact prefixLift 5943453
  have htrace : WordTrace (prefixWord ++ tailWord_5943453) baseStart_5943453 baseEnd_5943453 := by
    simpa [prefixWord, tailWord_5943453, baseEnd_5943453] using wordTrace_append hprefix tailTrace_5943453
  have hstable : (prefixWord ++ tailWord_5943453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5943453).length < 2 ^ (prefixWord ++ tailWord_5943453).sum := by decide
  have hdescent : baseEnd_5943453 < baseStart_5943453 := by decide
  rcases family_descends (prefixWord ++ tailWord_5943453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5943454 : List Nat := [4, 3, 1, 1, 3, 2, 1, 2, 1, 5]
def baseStart_5943454 : Nat := 118140960795 + 5943454 * 2 ^ 59
def prefixEnd_5943454 : Nat := 4983230072969 + 3 ^ 40 * 5943454 * 2
def baseEnd_5943454 : Nat := 1017282883295831480863853

theorem tailTrace_5943454 : CollatzResearch.WordTrace tailWord_5943454 prefixEnd_5943454 1017282883295831480863853 := by
  unfold tailWord_5943454
  simp only [CollatzResearch.WordTrace]
  refine ⟨27096947026236086746895677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144517050806592462650110277 27096947026236086746895677)
  ·
    refine ⟨10161355134838532530085879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27096947026236086746895677 10161355134838532530085879)
    ·
      refine ⟨15242032702257798795128819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10161355134838532530085879 15242032702257798795128819)
      ·
        refine ⟨22863049053386698192693229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15242032702257798795128819 22863049053386698192693229)
        ·
          refine ⟨8573643395020011822259961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22863049053386698192693229 8573643395020011822259961)
          ·
            refine ⟨6430232546265008866694971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8573643395020011822259961 6430232546265008866694971)
            ·
              refine ⟨9645348819397513300042457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6430232546265008866694971 9645348819397513300042457)
              ·
                refine ⟨7234011614548134975031843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9645348819397513300042457 7234011614548134975031843)
                ·
                  refine ⟨10851017421822202462547765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7234011614548134975031843 10851017421822202462547765)
                  ·
                    refine ⟨1017282883295831480863853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10851017421822202462547765 1017282883295831480863853)
                    ·
                      rfl

theorem cell23_5943454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_5943454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5943454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5943454 prefixEnd_5943454 := by exact prefixLift 5943454
  have htrace : WordTrace (prefixWord ++ tailWord_5943454) baseStart_5943454 baseEnd_5943454 := by
    simpa [prefixWord, tailWord_5943454, baseEnd_5943454] using wordTrace_append hprefix tailTrace_5943454
  have hstable : (prefixWord ++ tailWord_5943454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5943454).length < 2 ^ (prefixWord ++ tailWord_5943454).sum := by decide
  have hdescent : baseEnd_5943454 < baseStart_5943454 := by decide
  rcases family_descends (prefixWord ++ tailWord_5943454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5943457 : List Nat := [1, 2, 3, 3, 1, 4, 1, 2, 1, 1, 4]
def baseStart_5943457 : Nat := 118140960795 + 5943457 * 2 ^ 59
def prefixEnd_5943457 : Nat := 4983230072969 + 3 ^ 40 * 5943457 * 2
def baseEnd_5943457 : Nat := 3051850190329457930854045

theorem tailTrace_5943457 : CollatzResearch.WordTrace tailWord_5943457 prefixEnd_5943457 3051850190329457930854045 := by
  unfold tailWord_5943457
  simp only [CollatzResearch.WordTrace]
  refine ⟨216775685628877825487524625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144517123752585216991683083 216775685628877825487524625)
  ·
    refine ⟨162581764221658369115643469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216775685628877825487524625 162581764221658369115643469)
    ·
      refine ⟨60968161583121888418366301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162581764221658369115643469 60968161583121888418366301)
      ·
        refine ⟨22863060593670708156887363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60968161583121888418366301 22863060593670708156887363)
        ·
          refine ⟨34294590890506062235331045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22863060593670708156887363 34294590890506062235331045)
          ·
            refine ⟨6430235791969886669124571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34294590890506062235331045 6430235791969886669124571)
            ·
              refine ⟨9645353687954830003686857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6430235791969886669124571 9645353687954830003686857)
              ·
                refine ⟨7234015265966122502765143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9645353687954830003686857 7234015265966122502765143)
                ·
                  refine ⟨10851022898949183754147715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7234015265966122502765143 10851022898949183754147715)
                  ·
                    refine ⟨16276534348423775631221573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10851022898949183754147715 16276534348423775631221573)
                    ·
                      refine ⟨3051850190329457930854045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16276534348423775631221573 3051850190329457930854045)
                      ·
                        rfl

theorem cell23_5943457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_5943457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5943457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5943457 prefixEnd_5943457 := by exact prefixLift 5943457
  have htrace : WordTrace (prefixWord ++ tailWord_5943457) baseStart_5943457 baseEnd_5943457 := by
    simpa [prefixWord, tailWord_5943457, baseEnd_5943457] using wordTrace_append hprefix tailTrace_5943457
  have hstable : (prefixWord ++ tailWord_5943457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5943457).length < 2 ^ (prefixWord ++ tailWord_5943457).sum := by decide
  have hdescent : baseEnd_5943457 < baseStart_5943457 := by decide
  rcases family_descends (prefixWord ++ tailWord_5943457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5943474 : List Nat := [3, 2, 1, 1, 1, 3, 2, 5, 1, 2, 2]
def baseStart_5943474 : Nat := 118140960795 + 5943474 * 2 ^ 59
def prefixEnd_5943474 : Nat := 4983230072969 + 3 ^ 40 * 5943474 * 2
def baseEnd_5943474 : Nat := 3051858919500584364341467

theorem tailTrace_5943474 : CollatzResearch.WordTrace tailWord_5943474 prefixEnd_5943474 3051858919500584364341467 := by
  unfold tailWord_5943474
  simp only [CollatzResearch.WordTrace]
  refine ⟨54194076417454059347723369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144517537113210824927262317 54194076417454059347723369)
  ·
    refine ⟨40645557313090544510792527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54194076417454059347723369 40645557313090544510792527)
    ·
      refine ⟨60968335969635816766188791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40645557313090544510792527 60968335969635816766188791)
      ·
        refine ⟨91452503954453725149283187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60968335969635816766188791 91452503954453725149283187)
        ·
          refine ⟨137178755931680587723924781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91452503954453725149283187 137178755931680587723924781)
          ·
            refine ⟨51442033474380220396471793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137178755931680587723924781 51442033474380220396471793)
            ·
              refine ⟨38581525105785165297353845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51442033474380220396471793 38581525105785165297353845)
              ·
                refine ⟨3617017978667359246626923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38581525105785165297353845 3617017978667359246626923)
                ·
                  refine ⟨5425526968001038869940385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3617017978667359246626923 5425526968001038869940385)
                  ·
                    refine ⟨4069145226000779152455289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5425526968001038869940385 4069145226000779152455289)
                    ·
                      refine ⟨3051858919500584364341467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4069145226000779152455289 3051858919500584364341467)
                      ·
                        rfl

theorem cell23_5943474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 5, 1, 2, 2].length) (baseStart_5943474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5943474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5943474 prefixEnd_5943474 := by exact prefixLift 5943474
  have htrace : WordTrace (prefixWord ++ tailWord_5943474) baseStart_5943474 baseEnd_5943474 := by
    simpa [prefixWord, tailWord_5943474, baseEnd_5943474] using wordTrace_append hprefix tailTrace_5943474
  have hstable : (prefixWord ++ tailWord_5943474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5943474).length < 2 ^ (prefixWord ++ tailWord_5943474).sum := by decide
  have hdescent : baseEnd_5943474 < baseStart_5943474 := by decide
  rcases family_descends (prefixWord ++ tailWord_5943474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5943560 : List Nat := [2, 1, 3, 2, 3, 1, 2, 1, 2, 2, 4]
def baseStart_5943560 : Nat := 118140960795 + 5943560 * 2 ^ 59
def prefixEnd_5943560 : Nat := 4983230072969 + 3 ^ 40 * 5943560 * 2
def baseEnd_5943560 : Nat := 3051903078836871027866071

theorem tailTrace_5943560 : CollatzResearch.WordTrace tailWord_5943560 prefixEnd_5943560 3051903078836871027866071 := by
  unfold tailWord_5943560
  simp only [CollatzResearch.WordTrace]
  refine ⟨108389721173752337039262067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144519628231669782719016089 108389721173752337039262067)
  ·
    refine ⟨162584581760628505558893101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108389721173752337039262067 162584581760628505558893101)
    ·
      refine ⟨60969218160235689584584913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162584581760628505558893101 60969218160235689584584913)
      ·
        refine ⟨45726913620176767188438685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60969218160235689584584913 45726913620176767188438685)
        ·
          refine ⟨17147592607566287695664507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45726913620176767188438685 17147592607566287695664507)
          ·
            refine ⟨25721388911349431543496761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17147592607566287695664507 25721388911349431543496761)
            ·
              refine ⟨19291041683512073657622571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25721388911349431543496761 19291041683512073657622571)
              ·
                refine ⟨28936562525268110486433857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19291041683512073657622571 28936562525268110486433857)
                ·
                  refine ⟨21702421893951082864825393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28936562525268110486433857 21702421893951082864825393)
                  ·
                    refine ⟨16276816420463312148619045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21702421893951082864825393 16276816420463312148619045)
                    ·
                      refine ⟨3051903078836871027866071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16276816420463312148619045 3051903078836871027866071)
                      ·
                        rfl

theorem cell23_5943560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_5943560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5943560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5943560 prefixEnd_5943560 := by exact prefixLift 5943560
  have htrace : WordTrace (prefixWord ++ tailWord_5943560) baseStart_5943560 baseEnd_5943560 := by
    simpa [prefixWord, tailWord_5943560, baseEnd_5943560] using wordTrace_append hprefix tailTrace_5943560
  have hstable : (prefixWord ++ tailWord_5943560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5943560).length < 2 ^ (prefixWord ++ tailWord_5943560).sum := by decide
  have hdescent : baseEnd_5943560 < baseStart_5943560 := by decide
  rcases family_descends (prefixWord ++ tailWord_5943560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5943610 : List Nat := [3, 1, 1, 1, 4, 3, 1, 1, 1, 2, 5]
def baseStart_5943610 : Nat := 118140960795 + 5943610 * 2 ^ 59
def prefixEnd_5943610 : Nat := 4983230072969 + 3 ^ 40 * 5943610 * 2
def baseEnd_5943610 : Nat := 3051928752869595832240841

theorem tailTrace_5943610 : CollatzResearch.WordTrace tailWord_5943610 prefixEnd_5943610 3051928752869595832240841 := by
  unfold tailWord_5943610
  simp only [CollatzResearch.WordTrace]
  refine ⟨54195316499330883154461071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144520843998215688411896189 54195316499330883154461071)
  ·
    refine ⟨81292974748996324731691607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54195316499330883154461071 81292974748996324731691607)
    ·
      refine ⟨121939462123494487097537411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81292974748996324731691607 121939462123494487097537411)
      ·
        refine ⟨182909193185241730646306117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121939462123494487097537411 182909193185241730646306117)
        ·
          refine ⟨34295473722232824496182397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 182909193185241730646306117 34295473722232824496182397)
          ·
            refine ⟨12860802645837309186068399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34295473722232824496182397 12860802645837309186068399)
            ·
              refine ⟨19291203968755963779102599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12860802645837309186068399 19291203968755963779102599)
              ·
                refine ⟨28936805953133945668653899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19291203968755963779102599 28936805953133945668653899)
                ·
                  refine ⟨43405208929700918502980849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28936805953133945668653899 43405208929700918502980849)
                  ·
                    refine ⟨32553906697275688877235637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43405208929700918502980849 32553906697275688877235637)
                    ·
                      refine ⟨3051928752869595832240841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32553906697275688877235637 3051928752869595832240841)
                      ·
                        rfl

theorem cell23_5943610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 1, 2, 5].length) (baseStart_5943610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5943610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5943610 prefixEnd_5943610 := by exact prefixLift 5943610
  have htrace : WordTrace (prefixWord ++ tailWord_5943610) baseStart_5943610 baseEnd_5943610 := by
    simpa [prefixWord, tailWord_5943610, baseEnd_5943610] using wordTrace_append hprefix tailTrace_5943610
  have hstable : (prefixWord ++ tailWord_5943610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5943610).length < 2 ^ (prefixWord ++ tailWord_5943610).sum := by decide
  have hdescent : baseEnd_5943610 < baseStart_5943610 := by decide
  rcases family_descends (prefixWord ++ tailWord_5943610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5943664 : List Nat := [2, 1, 1, 1, 4, 4, 1, 4, 1, 4]
def baseStart_5943664 : Nat := 118140960795 + 5943664 * 2 ^ 59
def prefixEnd_5943664 : Nat := 4983230072969 + 3 ^ 40 * 5943664 * 2
def baseEnd_5943664 : Nat := 1017318826941646206988531

theorem tailTrace_5943664 : CollatzResearch.WordTrace tailWord_5943664 prefixEnd_5943664 1017318826941646206988531 := by
  unfold tailWord_5943664
  simp only [CollatzResearch.WordTrace]
  refine ⟨108391617769563949920155023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144522157026085266560206697 108391617769563949920155023)
  ·
    refine ⟨162587426654345924880232535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108391617769563949920155023 162587426654345924880232535)
    ·
      refine ⟨243881139981518887320348803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162587426654345924880232535 243881139981518887320348803)
      ·
        refine ⟨365821709972278330980523205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243881139981518887320348803 365821709972278330980523205)
        ·
          refine ⟨68591570619802187058848101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 365821709972278330980523205 68591570619802187058848101)
          ·
            refine ⟨12860919491212910073534019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68591570619802187058848101 12860919491212910073534019)
            ·
              refine ⟨19291379236819365110301029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12860919491212910073534019 19291379236819365110301029)
              ·
                refine ⟨3617133606903630958181443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19291379236819365110301029 3617133606903630958181443)
                ·
                  refine ⟨5425700410355446437272165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3617133606903630958181443 5425700410355446437272165)
                  ·
                    refine ⟨1017318826941646206988531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5425700410355446437272165 1017318826941646206988531)
                    ·
                      rfl

theorem cell23_5943664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 4, 1, 4].length) (baseStart_5943664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5943664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5943664 prefixEnd_5943664 := by exact prefixLift 5943664
  have htrace : WordTrace (prefixWord ++ tailWord_5943664) baseStart_5943664 baseEnd_5943664 := by
    simpa [prefixWord, tailWord_5943664, baseEnd_5943664] using wordTrace_append hprefix tailTrace_5943664
  have hstable : (prefixWord ++ tailWord_5943664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5943664).length < 2 ^ (prefixWord ++ tailWord_5943664).sum := by decide
  have hdescent : baseEnd_5943664 < baseStart_5943664 := by decide
  rcases family_descends (prefixWord ++ tailWord_5943664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5943714 : List Nat := [3, 3, 1, 2, 1, 1, 2, 1, 4, 3, 2]
def baseStart_5943714 : Nat := 118140960795 + 5943714 * 2 ^ 59
def prefixEnd_5943714 : Nat := 4983230072969 + 3 ^ 40 * 5943714 * 2
def baseEnd_5943714 : Nat := 3051982154857663425340363

theorem tailTrace_5943714 : CollatzResearch.WordTrace tailWord_5943714 prefixEnd_5943714 3051982154857663425340363 := by
  unfold tailWord_5943714
  simp only [CollatzResearch.WordTrace]
  refine ⟨54196264797236689594907549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144523372792631172253086797 54196264797236689594907549)
  ·
    refine ⟨20323599298963758598090331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54196264797236689594907549 20323599298963758598090331)
    ·
      refine ⟨30485398948445637897135497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20323599298963758598090331 30485398948445637897135497)
      ·
        refine ⟨22864049211334228422851623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30485398948445637897135497 22864049211334228422851623)
        ·
          refine ⟨34296073817001342634277435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22864049211334228422851623 34296073817001342634277435)
          ·
            refine ⟨51444110725502013951416153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34296073817001342634277435 51444110725502013951416153)
            ·
              refine ⟨38583083044126510463562115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51444110725502013951416153 38583083044126510463562115)
              ·
                refine ⟨57874624566189765695343173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38583083044126510463562115 57874624566189765695343173)
                ·
                  refine ⟨10851492106160581067876845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57874624566189765695343173 10851492106160581067876845)
                  ·
                    refine ⟨4069309539810217900453817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10851492106160581067876845 4069309539810217900453817)
                    ·
                      refine ⟨3051982154857663425340363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4069309539810217900453817 3051982154857663425340363)
                      ·
                        rfl

theorem cell23_5943714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 4, 3, 2].length) (baseStart_5943714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5943714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5943714 prefixEnd_5943714 := by exact prefixLift 5943714
  have htrace : WordTrace (prefixWord ++ tailWord_5943714) baseStart_5943714 baseEnd_5943714 := by
    simpa [prefixWord, tailWord_5943714, baseEnd_5943714] using wordTrace_append hprefix tailTrace_5943714
  have hstable : (prefixWord ++ tailWord_5943714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5943714).length < 2 ^ (prefixWord ++ tailWord_5943714).sum := by decide
  have hdescent : baseEnd_5943714 < baseStart_5943714 := by decide
  rcases family_descends (prefixWord ++ tailWord_5943714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5943737 : List Nat := [1, 2, 1, 4, 3, 1, 3, 1, 1, 6]
def baseStart_5943737 : Nat := 118140960795 + 5943737 * 2 ^ 59
def prefixEnd_5943737 : Nat := 4983230072969 + 3 ^ 40 * 5943737 * 2
def baseEnd_5943737 : Nat := 1017331321637572278450919

theorem tailTrace_5943737 : CollatzResearch.WordTrace tailWord_5943737 prefixEnd_5943737 1017331321637572278450919 := by
  unfold tailWord_5943737
  simp only [CollatzResearch.WordTrace]
  refine ⟨216785898067863433307717465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144523932045242288871811643 216785898067863433307717465)
  ·
    refine ⟨162589423550897574980788099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216785898067863433307717465 162589423550897574980788099)
    ·
      refine ⟨243884135326346362471182149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162589423550897574980788099 243884135326346362471182149)
      ·
        refine ⟨45728275373689942963346653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 243884135326346362471182149 45728275373689942963346653)
        ·
          refine ⟨17148103265133728611254995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45728275373689942963346653 17148103265133728611254995)
          ·
            refine ⟨25722154897700592916882493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17148103265133728611254995 25722154897700592916882493)
            ·
              refine ⟨9645808086637722343830935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25722154897700592916882493 9645808086637722343830935)
              ·
                refine ⟨14468712129956583515746403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9645808086637722343830935 14468712129956583515746403)
                ·
                  refine ⟨21703068194934875273619605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14468712129956583515746403 21703068194934875273619605)
                  ·
                    refine ⟨1017331321637572278450919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21703068194934875273619605 1017331321637572278450919)
                    ·
                      rfl

theorem cell23_5943737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 1, 1, 6].length) (baseStart_5943737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5943737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5943737 prefixEnd_5943737 := by exact prefixLift 5943737
  have htrace : WordTrace (prefixWord ++ tailWord_5943737) baseStart_5943737 baseEnd_5943737 := by
    simpa [prefixWord, tailWord_5943737, baseEnd_5943737] using wordTrace_append hprefix tailTrace_5943737
  have hstable : (prefixWord ++ tailWord_5943737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5943737).length < 2 ^ (prefixWord ++ tailWord_5943737).sum := by decide
  have hdescent : baseEnd_5943737 < baseStart_5943737 := by decide
  rcases family_descends (prefixWord ++ tailWord_5943737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5943764 : List Nat := [2, 4, 1, 2, 2, 2, 2, 1, 1, 1, 5]
def baseStart_5943764 : Nat := 118140960795 + 5943764 * 2 ^ 59
def prefixEnd_5943764 : Nat := 4983230072969 + 3 ^ 40 * 5943764 * 2
def baseEnd_5943764 : Nat := 3052007828890388229715133

theorem tailTrace_5943764 : CollatzResearch.WordTrace tailWord_5943764 prefixEnd_5943764 3052007828890388229715133 := by
  unfold tailWord_5943764
  simp only [CollatzResearch.WordTrace]
  refine ⟨108393441419382808459475173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144524588559177077945966897 108393441419382808459475173)
  ·
    refine ⟨20323770266134276586151595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108393441419382808459475173 20323770266134276586151595)
    ·
      refine ⟨30485655399201414879227393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20323770266134276586151595 30485655399201414879227393)
      ·
        refine ⟨22864241549401061159420545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30485655399201414879227393 22864241549401061159420545)
        ·
          refine ⟨17148181162050795869565409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22864241549401061159420545 17148181162050795869565409)
          ·
            refine ⟨12861135871538096902174057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17148181162050795869565409 12861135871538096902174057)
            ·
              refine ⟨9645851903653572676630543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12861135871538096902174057 9645851903653572676630543)
              ·
                refine ⟨14468777855480359014945815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9645851903653572676630543 14468777855480359014945815)
                ·
                  refine ⟨21703166783220538522418723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14468777855480359014945815 21703166783220538522418723)
                  ·
                    refine ⟨32554750174830807783628085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21703166783220538522418723 32554750174830807783628085)
                    ·
                      refine ⟨3052007828890388229715133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32554750174830807783628085 3052007828890388229715133)
                      ·
                        rfl

theorem cell23_5943764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_5943764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5943764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5943764 prefixEnd_5943764 := by exact prefixLift 5943764
  have htrace : WordTrace (prefixWord ++ tailWord_5943764) baseStart_5943764 baseEnd_5943764 := by
    simpa [prefixWord, tailWord_5943764, baseEnd_5943764] using wordTrace_append hprefix tailTrace_5943764
  have hstable : (prefixWord ++ tailWord_5943764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5943764).length < 2 ^ (prefixWord ++ tailWord_5943764).sum := by decide
  have hdescent : baseEnd_5943764 < baseStart_5943764 := by decide
  rcases family_descends (prefixWord ++ tailWord_5943764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5943828 : List Nat := [2, 4, 3, 1, 1, 1, 1, 4, 2, 1, 3]
def baseStart_5943828 : Nat := 118140960795 + 5943828 * 2 ^ 59
def prefixEnd_5943828 : Nat := 4983230072969 + 3 ^ 40 * 5943828 * 2
def baseEnd_5943828 : Nat := 3052040691652275979314839

theorem tailTrace_5943828 : CollatzResearch.WordTrace tailWord_5943828 prefixEnd_5943828 3052040691652275979314839 := by
  unfold tailWord_5943828
  simp only [CollatzResearch.WordTrace]
  refine ⟨108394608555266877924640069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144526144740355837232853425 108394608555266877924640069)
  ·
    refine ⟨20323989104112539610870013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108394608555266877924640069 20323989104112539610870013)
    ·
      refine ⟨7621495914042202354076255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20323989104112539610870013 7621495914042202354076255)
      ·
        refine ⟨11432243871063303531114383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7621495914042202354076255 11432243871063303531114383)
        ·
          refine ⟨17148365806594955296671575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11432243871063303531114383 17148365806594955296671575)
          ·
            refine ⟨25722548709892432945007363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17148365806594955296671575 25722548709892432945007363)
            ·
              refine ⟨38583823064838649417511045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25722548709892432945007363 38583823064838649417511045)
              ·
                refine ⟨7234466824657246765783321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38583823064838649417511045 7234466824657246765783321)
                ·
                  refine ⟨5425850118492935074337491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7234466824657246765783321 5425850118492935074337491)
                  ·
                    refine ⟨8138775177739402611506237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5425850118492935074337491 8138775177739402611506237)
                    ·
                      refine ⟨3052040691652275979314839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8138775177739402611506237 3052040691652275979314839)
                      ·
                        rfl

theorem cell23_5943828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_5943828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5943828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5943828 prefixEnd_5943828 := by exact prefixLift 5943828
  have htrace : WordTrace (prefixWord ++ tailWord_5943828) baseStart_5943828 baseEnd_5943828 := by
    simpa [prefixWord, tailWord_5943828, baseEnd_5943828] using wordTrace_append hprefix tailTrace_5943828
  have hstable : (prefixWord ++ tailWord_5943828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5943828).length < 2 ^ (prefixWord ++ tailWord_5943828).sum := by decide
  have hdescent : baseEnd_5943828 < baseStart_5943828 := by decide
  rcases family_descends (prefixWord ++ tailWord_5943828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5943885 : List Nat := [1, 6, 1, 1, 2, 1, 3, 2, 2, 2, 2]
def baseStart_5943885 : Nat := 118140960795 + 5943885 * 2 ^ 59
def prefixEnd_5943885 : Nat := 4983230072969 + 3 ^ 40 * 5943885 * 2
def baseEnd_5943885 : Nat := 3052069960049582256302077

theorem tailTrace_5943885 : CollatzResearch.WordTrace tailWord_5943885 prefixEnd_5943885 3052069960049582256302077 := by
  unfold tailWord_5943885
  simp only [CollatzResearch.WordTrace]
  refine ⟨216791296071327254584105109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144527530714218169722736739 216791296071327254584105109)
  ·
    refine ⟨10162092003343465058629927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 216791296071327254584105109 10162092003343465058629927)
    ·
      refine ⟨15243138005015197587944891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10162092003343465058629927 15243138005015197587944891)
      ·
        refine ⟨22864707007522796381917337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15243138005015197587944891 22864707007522796381917337)
        ·
          refine ⟨17148530255642097286438003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22864707007522796381917337 17148530255642097286438003)
          ·
            refine ⟨25722795383463145929657005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17148530255642097286438003 25722795383463145929657005)
            ·
              refine ⟨9646048268798679723621377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25722795383463145929657005 9646048268798679723621377)
              ·
                refine ⟨7234536201599009792716033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9646048268798679723621377 7234536201599009792716033)
                ·
                  refine ⟨5425902151199257344537025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7234536201599009792716033 5425902151199257344537025)
                  ·
                    refine ⟨4069426613399443008402769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5425902151199257344537025 4069426613399443008402769)
                    ·
                      refine ⟨3052069960049582256302077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4069426613399443008402769 3052069960049582256302077)
                      ·
                        rfl

theorem cell23_5943885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 2, 2, 2, 2].length) (baseStart_5943885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5943885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5943885 prefixEnd_5943885 := by exact prefixLift 5943885
  have htrace : WordTrace (prefixWord ++ tailWord_5943885) baseStart_5943885 baseEnd_5943885 := by
    simpa [prefixWord, tailWord_5943885, baseEnd_5943885] using wordTrace_append hprefix tailTrace_5943885
  have hstable : (prefixWord ++ tailWord_5943885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5943885).length < 2 ^ (prefixWord ++ tailWord_5943885).sum := by decide
  have hdescent : baseEnd_5943885 < baseStart_5943885 := by decide
  rcases family_descends (prefixWord ++ tailWord_5943885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5943887 : List Nat := [1, 1, 2, 1, 1, 2, 4, 4, 2, 5]
def baseStart_5943887 : Nat := 118140960795 + 5943887 * 2 ^ 59
def prefixEnd_5943887 : Nat := 4983230072969 + 3 ^ 40 * 5943887 * 2
def baseEnd_5943887 : Nat := 1017356995670297082825689

theorem tailTrace_5943887 : CollatzResearch.WordTrace tailWord_5943887 prefixEnd_5943887 1017356995670297082825689 := by
  unfold tailWord_5943887
  simp only [CollatzResearch.WordTrace]
  refine ⟨216791369017320008925677915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144527579344880005950451943 216791369017320008925677915)
  ·
    refine ⟨325187053525980013388516873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216791369017320008925677915 325187053525980013388516873)
    ·
      refine ⟨243890290144485010041387655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 325187053525980013388516873 243890290144485010041387655)
      ·
        refine ⟨365835435216727515062081483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243890290144485010041387655 365835435216727515062081483)
        ·
          refine ⟨548753152825091272593122225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365835435216727515062081483 548753152825091272593122225)
          ·
            refine ⟨411564864618818454444841669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 548753152825091272593122225 411564864618818454444841669)
            ·
              refine ⟨77168412116028460208407813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 411564864618818454444841669 77168412116028460208407813)
              ·
                refine ⟨14469077271755336289076465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77168412116028460208407813 14469077271755336289076465)
                ·
                  refine ⟨10851807953816502216807349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14469077271755336289076465 10851807953816502216807349)
                  ·
                    refine ⟨1017356995670297082825689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10851807953816502216807349 1017356995670297082825689)
                    ·
                      rfl

theorem cell23_5943887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 4, 2, 5].length) (baseStart_5943887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5943887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5943887 prefixEnd_5943887 := by exact prefixLift 5943887
  have htrace : WordTrace (prefixWord ++ tailWord_5943887) baseStart_5943887 baseEnd_5943887 := by
    simpa [prefixWord, tailWord_5943887, baseEnd_5943887] using wordTrace_append hprefix tailTrace_5943887
  have hstable : (prefixWord ++ tailWord_5943887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5943887).length < 2 ^ (prefixWord ++ tailWord_5943887).sum := by decide
  have hdescent : baseEnd_5943887 < baseStart_5943887 := by decide
  rcases family_descends (prefixWord ++ tailWord_5943887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5943907 : List Nat := [1, 1, 1, 5, 1, 2, 1, 1, 3, 3, 4]
def baseStart_5943907 : Nat := 118140960795 + 5943907 * 2 ^ 59
def prefixEnd_5943907 : Nat := 4983230072969 + 3 ^ 40 * 5943907 * 2
def baseEnd_5943907 : Nat := 3052081256623981170226975

theorem tailTrace_5943907 : CollatzResearch.WordTrace tailWord_5943907 prefixEnd_5943907 3052081256623981170226975 := by
  unfold tailWord_5943907
  simp only [CollatzResearch.WordTrace]
  refine ⟨216792098477247552341405975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144528065651498368227603983 216792098477247552341405975)
  ·
    refine ⟨325188147715871328512108963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216792098477247552341405975 325188147715871328512108963)
    ·
      refine ⟨487782221573806992768163445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325188147715871328512108963 487782221573806992768163445)
      ·
        refine ⟨45729583272544405572015323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 487782221573806992768163445 45729583272544405572015323)
        ·
          refine ⟨68594374908816608358022985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45729583272544405572015323 68594374908816608358022985)
          ·
            refine ⟨51445781181612456268517239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68594374908816608358022985 51445781181612456268517239)
            ·
              refine ⟨77168671772418684402775859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51445781181612456268517239 77168671772418684402775859)
              ·
                refine ⟨115753007658628026604163789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77168671772418684402775859 115753007658628026604163789)
                ·
                  refine ⟨43407377871985509976561421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 115753007658628026604163789 43407377871985509976561421)
                  ·
                    refine ⟨16277766701994566241210533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43407377871985509976561421 16277766701994566241210533)
                    ·
                      refine ⟨3052081256623981170226975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16277766701994566241210533 3052081256623981170226975)
                      ·
                        rfl

theorem cell23_5943907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_5943907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5943907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5943907 prefixEnd_5943907 := by exact prefixLift 5943907
  have htrace : WordTrace (prefixWord ++ tailWord_5943907) baseStart_5943907 baseEnd_5943907 := by
    simpa [prefixWord, tailWord_5943907, baseEnd_5943907] using wordTrace_append hprefix tailTrace_5943907
  have hstable : (prefixWord ++ tailWord_5943907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5943907).length < 2 ^ (prefixWord ++ tailWord_5943907).sum := by decide
  have hdescent : baseEnd_5943907 < baseStart_5943907 := by decide
  rcases family_descends (prefixWord ++ tailWord_5943907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5943925 : List Nat := [1, 3, 4, 2, 3, 1, 1, 3, 5]
def baseStart_5943925 : Nat := 118140960795 + 5943925 * 2 ^ 59
def prefixEnd_5943925 : Nat := 4983230072969 + 3 ^ 40 * 5943925 * 2
def baseEnd_5943925 : Nat := 339121166586195788866877

theorem tailTrace_5943925 : CollatzResearch.WordTrace tailWord_5943925 prefixEnd_5943925 339121166586195788866877 := by
  unfold tailWord_5943925
  simp only [CollatzResearch.WordTrace]
  refine ⟨216792754991182341415561229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144528503327454894277040819 216792754991182341415561229)
  ·
    refine ⟨81297283121693378030835461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216792754991182341415561229 81297283121693378030835461)
    ·
      refine ⟨15243240585317508380781649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81297283121693378030835461 15243240585317508380781649)
      ·
        refine ⟨11432430438988131285586237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15243240585317508380781649 11432430438988131285586237)
        ·
          refine ⟨4287161414620549232094839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11432430438988131285586237 4287161414620549232094839)
          ·
            refine ⟨6430742121930823848142259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4287161414620549232094839 6430742121930823848142259)
            ·
              refine ⟨9646113182896235772213389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6430742121930823848142259 9646113182896235772213389)
              ·
                refine ⟨3617292443586088414580021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9646113182896235772213389 3617292443586088414580021)
                ·
                  refine ⟨339121166586195788866877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3617292443586088414580021 339121166586195788866877)
                  ·
                    rfl

theorem cell23_5943925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 3, 5].length) (baseStart_5943925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5943925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5943925 prefixEnd_5943925 := by exact prefixLift 5943925
  have htrace : WordTrace (prefixWord ++ tailWord_5943925) baseStart_5943925 baseEnd_5943925 := by
    simpa [prefixWord, tailWord_5943925, baseEnd_5943925] using wordTrace_append hprefix tailTrace_5943925
  have hstable : (prefixWord ++ tailWord_5943925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5943925).length < 2 ^ (prefixWord ++ tailWord_5943925).sum := by decide
  have hdescent : baseEnd_5943925 < baseStart_5943925 := by decide
  rcases family_descends (prefixWord ++ tailWord_5943925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5944024 : List Nat := [2, 1, 2, 2, 3, 2, 1, 3, 1, 6]
def baseStart_5944024 : Nat := 118140960795 + 5944024 * 2 ^ 59
def prefixEnd_5944024 : Nat := 4983230072969 + 3 ^ 40 * 5944024 * 2
def baseEnd_5944024 : Nat := 1017380444620185737487979

theorem tailTrace_5944024 : CollatzResearch.WordTrace tailWord_5944024 prefixEnd_5944024 1017380444620185737487979 := by
  unfold tailWord_5944024
  simp only [CollatzResearch.WordTrace]
  refine ⟨108398182908911840661707563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144530910545215787548943417 108398182908911840661707563)
  ·
    refine ⟨162597274363367760992561345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108398182908911840661707563 162597274363367760992561345)
    ·
      refine ⟨121947955772525820744421009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162597274363367760992561345 121947955772525820744421009)
      ·
        refine ⟨91460966829394365558315757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121947955772525820744421009 91460966829394365558315757)
        ·
          refine ⟨34297862561022887084368409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91460966829394365558315757 34297862561022887084368409)
          ·
            refine ⟨25723396920767165313276307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34297862561022887084368409 25723396920767165313276307)
            ·
              refine ⟨38585095381150747969914461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25723396920767165313276307 38585095381150747969914461)
              ·
                refine ⟨14469410767931530488717923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38585095381150747969914461 14469410767931530488717923)
                ·
                  refine ⟨21704116151897295733076885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14469410767931530488717923 21704116151897295733076885)
                  ·
                    refine ⟨1017380444620185737487979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21704116151897295733076885 1017380444620185737487979)
                    ·
                      rfl

theorem cell23_5944024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 3, 1, 6].length) (baseStart_5944024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5944024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5944024 prefixEnd_5944024 := by exact prefixLift 5944024
  have htrace : WordTrace (prefixWord ++ tailWord_5944024) baseStart_5944024 baseEnd_5944024 := by
    simpa [prefixWord, tailWord_5944024, baseEnd_5944024] using wordTrace_append hprefix tailTrace_5944024
  have hstable : (prefixWord ++ tailWord_5944024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5944024).length < 2 ^ (prefixWord ++ tailWord_5944024).sum := by decide
  have hdescent : baseEnd_5944024 < baseStart_5944024 := by decide
  rcases family_descends (prefixWord ++ tailWord_5944024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5944035 : List Nat := [1, 1, 1, 7, 1, 3, 1, 1, 2, 3, 2]
def baseStart_5944035 : Nat := 118140960795 + 5944035 * 2 ^ 59
def prefixEnd_5944035 : Nat := 4983230072969 + 3 ^ 40 * 5944035 * 2
def baseEnd_5944035 : Nat := 3052146982147756669426387

theorem tailTrace_5944035 : CollatzResearch.WordTrace tailWord_5944035 prefixEnd_5944035 3052146982147756669426387 := by
  unfold tailWord_5944035
  simp only [CollatzResearch.WordTrace]
  refine ⟨216796767020783830202065559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144531178013855886801377039 216796767020783830202065559)
  ·
    refine ⟨325195150531175745303098339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216796767020783830202065559 325195150531175745303098339)
    ·
      refine ⟨487792725796763617954647509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325195150531175745303098339 487792725796763617954647509)
      ·
        refine ⟨11432642010861647295812051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 487792725796763617954647509 11432642010861647295812051)
        ·
          refine ⟨17148963016292470943718077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11432642010861647295812051 17148963016292470943718077)
          ·
            refine ⟨6430861131109676603894279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17148963016292470943718077 6430861131109676603894279)
            ·
              refine ⟨9646291696664514905841419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6430861131109676603894279 9646291696664514905841419)
              ·
                refine ⟨14469437544996772358762129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9646291696664514905841419 14469437544996772358762129)
                ·
                  refine ⟨10852078158747579269071597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14469437544996772358762129 10852078158747579269071597)
                  ·
                    refine ⟨4069529309530342225901849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10852078158747579269071597 4069529309530342225901849)
                    ·
                      refine ⟨3052146982147756669426387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4069529309530342225901849 3052146982147756669426387)
                      ·
                        rfl

theorem cell23_5944035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_5944035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5944035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5944035 prefixEnd_5944035 := by exact prefixLift 5944035
  have htrace : WordTrace (prefixWord ++ tailWord_5944035) baseStart_5944035 baseEnd_5944035 := by
    simpa [prefixWord, tailWord_5944035, baseEnd_5944035] using wordTrace_append hprefix tailTrace_5944035
  have hstable : (prefixWord ++ tailWord_5944035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5944035).length < 2 ^ (prefixWord ++ tailWord_5944035).sum := by decide
  have hdescent : baseEnd_5944035 < baseStart_5944035 := by decide
  rcases family_descends (prefixWord ++ tailWord_5944035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5944054 : List Nat := [5, 1, 1, 1, 1, 2, 12]
def baseStart_5944054 : Nat := 118140960795 + 5944054 * 2 ^ 59
def prefixEnd_5944054 : Nat := 4983230072969 + 3 ^ 40 * 5944054 * 2
def baseEnd_5944054 : Nat := 37680947386175211050479

theorem tailTrace_5944054 : CollatzResearch.WordTrace tailWord_5944054 prefixEnd_5944054 37680947386175211050479 := by
  unfold tailWord_5944054
  simp only [CollatzResearch.WordTrace]
  refine ⟨13549841250482187277937951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 144531640005143330964671477 13549841250482187277937951)
  ·
    refine ⟨20324761875723280916906927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13549841250482187277937951 20324761875723280916906927)
    ·
      refine ⟨30487142813584921375360391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20324761875723280916906927 30487142813584921375360391)
      ·
        refine ⟨45730714220377382063040587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30487142813584921375360391 45730714220377382063040587)
        ·
          refine ⟨68596071330566073094560881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45730714220377382063040587 68596071330566073094560881)
          ·
            refine ⟨51447053497924554820920661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68596071330566073094560881 51447053497924554820920661)
            ·
              refine ⟨37680947386175211050479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 51447053497924554820920661 37680947386175211050479)
              ·
                rfl

theorem cell23_5944054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 12].length) (baseStart_5944054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5944054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5944054 prefixEnd_5944054 := by exact prefixLift 5944054
  have htrace : WordTrace (prefixWord ++ tailWord_5944054) baseStart_5944054 baseEnd_5944054 := by
    simpa [prefixWord, tailWord_5944054, baseEnd_5944054] using wordTrace_append hprefix tailTrace_5944054
  have hstable : (prefixWord ++ tailWord_5944054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5944054).length < 2 ^ (prefixWord ++ tailWord_5944054).sum := by decide
  have hdescent : baseEnd_5944054 < baseStart_5944054 := by decide
  rcases family_descends (prefixWord ++ tailWord_5944054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5944081 : List Nat := [1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 3]
def baseStart_5944081 : Nat := 118140960795 + 5944081 * 2 ^ 59
def prefixEnd_5944081 : Nat := 4983230072969 + 3 ^ 40 * 5944081 * 2
def baseEnd_5944081 : Nat := 3052170602257863489451175

theorem tailTrace_5944081 : CollatzResearch.WordTrace tailWord_5944081 prefixEnd_5944081 3052170602257863489451175 := by
  unfold tailWord_5944081
  simp only [CollatzResearch.WordTrace]
  refine ⟨216798444778617180058240097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144532296519078120038826731 216798444778617180058240097)
  ·
    refine ⟨162598833583962885043680073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216798444778617180058240097 162598833583962885043680073)
    ·
      refine ⟨121949125187972163782760055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162598833583962885043680073 121949125187972163782760055)
      ·
        refine ⟨182923687781958245674140083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121949125187972163782760055 182923687781958245674140083)
        ·
          refine ⟨274385531672937368511210125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182923687781958245674140083 274385531672937368511210125)
          ·
            refine ⟨102894574377351513191703797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 274385531672937368511210125 102894574377351513191703797)
            ·
              refine ⟨9646366347876704361722231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 102894574377351513191703797 9646366347876704361722231)
              ·
                refine ⟨14469549521815056542583347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9646366347876704361722231 14469549521815056542583347)
                ·
                  refine ⟨21704324282722584813875021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14469549521815056542583347 21704324282722584813875021)
                  ·
                    refine ⟨8139121606020969305203133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21704324282722584813875021 8139121606020969305203133)
                    ·
                      refine ⟨3052170602257863489451175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8139121606020969305203133 3052170602257863489451175)
                      ·
                        rfl

theorem cell23_5944081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 3].length) (baseStart_5944081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5944081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5944081 prefixEnd_5944081 := by exact prefixLift 5944081
  have htrace : WordTrace (prefixWord ++ tailWord_5944081) baseStart_5944081 baseEnd_5944081 := by
    simpa [prefixWord, tailWord_5944081, baseEnd_5944081] using wordTrace_append hprefix tailTrace_5944081
  have hstable : (prefixWord ++ tailWord_5944081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5944081).length < 2 ^ (prefixWord ++ tailWord_5944081).sum := by decide
  have hdescent : baseEnd_5944081 < baseStart_5944081 := by decide
  rcases family_descends (prefixWord ++ tailWord_5944081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5944098 : List Nat := [3, 3, 1, 1, 2, 2, 1, 2, 4, 1, 3]
def baseStart_5944098 : Nat := 118140960795 + 5944098 * 2 ^ 59
def prefixEnd_5944098 : Nat := 4983230072969 + 3 ^ 40 * 5944098 * 2
def baseEnd_5944098 : Nat := 3052179331428989922938597

theorem tailTrace_5944098 : CollatzResearch.WordTrace tailWord_5944098 prefixEnd_5944098 3052179331428989922938597 := by
  unfold tailWord_5944098
  simp only [CollatzResearch.WordTrace]
  refine ⟨54199766204888897990402237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144532709879703727974405965 54199766204888897990402237)
  ·
    refine ⟨20324912326833336746400839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54199766204888897990402237 20324912326833336746400839)
    ·
      refine ⟨30487368490250005119601259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20324912326833336746400839 30487368490250005119601259)
      ·
        refine ⟨45731052735375007679401889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30487368490250005119601259 45731052735375007679401889)
        ·
          refine ⟨34298289551531255759551417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45731052735375007679401889 34298289551531255759551417)
          ·
            refine ⟨25723717163648441819663563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34298289551531255759551417 25723717163648441819663563)
            ·
              refine ⟨38585575745472662729495345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25723717163648441819663563 38585575745472662729495345)
              ·
                refine ⟨28939181809104497047121509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38585575745472662729495345 28939181809104497047121509)
                ·
                  refine ⟨5426096589207093196335283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28939181809104497047121509 5426096589207093196335283)
                  ·
                    refine ⟨8139144883810639794502925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5426096589207093196335283 8139144883810639794502925)
                    ·
                      refine ⟨3052179331428989922938597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8139144883810639794502925 3052179331428989922938597)
                      ·
                        rfl

theorem cell23_5944098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 4, 1, 3].length) (baseStart_5944098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5944098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5944098 prefixEnd_5944098 := by exact prefixLift 5944098
  have htrace : WordTrace (prefixWord ++ tailWord_5944098) baseStart_5944098 baseEnd_5944098 := by
    simpa [prefixWord, tailWord_5944098, baseEnd_5944098] using wordTrace_append hprefix tailTrace_5944098
  have hstable : (prefixWord ++ tailWord_5944098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5944098).length < 2 ^ (prefixWord ++ tailWord_5944098).sum := by decide
  have hdescent : baseEnd_5944098 < baseStart_5944098 := by decide
  rcases family_descends (prefixWord ++ tailWord_5944098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5944108 : List Nat := [2, 2, 1, 1, 1, 4, 1, 5, 1, 3, 2]
def baseStart_5944108 : Nat := 118140960795 + 5944108 * 2 ^ 59
def prefixEnd_5944108 : Nat := 4983230072969 + 3 ^ 40 * 5944108 * 2
def baseEnd_5944108 : Nat := 3052184466235534883813551

theorem tailTrace_5944108 : CollatzResearch.WordTrace tailWord_5944108 prefixEnd_5944108 3052184466235534883813551 := by
  unfold tailWord_5944108
  simp only [CollatzResearch.WordTrace]
  refine ⟨108399714774759681834736489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144532953033012909112981985 108399714774759681834736489)
  ·
    refine ⟨81299786081069761376052367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108399714774759681834736489 81299786081069761376052367)
    ·
      refine ⟨121949679121604642064078551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81299786081069761376052367 121949679121604642064078551)
      ·
        refine ⟨182924518682406963096117827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121949679121604642064078551 182924518682406963096117827)
        ·
          refine ⟨274386778023610444644176741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182924518682406963096117827 274386778023610444644176741)
          ·
            refine ⟨51447520879426958370783139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 274386778023610444644176741 51447520879426958370783139)
            ·
              refine ⟨77171281319140437556174709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51447520879426958370783139 77171281319140437556174709)
              ·
                refine ⟨7234807623669416020891379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77171281319140437556174709 7234807623669416020891379)
                ·
                  refine ⟨10852211435504124031337069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7234807623669416020891379 10852211435504124031337069)
                  ·
                    refine ⟨4069579288314046511751401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10852211435504124031337069 4069579288314046511751401)
                    ·
                      refine ⟨3052184466235534883813551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4069579288314046511751401 3052184466235534883813551)
                      ·
                        rfl

theorem cell23_5944108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 3, 2].length) (baseStart_5944108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5944108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5944108 prefixEnd_5944108 := by exact prefixLift 5944108
  have htrace : WordTrace (prefixWord ++ tailWord_5944108) baseStart_5944108 baseEnd_5944108 := by
    simpa [prefixWord, tailWord_5944108, baseEnd_5944108] using wordTrace_append hprefix tailTrace_5944108
  have hstable : (prefixWord ++ tailWord_5944108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5944108).length < 2 ^ (prefixWord ++ tailWord_5944108).sum := by decide
  have hdescent : baseEnd_5944108 < baseStart_5944108 := by decide
  rcases family_descends (prefixWord ++ tailWord_5944108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5944116 : List Nat := [2, 5, 1, 1, 3, 1, 3, 2, 1, 2, 2]
def baseStart_5944116 : Nat := 118140960795 + 5944116 * 2 ^ 59
def prefixEnd_5944116 : Nat := 4983230072969 + 3 ^ 40 * 5944116 * 2
def baseEnd_5944116 : Nat := 3052188574080770852513515

theorem tailTrace_5944116 : CollatzResearch.WordTrace tailWord_5944116 prefixEnd_5944116 3052188574080770852513515 := by
  unfold tailWord_5944116
  simp only [CollatzResearch.WordTrace]
  refine ⟨108399860666745190517882101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144533147555660254023842801 108399860666745190517882101)
  ·
    refine ⟨10162486937507361611051447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 108399860666745190517882101 10162486937507361611051447)
    ·
      refine ⟨15243730406261042416577171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10162486937507361611051447 15243730406261042416577171)
      ·
        refine ⟨22865595609391563624865757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15243730406261042416577171 22865595609391563624865757)
        ·
          refine ⟨8574598353521836359324659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22865595609391563624865757 8574598353521836359324659)
          ·
            refine ⟨12861897530282754538986989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8574598353521836359324659 12861897530282754538986989)
            ·
              refine ⟨4823211573856032952120121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12861897530282754538986989 4823211573856032952120121)
              ·
                refine ⟨3617408680392024714090091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4823211573856032952120121 3617408680392024714090091)
                ·
                  refine ⟨5426113020588037071135137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3617408680392024714090091 5426113020588037071135137)
                  ·
                    refine ⟨4069584765441027803351353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5426113020588037071135137 4069584765441027803351353)
                    ·
                      refine ⟨3052188574080770852513515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4069584765441027803351353 3052188574080770852513515)
                      ·
                        rfl

theorem cell23_5944116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 3, 2, 1, 2, 2].length) (baseStart_5944116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5944116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5944116 prefixEnd_5944116 := by exact prefixLift 5944116
  have htrace : WordTrace (prefixWord ++ tailWord_5944116) baseStart_5944116 baseEnd_5944116 := by
    simpa [prefixWord, tailWord_5944116, baseEnd_5944116] using wordTrace_append hprefix tailTrace_5944116
  have hstable : (prefixWord ++ tailWord_5944116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5944116).length < 2 ^ (prefixWord ++ tailWord_5944116).sum := by decide
  have hdescent : baseEnd_5944116 < baseStart_5944116 := by decide
  rcases family_descends (prefixWord ++ tailWord_5944116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5944124 : List Nat := [2, 2, 2, 2, 1, 1, 1, 1, 3, 3, 5]
def baseStart_5944124 : Nat := 118140960795 + 5944124 * 2 ^ 59
def prefixEnd_5944124 : Nat := 4983230072969 + 3 ^ 40 * 5944124 * 2
def baseEnd_5944124 : Nat := 3052192681926006821213477

theorem tailTrace_5944124 : CollatzResearch.WordTrace tailWord_5944124 prefixEnd_5944124 3052192681926006821213477 := by
  unfold tailWord_5944124
  simp only [CollatzResearch.WordTrace]
  refine ⟨108400006558730699201027713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144533342078307598934703617 108400006558730699201027713)
  ·
    refine ⟨81300004919048024400770785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108400006558730699201027713 81300004919048024400770785)
    ·
      refine ⟨60975003689286018300578089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81300004919048024400770785 60975003689286018300578089)
      ·
        refine ⟨45731252766964513725433567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60975003689286018300578089 45731252766964513725433567)
        ·
          refine ⟨68596879150446770588150351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45731252766964513725433567 68596879150446770588150351)
          ·
            refine ⟨102895318725670155882225527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68596879150446770588150351 102895318725670155882225527)
            ·
              refine ⟨154342978088505233823338291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102895318725670155882225527 154342978088505233823338291)
              ·
                refine ⟨231514467132757850735007437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154342978088505233823338291 231514467132757850735007437)
                ·
                  refine ⟨86817925174784194025627789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 231514467132757850735007437 86817925174784194025627789)
                  ·
                    refine ⟨32556721940544072759610421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 86817925174784194025627789 32556721940544072759610421)
                    ·
                      refine ⟨3052192681926006821213477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32556721940544072759610421 3052192681926006821213477)
                      ·
                        rfl

theorem cell23_5944124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_5944124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5944124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5944124 prefixEnd_5944124 := by exact prefixLift 5944124
  have htrace : WordTrace (prefixWord ++ tailWord_5944124) baseStart_5944124 baseEnd_5944124 := by
    simpa [prefixWord, tailWord_5944124, baseEnd_5944124] using wordTrace_append hprefix tailTrace_5944124
  have hstable : (prefixWord ++ tailWord_5944124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5944124).length < 2 ^ (prefixWord ++ tailWord_5944124).sum := by decide
  have hdescent : baseEnd_5944124 < baseStart_5944124 := by decide
  rcases family_descends (prefixWord ++ tailWord_5944124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5944138 : List Nat := [3, 1, 2, 1, 1, 1, 2, 2, 6, 2, 2]
def baseStart_5944138 : Nat := 118140960795 + 5944138 * 2 ^ 59
def prefixEnd_5944138 : Nat := 4983230072969 + 3 ^ 40 * 5944138 * 2
def baseEnd_5944138 : Nat := 3052199870655169766438413

theorem tailTrace_5944138 : CollatzResearch.WordTrace tailWord_5944138 prefixEnd_5944138 3052199870655169766438413 := by
  unfold tailWord_5944138
  simp only [CollatzResearch.WordTrace]
  refine ⟨54200130934852669698266267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144533682492940452528710045 54200130934852669698266267)
  ·
    refine ⟨81300196402279004547399401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54200130934852669698266267 81300196402279004547399401)
    ·
      refine ⟨60975147301709253410549551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81300196402279004547399401 60975147301709253410549551)
      ·
        refine ⟨91462720952563880115824327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60975147301709253410549551 91462720952563880115824327)
        ·
          refine ⟨137194081428845820173736491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91462720952563880115824327 137194081428845820173736491)
          ·
            refine ⟨205791122143268730260604737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137194081428845820173736491 205791122143268730260604737)
            ·
              refine ⟨154343341607451547695453553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 205791122143268730260604737 154343341607451547695453553)
              ·
                refine ⟨115757506205588660771590165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154343341607451547695453553 115757506205588660771590165)
                ·
                  refine ⟨5426133103386968473668289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 115757506205588660771590165 5426133103386968473668289)
                  ·
                    refine ⟨4069599827540226355251217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5426133103386968473668289 4069599827540226355251217)
                    ·
                      refine ⟨3052199870655169766438413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4069599827540226355251217 3052199870655169766438413)
                      ·
                        rfl

theorem cell23_5944138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 6, 2, 2].length) (baseStart_5944138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5944138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5944138 prefixEnd_5944138 := by exact prefixLift 5944138
  have htrace : WordTrace (prefixWord ++ tailWord_5944138) baseStart_5944138 baseEnd_5944138 := by
    simpa [prefixWord, tailWord_5944138, baseEnd_5944138] using wordTrace_append hprefix tailTrace_5944138
  have hstable : (prefixWord ++ tailWord_5944138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5944138).length < 2 ^ (prefixWord ++ tailWord_5944138).sum := by decide
  have hdescent : baseEnd_5944138 < baseStart_5944138 := by decide
  rcases family_descends (prefixWord ++ tailWord_5944138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5944144 : List Nat := [2, 1, 1, 1, 1, 4, 2, 4, 7]
def baseStart_5944144 : Nat := 118140960795 + 5944144 * 2 ^ 59
def prefixEnd_5944144 : Nat := 4983230072969 + 3 ^ 40 * 5944144 * 2
def baseEnd_5944144 : Nat := 339133661282121860329265

theorem tailTrace_5944144 : CollatzResearch.WordTrace tailWord_5944144 prefixEnd_5944144 339133661282121860329265 := by
  unfold tailWord_5944144
  simp only [CollatzResearch.WordTrace]
  refine ⟨108400371288694470908891743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144533828384925961211855657 108400371288694470908891743)
  ·
    refine ⟨162600556933041706363337615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108400371288694470908891743 162600556933041706363337615)
    ·
      refine ⟨243900835399562559545006423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162600556933041706363337615 243900835399562559545006423)
      ·
        refine ⟨365851253099343839317509635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243900835399562559545006423 365851253099343839317509635)
        ·
          refine ⟨548776879649015758976264453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365851253099343839317509635 548776879649015758976264453)
          ·
            refine ⟨102895664934190454808049585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 548776879649015758976264453 102895664934190454808049585)
            ·
              refine ⟨77171748700642841106037189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102895664934190454808049585 77171748700642841106037189)
              ·
                refine ⟨14469702881370532707381973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77171748700642841106037189 14469702881370532707381973)
                ·
                  refine ⟨339133661282121860329265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14469702881370532707381973 339133661282121860329265)
                  ·
                    rfl

theorem cell23_5944144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 4, 7].length) (baseStart_5944144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5944144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5944144 prefixEnd_5944144 := by exact prefixLift 5944144
  have htrace : WordTrace (prefixWord ++ tailWord_5944144) baseStart_5944144 baseEnd_5944144 := by
    simpa [prefixWord, tailWord_5944144, baseEnd_5944144] using wordTrace_append hprefix tailTrace_5944144
  have hstable : (prefixWord ++ tailWord_5944144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5944144).length < 2 ^ (prefixWord ++ tailWord_5944144).sum := by decide
  have hdescent : baseEnd_5944144 < baseStart_5944144 := by decide
  rcases family_descends (prefixWord ++ tailWord_5944144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5944184 : List Nat := [2, 1, 2, 1, 1, 1, 1, 5, 1, 1, 7]
def baseStart_5944184 : Nat := 118140960795 + 5944184 * 2 ^ 59
def prefixEnd_5944184 : Nat := 4983230072969 + 3 ^ 40 * 5944184 * 2
def baseEnd_5944184 : Nat := 3052223490765276586463201

theorem tailTrace_5944184 : CollatzResearch.WordTrace tailWord_5944184 prefixEnd_5944184 3052223490765276586463201 := by
  unfold tailWord_5944184
  simp only [CollatzResearch.WordTrace]
  refine ⟨108401100748622014324619803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144534800998162685766159737 108401100748622014324619803)
  ·
    refine ⟨162601651122933021486929705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108401100748622014324619803 162601651122933021486929705)
    ·
      refine ⟨121951238342199766115197279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162601651122933021486929705 121951238342199766115197279)
      ·
        refine ⟨182926857513299649172795919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121951238342199766115197279 182926857513299649172795919)
        ·
          refine ⟨274390286269949473759193879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182926857513299649172795919 274390286269949473759193879)
          ·
            refine ⟨411585429404924210638790819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274390286269949473759193879 411585429404924210638790819)
            ·
              refine ⟨617378144107386315958186229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 411585429404924210638790819 617378144107386315958186229)
              ·
                refine ⟨57879201010067467121079959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 617378144107386315958186229 57879201010067467121079959)
                ·
                  refine ⟨86818801515101200681619939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57879201010067467121079959 86818801515101200681619939)
                  ·
                    refine ⟨130228202272651801022429909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 86818801515101200681619939 130228202272651801022429909)
                    ·
                      refine ⟨3052223490765276586463201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 130228202272651801022429909 3052223490765276586463201)
                      ·
                        rfl

theorem cell23_5944184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 1, 1, 7].length) (baseStart_5944184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5944184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5944184 prefixEnd_5944184 := by exact prefixLift 5944184
  have htrace : WordTrace (prefixWord ++ tailWord_5944184) baseStart_5944184 baseEnd_5944184 := by
    simpa [prefixWord, tailWord_5944184, baseEnd_5944184] using wordTrace_append hprefix tailTrace_5944184
  have hstable : (prefixWord ++ tailWord_5944184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5944184).length < 2 ^ (prefixWord ++ tailWord_5944184).sum := by decide
  have hdescent : baseEnd_5944184 < baseStart_5944184 := by decide
  rcases family_descends (prefixWord ++ tailWord_5944184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5944211 : List Nat := [1, 1, 1, 2, 1, 2, 1, 7, 2, 1, 4]
def baseStart_5944211 : Nat := 118140960795 + 5944211 * 2 ^ 59
def prefixEnd_5944211 : Nat := 4983230072969 + 3 ^ 40 * 5944211 * 2
def baseEnd_5944211 : Nat := 3052237354742947980825577

theorem tailTrace_5944211 : CollatzResearch.WordTrace tailWord_5944211 prefixEnd_5944211 3052237354742947980825577 := by
  unfold tailWord_5944211
  simp only [CollatzResearch.WordTrace]
  refine ⟨216803186268146212260472487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144535457512097474840314991 216803186268146212260472487)
  ·
    refine ⟨325204779402219318390708731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216803186268146212260472487 325204779402219318390708731)
    ·
      refine ⟨487807169103328977586063097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325204779402219318390708731 487807169103328977586063097)
      ·
        refine ⟨365855376827496733189547323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 487807169103328977586063097 365855376827496733189547323)
        ·
          refine ⟨548783065241245099784320985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365855376827496733189547323 548783065241245099784320985)
          ·
            refine ⟨411587298930933824838240739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 548783065241245099784320985 411587298930933824838240739)
            ·
              refine ⟨617380948396400737257361109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 411587298930933824838240739 617380948396400737257361109)
              ·
                refine ⟨14469865978040642279469401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 617380948396400737257361109 14469865978040642279469401)
                ·
                  refine ⟨10852399483530481709602051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14469865978040642279469401 10852399483530481709602051)
                  ·
                    refine ⟨16278599225295722564403077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10852399483530481709602051 16278599225295722564403077)
                    ·
                      refine ⟨3052237354742947980825577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16278599225295722564403077 3052237354742947980825577)
                      ·
                        rfl

theorem cell23_5944211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 7, 2, 1, 4].length) (baseStart_5944211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5944211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5944211 prefixEnd_5944211 := by exact prefixLift 5944211
  have htrace : WordTrace (prefixWord ++ tailWord_5944211) baseStart_5944211 baseEnd_5944211 := by
    simpa [prefixWord, tailWord_5944211, baseEnd_5944211] using wordTrace_append hprefix tailTrace_5944211
  have hstable : (prefixWord ++ tailWord_5944211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5944211).length < 2 ^ (prefixWord ++ tailWord_5944211).sum := by decide
  have hdescent : baseEnd_5944211 < baseStart_5944211 := by decide
  rcases family_descends (prefixWord ++ tailWord_5944211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5944228 : List Nat := [2, 3, 1, 2, 1, 2, 1, 1, 4, 4, 2]
def baseStart_5944228 : Nat := 118140960795 + 5944228 * 2 ^ 59
def prefixEnd_5944228 : Nat := 4983230072969 + 3 ^ 40 * 5944228 * 2
def baseEnd_5944228 : Nat := 3052246083914074414312999

theorem tailTrace_5944228 : CollatzResearch.WordTrace tailWord_5944228 prefixEnd_5944228 3052246083914074414312999 := by
  unfold tailWord_5944228
  simp only [CollatzResearch.WordTrace]
  refine ⟨108401903154542312081920669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144535870872723082775894225 108401903154542312081920669)
  ·
    refine ⟨40650713682953367030720251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108401903154542312081920669 40650713682953367030720251)
    ·
      refine ⟨60976070524430050546080377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40650713682953367030720251 60976070524430050546080377)
      ·
        refine ⟨45732052893322537909560283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60976070524430050546080377 45732052893322537909560283)
        ·
          refine ⟨68598079339983806864340425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45732052893322537909560283 68598079339983806864340425)
          ·
            refine ⟨51448559504987855148255319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68598079339983806864340425 51448559504987855148255319)
            ·
              refine ⟨77172839257481782722382979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51448559504987855148255319 77172839257481782722382979)
              ·
                refine ⟨115759258886222674083574469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77172839257481782722382979 115759258886222674083574469)
                ·
                  refine ⟨21704861041166751390670213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 115759258886222674083574469 21704861041166751390670213)
                  ·
                    refine ⟨4069661445218765885750665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21704861041166751390670213 4069661445218765885750665)
                    ·
                      refine ⟨3052246083914074414312999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4069661445218765885750665 3052246083914074414312999)
                      ·
                        rfl

theorem cell23_5944228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 4, 4, 2].length) (baseStart_5944228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5944228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5944228 prefixEnd_5944228 := by exact prefixLift 5944228
  have htrace : WordTrace (prefixWord ++ tailWord_5944228) baseStart_5944228 baseEnd_5944228 := by
    simpa [prefixWord, tailWord_5944228, baseEnd_5944228] using wordTrace_append hprefix tailTrace_5944228
  have hstable : (prefixWord ++ tailWord_5944228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5944228).length < 2 ^ (prefixWord ++ tailWord_5944228).sum := by decide
  have hdescent : baseEnd_5944228 < baseStart_5944228 := by decide
  rcases family_descends (prefixWord ++ tailWord_5944228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5944302 : List Nat := [4, 1, 2, 1, 4, 2, 2, 1, 6]
def baseStart_5944302 : Nat := 118140960795 + 5944302 * 2 ^ 59
def prefixEnd_5944302 : Nat := 4983230072969 + 3 ^ 40 * 5944302 * 2
def baseEnd_5944302 : Nat := 339142675720278569420851

theorem tailTrace_5944302 : CollatzResearch.WordTrace tailWord_5944302 prefixEnd_5944302 339142675720278569420851 := by
  unfold tailWord_5944302
  simp only [CollatzResearch.WordTrace]
  refine ⟨27100813163852066850254395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144537670207211023201356773 27100813163852066850254395)
  ·
    refine ⟨40651219745778100275381593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27100813163852066850254395 40651219745778100275381593)
    ·
      refine ⟨30488414809333575206536195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40651219745778100275381593 30488414809333575206536195)
      ·
        refine ⟨45732622214000362809804293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30488414809333575206536195 45732622214000362809804293)
        ·
          refine ⟨8574866665125068026838305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45732622214000362809804293 8574866665125068026838305)
          ·
            refine ⟨6431149998843801020128729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8574866665125068026838305 6431149998843801020128729)
            ·
              refine ⟨4823362499132850765096547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6431149998843801020128729 4823362499132850765096547)
              ·
                refine ⟨7235043748699276147644821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4823362499132850765096547 7235043748699276147644821)
                ·
                  refine ⟨339142675720278569420851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7235043748699276147644821 339142675720278569420851)
                  ·
                    rfl

theorem cell23_5944302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 2, 1, 6].length) (baseStart_5944302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5944302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5944302 prefixEnd_5944302 := by exact prefixLift 5944302
  have htrace : WordTrace (prefixWord ++ tailWord_5944302) baseStart_5944302 baseEnd_5944302 := by
    simpa [prefixWord, tailWord_5944302, baseEnd_5944302] using wordTrace_append hprefix tailTrace_5944302
  have hstable : (prefixWord ++ tailWord_5944302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5944302).length < 2 ^ (prefixWord ++ tailWord_5944302).sum := by decide
  have hdescent : baseEnd_5944302 < baseStart_5944302 := by decide
  rcases family_descends (prefixWord ++ tailWord_5944302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5944328 : List Nat := [2, 1, 3, 2, 1, 4, 1, 2, 1, 6]
def baseStart_5944328 : Nat := 118140960795 + 5944328 * 2 ^ 59
def prefixEnd_5944328 : Nat := 4983230072969 + 3 ^ 40 * 5944328 * 2
def baseEnd_5944328 : Nat := 1017432477326508007687513

theorem tailTrace_5944328 : CollatzResearch.WordTrace tailWord_5944328 prefixEnd_5944328 1017432477326508007687513 := by
  unfold tailWord_5944328
  simp only [CollatzResearch.WordTrace]
  refine ⟨108403726804361170621240819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144538302405814894161654425 108403726804361170621240819)
  ·
    refine ⟨162605590206541755931861229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108403726804361170621240819 162605590206541755931861229)
    ·
      refine ⟨60977096327453158474447961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162605590206541755931861229 60977096327453158474447961)
      ·
        refine ⟨45732822245589868855835971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60977096327453158474447961 45732822245589868855835971)
        ·
          refine ⟨68599233368384803283753957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45732822245589868855835971 68599233368384803283753957)
          ·
            refine ⟨12862356256572150615703867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68599233368384803283753957 12862356256572150615703867)
            ·
              refine ⟨19293534384858225923555801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12862356256572150615703867 19293534384858225923555801)
              ·
                refine ⟨14470150788643669442666851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19293534384858225923555801 14470150788643669442666851)
                ·
                  refine ⟨21705226182965504164000277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14470150788643669442666851 21705226182965504164000277)
                  ·
                    refine ⟨1017432477326508007687513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21705226182965504164000277 1017432477326508007687513)
                    ·
                      rfl

theorem cell23_5944328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 2, 1, 6].length) (baseStart_5944328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5944328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5944328 prefixEnd_5944328 := by exact prefixLift 5944328
  have htrace : WordTrace (prefixWord ++ tailWord_5944328) baseStart_5944328 baseEnd_5944328 := by
    simpa [prefixWord, tailWord_5944328, baseEnd_5944328] using wordTrace_append hprefix tailTrace_5944328
  have hstable : (prefixWord ++ tailWord_5944328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5944328).length < 2 ^ (prefixWord ++ tailWord_5944328).sum := by decide
  have hdescent : baseEnd_5944328 < baseStart_5944328 := by decide
  rcases family_descends (prefixWord ++ tailWord_5944328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5944341 : List Nat := [1, 3, 2, 1, 4, 12]
def baseStart_5944341 : Nat := 118140960795 + 5944341 * 2 ^ 59
def prefixEnd_5944341 : Nat := 4983230072969 + 3 ^ 40 * 5944341 * 2
def baseEnd_5944341 : Nat := 12560922251967211819753

theorem tailTrace_5944341 : CollatzResearch.WordTrace tailWord_5944341 prefixEnd_5944341 12560922251967211819753 := by
  unfold tailWord_5944341
  simp only [CollatzResearch.WordTrace]
  refine ⟨216807927757675244462704877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144538618505116829641803251 216807927757675244462704877)
  ·
    refine ⟨81302972909128216673514329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216807927757675244462704877 81302972909128216673514329)
    ·
      refine ⟨60977229681846162505135747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81302972909128216673514329 60977229681846162505135747)
      ·
        refine ⟨91465844522769243757703621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60977229681846162505135747 91465844522769243757703621)
        ·
          refine ⟨17149845848019233204569429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91465844522769243757703621 17149845848019233204569429)
          ·
            refine ⟨12560922251967211819753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 17149845848019233204569429 12560922251967211819753)
            ·
              rfl

theorem cell23_5944341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 12].length) (baseStart_5944341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5944341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5944341 prefixEnd_5944341 := by exact prefixLift 5944341
  have htrace : WordTrace (prefixWord ++ tailWord_5944341) baseStart_5944341 baseEnd_5944341 := by
    simpa [prefixWord, tailWord_5944341, baseEnd_5944341] using wordTrace_append hprefix tailTrace_5944341
  have hstable : (prefixWord ++ tailWord_5944341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5944341).length < 2 ^ (prefixWord ++ tailWord_5944341).sum := by decide
  have hdescent : baseEnd_5944341 < baseStart_5944341 := by decide
  rcases family_descends (prefixWord ++ tailWord_5944341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5944371 : List Nat := [1, 1, 1, 2, 4, 1, 1, 1, 4, 7]
def baseStart_5944371 : Nat := 118140960795 + 5944371 * 2 ^ 59
def prefixEnd_5944371 : Nat := 4983230072969 + 3 ^ 40 * 5944371 * 2
def baseEnd_5944371 : Nat := 1017439837215889118274947

theorem tailTrace_5944371 : CollatzResearch.WordTrace tailWord_5944371 prefixEnd_5944371 1017439837215889118274947 := by
  unfold tailWord_5944371
  simp only [CollatzResearch.WordTrace]
  refine ⟨216809021947566559586296967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144539347965044373057531311 216809021947566559586296967)
  ·
    refine ⟨325213532921349839379445451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216809021947566559586296967 325213532921349839379445451)
    ·
      refine ⟨487820299382024759069168177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325213532921349839379445451 487820299382024759069168177)
      ·
        refine ⟨365865224536518569301876133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 487820299382024759069168177 365865224536518569301876133)
        ·
          refine ⟨68599729600597231744101775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 365865224536518569301876133 68599729600597231744101775)
          ·
            refine ⟨102899594400895847616152663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68599729600597231744101775 102899594400895847616152663)
            ·
              refine ⟨154349391601343771424228995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102899594400895847616152663 154349391601343771424228995)
              ·
                refine ⟨231524087402015657136343493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154349391601343771424228995 231524087402015657136343493)
                ·
                  refine ⟨43410766387877935713064405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 231524087402015657136343493 43410766387877935713064405)
                  ·
                    refine ⟨1017439837215889118274947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43410766387877935713064405 1017439837215889118274947)
                    ·
                      rfl

theorem cell23_5944371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 7].length) (baseStart_5944371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5944371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5944371 prefixEnd_5944371 := by exact prefixLift 5944371
  have htrace : WordTrace (prefixWord ++ tailWord_5944371) baseStart_5944371 baseEnd_5944371 := by
    simpa [prefixWord, tailWord_5944371, baseEnd_5944371] using wordTrace_append hprefix tailTrace_5944371
  have hstable : (prefixWord ++ tailWord_5944371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5944371).length < 2 ^ (prefixWord ++ tailWord_5944371).sum := by decide
  have hdescent : baseEnd_5944371 < baseStart_5944371 := by decide
  rcases family_descends (prefixWord ++ tailWord_5944371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5944372 : List Nat := [2, 5, 1, 2, 1, 1, 2, 1, 3, 2, 3]
def baseStart_5944372 : Nat := 118140960795 + 5944372 * 2 ^ 59
def prefixEnd_5944372 : Nat := 4983230072969 + 3 ^ 40 * 5944372 * 2
def baseEnd_5944372 : Nat := 3052320025128321850912337

theorem tailTrace_5944372 : CollatzResearch.WordTrace tailWord_5944372 prefixEnd_5944372 3052320025128321850912337 := by
  unfold tailWord_5944372
  simp only [CollatzResearch.WordTrace]
  refine ⟨108404529210281468378541685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144539372280375291171388913 108404529210281468378541685)
  ·
    refine ⟨10162924613463887660488283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 108404529210281468378541685 10162924613463887660488283)
    ·
      refine ⟨15244386920195831490732425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10162924613463887660488283 15244386920195831490732425)
      ·
        refine ⟨11433290190146873618049319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15244386920195831490732425 11433290190146873618049319)
        ·
          refine ⟨17149935285220310427073979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11433290190146873618049319 17149935285220310427073979)
          ·
            refine ⟨25724902927830465640610969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17149935285220310427073979 25724902927830465640610969)
            ·
              refine ⟨19293677195872849230458227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25724902927830465640610969 19293677195872849230458227)
              ·
                refine ⟨28940515793809273845687341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19293677195872849230458227 28940515793809273845687341)
                ·
                  refine ⟨10852693422678477692132753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28940515793809273845687341 10852693422678477692132753)
                  ·
                    refine ⟨8139520067008858269099565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10852693422678477692132753 8139520067008858269099565)
                    ·
                      refine ⟨3052320025128321850912337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8139520067008858269099565 3052320025128321850912337)
                      ·
                        rfl

theorem cell23_5944372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_5944372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5944372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5944372 prefixEnd_5944372 := by exact prefixLift 5944372
  have htrace : WordTrace (prefixWord ++ tailWord_5944372) baseStart_5944372 baseEnd_5944372 := by
    simpa [prefixWord, tailWord_5944372, baseEnd_5944372] using wordTrace_append hprefix tailTrace_5944372
  have hstable : (prefixWord ++ tailWord_5944372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5944372).length < 2 ^ (prefixWord ++ tailWord_5944372).sum := by decide
  have hdescent : baseEnd_5944372 < baseStart_5944372 := by decide
  rcases family_descends (prefixWord ++ tailWord_5944372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5944402 : List Nat := [3, 2, 2, 1, 3, 2, 1, 1, 4, 1, 3]
def baseStart_5944402 : Nat := 118140960795 + 5944402 * 2 ^ 59
def prefixEnd_5944402 : Nat := 4983230072969 + 3 ^ 40 * 5944402 * 2
def baseEnd_5944402 : Nat := 3052335429547956733537199

theorem tailTrace_5944402 : CollatzResearch.WordTrace tailWord_5944402 prefixEnd_5944402 3052335429547956733537199 := by
  unfold tailWord_5944402
  simp only [CollatzResearch.WordTrace]
  refine ⟨54202538152613562970168865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144540101740302834587116973 54202538152613562970168865)
  ·
    refine ⟨40651903614460172227626649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54202538152613562970168865 40651903614460172227626649)
    ·
      refine ⟨30488927710845129170719987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40651903614460172227626649 30488927710845129170719987)
      ·
        refine ⟨45733391566267693756079981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30488927710845129170719987 45733391566267693756079981)
        ·
          refine ⟨17150021837350385158529993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45733391566267693756079981 17150021837350385158529993)
          ·
            refine ⟨12862516378012788868897495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17150021837350385158529993 12862516378012788868897495)
            ·
              refine ⟨19293774567019183303346243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12862516378012788868897495 19293774567019183303346243)
              ·
                refine ⟨28940661850528774955019365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19293774567019183303346243 28940661850528774955019365)
                ·
                  refine ⟨5426374096974145304066131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28940661850528774955019365 5426374096974145304066131)
                  ·
                    refine ⟨8139561145461217956099197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5426374096974145304066131 8139561145461217956099197)
                    ·
                      refine ⟨3052335429547956733537199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8139561145461217956099197 3052335429547956733537199)
                      ·
                        rfl

theorem cell23_5944402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 4, 1, 3].length) (baseStart_5944402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5944402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5944402 prefixEnd_5944402 := by exact prefixLift 5944402
  have htrace : WordTrace (prefixWord ++ tailWord_5944402) baseStart_5944402 baseEnd_5944402 := by
    simpa [prefixWord, tailWord_5944402, baseEnd_5944402] using wordTrace_append hprefix tailTrace_5944402
  have hstable : (prefixWord ++ tailWord_5944402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5944402).length < 2 ^ (prefixWord ++ tailWord_5944402).sum := by decide
  have hdescent : baseEnd_5944402 < baseStart_5944402 := by decide
  rcases family_descends (prefixWord ++ tailWord_5944402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5944428 : List Nat := [2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 5]
def baseStart_5944428 : Nat := 118140960795 + 5944428 * 2 ^ 59
def prefixEnd_5944428 : Nat := 4983230072969 + 3 ^ 40 * 5944428 * 2
def baseEnd_5944428 : Nat := 3052348780044973631812079

theorem tailTrace_5944428 : CollatzResearch.WordTrace tailWord_5944428 prefixEnd_5944428 3052348780044973631812079 := by
  unfold tailWord_5944428
  simp only [CollatzResearch.WordTrace]
  refine ⟨108405550454180029160560969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144540733938906705547414625 108405550454180029160560969)
  ·
    refine ⟨81304162840635021870420727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108405550454180029160560969 81304162840635021870420727)
    ·
      refine ⟨121956244260952532805631091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81304162840635021870420727 121956244260952532805631091)
      ·
        refine ⟨182934366391428799208446637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121956244260952532805631091 182934366391428799208446637)
        ·
          refine ⟨68600387396785799703167489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182934366391428799208446637 68600387396785799703167489)
          ·
            refine ⟨51450290547589349777375617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68600387396785799703167489 51450290547589349777375617)
            ·
              refine ⟨38587717910692012333031713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51450290547589349777375617 38587717910692012333031713)
              ·
                refine ⟨28940788433019009249773785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38587717910692012333031713 28940788433019009249773785)
                ·
                  refine ⟨21705591324764256937330339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28940788433019009249773785 21705591324764256937330339)
                  ·
                    refine ⟨32558386987146385405995509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21705591324764256937330339 32558386987146385405995509)
                    ·
                      refine ⟨3052348780044973631812079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32558386987146385405995509 3052348780044973631812079)
                      ·
                        rfl

theorem cell23_5944428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 5].length) (baseStart_5944428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5944428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5944428 prefixEnd_5944428 := by exact prefixLift 5944428
  have htrace : WordTrace (prefixWord ++ tailWord_5944428) baseStart_5944428 baseEnd_5944428 := by
    simpa [prefixWord, tailWord_5944428, baseEnd_5944428] using wordTrace_append hprefix tailTrace_5944428
  have hstable : (prefixWord ++ tailWord_5944428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5944428).length < 2 ^ (prefixWord ++ tailWord_5944428).sum := by decide
  have hdescent : baseEnd_5944428 < baseStart_5944428 := by decide
  rcases family_descends (prefixWord ++ tailWord_5944428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5944429 : List Nat := [1, 5, 1, 1, 2, 3, 2, 2, 1, 3, 2]
def baseStart_5944429 : Nat := 118140960795 + 5944429 * 2 ^ 59
def prefixEnd_5944429 : Nat := 4983230072969 + 3 ^ 40 * 5944429 * 2
def baseEnd_5944429 : Nat := 3052349293525628127899575

theorem tailTrace_5944429 : CollatzResearch.WordTrace tailWord_5944429 prefixEnd_5944429 3052349293525628127899575 := by
  unfold tailWord_5944429
  simp only [CollatzResearch.WordTrace]
  refine ⟨216811137381356435491908341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144540758254237623661272227 216811137381356435491908341)
  ·
    refine ⟨20326044129502165827366407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 216811137381356435491908341 20326044129502165827366407)
    ·
      refine ⟨30489066194253248741049611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20326044129502165827366407 30489066194253248741049611)
      ·
        refine ⟨45733599291379873111574417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30489066194253248741049611 45733599291379873111574417)
        ·
          refine ⟨34300199468534904833680813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45733599291379873111574417 34300199468534904833680813)
          ·
            refine ⟨12862574800700589312630305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34300199468534904833680813 12862574800700589312630305)
            ·
              refine ⟨9646931100525441984472729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12862574800700589312630305 9646931100525441984472729)
              ·
                refine ⟨7235198325394081488354547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9646931100525441984472729 7235198325394081488354547)
                ·
                  refine ⟨10852797488091122232531821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7235198325394081488354547 10852797488091122232531821)
                  ·
                    refine ⟨4069799058034170837199433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10852797488091122232531821 4069799058034170837199433)
                    ·
                      refine ⟨3052349293525628127899575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4069799058034170837199433 3052349293525628127899575)
                      ·
                        rfl

theorem cell23_5944429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 2, 1, 3, 2].length) (baseStart_5944429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5944429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5944429 prefixEnd_5944429 := by exact prefixLift 5944429
  have htrace : WordTrace (prefixWord ++ tailWord_5944429) baseStart_5944429 baseEnd_5944429 := by
    simpa [prefixWord, tailWord_5944429, baseEnd_5944429] using wordTrace_append hprefix tailTrace_5944429
  have hstable : (prefixWord ++ tailWord_5944429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5944429).length < 2 ^ (prefixWord ++ tailWord_5944429).sum := by decide
  have hdescent : baseEnd_5944429 < baseStart_5944429 := by decide
  rcases family_descends (prefixWord ++ tailWord_5944429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5944458 : List Nat := [3, 1, 2, 3, 1, 1, 1, 1, 1, 2, 7]
def baseStart_5944458 : Nat := 118140960795 + 5944458 * 2 ^ 59
def prefixEnd_5944458 : Nat := 4983230072969 + 3 ^ 40 * 5944458 * 2
def baseEnd_5944458 : Nat := 3052364184464608514436941

theorem tailTrace_5944458 : CollatzResearch.WordTrace tailWord_5944458 prefixEnd_5944458 3052364184464608514436941 := by
  unfold tailWord_5944458
  simp only [CollatzResearch.WordTrace]
  refine ⟨54203048774562843361178507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144541463398834248963142685 54203048774562843361178507)
  ·
    refine ⟨81304573161844265041767761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54203048774562843361178507 81304573161844265041767761)
    ·
      refine ⟨60978429871383198781325821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81304573161844265041767761 60978429871383198781325821)
      ·
        refine ⟨22866911201768699542997183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60978429871383198781325821 22866911201768699542997183)
        ·
          refine ⟨34300366802653049314495775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22866911201768699542997183 34300366802653049314495775)
          ·
            refine ⟨51450550203979573971743663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34300366802653049314495775 51450550203979573971743663)
            ·
              refine ⟨77175825305969360957615495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51450550203979573971743663 77175825305969360957615495)
              ·
                refine ⟨115763737958954041436423243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77175825305969360957615495 115763737958954041436423243)
                ·
                  refine ⟨173645606938431062154634865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115763737958954041436423243 173645606938431062154634865)
                  ·
                    refine ⟨130234205203823296615976149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 173645606938431062154634865 130234205203823296615976149)
                    ·
                      refine ⟨3052364184464608514436941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 130234205203823296615976149 3052364184464608514436941)
                      ·
                        rfl

theorem cell23_5944458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_5944458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5944458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5944458 prefixEnd_5944458 := by exact prefixLift 5944458
  have htrace : WordTrace (prefixWord ++ tailWord_5944458) baseStart_5944458 baseEnd_5944458 := by
    simpa [prefixWord, tailWord_5944458, baseEnd_5944458] using wordTrace_append hprefix tailTrace_5944458
  have hstable : (prefixWord ++ tailWord_5944458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5944458).length < 2 ^ (prefixWord ++ tailWord_5944458).sum := by decide
  have hdescent : baseEnd_5944458 < baseStart_5944458 := by decide
  rcases family_descends (prefixWord ++ tailWord_5944458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5944476 : List Nat := [2, 2, 3, 2, 1, 2, 4, 1, 2, 2, 2]
def baseStart_5944476 : Nat := 118140960795 + 5944476 * 2 ^ 59
def prefixEnd_5944476 : Nat := 4983230072969 + 3 ^ 40 * 5944476 * 2
def baseEnd_5944476 : Nat := 3052373427116389444011859

theorem tailTrace_5944476 : CollatzResearch.WordTrace tailWord_5944476 prefixEnd_5944476 3052373427116389444011859 := by
  unfold tailWord_5944476
  simp only [CollatzResearch.WordTrace]
  refine ⟨108406425806093081259434641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144541901074790775012579521 108406425806093081259434641)
  ·
    refine ⟨81304819354569810944575981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108406425806093081259434641 81304819354569810944575981)
    ·
      refine ⟨30489307257963679104215993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81304819354569810944575981 30489307257963679104215993)
      ·
        refine ⟨22866980443472759328161995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30489307257963679104215993 22866980443472759328161995)
        ·
          refine ⟨34300470665209138992242993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22866980443472759328161995 34300470665209138992242993)
          ·
            refine ⟨25725352998906854244182245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34300470665209138992242993 25725352998906854244182245)
            ·
              refine ⟨4823503687295035170784171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25725352998906854244182245 4823503687295035170784171)
              ·
                refine ⟨7235255530942552756176257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4823503687295035170784171 7235255530942552756176257)
                ·
                  refine ⟨5426441648206914567132193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7235255530942552756176257 5426441648206914567132193)
                  ·
                    refine ⟨4069831236155185925349145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5426441648206914567132193 4069831236155185925349145)
                    ·
                      refine ⟨3052373427116389444011859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4069831236155185925349145 3052373427116389444011859)
                      ·
                        rfl

theorem cell23_5944476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 4, 1, 2, 2, 2].length) (baseStart_5944476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5944476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5944476 prefixEnd_5944476 := by exact prefixLift 5944476
  have htrace : WordTrace (prefixWord ++ tailWord_5944476) baseStart_5944476 baseEnd_5944476 := by
    simpa [prefixWord, tailWord_5944476, baseEnd_5944476] using wordTrace_append hprefix tailTrace_5944476
  have hstable : (prefixWord ++ tailWord_5944476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5944476).length < 2 ^ (prefixWord ++ tailWord_5944476).sum := by decide
  have hdescent : baseEnd_5944476 < baseStart_5944476 := by decide
  rcases family_descends (prefixWord ++ tailWord_5944476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5944516 : List Nat := [2, 3, 3, 1, 3, 2, 2, 2, 5]
def baseStart_5944516 : Nat := 118140960795 + 5944516 * 2 ^ 59
def prefixEnd_5944516 : Nat := 4983230072969 + 3 ^ 40 * 5944516 * 2
def baseEnd_5944516 : Nat := 339154885149174365279075

theorem tailTrace_5944516 : CollatzResearch.WordTrace tailWord_5944516 prefixEnd_5944516 339154885149174365279075 := by
  unfold tailWord_5944516
  simp only [CollatzResearch.WordTrace]
  refine ⟨108407155266020624675162701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144542873688027499566883601 108407155266020624675162701)
  ·
    refine ⟨40652683224757734253186013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108407155266020624675162701 40652683224757734253186013)
    ·
      refine ⟨15244756209284150344944755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40652683224757734253186013 15244756209284150344944755)
      ·
        refine ⟨22867134313926225517417133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15244756209284150344944755 22867134313926225517417133)
        ·
          refine ⟨8575175367722334569031425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22867134313926225517417133 8575175367722334569031425)
          ·
            refine ⟨6431381525791750926773569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8575175367722334569031425 6431381525791750926773569)
            ·
              refine ⟨4823536144343813195080177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6431381525791750926773569 4823536144343813195080177)
              ·
                refine ⟨3617652108257859896310133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4823536144343813195080177 3617652108257859896310133)
                ·
                  refine ⟨339154885149174365279075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3617652108257859896310133 339154885149174365279075)
                  ·
                    rfl

theorem cell23_5944516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 2, 2, 5].length) (baseStart_5944516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5944516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5944516 prefixEnd_5944516 := by exact prefixLift 5944516
  have htrace : WordTrace (prefixWord ++ tailWord_5944516) baseStart_5944516 baseEnd_5944516 := by
    simpa [prefixWord, tailWord_5944516, baseEnd_5944516] using wordTrace_append hprefix tailTrace_5944516
  have hstable : (prefixWord ++ tailWord_5944516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5944516).length < 2 ^ (prefixWord ++ tailWord_5944516).sum := by decide
  have hdescent : baseEnd_5944516 < baseStart_5944516 := by decide
  rcases family_descends (prefixWord ++ tailWord_5944516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5944535 : List Nat := [1, 1, 3, 2, 1, 2, 2, 2, 4, 2, 3]
def baseStart_5944535 : Nat := 118140960795 + 5944535 * 2 ^ 59
def prefixEnd_5944535 : Nat := 4983230072969 + 3 ^ 40 * 5944535 * 2
def baseEnd_5944535 : Nat := 3052403722475004713174087

theorem tailTrace_5944535 : CollatzResearch.WordTrace tailWord_5944535 prefixEnd_5944535 3052403722475004713174087 := by
  unfold tailWord_5944535
  simp only [CollatzResearch.WordTrace]
  refine ⟨216815003518972415595267059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144543335679314943730178039 216815003518972415595267059)
  ·
    refine ⟨325222505278458623392900589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216815003518972415595267059 325222505278458623392900589)
    ·
      refine ⟨121958439479421983772337721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 325222505278458623392900589 121958439479421983772337721)
      ·
        refine ⟨91468829609566487829253291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121958439479421983772337721 91468829609566487829253291)
        ·
          refine ⟨137203244414349731743879937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91468829609566487829253291 137203244414349731743879937)
          ·
            refine ⟨102902433310762298807909953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137203244414349731743879937 102902433310762298807909953)
            ·
              refine ⟨77176824983071724105932465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102902433310762298807909953 77176824983071724105932465)
              ·
                refine ⟨57882618737303793079449349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77176824983071724105932465 57882618737303793079449349)
                ·
                  refine ⟨10852991013244461202396753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57882618737303793079449349 10852991013244461202396753)
                  ·
                    refine ⟨8139743259933345901797565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10852991013244461202396753 8139743259933345901797565)
                    ·
                      refine ⟨3052403722475004713174087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8139743259933345901797565 3052403722475004713174087)
                      ·
                        rfl

theorem cell23_5944535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 4, 2, 3].length) (baseStart_5944535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5944535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5944535 prefixEnd_5944535 := by exact prefixLift 5944535
  have htrace : WordTrace (prefixWord ++ tailWord_5944535) baseStart_5944535 baseEnd_5944535 := by
    simpa [prefixWord, tailWord_5944535, baseEnd_5944535] using wordTrace_append hprefix tailTrace_5944535
  have hstable : (prefixWord ++ tailWord_5944535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5944535).length < 2 ^ (prefixWord ++ tailWord_5944535).sum := by decide
  have hdescent : baseEnd_5944535 < baseStart_5944535 := by decide
  rcases family_descends (prefixWord ++ tailWord_5944535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5944538 : List Nat := [3, 1, 1, 2, 2, 1, 1, 2, 10]
def baseStart_5944538 : Nat := 118140960795 + 5944538 * 2 ^ 59
def prefixEnd_5944538 : Nat := 4983230072969 + 3 ^ 40 * 5944538 * 2
def baseEnd_5944538 : Nat := 339156140324107577937397

theorem tailTrace_5944538 : CollatzResearch.WordTrace tailWord_5944538 prefixEnd_5944538 339156140324107577937397 := by
  unfold tailWord_5944538
  simp only [CollatzResearch.WordTrace]
  refine ⟨54203778234490386776906567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144543408625307698071750845 54203778234490386776906567)
  ·
    refine ⟨81305667351735580165359851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54203778234490386776906567 81305667351735580165359851)
    ·
      refine ⟨121958501027603370248039777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81305667351735580165359851 121958501027603370248039777)
      ·
        refine ⟨91468875770702527686029833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121958501027603370248039777 91468875770702527686029833)
        ·
          refine ⟨68601656828026895764522375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91468875770702527686029833 68601656828026895764522375)
          ·
            refine ⟨102902485242040343646783563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68601656828026895764522375 102902485242040343646783563)
            ·
              refine ⟨154353727863060515470175345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102902485242040343646783563 154353727863060515470175345)
              ·
                refine ⟨115765295897295386602631509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154353727863060515470175345 115765295897295386602631509)
                ·
                  refine ⟨339156140324107577937397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 115765295897295386602631509 339156140324107577937397)
                  ·
                    rfl

theorem cell23_5944538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 10].length) (baseStart_5944538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5944538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5944538 prefixEnd_5944538 := by exact prefixLift 5944538
  have htrace : WordTrace (prefixWord ++ tailWord_5944538) baseStart_5944538 baseEnd_5944538 := by
    simpa [prefixWord, tailWord_5944538, baseEnd_5944538] using wordTrace_append hprefix tailTrace_5944538
  have hstable : (prefixWord ++ tailWord_5944538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5944538).length < 2 ^ (prefixWord ++ tailWord_5944538).sum := by decide
  have hdescent : baseEnd_5944538 < baseStart_5944538 := by decide
  rcases family_descends (prefixWord ++ tailWord_5944538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5944549 : List Nat := [1, 3, 1, 4, 3, 2, 1, 1, 2, 1, 4]
def baseStart_5944549 : Nat := 118140960795 + 5944549 * 2 ^ 59
def prefixEnd_5944549 : Nat := 4983230072969 + 3 ^ 40 * 5944549 * 2
def baseEnd_5944549 : Nat := 3052410911204167658399023

theorem tailTrace_5944549 : CollatzResearch.WordTrace tailWord_5944549 prefixEnd_5944549 3052410911204167658399023 := by
  unfold tailWord_5944549
  simp only [CollatzResearch.WordTrace]
  refine ⟨216815514140921695986276701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144543676093947797324184467 216815514140921695986276701)
  ·
    refine ⟨81305817802845635994853763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216815514140921695986276701 81305817802845635994853763)
    ·
      refine ⟨121958726704268453992280645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81305817802845635994853763 121958726704268453992280645)
      ·
        refine ⟨22867261257050335123552621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121958726704268453992280645 22867261257050335123552621)
        ·
          refine ⟨8575222971393875671332233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22867261257050335123552621 8575222971393875671332233)
          ·
            refine ⟨6431417228545406753499175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8575222971393875671332233 6431417228545406753499175)
            ·
              refine ⟨9647125842818110130248763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6431417228545406753499175 9647125842818110130248763)
              ·
                refine ⟨14470688764227165195373145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9647125842818110130248763 14470688764227165195373145)
                ·
                  refine ⟨10853016573170373896529859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14470688764227165195373145 10853016573170373896529859)
                  ·
                    refine ⟨16279524859755560844794789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10853016573170373896529859 16279524859755560844794789)
                    ·
                      refine ⟨3052410911204167658399023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16279524859755560844794789 3052410911204167658399023)
                      ·
                        rfl

theorem cell23_5944549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_5944549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5944549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5944549 prefixEnd_5944549 := by exact prefixLift 5944549
  have htrace : WordTrace (prefixWord ++ tailWord_5944549) baseStart_5944549 baseEnd_5944549 := by
    simpa [prefixWord, tailWord_5944549, baseEnd_5944549] using wordTrace_append hprefix tailTrace_5944549
  have hstable : (prefixWord ++ tailWord_5944549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5944549).length < 2 ^ (prefixWord ++ tailWord_5944549).sum := by decide
  have hdescent : baseEnd_5944549 < baseStart_5944549 := by decide
  rcases family_descends (prefixWord ++ tailWord_5944549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5944602 : List Nat := [3, 1, 1, 3, 3, 1, 1, 4, 1, 5]
def baseStart_5944602 : Nat := 118140960795 + 5944602 * 2 ^ 59
def prefixEnd_5944602 : Nat := 4983230072969 + 3 ^ 40 * 5944602 * 2
def baseEnd_5944602 : Nat := 1017479375226285317012093

theorem tailTrace_5944602 : CollatzResearch.WordTrace tailWord_5944602 prefixEnd_5944602 1017479375226285317012093 := by
  unfold tailWord_5944602
  simp only [CollatzResearch.WordTrace]
  refine ⟨54204361802432421509489015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144544964806486457358637373 54204361802432421509489015)
  ·
    refine ⟨81306542703648632264233523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54204361802432421509489015 81306542703648632264233523)
    ·
      refine ⟨121959814055472948396350285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81306542703648632264233523 121959814055472948396350285)
      ·
        refine ⟨45734930270802355648631357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121959814055472948396350285 45734930270802355648631357)
        ·
          refine ⟨17150598851550883368236759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45734930270802355648631357 17150598851550883368236759)
          ·
            refine ⟨25725898277326325052355139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17150598851550883368236759 25725898277326325052355139)
            ·
              refine ⟨38588847415989487578532709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25725898277326325052355139 38588847415989487578532709)
              ·
                refine ⟨7235408890498028920974883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38588847415989487578532709 7235408890498028920974883)
                ·
                  refine ⟨10853113335747043381462325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7235408890498028920974883 10853113335747043381462325)
                  ·
                    refine ⟨1017479375226285317012093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10853113335747043381462325 1017479375226285317012093)
                    ·
                      rfl

theorem cell23_5944602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 4, 1, 5].length) (baseStart_5944602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5944602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5944602 prefixEnd_5944602 := by exact prefixLift 5944602
  have htrace : WordTrace (prefixWord ++ tailWord_5944602) baseStart_5944602 baseEnd_5944602 := by
    simpa [prefixWord, tailWord_5944602, baseEnd_5944602] using wordTrace_append hprefix tailTrace_5944602
  have hstable : (prefixWord ++ tailWord_5944602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5944602).length < 2 ^ (prefixWord ++ tailWord_5944602).sum := by decide
  have hdescent : baseEnd_5944602 < baseStart_5944602 := by decide
  rcases family_descends (prefixWord ++ tailWord_5944602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5944632 : List Nat := [2, 1, 2, 1, 3, 1, 1, 6, 2, 4]
def baseStart_5944632 : Nat := 118140960795 + 5944632 * 2 ^ 59
def prefixEnd_5944632 : Nat := 4983230072969 + 3 ^ 40 * 5944632 * 2
def baseEnd_5944632 : Nat := 1017484510032830277887047

theorem tailTrace_5944632 : CollatzResearch.WordTrace tailWord_5944632 prefixEnd_5944632 1017484510032830277887047 := by
  unfold tailWord_5944632
  simp only [CollatzResearch.WordTrace]
  refine ⟨108409270699810500580774075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144545694266414000774365433 108409270699810500580774075)
  ·
    refine ⟨162613906049715750871161113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108409270699810500580774075 162613906049715750871161113)
    ·
      refine ⟨121960429537286813153370835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162613906049715750871161113 121960429537286813153370835)
      ·
        refine ⟨182940644305930219730056253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121960429537286813153370835 182940644305930219730056253)
        ·
          refine ⟨68602741614723832398771095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182940644305930219730056253 68602741614723832398771095)
          ·
            refine ⟨102904112422085748598156643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68602741614723832398771095 102904112422085748598156643)
            ·
              refine ⟨154356168633128622897234965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102904112422085748598156643 154356168633128622897234965)
              ·
                refine ⟨7235445404677904198307889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 154356168633128622897234965 7235445404677904198307889)
                ·
                  refine ⟨5426584053508428148730917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7235445404677904198307889 5426584053508428148730917)
                  ·
                    refine ⟨1017484510032830277887047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5426584053508428148730917 1017484510032830277887047)
                    ·
                      rfl

theorem cell23_5944632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 6, 2, 4].length) (baseStart_5944632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5944632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5944632 prefixEnd_5944632 := by exact prefixLift 5944632
  have htrace : WordTrace (prefixWord ++ tailWord_5944632) baseStart_5944632 baseEnd_5944632 := by
    simpa [prefixWord, tailWord_5944632, baseEnd_5944632] using wordTrace_append hprefix tailTrace_5944632
  have hstable : (prefixWord ++ tailWord_5944632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5944632).length < 2 ^ (prefixWord ++ tailWord_5944632).sum := by decide
  have hdescent : baseEnd_5944632 < baseStart_5944632 := by decide
  rcases family_descends (prefixWord ++ tailWord_5944632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5944633 : List Nat := [1, 2, 1, 6, 3, 1, 1, 1, 3, 1, 3]
def baseStart_5944633 : Nat := 118140960795 + 5944633 * 2 ^ 59
def prefixEnd_5944633 : Nat := 4983230072969 + 3 ^ 40 * 5944633 * 2
def baseEnd_5944633 : Nat := 3052454043579145329748637

theorem tailTrace_5944633 : CollatzResearch.WordTrace tailWord_5944633 prefixEnd_5944633 3052454043579145329748637 := by
  unfold tailWord_5944633
  simp only [CollatzResearch.WordTrace]
  refine ⟨216818577872617378332334553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144545718581744918888223035 216818577872617378332334553)
  ·
    refine ⟨162613933404463033749250915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216818577872617378332334553 162613933404463033749250915)
    ·
      refine ⟨243920900106694550623876373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162613933404463033749250915 243920900106694550623876373)
      ·
        refine ⟨11433792192501307060494205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 243920900106694550623876373 11433792192501307060494205)
        ·
          refine ⟨4287672072187990147685327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11433792192501307060494205 4287672072187990147685327)
          ·
            refine ⟨6431508108281985221527991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4287672072187990147685327 6431508108281985221527991)
            ·
              refine ⟨9647262162422977832291987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6431508108281985221527991 9647262162422977832291987)
              ·
                refine ⟨14470893243634466748437981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9647262162422977832291987 14470893243634466748437981)
                ·
                  refine ⟨5426584966362925030664243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14470893243634466748437981 5426584966362925030664243)
                  ·
                    refine ⟨8139877449544387545996365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5426584966362925030664243 8139877449544387545996365)
                    ·
                      refine ⟨3052454043579145329748637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8139877449544387545996365 3052454043579145329748637)
                      ·
                        rfl

theorem cell23_5944633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_5944633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5944633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5944633 prefixEnd_5944633 := by exact prefixLift 5944633
  have htrace : WordTrace (prefixWord ++ tailWord_5944633) baseStart_5944633 baseEnd_5944633 := by
    simpa [prefixWord, tailWord_5944633, baseEnd_5944633] using wordTrace_append hprefix tailTrace_5944633
  have hstable : (prefixWord ++ tailWord_5944633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5944633).length < 2 ^ (prefixWord ++ tailWord_5944633).sum := by decide
  have hdescent : baseEnd_5944633 < baseStart_5944633 := by decide
  rcases family_descends (prefixWord ++ tailWord_5944633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5944649 : List Nat := [1, 2, 1, 1, 2, 3, 6, 1, 2, 4]
def baseStart_5944649 : Nat := 118140960795 + 5944649 * 2 ^ 59
def prefixEnd_5944649 : Nat := 4983230072969 + 3 ^ 40 * 5944649 * 2
def baseEnd_5944649 : Nat := 1017487419756539089049521

theorem tailTrace_5944649 : CollatzResearch.WordTrace tailWord_5944649 prefixEnd_5944649 1017487419756539089049521 := by
  unfold tailWord_5944649
  simp only [CollatzResearch.WordTrace]
  refine ⟨216819161440559413064917001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144546107627039608709944667 216819161440559413064917001)
  ·
    refine ⟨162614371080419559798687751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216819161440559413064917001 162614371080419559798687751)
    ·
      refine ⟨243921556620629339698031627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162614371080419559798687751 243921556620629339698031627)
      ·
        refine ⟨365882334930944009547047441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243921556620629339698031627 365882334930944009547047441)
        ·
          refine ⟨274411751198208007160285581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 365882334930944009547047441 274411751198208007160285581)
          ·
            refine ⟨102904406699328002685107093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 274411751198208007160285581 102904406699328002685107093)
            ·
              refine ⟨4823644064031000125864395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 102904406699328002685107093 4823644064031000125864395)
              ·
                refine ⟨7235466096046500188796593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4823644064031000125864395 7235466096046500188796593)
                ·
                  refine ⟨5426599572034875141597445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7235466096046500188796593 5426599572034875141597445)
                  ·
                    refine ⟨1017487419756539089049521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5426599572034875141597445 1017487419756539089049521)
                    ·
                      rfl

theorem cell23_5944649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 6, 1, 2, 4].length) (baseStart_5944649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5944649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5944649 prefixEnd_5944649 := by exact prefixLift 5944649
  have htrace : WordTrace (prefixWord ++ tailWord_5944649) baseStart_5944649 baseEnd_5944649 := by
    simpa [prefixWord, tailWord_5944649, baseEnd_5944649] using wordTrace_append hprefix tailTrace_5944649
  have hstable : (prefixWord ++ tailWord_5944649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5944649).length < 2 ^ (prefixWord ++ tailWord_5944649).sum := by decide
  have hdescent : baseEnd_5944649 < baseStart_5944649 := by decide
  rcases family_descends (prefixWord ++ tailWord_5944649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5944653 : List Nat := [1, 6, 1, 3, 1, 2, 1, 2, 1, 5]
def baseStart_5944653 : Nat := 118140960795 + 5944653 * 2 ^ 59
def prefixEnd_5944653 : Nat := 4983230072969 + 3 ^ 40 * 5944653 * 2
def baseEnd_5944653 : Nat := 1017488104397411750499515

theorem tailTrace_5944653 : CollatzResearch.WordTrace tailWord_5944653 prefixEnd_5944653 1017488104397411750499515 := by
  unfold tailWord_5944653
  simp only [CollatzResearch.WordTrace]
  refine ⟨216819307332544921748062613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144546204888363281165375075 216819307332544921748062613)
  ·
    refine ⟨10163405031213043206940435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 216819307332544921748062613 10163405031213043206940435)
    ·
      refine ⟨15245107546819564810410653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10163405031213043206940435 15245107546819564810410653)
      ·
        refine ⟨5716915330057336803903995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15245107546819564810410653 5716915330057336803903995)
        ·
          refine ⟨8575372995086005205855993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5716915330057336803903995 8575372995086005205855993)
          ·
            refine ⟨6431529746314503904391995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8575372995086005205855993 6431529746314503904391995)
            ·
              refine ⟨9647294619471755856587993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6431529746314503904391995 9647294619471755856587993)
              ·
                refine ⟨7235470964603816892440995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9647294619471755856587993 7235470964603816892440995)
                ·
                  refine ⟨10853206446905725338661493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7235470964603816892440995 10853206446905725338661493)
                  ·
                    refine ⟨1017488104397411750499515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10853206446905725338661493 1017488104397411750499515)
                    ·
                      rfl

theorem cell23_5944653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_5944653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5944653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5944653 prefixEnd_5944653 := by exact prefixLift 5944653
  have htrace : WordTrace (prefixWord ++ tailWord_5944653) baseStart_5944653 baseEnd_5944653 := by
    simpa [prefixWord, tailWord_5944653, baseEnd_5944653] using wordTrace_append hprefix tailTrace_5944653
  have hstable : (prefixWord ++ tailWord_5944653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5944653).length < 2 ^ (prefixWord ++ tailWord_5944653).sum := by decide
  have hdescent : baseEnd_5944653 < baseStart_5944653 := by decide
  rcases family_descends (prefixWord ++ tailWord_5944653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5944672 : List Nat := [2, 1, 1, 3, 4, 1, 1, 1, 3, 3, 3]
def baseStart_5944672 : Nat := 118140960795 + 5944672 * 2 ^ 59
def prefixEnd_5944672 : Nat := 4983230072969 + 3 ^ 40 * 5944672 * 2
def baseEnd_5944672 : Nat := 3052474069324670677160957

theorem tailTrace_5944672 : CollatzResearch.WordTrace tailWord_5944672 prefixEnd_5944672 3052474069324670677160957 := by
  unfold tailWord_5944672
  simp only [CollatzResearch.WordTrace]
  refine ⟨108410000159738043996502135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144546666879650725328669513 108410000159738043996502135)
  ·
    refine ⟨162615000239607065994753203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108410000159738043996502135 162615000239607065994753203)
    ·
      refine ⟨243922500359410598992129805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162615000239607065994753203 243922500359410598992129805)
      ·
        refine ⟨91470937634778974622048677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 243922500359410598992129805 91470937634778974622048677)
        ·
          refine ⟨17150800806521057741634127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91470937634778974622048677 17150800806521057741634127)
          ·
            refine ⟨25726201209781586612451191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17150800806521057741634127 25726201209781586612451191)
            ·
              refine ⟨38589301814672379918676787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25726201209781586612451191 38589301814672379918676787)
              ·
                refine ⟨57883952722008569878015181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38589301814672379918676787 57883952722008569878015181)
                ·
                  refine ⟨21706482270753213704255693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57883952722008569878015181 21706482270753213704255693)
                  ·
                    refine ⟨8139930851532455139095885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21706482270753213704255693 8139930851532455139095885)
                    ·
                      refine ⟨3052474069324670677160957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8139930851532455139095885 3052474069324670677160957)
                      ·
                        rfl

theorem cell23_5944672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 3, 3, 3].length) (baseStart_5944672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5944672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5944672 prefixEnd_5944672 := by exact prefixLift 5944672
  have htrace : WordTrace (prefixWord ++ tailWord_5944672) baseStart_5944672 baseEnd_5944672 := by
    simpa [prefixWord, tailWord_5944672, baseEnd_5944672] using wordTrace_append hprefix tailTrace_5944672
  have hstable : (prefixWord ++ tailWord_5944672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5944672).length < 2 ^ (prefixWord ++ tailWord_5944672).sum := by decide
  have hdescent : baseEnd_5944672 < baseStart_5944672 := by decide
  rcases family_descends (prefixWord ++ tailWord_5944672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5944676 : List Nat := [2, 3, 1, 1, 3, 3, 3, 1, 1, 2, 3]
def baseStart_5944676 : Nat := 118140960795 + 5944676 * 2 ^ 59
def prefixEnd_5944676 : Nat := 4983230072969 + 3 ^ 40 * 5944676 * 2
def baseEnd_5944676 : Nat := 3052476123247288661510939

theorem tailTrace_5944676 : CollatzResearch.WordTrace tailWord_5944676 prefixEnd_5944676 3052476123247288661510939 := by
  unfold tailWord_5944676
  simp only [CollatzResearch.WordTrace]
  refine ⟨108410073105730798338074941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144546764140974397784099921 108410073105730798338074941)
  ·
    refine ⟨40653777414649049376778103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108410073105730798338074941 40653777414649049376778103)
    ·
      refine ⟨60980666121973574065167155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40653777414649049376778103 60980666121973574065167155)
      ·
        refine ⟨91470999182960361097750733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60980666121973574065167155 91470999182960361097750733)
        ·
          refine ⟨34301624693610135411656525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91470999182960361097750733 34301624693610135411656525)
          ·
            refine ⟨12863109260103800779371197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34301624693610135411656525 12863109260103800779371197)
            ·
              refine ⟨4823665972538925292264199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12863109260103800779371197 4823665972538925292264199)
              ·
                refine ⟨7235498958808387938396299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4823665972538925292264199 7235498958808387938396299)
                ·
                  refine ⟨10853248438212581907594449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7235498958808387938396299 10853248438212581907594449)
                  ·
                    refine ⟨8139936328659436430695837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10853248438212581907594449 8139936328659436430695837)
                    ·
                      refine ⟨3052476123247288661510939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8139936328659436430695837 3052476123247288661510939)
                      ·
                        rfl

theorem cell23_5944676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 3, 1, 1, 2, 3].length) (baseStart_5944676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5944676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5944676 prefixEnd_5944676 := by exact prefixLift 5944676
  have htrace : WordTrace (prefixWord ++ tailWord_5944676) baseStart_5944676 baseEnd_5944676 := by
    simpa [prefixWord, tailWord_5944676, baseEnd_5944676] using wordTrace_append hprefix tailTrace_5944676
  have hstable : (prefixWord ++ tailWord_5944676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5944676).length < 2 ^ (prefixWord ++ tailWord_5944676).sum := by decide
  have hdescent : baseEnd_5944676 < baseStart_5944676 := by decide
  rcases family_descends (prefixWord ++ tailWord_5944676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5944689 : List Nat := [1, 2, 2, 2, 1, 2, 3, 4, 2, 1, 3]
def baseStart_5944689 : Nat := 118140960795 + 5944689 * 2 ^ 59
def prefixEnd_5944689 : Nat := 4983230072969 + 3 ^ 40 * 5944689 * 2
def baseEnd_5944689 : Nat := 3052482798495797110648379

theorem tailTrace_5944689 : CollatzResearch.WordTrace tailWord_5944689 prefixEnd_5944689 3052482798495797110648379 := by
  unfold tailWord_5944689
  simp only [CollatzResearch.WordTrace]
  refine ⟨216820620360414499896373121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144547080240276333264248747 216820620360414499896373121)
  ·
    refine ⟨162615465270310874922279841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216820620360414499896373121 162615465270310874922279841)
    ·
      refine ⟨121961598952733156191709881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162615465270310874922279841 121961598952733156191709881)
      ·
        refine ⟨91471199214549867143782411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121961598952733156191709881 91471199214549867143782411)
        ·
          refine ⟨137206798821824800715673617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91471199214549867143782411 137206798821824800715673617)
          ·
            refine ⟨102905099116368600536755213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137206798821824800715673617 102905099116368600536755213)
            ·
              refine ⟨38589412168638225201283205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102905099116368600536755213 38589412168638225201283205)
              ·
                refine ⟨7235514781619667225240601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38589412168638225201283205 7235514781619667225240601)
                ·
                  refine ⟨5426636086214750418930451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7235514781619667225240601 5426636086214750418930451)
                  ·
                    refine ⟨8139954129322125628395677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5426636086214750418930451 8139954129322125628395677)
                    ·
                      refine ⟨3052482798495797110648379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8139954129322125628395677 3052482798495797110648379)
                      ·
                        rfl

theorem cell23_5944689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 4, 2, 1, 3].length) (baseStart_5944689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5944689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5944689 prefixEnd_5944689 := by exact prefixLift 5944689
  have htrace : WordTrace (prefixWord ++ tailWord_5944689) baseStart_5944689 baseEnd_5944689 := by
    simpa [prefixWord, tailWord_5944689, baseEnd_5944689] using wordTrace_append hprefix tailTrace_5944689
  have hstable : (prefixWord ++ tailWord_5944689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5944689).length < 2 ^ (prefixWord ++ tailWord_5944689).sum := by decide
  have hdescent : baseEnd_5944689 < baseStart_5944689 := by decide
  rcases family_descends (prefixWord ++ tailWord_5944689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5944695 : List Nat := [1, 1, 3, 1, 1, 2, 3, 1, 1, 5, 4]
def baseStart_5944695 : Nat := 118140960795 + 5944695 * 2 ^ 59
def prefixEnd_5944695 : Nat := 4983230072969 + 3 ^ 40 * 5944695 * 2
def baseEnd_5944695 : Nat := 3052485879379724087173351

theorem tailTrace_5944695 : CollatzResearch.WordTrace tailWord_5944695 prefixEnd_5944695 3052485879379724087173351 := by
  unfold tailWord_5944695
  simp only [CollatzResearch.WordTrace]
  refine ⟨216820839198392762921091539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144547226132261841947394359 216820839198392762921091539)
  ·
    refine ⟨325231258797589144381637309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216820839198392762921091539 325231258797589144381637309)
    ·
      refine ⟨121961722049095929143113991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 325231258797589144381637309 121961722049095929143113991)
      ·
        refine ⟨182942583073643893714670987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121961722049095929143113991 182942583073643893714670987)
        ·
          refine ⟨274413874610465840572006481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182942583073643893714670987 274413874610465840572006481)
          ·
            refine ⟨205810405957849380429004861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 274413874610465840572006481 205810405957849380429004861)
            ·
              refine ⟨77178902234193517660876823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 205810405957849380429004861 77178902234193517660876823)
              ·
                refine ⟨115768353351290276491315235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77178902234193517660876823 115768353351290276491315235)
                ·
                  refine ⟨173652530026935414736972853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115768353351290276491315235 173652530026935414736972853)
                  ·
                    refine ⟨16279924690025195131591205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 173652530026935414736972853 16279924690025195131591205)
                    ·
                      refine ⟨3052485879379724087173351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16279924690025195131591205 3052485879379724087173351)
                      ·
                        rfl

theorem cell23_5944695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 5, 4].length) (baseStart_5944695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5944695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5944695 prefixEnd_5944695 := by exact prefixLift 5944695
  have htrace : WordTrace (prefixWord ++ tailWord_5944695) baseStart_5944695 baseEnd_5944695 := by
    simpa [prefixWord, tailWord_5944695, baseEnd_5944695] using wordTrace_append hprefix tailTrace_5944695
  have hstable : (prefixWord ++ tailWord_5944695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5944695).length < 2 ^ (prefixWord ++ tailWord_5944695).sum := by decide
  have hdescent : baseEnd_5944695 < baseStart_5944695 := by decide
  rcases family_descends (prefixWord ++ tailWord_5944695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5944706 : List Nat := [3, 4, 2, 1, 1, 1, 1, 3, 1, 3, 3]
def baseStart_5944706 : Nat := 118140960795 + 5944706 * 2 ^ 59
def prefixEnd_5944706 : Nat := 4983230072969 + 3 ^ 40 * 5944706 * 2
def baseEnd_5944706 : Nat := 3052491527666923544135801

theorem tailTrace_5944706 : CollatzResearch.WordTrace tailWord_5944706 prefixEnd_5944706 3052491527666923544135801 := by
  unfold tailWord_5944706
  simp only [CollatzResearch.WordTrace]
  refine ⟨54205310100338227949935493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144547493600901941199827981 54205310100338227949935493)
  ·
    refine ⟨10163495643813417740612905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54205310100338227949935493 10163495643813417740612905)
    ·
      refine ⟨7622621732860063305459679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10163495643813417740612905 7622621732860063305459679)
      ·
        refine ⟨11433932599290094958189519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7622621732860063305459679 11433932599290094958189519)
        ·
          refine ⟨17150898898935142437284279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11433932599290094958189519 17150898898935142437284279)
          ·
            refine ⟨25726348348402713655926419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17150898898935142437284279 25726348348402713655926419)
            ·
              refine ⟨38589522522604070483889629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25726348348402713655926419 38589522522604070483889629)
              ·
                refine ⟨14471070945976526431458611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38589522522604070483889629 14471070945976526431458611)
                ·
                  refine ⟨21706606418964789647187917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14471070945976526431458611 21706606418964789647187917)
                  ·
                    refine ⟨8139977407111796117695469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21706606418964789647187917 8139977407111796117695469)
                    ·
                      refine ⟨3052491527666923544135801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8139977407111796117695469 3052491527666923544135801)
                      ·
                        rfl

theorem cell23_5944706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_5944706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5944706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5944706 prefixEnd_5944706 := by exact prefixLift 5944706
  have htrace : WordTrace (prefixWord ++ tailWord_5944706) baseStart_5944706 baseEnd_5944706 := by
    simpa [prefixWord, tailWord_5944706, baseEnd_5944706] using wordTrace_append hprefix tailTrace_5944706
  have hstable : (prefixWord ++ tailWord_5944706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5944706).length < 2 ^ (prefixWord ++ tailWord_5944706).sum := by decide
  have hdescent : baseEnd_5944706 < baseStart_5944706 := by decide
  rcases family_descends (prefixWord ++ tailWord_5944706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5944729 : List Nat := [1, 2, 1, 2, 1, 5, 2, 2, 1, 4, 2]
def baseStart_5944729 : Nat := 118140960795 + 5944729 * 2 ^ 59
def prefixEnd_5944729 : Nat := 4983230072969 + 3 ^ 40 * 5944729 * 2
def baseEnd_5944729 : Nat := 3052503337721976954148195

theorem tailTrace_5944729 : CollatzResearch.WordTrace tailWord_5944729 prefixEnd_5944729 3052503337721976954148195 := by
  unfold tailWord_5944729
  simp only [CollatzResearch.WordTrace]
  refine ⟨216822079280269586727829241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144548052853513057818552827 216822079280269586727829241)
  ·
    refine ⟨162616559460202190045871931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216822079280269586727829241 162616559460202190045871931)
    ·
      refine ⟨243924839190303285068807897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162616559460202190045871931 243924839190303285068807897)
      ·
        refine ⟨182943629392727463801605923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243924839190303285068807897 182943629392727463801605923)
        ·
          refine ⟨274415444089091195702408885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182943629392727463801605923 274415444089091195702408885)
          ·
            refine ⟨25726447883352299597100833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 274415444089091195702408885 25726447883352299597100833)
            ·
              refine ⟨19294835912514224697825625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25726447883352299597100833 19294835912514224697825625)
              ·
                refine ⟨14471126934385668523369219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19294835912514224697825625 14471126934385668523369219)
                ·
                  refine ⟨21706690401578502785053829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14471126934385668523369219 21706690401578502785053829)
                  ·
                    refine ⟨4070004450295969272197593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21706690401578502785053829 4070004450295969272197593)
                    ·
                      refine ⟨3052503337721976954148195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4070004450295969272197593 3052503337721976954148195)
                      ·
                        rfl

theorem cell23_5944729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 2, 1, 4, 2].length) (baseStart_5944729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5944729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5944729 prefixEnd_5944729 := by exact prefixLift 5944729
  have htrace : WordTrace (prefixWord ++ tailWord_5944729) baseStart_5944729 baseEnd_5944729 := by
    simpa [prefixWord, tailWord_5944729, baseEnd_5944729] using wordTrace_append hprefix tailTrace_5944729
  have hstable : (prefixWord ++ tailWord_5944729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5944729).length < 2 ^ (prefixWord ++ tailWord_5944729).sum := by decide
  have hdescent : baseEnd_5944729 < baseStart_5944729 := by decide
  rcases family_descends (prefixWord ++ tailWord_5944729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5944733 : List Nat := [1, 4, 2, 1, 3, 1, 4, 1, 1, 3, 2]
def baseStart_5944733 : Nat := 118140960795 + 5944733 * 2 ^ 59
def prefixEnd_5944733 : Nat := 4983230072969 + 3 ^ 40 * 5944733 * 2
def baseEnd_5944733 : Nat := 3052505391644594938498177

theorem tailTrace_5944733 : CollatzResearch.WordTrace tailWord_5944733 prefixEnd_5944733 3052505391644594938498177 := by
  unfold tailWord_5944733
  simp only [CollatzResearch.WordTrace]
  refine ⟨216822225172255095410974853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144548150114836730273983235 216822225172255095410974853)
  ·
    refine ⟨40654167219797830389557785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 216822225172255095410974853 40654167219797830389557785)
    ·
      refine ⟨30490625414848372792168339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40654167219797830389557785 30490625414848372792168339)
      ·
        refine ⟨45735938122272559188252509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30490625414848372792168339 45735938122272559188252509)
        ·
          refine ⟨17150976795852209695594691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45735938122272559188252509 17150976795852209695594691)
          ·
            refine ⟨25726465193778314543392037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17150976795852209695594691 25726465193778314543392037)
            ·
              refine ⟨4823712223833433976886007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25726465193778314543392037 4823712223833433976886007)
              ·
                refine ⟨7235568335750150965329011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4823712223833433976886007 7235568335750150965329011)
                ·
                  refine ⟨10853352503625226447993517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7235568335750150965329011 10853352503625226447993517)
                  ·
                    refine ⟨4070007188859459917997569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10853352503625226447993517 4070007188859459917997569)
                    ·
                      refine ⟨3052505391644594938498177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4070007188859459917997569 3052505391644594938498177)
                      ·
                        rfl

theorem cell23_5944733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 4, 1, 1, 3, 2].length) (baseStart_5944733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5944733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5944733 prefixEnd_5944733 := by exact prefixLift 5944733
  have htrace : WordTrace (prefixWord ++ tailWord_5944733) baseStart_5944733 baseEnd_5944733 := by
    simpa [prefixWord, tailWord_5944733, baseEnd_5944733] using wordTrace_append hprefix tailTrace_5944733
  have hstable : (prefixWord ++ tailWord_5944733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5944733).length < 2 ^ (prefixWord ++ tailWord_5944733).sum := by decide
  have hdescent : baseEnd_5944733 < baseStart_5944733 := by decide
  rcases family_descends (prefixWord ++ tailWord_5944733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5944782 : List Nat := [4, 1, 1, 1, 2, 1, 4, 1, 1, 7]
def baseStart_5944782 : Nat := 118140960795 + 5944782 * 2 ^ 59
def prefixEnd_5944782 : Nat := 4983230072969 + 3 ^ 40 * 5944782 * 2
def baseEnd_5944782 : Nat := 1017510184065555082261817

theorem tailTrace_5944782 : CollatzResearch.WordTrace tailWord_5944782 prefixEnd_5944782 1017510184065555082261817 := by
  unfold tailWord_5944782
  simp only [CollatzResearch.WordTrace]
  refine ⟨27103001543634697097438575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144549341566051717853005733 27103001543634697097438575)
  ·
    refine ⟨40654502315452045646157863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27103001543634697097438575 40654502315452045646157863)
    ·
      refine ⟨60981753473178068469236795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40654502315452045646157863 60981753473178068469236795)
      ·
        refine ⟨91472630209767102703855193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60981753473178068469236795 91472630209767102703855193)
        ·
          refine ⟨68604472657325327027891395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91472630209767102703855193 68604472657325327027891395)
          ·
            refine ⟨102906708985987990541837093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68604472657325327027891395 102906708985987990541837093)
            ·
              refine ⟨19295007934872748226594455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102906708985987990541837093 19295007934872748226594455)
              ·
                refine ⟨28942511902309122339891683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19295007934872748226594455 28942511902309122339891683)
                ·
                  refine ⟨43413767853463683509837525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28942511902309122339891683 43413767853463683509837525)
                  ·
                    refine ⟨1017510184065555082261817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43413767853463683509837525 1017510184065555082261817)
                    ·
                      rfl

theorem cell23_5944782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 1, 7].length) (baseStart_5944782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5944782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5944782 prefixEnd_5944782 := by exact prefixLift 5944782
  have htrace : WordTrace (prefixWord ++ tailWord_5944782) baseStart_5944782 baseEnd_5944782 := by
    simpa [prefixWord, tailWord_5944782, baseEnd_5944782] using wordTrace_append hprefix tailTrace_5944782
  have hstable : (prefixWord ++ tailWord_5944782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5944782).length < 2 ^ (prefixWord ++ tailWord_5944782).sum := by decide
  have hdescent : baseEnd_5944782 < baseStart_5944782 := by decide
  rcases family_descends (prefixWord ++ tailWord_5944782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5944863 : List Nat := [1, 1, 2, 4, 1, 1, 6, 2, 1, 4]
def baseStart_5944863 : Nat := 118140960795 + 5944863 * 2 ^ 59
def prefixEnd_5944863 : Nat := 4983230072969 + 3 ^ 40 * 5944863 * 2
def baseEnd_5944863 : Nat := 1017524048043226476624193

theorem tailTrace_5944863 : CollatzResearch.WordTrace tailWord_5944863 prefixEnd_5944863 1017524048043226476624193 := by
  unfold tailWord_5944863
  simp only [CollatzResearch.WordTrace]
  refine ⟨216826966661784127613207243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144551311107856085075471495 216826966661784127613207243)
  ·
    refine ⟨325240449992676191419810865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216826966661784127613207243 325240449992676191419810865)
    ·
      refine ⟨243930337494507143564858149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 325240449992676191419810865 243930337494507143564858149)
      ·
        refine ⟨45736938280220089418410903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 243930337494507143564858149 45736938280220089418410903)
        ·
          refine ⟨68605407420330134127616355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45736938280220089418410903 68605407420330134127616355)
          ·
            refine ⟨102908111130495201191424533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68605407420330134127616355 102908111130495201191424533)
            ·
              refine ⟨4823817709241962555848025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 102908111130495201191424533 4823817709241962555848025)
              ·
                refine ⟨3617863281931471916886019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4823817709241962555848025 3617863281931471916886019)
                ·
                  refine ⟨5426794922897207875329029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3617863281931471916886019 5426794922897207875329029)
                  ·
                    refine ⟨1017524048043226476624193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5426794922897207875329029 1017524048043226476624193)
                    ·
                      rfl

theorem cell23_5944863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 6, 2, 1, 4].length) (baseStart_5944863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5944863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5944863 prefixEnd_5944863 := by exact prefixLift 5944863
  have htrace : WordTrace (prefixWord ++ tailWord_5944863) baseStart_5944863 baseEnd_5944863 := by
    simpa [prefixWord, tailWord_5944863, baseEnd_5944863] using wordTrace_append hprefix tailTrace_5944863
  have hstable : (prefixWord ++ tailWord_5944863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5944863).length < 2 ^ (prefixWord ++ tailWord_5944863).sum := by decide
  have hdescent : baseEnd_5944863 < baseStart_5944863 := by decide
  rcases family_descends (prefixWord ++ tailWord_5944863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5944882 : List Nat := [3, 2, 1, 1, 2, 1, 1, 1, 1, 3, 7]
def baseStart_5944882 : Nat := 118140960795 + 5944882 * 2 ^ 59
def prefixEnd_5944882 : Nat := 4983230072969 + 3 ^ 40 * 5944882 * 2
def baseEnd_5944882 : Nat := 3052581900262114855534991

theorem tailTrace_5944882 : CollatzResearch.WordTrace tailWord_5944882 prefixEnd_5944882 3052581900262114855534991 := by
  unfold tailWord_5944882
  simp only [CollatzResearch.WordTrace]
  refine ⟨54206914912178823464537225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144551773099143529238765933 54206914912178823464537225)
  ·
    refine ⟨40655186184134117598402919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54206914912178823464537225 40655186184134117598402919)
    ·
      refine ⟨60982779276201176397604379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40655186184134117598402919 60982779276201176397604379)
      ·
        refine ⟨91474168914301764596406569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60982779276201176397604379 91474168914301764596406569)
        ·
          refine ⟨68605626685726323447304927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91474168914301764596406569 68605626685726323447304927)
          ·
            refine ⟨102908440028589485170957391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68605626685726323447304927 102908440028589485170957391)
            ·
              refine ⟨154362660042884227756436087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102908440028589485170957391 154362660042884227756436087)
              ·
                refine ⟨231543990064326341634654131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154362660042884227756436087 231543990064326341634654131)
                ·
                  refine ⟨347315985096489512451981197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 231543990064326341634654131 347315985096489512451981197)
                  ·
                    refine ⟨130243494411183567169492949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 347315985096489512451981197 130243494411183567169492949)
                    ·
                      refine ⟨3052581900262114855534991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 130243494411183567169492949 3052581900262114855534991)
                      ·
                        rfl

theorem cell23_5944882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_5944882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5944882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5944882 prefixEnd_5944882 := by exact prefixLift 5944882
  have htrace : WordTrace (prefixWord ++ tailWord_5944882) baseStart_5944882 baseEnd_5944882 := by
    simpa [prefixWord, tailWord_5944882, baseEnd_5944882] using wordTrace_append hprefix tailTrace_5944882
  have hstable : (prefixWord ++ tailWord_5944882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5944882).length < 2 ^ (prefixWord ++ tailWord_5944882).sum := by decide
  have hdescent : baseEnd_5944882 < baseStart_5944882 := by decide
  rcases family_descends (prefixWord ++ tailWord_5944882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5944889 : List Nat := [1, 2, 1, 5, 1, 2, 2, 1, 3, 5]
def baseStart_5944889 : Nat := 118140960795 + 5944889 * 2 ^ 59
def prefixEnd_5944889 : Nat := 4983230072969 + 3 ^ 40 * 5944889 * 2
def baseEnd_5944889 : Nat := 1017528498208898776049153

theorem tailTrace_5944889 : CollatzResearch.WordTrace tailWord_5944889 prefixEnd_5944889 1017528498208898776049153 := by
  unfold tailWord_5944889
  simp only [CollatzResearch.WordTrace]
  refine ⟨216827914959689934053653721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144551943306459956035769147 216827914959689934053653721)
  ·
    refine ⟨162620936219767450540240291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216827914959689934053653721 162620936219767450540240291)
    ·
      refine ⟨243931404329651175810360437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162620936219767450540240291 243931404329651175810360437)
      ·
        refine ⟨22868569155904797732221291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 243931404329651175810360437 22868569155904797732221291)
        ·
          refine ⟨34302853733857196598331937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22868569155904797732221291 34302853733857196598331937)
          ·
            refine ⟨25727140300392897448748953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34302853733857196598331937 25727140300392897448748953)
            ·
              refine ⟨19295355225294673086561715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25727140300392897448748953 19295355225294673086561715)
              ·
                refine ⟨28943032837942009629842573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19295355225294673086561715 28943032837942009629842573)
                ·
                  refine ⟨10853637314228253611190965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28943032837942009629842573 10853637314228253611190965)
                  ·
                    refine ⟨1017528498208898776049153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10853637314228253611190965 1017528498208898776049153)
                    ·
                      rfl

theorem cell23_5944889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 3, 5].length) (baseStart_5944889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5944889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5944889 prefixEnd_5944889 := by exact prefixLift 5944889
  have htrace : WordTrace (prefixWord ++ tailWord_5944889) baseStart_5944889 baseEnd_5944889 := by
    simpa [prefixWord, tailWord_5944889, baseEnd_5944889] using wordTrace_append hprefix tailTrace_5944889
  have hstable : (prefixWord ++ tailWord_5944889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5944889).length < 2 ^ (prefixWord ++ tailWord_5944889).sum := by decide
  have hdescent : baseEnd_5944889 < baseStart_5944889 := by decide
  rcases family_descends (prefixWord ++ tailWord_5944889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5944929 : List Nat := [1, 2, 3, 1, 1, 3, 3, 2, 1, 1, 5]
def baseStart_5944929 : Nat := 118140960795 + 5944929 * 2 ^ 59
def prefixEnd_5944929 : Nat := 4983230072969 + 3 ^ 40 * 5944929 * 2
def baseEnd_5944929 : Nat := 3052606033852876171647275

theorem tailTrace_5944929 : CollatzResearch.WordTrace tailWord_5944929 prefixEnd_5944929 3052606033852876171647275 := by
  unfold tailWord_5944929
  simp only [CollatzResearch.WordTrace]
  refine ⟨216829373879545020885109841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144552915919696680590073227 216829373879545020885109841)
  ·
    refine ⟨162622030409658765663832381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216829373879545020885109841 162622030409658765663832381)
    ·
      refine ⟨60983261403622037123937143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162622030409658765663832381 60983261403622037123937143)
      ·
        refine ⟨91474892105433055685905715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60983261403622037123937143 91474892105433055685905715)
        ·
          refine ⟨137212338158149583528858573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91474892105433055685905715 137212338158149583528858573)
          ·
            refine ⟨51454626809306093823321965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137212338158149583528858573 51454626809306093823321965)
            ·
              refine ⟨19295485053489785183745737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51454626809306093823321965 19295485053489785183745737)
              ·
                refine ⟨14471613790117338887809303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19295485053489785183745737 14471613790117338887809303)
                ·
                  refine ⟨21707420685176008331713955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14471613790117338887809303 21707420685176008331713955)
                  ·
                    refine ⟨32561131027764012497570933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21707420685176008331713955 32561131027764012497570933)
                    ·
                      refine ⟨3052606033852876171647275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32561131027764012497570933 3052606033852876171647275)
                      ·
                        rfl

theorem cell23_5944929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 2, 1, 1, 5].length) (baseStart_5944929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5944929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5944929 prefixEnd_5944929 := by exact prefixLift 5944929
  have htrace : WordTrace (prefixWord ++ tailWord_5944929) baseStart_5944929 baseEnd_5944929 := by
    simpa [prefixWord, tailWord_5944929, baseEnd_5944929] using wordTrace_append hprefix tailTrace_5944929
  have hstable : (prefixWord ++ tailWord_5944929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5944929).length < 2 ^ (prefixWord ++ tailWord_5944929).sum := by decide
  have hdescent : baseEnd_5944929 < baseStart_5944929 := by decide
  rcases family_descends (prefixWord ++ tailWord_5944929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5944936 : List Nat := [2, 1, 4, 3, 1, 1, 3, 1, 1, 6]
def baseStart_5944936 : Nat := 118140960795 + 5944936 * 2 ^ 59
def prefixEnd_5944936 : Nat := 4983230072969 + 3 ^ 40 * 5944936 * 2
def baseEnd_5944936 : Nat := 1017536542739152548086581

theorem tailTrace_5944936 : CollatzResearch.WordTrace tailWord_5944936 prefixEnd_5944936 1017536542739152548086581 := by
  unfold tailWord_5944936
  simp only [CollatzResearch.WordTrace]
  refine ⟨108414814595259830540307331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144553086127013107387076441 108414814595259830540307331)
  ·
    refine ⟨162622221892889745810460997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108414814595259830540307331 162622221892889745810460997)
    ·
      refine ⟨30491666604916827339461437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 162622221892889745810460997 30491666604916827339461437)
      ·
        refine ⟨11434374976843810252298039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30491666604916827339461437 11434374976843810252298039)
        ·
          refine ⟨17151562465265715378447059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11434374976843810252298039 17151562465265715378447059)
          ·
            refine ⟨25727343697898573067670589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17151562465265715378447059 25727343697898573067670589)
            ·
              refine ⟨9647753886711964900376471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25727343697898573067670589 9647753886711964900376471)
              ·
                refine ⟨14471630830067947350564707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9647753886711964900376471 14471630830067947350564707)
                ·
                  refine ⟨21707446245101921025847061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14471630830067947350564707 21707446245101921025847061)
                  ·
                    refine ⟨1017536542739152548086581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21707446245101921025847061 1017536542739152548086581)
                    ·
                      rfl

theorem cell23_5944936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 1, 1, 6].length) (baseStart_5944936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5944936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5944936 prefixEnd_5944936 := by exact prefixLift 5944936
  have htrace : WordTrace (prefixWord ++ tailWord_5944936) baseStart_5944936 baseEnd_5944936 := by
    simpa [prefixWord, tailWord_5944936, baseEnd_5944936] using wordTrace_append hprefix tailTrace_5944936
  have hstable : (prefixWord ++ tailWord_5944936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5944936).length < 2 ^ (prefixWord ++ tailWord_5944936).sum := by decide
  have hdescent : baseEnd_5944936 < baseStart_5944936 := by decide
  rcases family_descends (prefixWord ++ tailWord_5944936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5945019 : List Nat := [1, 1, 1, 1, 1, 2, 3, 2, 4, 4, 3]
def baseStart_5945019 : Nat := 118140960795 + 5945019 * 2 ^ 59
def prefixEnd_5945019 : Nat := 4983230072969 + 3 ^ 40 * 5945019 * 2
def baseEnd_5945019 : Nat := 3052652247111780819521861

theorem tailTrace_5945019 : CollatzResearch.WordTrace tailWord_5945019 prefixEnd_5945019 3052652247111780819521861 := by
  unfold tailWord_5945019
  simp only [CollatzResearch.WordTrace]
  refine ⟨216832656449218966255886111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144555104299479310837257407 216832656449218966255886111)
  ·
    refine ⟨325248984673828449383829167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216832656449218966255886111 325248984673828449383829167)
    ·
      refine ⟨487873477010742674075743751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325248984673828449383829167 487873477010742674075743751)
      ·
        refine ⟨731810215516114011113615627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 487873477010742674075743751 731810215516114011113615627)
        ·
          refine ⟨1097715323274171016670423441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 731810215516114011113615627 1097715323274171016670423441)
          ·
            refine ⟨823286492455628262502817581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1097715323274171016670423441 823286492455628262502817581)
            ·
              refine ⟨308732434670860598438556593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 823286492455628262502817581 308732434670860598438556593)
              ·
                refine ⟨231549326003145448828917445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 308732434670860598438556593 231549326003145448828917445)
                ·
                  refine ⟨43415498625589771655422021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 231549326003145448828917445 43415498625589771655422021)
                  ·
                    refine ⟨8140405992298082185391629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43415498625589771655422021 8140405992298082185391629)
                    ·
                      refine ⟨3052652247111780819521861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8140405992298082185391629 3052652247111780819521861)
                      ·
                        rfl

theorem cell23_5945019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 4, 3].length) (baseStart_5945019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5945019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5945019 prefixEnd_5945019 := by exact prefixLift 5945019
  have htrace : WordTrace (prefixWord ++ tailWord_5945019) baseStart_5945019 baseEnd_5945019 := by
    simpa [prefixWord, tailWord_5945019, baseEnd_5945019] using wordTrace_append hprefix tailTrace_5945019
  have hstable : (prefixWord ++ tailWord_5945019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5945019).length < 2 ^ (prefixWord ++ tailWord_5945019).sum := by decide
  have hdescent : baseEnd_5945019 < baseStart_5945019 := by decide
  rcases family_descends (prefixWord ++ tailWord_5945019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5945029 : List Nat := [1, 3, 1, 1, 1, 1, 2, 3, 4, 2, 4]
def baseStart_5945029 : Nat := 118140960795 + 5945029 * 2 ^ 59
def prefixEnd_5945029 : Nat := 4983230072969 + 3 ^ 40 * 5945029 * 2
def baseEnd_5945029 : Nat := 3052657381918325780396815

theorem tailTrace_5945029 : CollatzResearch.WordTrace tailWord_5945029 prefixEnd_5945029 3052657381918325780396815 := by
  unfold tailWord_5945029
  simp only [CollatzResearch.WordTrace]
  refine ⟨216833021179182737963750141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144555347452788491975833427 216833021179182737963750141)
  ·
    refine ⟨81312382942193526736406303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216833021179182737963750141 81312382942193526736406303)
    ·
      refine ⟨121968574413290290104609455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81312382942193526736406303 121968574413290290104609455)
      ·
        refine ⟨182952861619935435156914183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121968574413290290104609455 182952861619935435156914183)
        ·
          refine ⟨274429292429903152735371275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182952861619935435156914183 274429292429903152735371275)
          ·
            refine ⟨411643938644854729103056913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274429292429903152735371275 411643938644854729103056913)
            ·
              refine ⟨308732953983641046827292685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 411643938644854729103056913 308732953983641046827292685)
              ·
                refine ⟨115774857743865392560234757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 308732953983641046827292685 115774857743865392560234757)
                ·
                  refine ⟨21707785826974761105044017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 115774857743865392560234757 21707785826974761105044017)
                  ·
                    refine ⟨16280839370231070828783013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21707785826974761105044017 16280839370231070828783013)
                    ·
                      refine ⟨3052657381918325780396815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16280839370231070828783013 3052657381918325780396815)
                      ·
                        rfl

theorem cell23_5945029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 4, 2, 4].length) (baseStart_5945029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5945029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5945029 prefixEnd_5945029 := by exact prefixLift 5945029
  have htrace : WordTrace (prefixWord ++ tailWord_5945029) baseStart_5945029 baseEnd_5945029 := by
    simpa [prefixWord, tailWord_5945029, baseEnd_5945029] using wordTrace_append hprefix tailTrace_5945029
  have hstable : (prefixWord ++ tailWord_5945029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5945029).length < 2 ^ (prefixWord ++ tailWord_5945029).sum := by decide
  have hdescent : baseEnd_5945029 < baseStart_5945029 := by decide
  rcases family_descends (prefixWord ++ tailWord_5945029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5945050 : List Nat := [3, 1, 1, 2, 2, 3, 2, 3, 2, 2, 2]
def baseStart_5945050 : Nat := 118140960795 + 5945050 * 2 ^ 59
def prefixEnd_5945050 : Nat := 4983230072969 + 3 ^ 40 * 5945050 * 2
def baseEnd_5945050 : Nat := 3052668165012070198234219

theorem tailTrace_5945050 : CollatzResearch.WordTrace tailWord_5945050 prefixEnd_5945050 3052668165012070198234219 := by
  unfold tailWord_5945050
  simp only [CollatzResearch.WordTrace]
  refine ⟨54208446778026664637566151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144555858074737772366843069 54208446778026664637566151)
  ·
    refine ⟨81312670167039996956349227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54208446778026664637566151 81312670167039996956349227)
    ·
      refine ⟨121969005250559995434523841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81312670167039996956349227 121969005250559995434523841)
      ·
        refine ⟨91476753937919996575892881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121969005250559995434523841 91476753937919996575892881)
        ·
          refine ⟨68607565453439997431919661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91476753937919996575892881 68607565453439997431919661)
          ·
            refine ⟨25727837045039999036969873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68607565453439997431919661 25727837045039999036969873)
            ·
              refine ⟨19295877783779999277727405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25727837045039999036969873 19295877783779999277727405)
              ·
                refine ⟨7235954168917499729147777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19295877783779999277727405 7235954168917499729147777)
                ·
                  refine ⟨5426965626688124796860833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7235954168917499729147777 5426965626688124796860833)
                  ·
                    refine ⟨4070224220016093597645625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5426965626688124796860833 4070224220016093597645625)
                    ·
                      refine ⟨3052668165012070198234219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4070224220016093597645625 3052668165012070198234219)
                      ·
                        rfl

theorem cell23_5945050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 3, 2, 2, 2].length) (baseStart_5945050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5945050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5945050 prefixEnd_5945050 := by exact prefixLift 5945050
  have htrace : WordTrace (prefixWord ++ tailWord_5945050) baseStart_5945050 baseEnd_5945050 := by
    simpa [prefixWord, tailWord_5945050, baseEnd_5945050] using wordTrace_append hprefix tailTrace_5945050
  have hstable : (prefixWord ++ tailWord_5945050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5945050).length < 2 ^ (prefixWord ++ tailWord_5945050).sum := by decide
  have hdescent : baseEnd_5945050 < baseStart_5945050 := by decide
  rcases family_descends (prefixWord ++ tailWord_5945050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5945073 : List Nat := [1, 2, 2, 2, 2, 4, 2, 3, 5]
def baseStart_5945073 : Nat := 118140960795 + 5945073 * 2 ^ 59
def prefixEnd_5945073 : Nat := 4983230072969 + 3 ^ 40 * 5945073 * 2
def baseEnd_5945073 : Nat := 339186663896347067582957

theorem tailTrace_5945073 : CollatzResearch.WordTrace tailWord_5945073 prefixEnd_5945073 339186663896347067582957 := by
  unfold tailWord_5945073
  simp only [CollatzResearch.WordTrace]
  refine ⟨216834625991023333478351873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144556417327348888985567915 216834625991023333478351873)
  ·
    refine ⟨162625969493267500108763905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216834625991023333478351873 162625969493267500108763905)
    ·
      refine ⟨121969477119950625081572929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162625969493267500108763905 121969477119950625081572929)
      ·
        refine ⟨91477107839962968811179697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121969477119950625081572929 91477107839962968811179697)
        ·
          refine ⟨68607830879972226608384773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91477107839962968811179697 68607830879972226608384773)
          ·
            refine ⟨12863968289994792489072145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68607830879972226608384773 12863968289994792489072145)
            ·
              refine ⟨9647976217496094366804109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12863968289994792489072145 9647976217496094366804109)
              ·
                refine ⟨3617991081561035387551541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9647976217496094366804109 3617991081561035387551541)
                ·
                  refine ⟨339186663896347067582957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3617991081561035387551541 339186663896347067582957)
                  ·
                    rfl

theorem cell23_5945073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 3, 5].length) (baseStart_5945073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5945073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5945073 prefixEnd_5945073 := by exact prefixLift 5945073
  have htrace : WordTrace (prefixWord ++ tailWord_5945073) baseStart_5945073 baseEnd_5945073 := by
    simpa [prefixWord, tailWord_5945073, baseEnd_5945073] using wordTrace_append hprefix tailTrace_5945073
  have hstable : (prefixWord ++ tailWord_5945073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5945073).length < 2 ^ (prefixWord ++ tailWord_5945073).sum := by decide
  have hdescent : baseEnd_5945073 < baseStart_5945073 := by decide
  rcases family_descends (prefixWord ++ tailWord_5945073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5945079 : List Nat := [1, 1, 3, 1, 1, 1, 4, 1, 3, 2, 5]
def baseStart_5945079 : Nat := 118140960795 + 5945079 * 2 ^ 59
def prefixEnd_5945079 : Nat := 4983230072969 + 3 ^ 40 * 5945079 * 2
def baseEnd_5945079 : Nat := 3052683055951050584771585

theorem tailTrace_5945079 : CollatzResearch.WordTrace tailWord_5945079 prefixEnd_5945079 3052683055951050584771585 := by
  unfold tailWord_5945079
  simp only [CollatzResearch.WordTrace]
  refine ⟨216834844829001596503070291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144556563219334397668713527 216834844829001596503070291)
  ·
    refine ⟨325252267243502394754605437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216834844829001596503070291 325252267243502394754605437)
    ·
      refine ⟨121969600216313398032977039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 325252267243502394754605437 121969600216313398032977039)
      ·
        refine ⟨182954400324470097049465559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121969600216313398032977039 182954400324470097049465559)
        ·
          refine ⟨274431600486705145574198339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182954400324470097049465559 274431600486705145574198339)
          ·
            refine ⟨411647400730057718361297509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274431600486705145574198339 411647400730057718361297509)
            ·
              refine ⟨77183887636885822192743283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 411647400730057718361297509 77183887636885822192743283)
              ·
                refine ⟨115775831455328733289114925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77183887636885822192743283 115775831455328733289114925)
                ·
                  refine ⟨43415936795748274983418097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 115775831455328733289114925 43415936795748274983418097)
                  ·
                    refine ⟨32561952596811206237563573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43415936795748274983418097 32561952596811206237563573)
                    ·
                      refine ⟨3052683055951050584771585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32561952596811206237563573 3052683055951050584771585)
                      ·
                        rfl

theorem cell23_5945079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 2, 5].length) (baseStart_5945079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5945079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5945079 prefixEnd_5945079 := by exact prefixLift 5945079
  have htrace : WordTrace (prefixWord ++ tailWord_5945079) baseStart_5945079 baseEnd_5945079 := by
    simpa [prefixWord, tailWord_5945079, baseEnd_5945079] using wordTrace_append hprefix tailTrace_5945079
  have hstable : (prefixWord ++ tailWord_5945079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5945079).length < 2 ^ (prefixWord ++ tailWord_5945079).sum := by decide
  have hdescent : baseEnd_5945079 < baseStart_5945079 := by decide
  rcases family_descends (prefixWord ++ tailWord_5945079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5945140 : List Nat := [2, 5, 1, 1, 2, 2, 1, 2, 2, 1, 4]
def baseStart_5945140 : Nat := 118140960795 + 5945140 * 2 ^ 59
def prefixEnd_5945140 : Nat := 4983230072969 + 3 ^ 40 * 5945140 * 2
def baseEnd_5945140 : Nat := 3052714378270974846108805

theorem tailTrace_5945140 : CollatzResearch.WordTrace tailWord_5945140 prefixEnd_5945140 3052714378270974846108805 := by
  unfold tailWord_5945140
  simp only [CollatzResearch.WordTrace]
  refine ⟨108418534840890301960520437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144558046454520402614027249 108418534840890301960520437)
  ·
    refine ⟨10164237641333465808798791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 108418534840890301960520437 10164237641333465808798791)
    ·
      refine ⟨15246356462000198713198187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10164237641333465808798791 15246356462000198713198187)
      ·
        refine ⟨22869534693000298069797281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15246356462000198713198187 22869534693000298069797281)
        ·
          refine ⟨17152151019750223552347961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22869534693000298069797281 17152151019750223552347961)
          ·
            refine ⟨12864113264812667664260971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17152151019750223552347961 12864113264812667664260971)
            ·
              refine ⟨19296169897219001496391457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12864113264812667664260971 19296169897219001496391457)
              ·
                refine ⟨14472127422914251122293593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19296169897219001496391457 14472127422914251122293593)
                ·
                  refine ⟨10854095567185688341720195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14472127422914251122293593 10854095567185688341720195)
                  ·
                    refine ⟨16281143350778532512580293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10854095567185688341720195 16281143350778532512580293)
                    ·
                      refine ⟨3052714378270974846108805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16281143350778532512580293 3052714378270974846108805)
                      ·
                        rfl

theorem cell23_5945140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_5945140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5945140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5945140 prefixEnd_5945140 := by exact prefixLift 5945140
  have htrace : WordTrace (prefixWord ++ tailWord_5945140) baseStart_5945140 baseEnd_5945140 := by
    simpa [prefixWord, tailWord_5945140, baseEnd_5945140] using wordTrace_append hprefix tailTrace_5945140
  have hstable : (prefixWord ++ tailWord_5945140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5945140).length < 2 ^ (prefixWord ++ tailWord_5945140).sum := by decide
  have hdescent : baseEnd_5945140 < baseStart_5945140 := by decide
  rcases family_descends (prefixWord ++ tailWord_5945140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5945146 : List Nat := [3, 1, 1, 1, 5, 1, 2, 1, 8]
def baseStart_5945146 : Nat := 118140960795 + 5945146 * 2 ^ 59
def prefixEnd_5945146 : Nat := 4983230072969 + 3 ^ 40 * 5945146 * 2
def baseEnd_5945146 : Nat := 339190828794989091403753

theorem tailTrace_5945146 : CollatzResearch.WordTrace tailWord_5945146 prefixEnd_5945146 339190828794989091403753 := by
  unfold tailWord_5945146
  simp only [CollatzResearch.WordTrace]
  refine ⟨54209322129939716736439823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144558192346505911297172861 54209322129939716736439823)
  ·
    refine ⟨81313983194909575104659735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54209322129939716736439823 81313983194909575104659735)
    ·
      refine ⟨121970974792364362656989603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81313983194909575104659735 121970974792364362656989603)
      ·
        refine ⟨182956462188546543985484405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121970974792364362656989603 182956462188546543985484405)
        ·
          refine ⟨17152168330176238498639163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 182956462188546543985484405 17152168330176238498639163)
          ·
            refine ⟨25728252495264357747958745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17152168330176238498639163 25728252495264357747958745)
            ·
              refine ⟨19296189371448268310969059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25728252495264357747958745 19296189371448268310969059)
              ·
                refine ⟨28944284057172402466453589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19296189371448268310969059 28944284057172402466453589)
                ·
                  refine ⟨339190828794989091403753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28944284057172402466453589 339190828794989091403753)
                  ·
                    rfl

theorem cell23_5945146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 8].length) (baseStart_5945146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5945146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5945146 prefixEnd_5945146 := by exact prefixLift 5945146
  have htrace : WordTrace (prefixWord ++ tailWord_5945146) baseStart_5945146 baseEnd_5945146 := by
    simpa [prefixWord, tailWord_5945146, baseEnd_5945146] using wordTrace_append hprefix tailTrace_5945146
  have hstable : (prefixWord ++ tailWord_5945146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5945146).length < 2 ^ (prefixWord ++ tailWord_5945146).sum := by decide
  have hdescent : baseEnd_5945146 < baseStart_5945146 := by decide
  rcases family_descends (prefixWord ++ tailWord_5945146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5945150 : List Nat := [4, 2, 1, 2, 2, 1, 3, 1, 3, 4]
def baseStart_5945150 : Nat := 118140960795 + 5945150 * 2 ^ 59
def prefixEnd_5945150 : Nat := 4983230072969 + 3 ^ 40 * 5945150 * 2
def baseEnd_5945150 : Nat := 1017573171025839935661253

theorem tailTrace_5945150 : CollatzResearch.WordTrace tailWord_5945150 prefixEnd_5945150 1017573171025839935661253 := by
  unfold tailWord_5945150
  simp only [CollatzResearch.WordTrace]
  refine ⟨27104679301468046953613113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144558289607829583752603269 27104679301468046953613113)
  ·
    refine ⟨20328509476101035215209835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27104679301468046953613113 20328509476101035215209835)
    ·
      refine ⟨30492764214151552822814753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20328509476101035215209835 30492764214151552822814753)
      ·
        refine ⟨22869573160613664617111065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30492764214151552822814753 22869573160613664617111065)
        ·
          refine ⟨17152179870460248462833299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22869573160613664617111065 17152179870460248462833299)
          ·
            refine ⟨25728269805690372694249949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17152179870460248462833299 25728269805690372694249949)
            ·
              refine ⟨9648101177133889760343731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25728269805690372694249949 9648101177133889760343731)
              ·
                refine ⟨14472151765700834640515597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9648101177133889760343731 14472151765700834640515597)
                ·
                  refine ⟨5427056912137812990193349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14472151765700834640515597 5427056912137812990193349)
                  ·
                    refine ⟨1017573171025839935661253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5427056912137812990193349 1017573171025839935661253)
                    ·
                      rfl

theorem cell23_5945150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 1, 3, 4].length) (baseStart_5945150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5945150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5945150 prefixEnd_5945150 := by exact prefixLift 5945150
  have htrace : WordTrace (prefixWord ++ tailWord_5945150) baseStart_5945150 baseEnd_5945150 := by
    simpa [prefixWord, tailWord_5945150, baseEnd_5945150] using wordTrace_append hprefix tailTrace_5945150
  have hstable : (prefixWord ++ tailWord_5945150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5945150).length < 2 ^ (prefixWord ++ tailWord_5945150).sum := by decide
  have hdescent : baseEnd_5945150 < baseStart_5945150 := by decide
  rcases family_descends (prefixWord ++ tailWord_5945150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5945213 : List Nat := [1, 4, 1, 1, 2, 1, 1, 2, 2, 6, 2]
def baseStart_5945213 : Nat := 118140960795 + 5945213 * 2 ^ 59
def prefixEnd_5945213 : Nat := 4983230072969 + 3 ^ 40 * 5945213 * 2
def baseEnd_5945213 : Nat := 3052751862358753060495969

theorem tailTrace_5945213 : CollatzResearch.WordTrace tailWord_5945213 prefixEnd_5945213 3052751862358753060495969 := by
  unfold tailWord_5945213
  simp only [CollatzResearch.WordTrace]
  refine ⟨216839732210516137388448293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144559821473677424925632195 216839732210516137388448293)
  ·
    refine ⟨40657449789471775760334055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 216839732210516137388448293 40657449789471775760334055)
    ·
      refine ⟨60986174684207663640501083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40657449789471775760334055 60986174684207663640501083)
      ·
        refine ⟨91479262026311495460751625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60986174684207663640501083 91479262026311495460751625)
        ·
          refine ⟨68609446519733621595563719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91479262026311495460751625 68609446519733621595563719)
          ·
            refine ⟨102914169779600432393345579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68609446519733621595563719 102914169779600432393345579)
            ·
              refine ⟨154371254669400648590018369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102914169779600432393345579 154371254669400648590018369)
              ·
                refine ⟨115778441002050486442513777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154371254669400648590018369 115778441002050486442513777)
                ·
                  refine ⟨86833830751537864831885333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115778441002050486442513777 86833830751537864831885333)
                  ·
                    refine ⟨4070335816478337413994625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 86833830751537864831885333 4070335816478337413994625)
                    ·
                      refine ⟨3052751862358753060495969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4070335816478337413994625 3052751862358753060495969)
                      ·
                        rfl

theorem cell23_5945213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 6, 2].length) (baseStart_5945213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5945213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5945213 prefixEnd_5945213 := by exact prefixLift 5945213
  have htrace : WordTrace (prefixWord ++ tailWord_5945213) baseStart_5945213 baseEnd_5945213 := by
    simpa [prefixWord, tailWord_5945213, baseEnd_5945213] using wordTrace_append hprefix tailTrace_5945213
  have hstable : (prefixWord ++ tailWord_5945213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5945213).length < 2 ^ (prefixWord ++ tailWord_5945213).sum := by decide
  have hdescent : baseEnd_5945213 < baseStart_5945213 := by decide
  rcases family_descends (prefixWord ++ tailWord_5945213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5945216 : List Nat := [2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 5]
def baseStart_5945216 : Nat := 118140960795 + 5945216 * 2 ^ 59
def prefixEnd_5945216 : Nat := 4983230072969 + 3 ^ 40 * 5945216 * 2
def baseEnd_5945216 : Nat := 3052753402800716548758455

theorem tailTrace_5945216 : CollatzResearch.WordTrace tailWord_5945216 prefixEnd_5945216 3052753402800716548758455 := by
  unfold tailWord_5945216
  simp only [CollatzResearch.WordTrace]
  refine ⟨108419920814752634450403751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144559894419670179267205001 108419920814752634450403751)
  ·
    refine ⟨162629881222128951675605627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108419920814752634450403751 162629881222128951675605627)
    ·
      refine ⟨243944821833193427513408441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162629881222128951675605627 243944821833193427513408441)
      ·
        refine ⟨182958616374895070635056331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243944821833193427513408441 182958616374895070635056331)
        ·
          refine ⟨274437924562342605952584497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182958616374895070635056331 274437924562342605952584497)
          ·
            refine ⟨205828443421756954464438373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 274437924562342605952584497 205828443421756954464438373)
            ·
              refine ⟨38592833141579428962082195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 205828443421756954464438373 38592833141579428962082195)
              ·
                refine ⟨57889249712369143443123293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38592833141579428962082195 57889249712369143443123293)
                ·
                  refine ⟨21708468642138428791171235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57889249712369143443123293 21708468642138428791171235)
                  ·
                    refine ⟨32562702963207643186756853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21708468642138428791171235 32562702963207643186756853)
                    ·
                      refine ⟨3052753402800716548758455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32562702963207643186756853 3052753402800716548758455)
                      ·
                        rfl

theorem cell23_5945216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 5].length) (baseStart_5945216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5945216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5945216 prefixEnd_5945216 := by exact prefixLift 5945216
  have htrace : WordTrace (prefixWord ++ tailWord_5945216) baseStart_5945216 baseEnd_5945216 := by
    simpa [prefixWord, tailWord_5945216, baseEnd_5945216] using wordTrace_append hprefix tailTrace_5945216
  have hstable : (prefixWord ++ tailWord_5945216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5945216).length < 2 ^ (prefixWord ++ tailWord_5945216).sum := by decide
  have hdescent : baseEnd_5945216 < baseStart_5945216 := by decide
  rcases family_descends (prefixWord ++ tailWord_5945216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
