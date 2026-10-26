import V185TrunkScan22Chunk056

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_512112 : List Nat := [2, 1, 1, 1, 5, 2, 1, 2, 7]
def baseStart_512112 : Nat := 118140960795 + 512112 * 2 ^ 59
def prefixEnd_512112 : Nat := 4983230072969 + 3 ^ 40 * 512112 * 2
def baseEnd_512112 : Nat := 58435467763423465143299

theorem tailTrace_512112 : CollatzResearch.WordTrace tailWord_512112 prefixEnd_512112 58435467763423465143299 := by
  unfold tailWord_512112
  simp only [CollatzResearch.WordTrace]
  refine ⟨9339129560356580305761295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12452172747142107074348393 9339129560356580305761295)
  ·
    refine ⟨14008694340534870458641943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9339129560356580305761295 14008694340534870458641943)
    ·
      refine ⟨21013041510802305687962915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14008694340534870458641943 21013041510802305687962915)
      ·
        refine ⟨31519562266203458531944373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21013041510802305687962915 31519562266203458531944373)
        ·
          refine ⟨2954958962456574237369785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31519562266203458531944373 2954958962456574237369785)
          ·
            refine ⟨2216219221842430678027339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2954958962456574237369785 2216219221842430678027339)
            ·
              refine ⟨3324328832763646017041009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2216219221842430678027339 3324328832763646017041009)
              ·
                refine ⟨2493246624572734512780757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3324328832763646017041009 2493246624572734512780757)
                ·
                  refine ⟨58435467763423465143299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2493246624572734512780757 58435467763423465143299)
                  ·
                    rfl

theorem cell22_512112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 7].length) (baseStart_512112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_512112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_512112 prefixEnd_512112 := by exact prefixLift 512112
  have htrace : WordTrace (prefixWord ++ tailWord_512112) baseStart_512112 baseEnd_512112 := by
    simpa [prefixWord, tailWord_512112, baseEnd_512112] using wordTrace_append hprefix tailTrace_512112
  have hstable : (prefixWord ++ tailWord_512112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512112).length < 2 ^ (prefixWord ++ tailWord_512112).sum := by decide
  have hdescent : baseEnd_512112 < baseStart_512112 := by decide
  rcases family_descends (prefixWord ++ tailWord_512112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512206 : List Nat := [4, 1, 1, 1, 4, 2, 2, 1, 1, 5]
def baseStart_512206 : Nat := 118140960795 + 512206 * 2 ^ 59
def prefixEnd_512206 : Nat := 4983230072969 + 3 ^ 40 * 512206 * 2
def baseEnd_512206 : Nat := 175338581411285483579609

theorem tailTrace_512206 : CollatzResearch.WordTrace tailWord_512206 prefixEnd_512206 175338581411285483579609 := by
  unfold tailWord_512206
  simp only [CollatzResearch.WordTrace]
  refine ⟨2335210947796576833180559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12454458388248409776962981 2335210947796576833180559)
  ·
    refine ⟨3502816421694865249770839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2335210947796576833180559 3502816421694865249770839)
    ·
      refine ⟨5254224632542297874656259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3502816421694865249770839 5254224632542297874656259)
      ·
        refine ⟨7881336948813446811984389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5254224632542297874656259 7881336948813446811984389)
        ·
          refine ⟨1477750677902521277247073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7881336948813446811984389 1477750677902521277247073)
          ·
            refine ⟨1108313008426890957935305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1477750677902521277247073 1108313008426890957935305)
            ·
              refine ⟨831234756320168218451479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1108313008426890957935305 831234756320168218451479)
              ·
                refine ⟨1246852134480252327677219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 831234756320168218451479 1246852134480252327677219)
                ·
                  refine ⟨1870278201720378491515829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1246852134480252327677219 1870278201720378491515829)
                  ·
                    refine ⟨175338581411285483579609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1870278201720378491515829 175338581411285483579609)
                    ·
                      rfl

theorem cell22_512206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 1, 1, 5].length) (baseStart_512206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_512206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_512206 prefixEnd_512206 := by exact prefixLift 512206
  have htrace : WordTrace (prefixWord ++ tailWord_512206) baseStart_512206 baseEnd_512206 := by
    simpa [prefixWord, tailWord_512206, baseEnd_512206] using wordTrace_append hprefix tailTrace_512206
  have hstable : (prefixWord ++ tailWord_512206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512206).length < 2 ^ (prefixWord ++ tailWord_512206).sum := by decide
  have hdescent : baseEnd_512206 < baseStart_512206 := by decide
  rcases family_descends (prefixWord ++ tailWord_512206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512221 : List Nat := [1, 4, 3, 2, 1, 2, 1, 1, 1, 6]
def baseStart_512221 : Nat := 118140960795 + 512221 * 2 ^ 59
def prefixEnd_512221 : Nat := 4983230072969 + 3 ^ 40 * 512221 * 2
def baseEnd_512221 : Nat := 175343716217830444454563

theorem tailTrace_512221 : CollatzResearch.WordTrace tailWord_512221 prefixEnd_512221 175343716217830444454563 := by
  unfold tailWord_512221
  simp only [CollatzResearch.WordTrace]
  refine ⟨18682234677318272227240517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12454823118212181484827011 18682234677318272227240517)
  ·
    refine ⟨3502919001997176042607597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18682234677318272227240517 3502919001997176042607597)
    ·
      refine ⟨1313594625748941015977849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3502919001997176042607597 1313594625748941015977849)
      ·
        refine ⟨985195969311705761983387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1313594625748941015977849 985195969311705761983387)
        ·
          refine ⟨1477793953967558642975081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 985195969311705761983387 1477793953967558642975081)
          ·
            refine ⟨1108345465475668982231311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1477793953967558642975081 1108345465475668982231311)
            ·
              refine ⟨1662518198213503473346967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1108345465475668982231311 1662518198213503473346967)
              ·
                refine ⟨2493777297320255210020451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1662518198213503473346967 2493777297320255210020451)
                ·
                  refine ⟨3740665945980382815030677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2493777297320255210020451 3740665945980382815030677)
                  ·
                    refine ⟨175343716217830444454563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3740665945980382815030677 175343716217830444454563)
                    ·
                      rfl

theorem cell22_512221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_512221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_512221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_512221 prefixEnd_512221 := by exact prefixLift 512221
  have htrace : WordTrace (prefixWord ++ tailWord_512221) baseStart_512221 baseEnd_512221 := by
    simpa [prefixWord, tailWord_512221, baseEnd_512221] using wordTrace_append hprefix tailTrace_512221
  have hstable : (prefixWord ++ tailWord_512221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512221).length < 2 ^ (prefixWord ++ tailWord_512221).sum := by decide
  have hdescent : baseEnd_512221 < baseStart_512221 := by decide
  rcases family_descends (prefixWord ++ tailWord_512221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512227 : List Nat := [1, 1, 1, 8, 2, 1, 2, 1, 1, 4]
def baseStart_512227 : Nat := 118140960795 + 512227 * 2 ^ 59
def prefixEnd_512227 : Nat := 4983230072969 + 3 ^ 40 * 512227 * 2
def baseEnd_512227 : Nat := 175345770140448428804545

theorem tailTrace_512227 : CollatzResearch.WordTrace tailWord_512227 prefixEnd_512227 175345770140448428804545 := by
  unfold tailWord_512227
  simp only [CollatzResearch.WordTrace]
  refine ⟨18682453515296535251958935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12454969010197690167972623 18682453515296535251958935)
  ·
    refine ⟨28023680272944802877938403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18682453515296535251958935 28023680272944802877938403)
    ·
      refine ⟨42035520409417204316907605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28023680272944802877938403 42035520409417204316907605)
      ·
        refine ⟨492603754797857863088761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 42035520409417204316907605 492603754797857863088761)
        ·
          refine ⟨369452816098393397316571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 492603754797857863088761 369452816098393397316571)
          ·
            refine ⟨554179224147590095974857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369452816098393397316571 554179224147590095974857)
            ·
              refine ⟨415634418110692571981143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 554179224147590095974857 415634418110692571981143)
              ·
                refine ⟨623451627166038857971715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 415634418110692571981143 623451627166038857971715)
                ·
                  refine ⟨935177440749058286957573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 623451627166038857971715 935177440749058286957573)
                  ·
                    refine ⟨175345770140448428804545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 935177440749058286957573 175345770140448428804545)
                    ·
                      rfl

theorem cell22_512227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 2, 1, 1, 4].length) (baseStart_512227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_512227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_512227 prefixEnd_512227 := by exact prefixLift 512227
  have htrace : WordTrace (prefixWord ++ tailWord_512227) baseStart_512227 baseEnd_512227 := by
    simpa [prefixWord, tailWord_512227, baseEnd_512227] using wordTrace_append hprefix tailTrace_512227
  have hstable : (prefixWord ++ tailWord_512227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512227).length < 2 ^ (prefixWord ++ tailWord_512227).sum := by decide
  have hdescent : baseEnd_512227 < baseStart_512227 := by decide
  rcases family_descends (prefixWord ++ tailWord_512227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512302 : List Nat := [4, 1, 3, 3, 1, 2, 1, 1, 3, 3]
def baseStart_512302 : Nat := 118140960795 + 512302 * 2 ^ 59
def prefixEnd_512302 : Nat := 4983230072969 + 3 ^ 40 * 512302 * 2
def baseEnd_512302 : Nat := 175371444173173233179315

theorem tailTrace_512302 : CollatzResearch.WordTrace tailWord_512302 prefixEnd_512302 175371444173173233179315 := by
  unfold tailWord_512302
  simp only [CollatzResearch.WordTrace]
  refine ⟨2335648623753102882617395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12456792660016548707292773 2335648623753102882617395)
  ·
    refine ⟨3503472935629654323926093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2335648623753102882617395 3503472935629654323926093)
    ·
      refine ⟨1313802350861120371472285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3503472935629654323926093 1313802350861120371472285)
      ·
        refine ⟨492675881572920139302107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1313802350861120371472285 492675881572920139302107)
        ·
          refine ⟨739013822359380208953161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 492675881572920139302107 739013822359380208953161)
          ·
            refine ⟨554260366769535156714871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 739013822359380208953161 554260366769535156714871)
            ·
              refine ⟨831390550154302735072307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 554260366769535156714871 831390550154302735072307)
              ·
                refine ⟨1247085825231454102608461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 831390550154302735072307 1247085825231454102608461)
                ·
                  refine ⟨467657184461795288478173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1247085825231454102608461 467657184461795288478173)
                  ·
                    refine ⟨175371444173173233179315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 467657184461795288478173 175371444173173233179315)
                    ·
                      rfl

theorem cell22_512302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_512302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_512302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_512302 prefixEnd_512302 := by exact prefixLift 512302
  have htrace : WordTrace (prefixWord ++ tailWord_512302) baseStart_512302 baseEnd_512302 := by
    simpa [prefixWord, tailWord_512302, baseEnd_512302] using wordTrace_append hprefix tailTrace_512302
  have hstable : (prefixWord ++ tailWord_512302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512302).length < 2 ^ (prefixWord ++ tailWord_512302).sum := by decide
  have hdescent : baseEnd_512302 < baseStart_512302 := by decide
  rcases family_descends (prefixWord ++ tailWord_512302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512356 : List Nat := [2, 3, 1, 1, 3, 1, 1, 4, 2, 4]
def baseStart_512356 : Nat := 118140960795 + 512356 * 2 ^ 59
def prefixEnd_512356 : Nat := 4983230072969 + 3 ^ 40 * 512356 * 2
def baseEnd_512356 : Nat := 175389929476735092329149

theorem tailTrace_512356 : CollatzResearch.WordTrace tailWord_512356 prefixEnd_512356 175389929476735092329149 := by
  unfold tailWord_512356
  simp only [CollatzResearch.WordTrace]
  refine ⟨9343579265914595141702461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12458105687886126855603281 9343579265914595141702461)
  ·
    refine ⟨3503842224717973178138423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9343579265914595141702461 3503842224717973178138423)
    ·
      refine ⟨5255763337076959767207635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3503842224717973178138423 5255763337076959767207635)
      ·
        refine ⟨7883645005615439650811453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5255763337076959767207635 7883645005615439650811453)
        ·
          refine ⟨2956366877105789869054295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7883645005615439650811453 2956366877105789869054295)
          ·
            refine ⟨4434550315658684803581443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2956366877105789869054295 4434550315658684803581443)
            ·
              refine ⟨6651825473488027205372165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4434550315658684803581443 6651825473488027205372165)
              ·
                refine ⟨1247217276279005101007281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6651825473488027205372165 1247217276279005101007281)
                ·
                  refine ⟨935412957209253825755461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1247217276279005101007281 935412957209253825755461)
                  ·
                    refine ⟨175389929476735092329149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 935412957209253825755461 175389929476735092329149)
                    ·
                      rfl

theorem cell22_512356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 4, 2, 4].length) (baseStart_512356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_512356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_512356 prefixEnd_512356 := by exact prefixLift 512356
  have htrace : WordTrace (prefixWord ++ tailWord_512356) baseStart_512356 baseEnd_512356 := by
    simpa [prefixWord, tailWord_512356, baseEnd_512356] using wordTrace_append hprefix tailTrace_512356
  have hstable : (prefixWord ++ tailWord_512356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512356).length < 2 ^ (prefixWord ++ tailWord_512356).sum := by decide
  have hdescent : baseEnd_512356 < baseStart_512356 := by decide
  rcases family_descends (prefixWord ++ tailWord_512356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512360 : List Nat := [2, 1, 4, 2, 2, 1, 4, 2, 4]
def baseStart_512360 : Nat := 118140960795 + 512360 * 2 ^ 59
def prefixEnd_512360 : Nat := 4983230072969 + 3 ^ 40 * 512360 * 2
def baseEnd_512360 : Nat := 58463766252826805076379

theorem tailTrace_512360 : CollatzResearch.WordTrace tailWord_512360 prefixEnd_512360 58463766252826805076379 := by
  unfold tailWord_512360
  simp only [CollatzResearch.WordTrace]
  refine ⟨9343652211907349483275267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12458202949209799311033689 9343652211907349483275267)
  ·
    refine ⟨14015478317861024224912901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9343652211907349483275267 14015478317861024224912901)
    ·
      refine ⟨2627902184598942042171169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14015478317861024224912901 2627902184598942042171169)
      ·
        refine ⟨1970926638449206531628377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2627902184598942042171169 1970926638449206531628377)
        ·
          refine ⟨1478194978836904898721283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1970926638449206531628377 1478194978836904898721283)
          ·
            refine ⟨2217292468255357348081925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1478194978836904898721283 2217292468255357348081925)
            ·
              refine ⟨415742337797879502765361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2217292468255357348081925 415742337797879502765361)
              ·
                refine ⟨311806753348409627074021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 415742337797879502765361 311806753348409627074021)
                ·
                  refine ⟨58463766252826805076379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 311806753348409627074021 58463766252826805076379)
                  ·
                    rfl

theorem cell22_512360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 4, 2, 4].length) (baseStart_512360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_512360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_512360 prefixEnd_512360 := by exact prefixLift 512360
  have htrace : WordTrace (prefixWord ++ tailWord_512360) baseStart_512360 baseEnd_512360 := by
    simpa [prefixWord, tailWord_512360, baseEnd_512360] using wordTrace_append hprefix tailTrace_512360
  have hstable : (prefixWord ++ tailWord_512360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512360).length < 2 ^ (prefixWord ++ tailWord_512360).sum := by decide
  have hdescent : baseEnd_512360 < baseStart_512360 := by decide
  rcases family_descends (prefixWord ++ tailWord_512360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512369 : List Nat := [1, 2, 2, 2, 1, 2, 1, 2, 2, 7]
def baseStart_512369 : Nat := 118140960795 + 512369 * 2 ^ 59
def prefixEnd_512369 : Nat := 4983230072969 + 3 ^ 40 * 512369 * 2
def baseEnd_512369 : Nat := 175394379642407391754109

theorem tailTrace_512369 : CollatzResearch.WordTrace tailWord_512369 prefixEnd_512369 175394379642407391754109 := by
  unfold tailWord_512369
  simp only [CollatzResearch.WordTrace]
  refine ⟨18687632680782093503628161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12458421787188062335752107 18687632680782093503628161)
  ·
    refine ⟨14015724510586570127721121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18687632680782093503628161 14015724510586570127721121)
    ·
      refine ⟨10511793382939927595790841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14015724510586570127721121 10511793382939927595790841)
      ·
        refine ⟨7883845037204945696843131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10511793382939927595790841 7883845037204945696843131)
        ·
          refine ⟨11825767555807418545264697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7883845037204945696843131 11825767555807418545264697)
          ·
            refine ⟨8869325666855563908948523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11825767555807418545264697 8869325666855563908948523)
            ·
              refine ⟨13303988500283345863422785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8869325666855563908948523 13303988500283345863422785)
              ·
                refine ⟨9977991375212509397567089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13303988500283345863422785 9977991375212509397567089)
                ·
                  refine ⟨7483493531409382048175317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9977991375212509397567089 7483493531409382048175317)
                  ·
                    refine ⟨175394379642407391754109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7483493531409382048175317 175394379642407391754109)
                    ·
                      rfl

theorem cell22_512369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 7].length) (baseStart_512369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_512369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_512369 prefixEnd_512369 := by exact prefixLift 512369
  have htrace : WordTrace (prefixWord ++ tailWord_512369) baseStart_512369 baseEnd_512369 := by
    simpa [prefixWord, tailWord_512369, baseEnd_512369] using wordTrace_append hprefix tailTrace_512369
  have hstable : (prefixWord ++ tailWord_512369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512369).length < 2 ^ (prefixWord ++ tailWord_512369).sum := by decide
  have hdescent : baseEnd_512369 < baseStart_512369 := by decide
  rcases family_descends (prefixWord ++ tailWord_512369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512416 : List Nat := [2, 1, 1, 4, 1, 4, 1, 1, 7]
def baseStart_512416 : Nat := 118140960795 + 512416 * 2 ^ 59
def prefixEnd_512416 : Nat := 4983230072969 + 3 ^ 40 * 512416 * 2
def baseEnd_512416 : Nat := 58470156234304978609655

theorem tailTrace_512416 : CollatzResearch.WordTrace tailWord_512416 prefixEnd_512416 58470156234304978609655 := by
  unfold tailWord_512416
  simp only [CollatzResearch.WordTrace]
  refine ⟨9344673455805910265294551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12459564607741213687059401 9344673455805910265294551)
  ·
    refine ⟨14017010183708865397941827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9344673455805910265294551 14017010183708865397941827)
    ·
      refine ⟨21025515275563298096912741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14017010183708865397941827 21025515275563298096912741)
      ·
        refine ⟨3942284114168118393171139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21025515275563298096912741 3942284114168118393171139)
        ·
          refine ⟨5913426171252177589756709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3942284114168118393171139 5913426171252177589756709)
          ·
            refine ⟨1108767407109783298079383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5913426171252177589756709 1108767407109783298079383)
            ·
              refine ⟨1663151110664674947119075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1108767407109783298079383 1663151110664674947119075)
              ·
                refine ⟨2494726665997012420678613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1663151110664674947119075 2494726665997012420678613)
                ·
                  refine ⟨58470156234304978609655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2494726665997012420678613 58470156234304978609655)
                  ·
                    rfl

theorem cell22_512416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 7].length) (baseStart_512416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_512416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_512416 prefixEnd_512416 := by exact prefixLift 512416
  have htrace : WordTrace (prefixWord ++ tailWord_512416) baseStart_512416 baseEnd_512416 := by
    simpa [prefixWord, tailWord_512416, baseEnd_512416] using wordTrace_append hprefix tailTrace_512416
  have hstable : (prefixWord ++ tailWord_512416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512416).length < 2 ^ (prefixWord ++ tailWord_512416).sum := by decide
  have hdescent : baseEnd_512416 < baseStart_512416 := by decide
  rcases family_descends (prefixWord ++ tailWord_512416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512420 : List Nat := [2, 3, 1, 2, 1, 1, 4, 4, 1, 3]
def baseStart_512420 : Nat := 118140960795 + 512420 * 2 ^ 59
def prefixEnd_512420 : Nat := 4983230072969 + 3 ^ 40 * 512420 * 2
def baseEnd_512420 : Nat := 175411837984660258728953

theorem tailTrace_512420 : CollatzResearch.WordTrace tailWord_512420 prefixEnd_512420 175411837984660258728953 := by
  unfold tailWord_512420
  simp only [CollatzResearch.WordTrace]
  refine ⟨9344746401798664606867357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12459661869064886142489809 9344746401798664606867357)
  ·
    refine ⟨3504279900674499227575259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9344746401798664606867357 3504279900674499227575259)
    ·
      refine ⟨5256419851011748841362889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3504279900674499227575259 5256419851011748841362889)
      ·
        refine ⟨3942314888258811631022167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5256419851011748841362889 3942314888258811631022167)
        ·
          refine ⟨5913472332388217446533251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3942314888258811631022167 5913472332388217446533251)
          ·
            refine ⟨8870208498582326169799877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5913472332388217446533251 8870208498582326169799877)
            ·
              refine ⟨1663164093484186156837477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8870208498582326169799877 1663164093484186156837477)
              ·
                refine ⟨311843267528284904407027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1663164093484186156837477 311843267528284904407027)
                ·
                  refine ⟨467764901292427356610541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 311843267528284904407027 467764901292427356610541)
                  ·
                    refine ⟨175411837984660258728953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 467764901292427356610541 175411837984660258728953)
                    ·
                      rfl

theorem cell22_512420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 4, 1, 3].length) (baseStart_512420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_512420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_512420 prefixEnd_512420 := by exact prefixLift 512420
  have htrace : WordTrace (prefixWord ++ tailWord_512420) baseStart_512420 baseEnd_512420 := by
    simpa [prefixWord, tailWord_512420, baseEnd_512420] using wordTrace_append hprefix tailTrace_512420
  have hstable : (prefixWord ++ tailWord_512420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512420).length < 2 ^ (prefixWord ++ tailWord_512420).sum := by decide
  have hdescent : baseEnd_512420 < baseStart_512420 := by decide
  rcases family_descends (prefixWord ++ tailWord_512420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512426 : List Nat := [3, 1, 6, 1, 1, 1, 3, 1, 2, 3]
def baseStart_512426 : Nat := 118140960795 + 512426 * 2 ^ 59
def prefixEnd_512426 : Nat := 4983230072969 + 3 ^ 40 * 512426 * 2
def baseEnd_512426 : Nat := 175413891907278243078935

theorem tailTrace_512426 : CollatzResearch.WordTrace tailWord_512426 prefixEnd_512426 175413891907278243078935 := by
  unfold tailWord_512426
  simp only [CollatzResearch.WordTrace]
  refine ⟨4672427910393898059613283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12459807761050394825635421 4672427910393898059613283)
  ·
    refine ⟨7008641865590847089419925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4672427910393898059613283 7008641865590847089419925)
    ·
      refine ⟨328530087449570957316559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7008641865590847089419925 328530087449570957316559)
      ·
        refine ⟨492795131174356435974839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328530087449570957316559 492795131174356435974839)
        ·
          refine ⟨739192696761534653962259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 492795131174356435974839 739192696761534653962259)
          ·
            refine ⟨1108789045142301980943389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 739192696761534653962259 1108789045142301980943389)
            ·
              refine ⟨415795891928363242853771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1108789045142301980943389 415795891928363242853771)
              ·
                refine ⟨623693837892544864280657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 415795891928363242853771 623693837892544864280657)
                ·
                  refine ⟨467770378419408648210493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 623693837892544864280657 467770378419408648210493)
                  ·
                    refine ⟨175413891907278243078935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 467770378419408648210493 175413891907278243078935)
                    ·
                      rfl

theorem cell22_512426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_512426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_512426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_512426 prefixEnd_512426 := by exact prefixLift 512426
  have htrace : WordTrace (prefixWord ++ tailWord_512426) baseStart_512426 baseEnd_512426 := by
    simpa [prefixWord, tailWord_512426, baseEnd_512426] using wordTrace_append hprefix tailTrace_512426
  have hstable : (prefixWord ++ tailWord_512426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512426).length < 2 ^ (prefixWord ++ tailWord_512426).sum := by decide
  have hdescent : baseEnd_512426 < baseStart_512426 := by decide
  rcases family_descends (prefixWord ++ tailWord_512426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512491 : List Nat := [1, 1, 1, 1, 2, 3, 3, 2, 4, 4]
def baseStart_512491 : Nat := 118140960795 + 512491 * 2 ^ 59
def prefixEnd_512491 : Nat := 4983230072969 + 3 ^ 40 * 512491 * 2
def baseEnd_512491 : Nat := 175436142735639740203735

theorem tailTrace_512491 : CollatzResearch.WordTrace tailWord_512491 prefixEnd_512491 175436142735639740203735 := by
  unfold tailWord_512491
  simp only [CollatzResearch.WordTrace]
  refine ⟨18692082386340108339569327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12461388257560072226379551 18692082386340108339569327)
  ·
    refine ⟨28038123579510162509353991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18692082386340108339569327 28038123579510162509353991)
    ·
      refine ⟨42057185369265243764030987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28038123579510162509353991 42057185369265243764030987)
      ·
        refine ⟨63085778053897865646046481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42057185369265243764030987 63085778053897865646046481)
        ·
          refine ⟨47314333540423399234534861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63085778053897865646046481 47314333540423399234534861)
          ·
            refine ⟨17742875077658774712950573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47314333540423399234534861 17742875077658774712950573)
            ·
              refine ⟨6653578154122040517356465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17742875077658774712950573 6653578154122040517356465)
              ·
                refine ⟨4990183615591530388017349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6653578154122040517356465 4990183615591530388017349)
                ·
                  refine ⟨935659427923411947753253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4990183615591530388017349 935659427923411947753253)
                  ·
                    refine ⟨175436142735639740203735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 935659427923411947753253 175436142735639740203735)
                    ·
                      rfl

theorem cell22_512491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 4, 4].length) (baseStart_512491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_512491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_512491 prefixEnd_512491 := by exact prefixLift 512491
  have htrace : WordTrace (prefixWord ++ tailWord_512491) baseStart_512491 baseEnd_512491 := by
    simpa [prefixWord, tailWord_512491, baseEnd_512491] using wordTrace_append hprefix tailTrace_512491
  have hstable : (prefixWord ++ tailWord_512491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512491).length < 2 ^ (prefixWord ++ tailWord_512491).sum := by decide
  have hdescent : baseEnd_512491 < baseStart_512491 := by decide
  rcases family_descends (prefixWord ++ tailWord_512491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512514 : List Nat := [3, 4, 1, 2, 2, 1, 3, 1, 1, 4]
def baseStart_512514 : Nat := 118140960795 + 512514 * 2 ^ 59
def prefixEnd_512514 : Nat := 4983230072969 + 3 ^ 40 * 512514 * 2
def baseEnd_512514 : Nat := 175444016105675346878665

theorem tailTrace_512514 : CollatzResearch.WordTrace tailWord_512514 prefixEnd_512514 175444016105675346878665 := by
  unfold tailWord_512514
  simp only [CollatzResearch.WordTrace]
  refine ⟨4673230316314195816914149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12461947510171188845104397 4673230316314195816914149)
  ·
    refine ⟨876230684308911715671403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4673230316314195816914149 876230684308911715671403)
    ·
      refine ⟨1314346026463367573507105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 876230684308911715671403 1314346026463367573507105)
      ·
        refine ⟨985759519847525680130329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1314346026463367573507105 985759519847525680130329)
        ·
          refine ⟨739319639885644260097747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 985759519847525680130329 739319639885644260097747)
          ·
            refine ⟨1108979459828466390146621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 739319639885644260097747 1108979459828466390146621)
            ·
              refine ⟨415867297435674896304983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1108979459828466390146621 415867297435674896304983)
              ·
                refine ⟨623800946153512344457475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 415867297435674896304983 623800946153512344457475)
                ·
                  refine ⟨935701419230268516686213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 623800946153512344457475 935701419230268516686213)
                  ·
                    refine ⟨175444016105675346878665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 935701419230268516686213 175444016105675346878665)
                    ·
                      rfl

theorem cell22_512514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_512514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_512514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_512514 prefixEnd_512514 := by exact prefixLift 512514
  have htrace : WordTrace (prefixWord ++ tailWord_512514) baseStart_512514 baseEnd_512514 := by
    simpa [prefixWord, tailWord_512514, baseEnd_512514] using wordTrace_append hprefix tailTrace_512514
  have hstable : (prefixWord ++ tailWord_512514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512514).length < 2 ^ (prefixWord ++ tailWord_512514).sum := by decide
  have hdescent : baseEnd_512514 < baseStart_512514 := by decide
  rcases family_descends (prefixWord ++ tailWord_512514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512572 : List Nat := [2, 2, 2, 2, 3, 1, 1, 5, 1, 3]
def baseStart_512572 : Nat := 118140960795 + 512572 * 2 ^ 59
def prefixEnd_512572 : Nat := 4983230072969 + 3 ^ 40 * 512572 * 2
def baseEnd_512572 : Nat := 175463870690982528928487

theorem tailTrace_512572 : CollatzResearch.WordTrace tailWord_512572 prefixEnd_512572 175463870690982528928487 := by
  unfold tailWord_512572
  simp only [CollatzResearch.WordTrace]
  refine ⟨9347518349523329586633985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12463357799364439448845313 9347518349523329586633985)
  ·
    refine ⟨7010638762142497189975489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9347518349523329586633985 7010638762142497189975489)
    ·
      refine ⟨5257979071606872892481617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7010638762142497189975489 5257979071606872892481617)
      ·
        refine ⟨3943484303705154669361213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5257979071606872892481617 3943484303705154669361213)
        ·
          refine ⟨1478806613889433001010455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3943484303705154669361213 1478806613889433001010455)
          ·
            refine ⟨2218209920834149501515683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1478806613889433001010455 2218209920834149501515683)
            ·
              refine ⟨3327314881251224252273525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2218209920834149501515683 3327314881251224252273525)
              ·
                refine ⟨311935770117302273650643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3327314881251224252273525 311935770117302273650643)
                ·
                  refine ⟨467903655175953410475965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 311935770117302273650643 467903655175953410475965)
                  ·
                    refine ⟨175463870690982528928487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 467903655175953410475965 175463870690982528928487)
                    ·
                      rfl

theorem cell22_512572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 5, 1, 3].length) (baseStart_512572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_512572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_512572 prefixEnd_512572 := by exact prefixLift 512572
  have htrace : WordTrace (prefixWord ++ tailWord_512572) baseStart_512572 baseEnd_512572 := by
    simpa [prefixWord, tailWord_512572, baseEnd_512572] using wordTrace_append hprefix tailTrace_512572
  have hstable : (prefixWord ++ tailWord_512572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512572).length < 2 ^ (prefixWord ++ tailWord_512572).sum := by decide
  have hdescent : baseEnd_512572 < baseStart_512572 := by decide
  rcases family_descends (prefixWord ++ tailWord_512572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512583 : List Nat := [1, 1, 4, 1, 4, 1, 1, 2, 2, 5]
def baseStart_512583 : Nat := 118140960795 + 512583 * 2 ^ 59
def prefixEnd_512583 : Nat := 4983230072969 + 3 ^ 40 * 512583 * 2
def baseEnd_512583 : Nat := 175467636215782166903453

theorem tailTrace_512583 : CollatzResearch.WordTrace tailWord_512583 prefixEnd_512583 175467636215782166903453 := by
  unfold tailWord_512583
  simp only [CollatzResearch.WordTrace]
  refine ⟨18695437902006808051918403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12463625268004538701278935 18695437902006808051918403)
  ·
    refine ⟨28043156853010212077877605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18695437902006808051918403 28043156853010212077877605)
    ·
      refine ⟨5258091909939414764602051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28043156853010212077877605 5258091909939414764602051)
      ·
        refine ⟨7887137864909122146903077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5258091909939414764602051 7887137864909122146903077)
        ·
          refine ⟨1478838349670460402544327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7887137864909122146903077 1478838349670460402544327)
          ·
            refine ⟨2218257524505690603816491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1478838349670460402544327 2218257524505690603816491)
            ·
              refine ⟨3327386286758535905724737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2218257524505690603816491 3327386286758535905724737)
              ·
                refine ⟨2495539715068901929293553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3327386286758535905724737 2495539715068901929293553)
                ·
                  refine ⟨1871654786301676446970165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2495539715068901929293553 1871654786301676446970165)
                  ·
                    refine ⟨175467636215782166903453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1871654786301676446970165 175467636215782166903453)
                    ·
                      rfl

theorem cell22_512583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 2, 5].length) (baseStart_512583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_512583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_512583 prefixEnd_512583 := by exact prefixLift 512583
  have htrace : WordTrace (prefixWord ++ tailWord_512583) baseStart_512583 baseEnd_512583 := by
    simpa [prefixWord, tailWord_512583, baseEnd_512583] using wordTrace_append hprefix tailTrace_512583
  have hstable : (prefixWord ++ tailWord_512583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512583).length < 2 ^ (prefixWord ++ tailWord_512583).sum := by decide
  have hdescent : baseEnd_512583 < baseStart_512583 := by decide
  rcases family_descends (prefixWord ++ tailWord_512583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512589 : List Nat := [1, 6, 1, 1, 2, 1, 2, 4, 1, 3]
def baseStart_512589 : Nat := 118140960795 + 512589 * 2 ^ 59
def prefixEnd_512589 : Nat := 4983230072969 + 3 ^ 40 * 512589 * 2
def baseEnd_512589 : Nat := 175469690138400151253435

theorem tailTrace_512589 : CollatzResearch.WordTrace tailWord_512589 prefixEnd_512589 175469690138400151253435 := by
  unfold tailWord_512589
  simp only [CollatzResearch.WordTrace]
  refine ⟨18695656739985071076636821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12463771159990047384424547 18695656739985071076636821)
  ·
    refine ⟨876358909686800206717351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18695656739985071076636821 876358909686800206717351)
    ·
      refine ⟨1314538364530200310076027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 876358909686800206717351 1314538364530200310076027)
      ·
        refine ⟨1971807546795300465114041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1314538364530200310076027 1971807546795300465114041)
        ·
          refine ⟨1478855660096475348835531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1971807546795300465114041 1478855660096475348835531)
          ·
            refine ⟨2218283490144713023253297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1478855660096475348835531 2218283490144713023253297)
            ·
              refine ⟨1663712617608534767439973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2218283490144713023253297 1663712617608534767439973)
              ·
                refine ⟨311946115801600268894995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1663712617608534767439973 311946115801600268894995)
                ·
                  refine ⟨467919173702400403342493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 311946115801600268894995 467919173702400403342493)
                  ·
                    refine ⟨175469690138400151253435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 467919173702400403342493 175469690138400151253435)
                    ·
                      rfl

theorem cell22_512589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_512589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_512589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_512589 prefixEnd_512589 := by exact prefixLift 512589
  have htrace : WordTrace (prefixWord ++ tailWord_512589) baseStart_512589 baseEnd_512589 := by
    simpa [prefixWord, tailWord_512589, baseEnd_512589] using wordTrace_append hprefix tailTrace_512589
  have hstable : (prefixWord ++ tailWord_512589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512589).length < 2 ^ (prefixWord ++ tailWord_512589).sum := by decide
  have hdescent : baseEnd_512589 < baseStart_512589 := by decide
  rcases family_descends (prefixWord ++ tailWord_512589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512643 : List Nat := [1, 1, 1, 3, 3, 1, 3, 1, 4, 4]
def baseStart_512643 : Nat := 118140960795 + 512643 * 2 ^ 59
def prefixEnd_512643 : Nat := 4983230072969 + 3 ^ 40 * 512643 * 2
def baseEnd_512643 : Nat := 175488175441962010403269

theorem tailTrace_512643 : CollatzResearch.WordTrace tailWord_512643 prefixEnd_512643 175488175441962010403269 := by
  unfold tailWord_512643
  simp only [CollatzResearch.WordTrace]
  refine ⟨18697626281789438299102583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12465084187859625532735055 18697626281789438299102583)
  ·
    refine ⟨28046439422684157448653875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18697626281789438299102583 28046439422684157448653875)
    ·
      refine ⟨42069659134026236172980813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28046439422684157448653875 42069659134026236172980813)
      ·
        refine ⟨15776122175259838564867805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42069659134026236172980813 15776122175259838564867805)
        ·
          refine ⟨5916045815722439461825427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15776122175259838564867805 5916045815722439461825427)
          ·
            refine ⟨8874068723583659192738141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5916045815722439461825427 8874068723583659192738141)
            ·
              refine ⟨3327775771343872197276803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8874068723583659192738141 3327775771343872197276803)
              ·
                refine ⟨4991663657015808295915205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3327775771343872197276803 4991663657015808295915205)
                ·
                  refine ⟨935936935690464055484101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4991663657015808295915205 935936935690464055484101)
                  ·
                    refine ⟨175488175441962010403269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 935936935690464055484101 175488175441962010403269)
                    ·
                      rfl

theorem cell22_512643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 4, 4].length) (baseStart_512643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_512643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_512643 prefixEnd_512643 := by exact prefixLift 512643
  have htrace : WordTrace (prefixWord ++ tailWord_512643) baseStart_512643 baseEnd_512643 := by
    simpa [prefixWord, tailWord_512643, baseEnd_512643] using wordTrace_append hprefix tailTrace_512643
  have hstable : (prefixWord ++ tailWord_512643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512643).length < 2 ^ (prefixWord ++ tailWord_512643).sum := by decide
  have hdescent : baseEnd_512643 < baseStart_512643 := by decide
  rcases family_descends (prefixWord ++ tailWord_512643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512645 : List Nat := [1, 3, 1, 1, 4, 2, 2, 1, 4, 3]
def baseStart_512645 : Nat := 118140960795 + 512645 * 2 ^ 59
def prefixEnd_512645 : Nat := 4983230072969 + 3 ^ 40 * 512645 * 2
def baseEnd_512645 : Nat := 175488860082834671853263

theorem tailTrace_512645 : CollatzResearch.WordTrace tailWord_512645 prefixEnd_512645 175488860082834671853263 := by
  unfold tailWord_512645
  simp only [CollatzResearch.WordTrace]
  refine ⟨18697699227782192640675389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12465132818521461760450259 18697699227782192640675389)
  ·
    refine ⟨7011637210418322240253271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18697699227782192640675389 7011637210418322240253271)
    ·
      refine ⟨10517455815627483360379907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7011637210418322240253271 10517455815627483360379907)
      ·
        refine ⟨15776183723441225040569861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10517455815627483360379907 15776183723441225040569861)
        ·
          refine ⟨2958034448145229695106849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15776183723441225040569861 2958034448145229695106849)
          ·
            refine ⟨2218525836108922271330137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2958034448145229695106849 2218525836108922271330137)
            ·
              refine ⟨1663894377081691703497603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2218525836108922271330137 1663894377081691703497603)
              ·
                refine ⟨2495841565622537555246405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1663894377081691703497603 2495841565622537555246405)
                ·
                  refine ⟨467970293554225791608701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2495841565622537555246405 467970293554225791608701)
                  ·
                    refine ⟨175488860082834671853263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 467970293554225791608701 175488860082834671853263)
                    ·
                      rfl

theorem cell22_512645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 4, 3].length) (baseStart_512645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_512645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_512645 prefixEnd_512645 := by exact prefixLift 512645
  have htrace : WordTrace (prefixWord ++ tailWord_512645) baseStart_512645 baseEnd_512645 := by
    simpa [prefixWord, tailWord_512645, baseEnd_512645] using wordTrace_append hprefix tailTrace_512645
  have hstable : (prefixWord ++ tailWord_512645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512645).length < 2 ^ (prefixWord ++ tailWord_512645).sum := by decide
  have hdescent : baseEnd_512645 < baseStart_512645 := by decide
  rcases family_descends (prefixWord ++ tailWord_512645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512647 : List Nat := [1, 1, 4, 2, 1, 2, 5, 2, 4]
def baseStart_512647 : Nat := 118140960795 + 512647 * 2 ^ 59
def prefixEnd_512647 : Nat := 4983230072969 + 3 ^ 40 * 512647 * 2
def baseEnd_512647 : Nat := 58496514907902444434419

theorem tailTrace_512647 : CollatzResearch.WordTrace tailWord_512647 prefixEnd_512647 58496514907902444434419 := by
  unfold tailWord_512647
  simp only [CollatzResearch.WordTrace]
  refine ⟨18697772173774946982248195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12465181449183297988165463 18697772173774946982248195)
  ·
    refine ⟨28046658260662420473372293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18697772173774946982248195 28046658260662420473372293)
    ·
      refine ⟨5258748423874203838757305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28046658260662420473372293 5258748423874203838757305)
      ·
        refine ⟨3944061317905652879067979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5258748423874203838757305 3944061317905652879067979)
        ·
          refine ⟨5916091976858479318601969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3944061317905652879067979 5916091976858479318601969)
          ·
            refine ⟨4437068982643859488951477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5916091976858479318601969 4437068982643859488951477)
            ·
              refine ⟨415975217122861827089201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4437068982643859488951477 415975217122861827089201)
              ·
                refine ⟨311981412842146370316901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 415975217122861827089201 311981412842146370316901)
                ·
                  refine ⟨58496514907902444434419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 311981412842146370316901 58496514907902444434419)
                  ·
                    rfl

theorem cell22_512647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 5, 2, 4].length) (baseStart_512647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_512647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_512647 prefixEnd_512647 := by exact prefixLift 512647
  have htrace : WordTrace (prefixWord ++ tailWord_512647) baseStart_512647 baseEnd_512647 := by
    simpa [prefixWord, tailWord_512647, baseEnd_512647] using wordTrace_append hprefix tailTrace_512647
  have hstable : (prefixWord ++ tailWord_512647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512647).length < 2 ^ (prefixWord ++ tailWord_512647).sum := by decide
  have hdescent : baseEnd_512647 < baseStart_512647 := by decide
  rcases family_descends (prefixWord ++ tailWord_512647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512666 : List Nat := [3, 1, 1, 6, 2, 1, 1, 2, 1, 4]
def baseStart_512666 : Nat := 118140960795 + 512666 * 2 ^ 59
def prefixEnd_512666 : Nat := 4983230072969 + 3 ^ 40 * 512666 * 2
def baseEnd_512666 : Nat := 175496048811997617078199

theorem tailTrace_512666 : CollatzResearch.WordTrace tailWord_512666 prefixEnd_512666 175496048811997617078199 := by
  unfold tailWord_512666
  simp only [CollatzResearch.WordTrace]
  refine ⟨4674616290176528306797463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12465643440470742151459901 4674616290176528306797463)
  ·
    refine ⟨7011924435264792460196195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4674616290176528306797463 7011924435264792460196195)
    ·
      refine ⟨10517886652897188690294293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7011924435264792460196195 10517886652897188690294293)
      ·
        refine ⟨493025936854555719857545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 10517886652897188690294293 493025936854555719857545)
        ·
          refine ⟨369769452640916789893159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 493025936854555719857545 369769452640916789893159)
          ·
            refine ⟨554654178961375184839739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369769452640916789893159 554654178961375184839739)
            ·
              refine ⟨831981268442062777259609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 554654178961375184839739 831981268442062777259609)
              ·
                refine ⟨623985951331547082944707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 831981268442062777259609 623985951331547082944707)
                ·
                  refine ⟨935978926997320624417061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 623985951331547082944707 935978926997320624417061)
                  ·
                    refine ⟨175496048811997617078199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 935978926997320624417061 175496048811997617078199)
                    ·
                      rfl

theorem cell22_512666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 2, 1, 4].length) (baseStart_512666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_512666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_512666 prefixEnd_512666 := by exact prefixLift 512666
  have htrace : WordTrace (prefixWord ++ tailWord_512666) baseStart_512666 baseEnd_512666 := by
    simpa [prefixWord, tailWord_512666, baseEnd_512666] using wordTrace_append hprefix tailTrace_512666
  have hstable : (prefixWord ++ tailWord_512666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512666).length < 2 ^ (prefixWord ++ tailWord_512666).sum := by decide
  have hdescent : baseEnd_512666 < baseStart_512666 := by decide
  rcases family_descends (prefixWord ++ tailWord_512666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512724 : List Nat := [2, 4, 1, 3, 2, 1, 1, 2, 3, 3]
def baseStart_512724 : Nat := 118140960795 + 512724 * 2 ^ 59
def prefixEnd_512724 : Nat := 4983230072969 + 3 ^ 40 * 512724 * 2
def baseEnd_512724 : Nat := 175515903397304799128021

theorem tailTrace_512724 : CollatzResearch.WordTrace tailWord_512724 prefixEnd_512724 175515903397304799128021 := by
  unfold tailWord_512724
  simp only [CollatzResearch.WordTrace]
  refine ⟨9350290297247994566400613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12467053729663992755200817 9350290297247994566400613)
  ·
    refine ⟨1753179430733998981200115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9350290297247994566400613 1753179430733998981200115)
    ·
      refine ⟨2629769146100998471800173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1753179430733998981200115 2629769146100998471800173)
      ·
        refine ⟨986163429787874426925065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2629769146100998471800173 986163429787874426925065)
        ·
          refine ⟨739622572340905820193799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 986163429787874426925065 739622572340905820193799)
          ·
            refine ⟨1109433858511358730290699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 739622572340905820193799 1109433858511358730290699)
            ·
              refine ⟨1664150787767038095436049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1109433858511358730290699 1664150787767038095436049)
              ·
                refine ⟨1248113090825278571577037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1664150787767038095436049 1248113090825278571577037)
                ·
                  refine ⟨468042409059479464341389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1248113090825278571577037 468042409059479464341389)
                  ·
                    refine ⟨175515903397304799128021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 468042409059479464341389 175515903397304799128021)
                    ·
                      rfl

theorem cell22_512724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 2, 3, 3].length) (baseStart_512724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_512724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_512724 prefixEnd_512724 := by exact prefixLift 512724
  have htrace : WordTrace (prefixWord ++ tailWord_512724) baseStart_512724 baseEnd_512724 := by
    simpa [prefixWord, tailWord_512724, baseEnd_512724] using wordTrace_append hprefix tailTrace_512724
  have hstable : (prefixWord ++ tailWord_512724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512724).length < 2 ^ (prefixWord ++ tailWord_512724).sum := by decide
  have hdescent : baseEnd_512724 < baseStart_512724 := by decide
  rcases family_descends (prefixWord ++ tailWord_512724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512748 : List Nat := [2, 2, 1, 1, 2, 2, 1, 1, 10]
def baseStart_512748 : Nat := 118140960795 + 512748 * 2 ^ 59
def prefixEnd_512748 : Nat := 4983230072969 + 3 ^ 40 * 512748 * 2
def baseEnd_512748 : Nat := 58508039695925578842649

theorem tailTrace_512748 : CollatzResearch.WordTrace tailWord_512748 prefixEnd_512748 58508039695925578842649 := by
  unfold tailWord_512748
  simp only [CollatzResearch.WordTrace]
  refine ⟨9350727973204520615837449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12467637297606027487783265 9350727973204520615837449)
  ·
    refine ⟨7013045979903390461878087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9350727973204520615837449 7013045979903390461878087)
    ·
      refine ⟨10519568969855085692817131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7013045979903390461878087 10519568969855085692817131)
      ·
        refine ⟨15779353454782628539225697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10519568969855085692817131 15779353454782628539225697)
        ·
          refine ⟨11834515091086971404419273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15779353454782628539225697 11834515091086971404419273)
          ·
            refine ⟨8875886318315228553314455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11834515091086971404419273 8875886318315228553314455)
            ·
              refine ⟨13313829477472842829971683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8875886318315228553314455 13313829477472842829971683)
              ·
                refine ⟨19970744216209264244957525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13313829477472842829971683 19970744216209264244957525)
                ·
                  refine ⟨58508039695925578842649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 19970744216209264244957525 58508039695925578842649)
                  ·
                    rfl

theorem cell22_512748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 10].length) (baseStart_512748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_512748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_512748 prefixEnd_512748 := by exact prefixLift 512748
  have htrace : WordTrace (prefixWord ++ tailWord_512748) baseStart_512748 baseEnd_512748 := by
    simpa [prefixWord, tailWord_512748, baseEnd_512748] using wordTrace_append hprefix tailTrace_512748
  have hstable : (prefixWord ++ tailWord_512748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512748).length < 2 ^ (prefixWord ++ tailWord_512748).sum := by decide
  have hdescent : baseEnd_512748 < baseStart_512748 := by decide
  rcases family_descends (prefixWord ++ tailWord_512748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512765 : List Nat := [1, 4, 1, 1, 1, 1, 6, 1, 6]
def baseStart_512765 : Nat := 118140960795 + 512765 * 2 ^ 59
def prefixEnd_512765 : Nat := 4983230072969 + 3 ^ 40 * 512765 * 2
def baseEnd_512765 : Nat := 58509979511731452950965

theorem tailTrace_512765 : CollatzResearch.WordTrace tailWord_512765 prefixEnd_512765 58509979511731452950965 := by
  unfold tailWord_512765
  simp only [CollatzResearch.WordTrace]
  refine ⟨18702075987347453135043749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12468050658231635423362499 18702075987347453135043749)
  ·
    refine ⟨3506639247627647462820703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18702075987347453135043749 3506639247627647462820703)
    ·
      refine ⟨5259958871441471194231055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3506639247627647462820703 5259958871441471194231055)
      ·
        refine ⟨7889938307162206791346583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5259958871441471194231055 7889938307162206791346583)
        ·
          refine ⟨11834907460743310187019875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7889938307162206791346583 11834907460743310187019875)
          ·
            refine ⟨17752361191114965280529813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11834907460743310187019875 17752361191114965280529813)
            ·
              refine ⟨832141930833513997524835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17752361191114965280529813 832141930833513997524835)
              ·
                refine ⟨1248212896250270996287253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 832141930833513997524835 1248212896250270996287253)
                ·
                  refine ⟨58509979511731452950965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1248212896250270996287253 58509979511731452950965)
                  ·
                    rfl

theorem cell22_512765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 1, 6].length) (baseStart_512765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_512765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_512765 prefixEnd_512765 := by exact prefixLift 512765
  have htrace : WordTrace (prefixWord ++ tailWord_512765) baseStart_512765 baseEnd_512765 := by
    simpa [prefixWord, tailWord_512765, baseEnd_512765] using wordTrace_append hprefix tailTrace_512765
  have hstable : (prefixWord ++ tailWord_512765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512765).length < 2 ^ (prefixWord ++ tailWord_512765).sum := by decide
  have hdescent : baseEnd_512765 < baseStart_512765 := by decide
  rcases family_descends (prefixWord ++ tailWord_512765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512799 : List Nat := [1, 1, 2, 4, 2, 4, 1, 3, 4]
def baseStart_512799 : Nat := 118140960795 + 512799 * 2 ^ 59
def prefixEnd_512799 : Nat := 4983230072969 + 3 ^ 40 * 512799 * 2
def baseEnd_512799 : Nat := 58513859143343201167597

theorem tailTrace_512799 : CollatzResearch.WordTrace tailWord_512799 prefixEnd_512799 58513859143343201167597 := by
  unfold tailWord_512799
  simp only [CollatzResearch.WordTrace]
  refine ⟨18703316069224276941781451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12468877379482851294520967 18703316069224276941781451)
  ·
    refine ⟨28054974103836415412672177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18703316069224276941781451 28054974103836415412672177)
    ·
      refine ⟨21041230577877311559504133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28054974103836415412672177 21041230577877311559504133)
      ·
        refine ⟨3945230733351995917407025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21041230577877311559504133 3945230733351995917407025)
        ·
          refine ⟨2958923050013996938055269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3945230733351995917407025 2958923050013996938055269)
          ·
            refine ⟨554798071877624425885363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2958923050013996938055269 554798071877624425885363)
            ·
              refine ⟨832197107816436638828045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 554798071877624425885363 832197107816436638828045)
              ·
                refine ⟨312073915431163739560517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 832197107816436638828045 312073915431163739560517)
                ·
                  refine ⟨58513859143343201167597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 312073915431163739560517 58513859143343201167597)
                  ·
                    rfl

theorem cell22_512799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 3, 4].length) (baseStart_512799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_512799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_512799 prefixEnd_512799 := by exact prefixLift 512799
  have htrace : WordTrace (prefixWord ++ tailWord_512799) baseStart_512799 baseEnd_512799 := by
    simpa [prefixWord, tailWord_512799, baseEnd_512799] using wordTrace_append hprefix tailTrace_512799
  have hstable : (prefixWord ++ tailWord_512799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512799).length < 2 ^ (prefixWord ++ tailWord_512799).sum := by decide
  have hdescent : baseEnd_512799 < baseStart_512799 := by decide
  rcases family_descends (prefixWord ++ tailWord_512799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512814 : List Nat := [4, 1, 3, 2, 1, 1, 2, 1, 4, 3]
def baseStart_512814 : Nat := 118140960795 + 512814 * 2 ^ 59
def prefixEnd_512814 : Nat := 4983230072969 + 3 ^ 40 * 512814 * 2
def baseEnd_512814 : Nat := 175546712236574564377745

theorem tailTrace_512814 : CollatzResearch.WordTrace tailWord_512814 prefixEnd_512814 175546712236574564377745 := by
  unfold tailWord_512814
  simp only [CollatzResearch.WordTrace]
  refine ⟨2337982895521241812947187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12469242109446623002384997 2337982895521241812947187)
  ·
    refine ⟨3506974343281862719420781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2337982895521241812947187 3506974343281862719420781)
    ·
      refine ⟨1315115378730698519782793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3506974343281862719420781 1315115378730698519782793)
      ·
        refine ⟨986336534048023889837095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1315115378730698519782793 986336534048023889837095)
        ·
          refine ⟨1479504801072035834755643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 986336534048023889837095 1479504801072035834755643)
          ·
            refine ⟨2219257201608053752133465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1479504801072035834755643 2219257201608053752133465)
            ·
              refine ⟨1664442901206040314100099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2219257201608053752133465 1664442901206040314100099)
              ·
                refine ⟨2496664351809060471150149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1664442901206040314100099 2496664351809060471150149)
                ·
                  refine ⟨468124565964198838340653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2496664351809060471150149 468124565964198838340653)
                  ·
                    refine ⟨175546712236574564377745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 468124565964198838340653 175546712236574564377745)
                    ·
                      rfl

theorem cell22_512814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_512814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_512814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_512814 prefixEnd_512814 := by exact prefixLift 512814
  have htrace : WordTrace (prefixWord ++ tailWord_512814) baseStart_512814 baseEnd_512814 := by
    simpa [prefixWord, tailWord_512814, baseEnd_512814] using wordTrace_append hprefix tailTrace_512814
  have hstable : (prefixWord ++ tailWord_512814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512814).length < 2 ^ (prefixWord ++ tailWord_512814).sum := by decide
  have hdescent : baseEnd_512814 < baseStart_512814 := by decide
  rcases family_descends (prefixWord ++ tailWord_512814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512831 : List Nat := [1, 1, 2, 2, 5, 3, 2, 1, 2, 3]
def baseStart_512831 : Nat := 118140960795 + 512831 * 2 ^ 59
def prefixEnd_512831 : Nat := 4983230072969 + 3 ^ 40 * 512831 * 2
def baseEnd_512831 : Nat := 175552531683992186702693

theorem tailTrace_512831 : CollatzResearch.WordTrace tailWord_512831 prefixEnd_512831 175552531683992186702693 := by
  unfold tailWord_512831
  simp only [CollatzResearch.WordTrace]
  refine ⟨18704483205108346406946347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12469655470072230937964231 18704483205108346406946347)
  ·
    refine ⟨28056724807662519610419521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18704483205108346406946347 28056724807662519610419521)
    ·
      refine ⟨21042543605746889707814641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28056724807662519610419521 21042543605746889707814641)
      ·
        refine ⟨15781907704310167280860981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21042543605746889707814641 15781907704310167280860981)
        ·
          refine ⟨1479553847279078182580717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15781907704310167280860981 1479553847279078182580717)
          ·
            refine ⟨554832692729654318467769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1479553847279078182580717 554832692729654318467769)
            ·
              refine ⟨416124519547240738850827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 554832692729654318467769 416124519547240738850827)
              ·
                refine ⟨624186779320861108276241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 416124519547240738850827 624186779320861108276241)
                ·
                  refine ⟨468140084490645831207181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 624186779320861108276241 468140084490645831207181)
                  ·
                    refine ⟨175552531683992186702693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 468140084490645831207181 175552531683992186702693)
                    ·
                      rfl

theorem cell22_512831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 2, 1, 2, 3].length) (baseStart_512831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_512831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_512831 prefixEnd_512831 := by exact prefixLift 512831
  have htrace : WordTrace (prefixWord ++ tailWord_512831) baseStart_512831 baseEnd_512831 := by
    simpa [prefixWord, tailWord_512831, baseEnd_512831] using wordTrace_append hprefix tailTrace_512831
  have hstable : (prefixWord ++ tailWord_512831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512831).length < 2 ^ (prefixWord ++ tailWord_512831).sum := by decide
  have hdescent : baseEnd_512831 < baseStart_512831 := by decide
  rcases family_descends (prefixWord ++ tailWord_512831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512872 : List Nat := [2, 1, 4, 2, 1, 2, 1, 4, 5]
def baseStart_512872 : Nat := 118140960795 + 512872 * 2 ^ 59
def prefixEnd_512872 : Nat := 4983230072969 + 3 ^ 40 * 512872 * 2
def baseEnd_512872 : Nat := 58522188940627248809189

theorem tailTrace_512872 : CollatzResearch.WordTrace tailWord_512872 prefixEnd_512872 58522188940627248809189 := by
  unfold tailWord_512872
  simp only [CollatzResearch.WordTrace]
  refine ⟨9352989298979905204594435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12470652398639873606125913 9352989298979905204594435)
  ·
    refine ⟨14029483948469857806891653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9352989298979905204594435 14029483948469857806891653)
    ·
      refine ⟨2630528240338098338792185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14029483948469857806891653 2630528240338098338792185)
      ·
        refine ⟨1972896180253573754094139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2630528240338098338792185 1972896180253573754094139)
        ·
          refine ⟨2959344270380360631141209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1972896180253573754094139 2959344270380360631141209)
          ·
            refine ⟨2219508202785270473355907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2959344270380360631141209 2219508202785270473355907)
            ·
              refine ⟨3329262304177905710033861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2219508202785270473355907 3329262304177905710033861)
              ·
                refine ⟨624236682033357320631349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3329262304177905710033861 624236682033357320631349)
                ·
                  refine ⟨58522188940627248809189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 624236682033357320631349 58522188940627248809189)
                  ·
                    rfl

theorem cell22_512872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 4, 5].length) (baseStart_512872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_512872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_512872 prefixEnd_512872 := by exact prefixLift 512872
  have htrace : WordTrace (prefixWord ++ tailWord_512872) baseStart_512872 baseEnd_512872 := by
    simpa [prefixWord, tailWord_512872, baseEnd_512872] using wordTrace_append hprefix tailTrace_512872
  have hstable : (prefixWord ++ tailWord_512872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512872).length < 2 ^ (prefixWord ++ tailWord_512872).sum := by decide
  have hdescent : baseEnd_512872 < baseStart_512872 := by decide
  rcases family_descends (prefixWord ++ tailWord_512872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512915 : List Nat := [1, 1, 1, 2, 1, 2, 1, 5, 3, 5]
def baseStart_512915 : Nat := 118140960795 + 512915 * 2 ^ 59
def prefixEnd_512915 : Nat := 4983230072969 + 3 ^ 40 * 512915 * 2
def baseEnd_512915 : Nat := 175581286600643967602435

theorem tailTrace_512915 : CollatzResearch.WordTrace tailWord_512915 prefixEnd_512915 175581286600643967602435 := by
  unfold tailWord_512915
  simp only [CollatzResearch.WordTrace]
  refine ⟨18707546936804028753004199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12471697957869352502002799 18707546936804028753004199)
  ·
    refine ⟨28061320405206043129506299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18707546936804028753004199 28061320405206043129506299)
    ·
      refine ⟨42091980607809064694259449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28061320405206043129506299 42091980607809064694259449)
      ·
        refine ⟨31568985455856798520694587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42091980607809064694259449 31568985455856798520694587)
        ·
          refine ⟨47353478183785197781041881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31568985455856798520694587 47353478183785197781041881)
          ·
            refine ⟨35515108637838898335781411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47353478183785197781041881 35515108637838898335781411)
            ·
              refine ⟨53272662956758347503672117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35515108637838898335781411 53272662956758347503672117)
              ·
                refine ⟨4994312152196095078469261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53272662956758347503672117 4994312152196095078469261)
                ·
                  refine ⟨1872867057073535654425973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4994312152196095078469261 1872867057073535654425973)
                  ·
                    refine ⟨175581286600643967602435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1872867057073535654425973 175581286600643967602435)
                    ·
                      rfl

theorem cell22_512915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 3, 5].length) (baseStart_512915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_512915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_512915 prefixEnd_512915 := by exact prefixLift 512915
  have htrace : WordTrace (prefixWord ++ tailWord_512915) baseStart_512915 baseEnd_512915 := by
    simpa [prefixWord, tailWord_512915, baseEnd_512915] using wordTrace_append hprefix tailTrace_512915
  have hstable : (prefixWord ++ tailWord_512915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512915).length < 2 ^ (prefixWord ++ tailWord_512915).sum := by decide
  have hdescent : baseEnd_512915 < baseStart_512915 := by decide
  rcases family_descends (prefixWord ++ tailWord_512915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512968 : List Nat := [2, 1, 3, 1, 6, 1, 1, 3, 4]
def baseStart_512968 : Nat := 118140960795 + 512968 * 2 ^ 59
def prefixEnd_512968 : Nat := 4983230072969 + 3 ^ 40 * 512968 * 2
def baseEnd_512968 : Nat := 58533143194589832009091

theorem tailTrace_512968 : CollatzResearch.WordTrace tailWord_512968 prefixEnd_512968 58533143194589832009091 := by
  unfold tailWord_512968
  simp only [CollatzResearch.WordTrace]
  refine ⟨9354740002806009402341779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12472986670408012536455705 9354740002806009402341779)
  ·
    refine ⟨14032110004209014103512669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9354740002806009402341779 14032110004209014103512669)
    ·
      refine ⟨5262041251578380288817251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14032110004209014103512669 5262041251578380288817251)
      ·
        refine ⟨7893061877367570433225877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5262041251578380288817251 7893061877367570433225877)
        ·
          refine ⟨369987275501604864057463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7893061877367570433225877 369987275501604864057463)
          ·
            refine ⟨554980913252407296086195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369987275501604864057463 554980913252407296086195)
            ·
              refine ⟨832471369878610944129293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 554980913252407296086195 832471369878610944129293)
              ·
                refine ⟨312176763704479104048485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 832471369878610944129293 312176763704479104048485)
                ·
                  refine ⟨58533143194589832009091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 312176763704479104048485 58533143194589832009091)
                  ·
                    rfl

theorem cell22_512968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 3, 4].length) (baseStart_512968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_512968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_512968 prefixEnd_512968 := by exact prefixLift 512968
  have htrace : WordTrace (prefixWord ++ tailWord_512968) baseStart_512968 baseEnd_512968 := by
    simpa [prefixWord, tailWord_512968, baseEnd_512968] using wordTrace_append hprefix tailTrace_512968
  have hstable : (prefixWord ++ tailWord_512968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512968).length < 2 ^ (prefixWord ++ tailWord_512968).sum := by decide
  have hdescent : baseEnd_512968 < baseStart_512968 := by decide
  rcases family_descends (prefixWord ++ tailWord_512968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513045 : List Nat := [1, 3, 2, 1, 4, 3, 2, 2, 1, 3]
def baseStart_513045 : Nat := 118140960795 + 513045 * 2 ^ 59
def prefixEnd_513045 : Nat := 4983230072969 + 3 ^ 40 * 513045 * 2
def baseEnd_513045 : Nat := 175625788257366961852037

theorem tailTrace_513045 : CollatzResearch.WordTrace tailWord_513045 prefixEnd_513045 175625788257366961852037 := by
  unfold tailWord_513045
  simp only [CollatzResearch.WordTrace]
  refine ⟨18712288426333060955236589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12474858950888707303491059 18712288426333060955236589)
  ·
    refine ⟨7017108159874897858213721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18712288426333060955236589 7017108159874897858213721)
    ·
      refine ⟨5262831119906173393660291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7017108159874897858213721 5262831119906173393660291)
      ·
        refine ⟨7894246679859260090490437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5262831119906173393660291 7894246679859260090490437)
        ·
          refine ⟨1480171252473611266966957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7894246679859260090490437 1480171252473611266966957)
          ·
            refine ⟨555064219677604225112609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1480171252473611266966957 555064219677604225112609)
            ·
              refine ⟨416298164758203168834457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 555064219677604225112609 416298164758203168834457)
              ·
                refine ⟨312223623568652376625843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 416298164758203168834457 312223623568652376625843)
                ·
                  refine ⟨468335435352978564938765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 312223623568652376625843 468335435352978564938765)
                  ·
                    refine ⟨175625788257366961852037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 468335435352978564938765 175625788257366961852037)
                    ·
                      rfl

theorem cell22_513045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 2, 2, 1, 3].length) (baseStart_513045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_513045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_513045 prefixEnd_513045 := by exact prefixLift 513045
  have htrace : WordTrace (prefixWord ++ tailWord_513045) baseStart_513045 baseEnd_513045 := by
    simpa [prefixWord, tailWord_513045, baseEnd_513045] using wordTrace_append hprefix tailTrace_513045
  have hstable : (prefixWord ++ tailWord_513045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513045).length < 2 ^ (prefixWord ++ tailWord_513045).sum := by decide
  have hdescent : baseEnd_513045 < baseStart_513045 := by decide
  rcases family_descends (prefixWord ++ tailWord_513045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513056 : List Nat := [2, 1, 1, 7, 1, 1, 1, 1, 2, 5]
def baseStart_513056 : Nat := 118140960795 + 513056 * 2 ^ 59
def prefixEnd_513056 : Nat := 4983230072969 + 3 ^ 40 * 513056 * 2
def baseEnd_513056 : Nat := 175629553782166599827003

theorem tailTrace_513056 : CollatzResearch.WordTrace tailWord_513056 prefixEnd_513056 175629553782166599827003 := by
  unfold tailWord_513056
  simp only [CollatzResearch.WordTrace]
  refine ⟨9356344814646604916943511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12475126419528806555924681 9356344814646604916943511)
  ·
    refine ⟨14034517221969907375415267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9356344814646604916943511 14034517221969907375415267)
    ·
      refine ⟨21051775832954861063122901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14034517221969907375415267 21051775832954861063122901)
      ·
        refine ⟨493400996084879556166943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 21051775832954861063122901 493400996084879556166943)
        ·
          refine ⟨740101494127319334250415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493400996084879556166943 740101494127319334250415)
          ·
            refine ⟨1110152241190979001375623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 740101494127319334250415 1110152241190979001375623)
            ·
              refine ⟨1665228361786468502063435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1110152241190979001375623 1665228361786468502063435)
              ·
                refine ⟨2497842542679702753095153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1665228361786468502063435 2497842542679702753095153)
                ·
                  refine ⟨1873381907009777064821365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2497842542679702753095153 1873381907009777064821365)
                  ·
                    refine ⟨175629553782166599827003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1873381907009777064821365 175629553782166599827003)
                    ·
                      rfl

theorem cell22_513056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 2, 5].length) (baseStart_513056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_513056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_513056 prefixEnd_513056 := by exact prefixLift 513056
  have htrace : WordTrace (prefixWord ++ tailWord_513056) baseStart_513056 baseEnd_513056 := by
    simpa [prefixWord, tailWord_513056, baseEnd_513056] using wordTrace_append hprefix tailTrace_513056
  have hstable : (prefixWord ++ tailWord_513056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513056).length < 2 ^ (prefixWord ++ tailWord_513056).sum := by decide
  have hdescent : baseEnd_513056 < baseStart_513056 := by decide
  rcases family_descends (prefixWord ++ tailWord_513056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513084 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 1, 5]
def baseStart_513084 : Nat := 118140960795 + 513084 * 2 ^ 59
def prefixEnd_513084 : Nat := 4983230072969 + 3 ^ 40 * 513084 * 2
def baseEnd_513084 : Nat := 175639138754383860126917

theorem tailTrace_513084 : CollatzResearch.WordTrace tailWord_513084 prefixEnd_513084 175639138754383860126917 := by
  unfold tailWord_513084
  simp only [CollatzResearch.WordTrace]
  refine ⟨9356855436595885307953153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12475807248794513743937537 9356855436595885307953153)
  ·
    refine ⟨7017641577446913980964865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9356855436595885307953153 7017641577446913980964865)
    ·
      refine ⟨5263231183085185485723649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7017641577446913980964865 5263231183085185485723649)
      ·
        refine ⟨3947423387313889114292737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5263231183085185485723649 3947423387313889114292737)
        ·
          refine ⟨2960567540485416835719553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3947423387313889114292737 2960567540485416835719553)
          ·
            refine ⟨2220425655364062626789665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2960567540485416835719553 2220425655364062626789665)
            ·
              refine ⟨1665319241523046970092249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2220425655364062626789665 1665319241523046970092249)
              ·
                refine ⟨1248989431142285227569187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1665319241523046970092249 1248989431142285227569187)
                ·
                  refine ⟨1873484146713427841353781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1248989431142285227569187 1873484146713427841353781)
                  ·
                    refine ⟨175639138754383860126917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1873484146713427841353781 175639138754383860126917)
                    ·
                      rfl

theorem cell22_513084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 1, 5].length) (baseStart_513084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_513084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_513084 prefixEnd_513084 := by exact prefixLift 513084
  have htrace : WordTrace (prefixWord ++ tailWord_513084) baseStart_513084 baseEnd_513084 := by
    simpa [prefixWord, tailWord_513084, baseEnd_513084] using wordTrace_append hprefix tailTrace_513084
  have hstable : (prefixWord ++ tailWord_513084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513084).length < 2 ^ (prefixWord ++ tailWord_513084).sum := by decide
  have hdescent : baseEnd_513084 < baseStart_513084 := by decide
  rcases family_descends (prefixWord ++ tailWord_513084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513159 : List Nat := [1, 1, 4, 2, 1, 1, 1, 6, 5]
def baseStart_513159 : Nat := 118140960795 + 513159 * 2 ^ 59
def prefixEnd_513159 : Nat := 4983230072969 + 3 ^ 40 * 513159 * 2
def baseEnd_513159 : Nat := 58554937595702888167229

theorem tailTrace_513159 : CollatzResearch.WordTrace tailWord_513159 prefixEnd_513159 58554937595702888167229 := by
  unfold tailWord_513159
  simp only [CollatzResearch.WordTrace]
  refine ⟨18716446347920058424886531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12477630898613372283257687 18716446347920058424886531)
  ·
    refine ⟨28074669521880087637329797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18716446347920058424886531 28074669521880087637329797)
    ·
      refine ⟨5264000535352516431999337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28074669521880087637329797 5264000535352516431999337)
      ·
        refine ⟨3948000401514387323999503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5264000535352516431999337 3948000401514387323999503)
        ·
          refine ⟨5922000602271580985999255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3948000401514387323999503 5922000602271580985999255)
          ·
            refine ⟨8883000903407371478998883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5922000602271580985999255 8883000903407371478998883)
            ·
              refine ⟨13324501355111057218498325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8883000903407371478998883 13324501355111057218498325)
              ·
                refine ⟨624586001020830807117109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13324501355111057218498325 624586001020830807117109)
                ·
                  refine ⟨58554937595702888167229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 624586001020830807117109 58554937595702888167229)
                  ·
                    rfl

theorem cell22_513159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 6, 5].length) (baseStart_513159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_513159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_513159 prefixEnd_513159 := by exact prefixLift 513159
  have htrace : WordTrace (prefixWord ++ tailWord_513159) baseStart_513159 baseEnd_513159 := by
    simpa [prefixWord, tailWord_513159, baseEnd_513159] using wordTrace_append hprefix tailTrace_513159
  have hstable : (prefixWord ++ tailWord_513159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513159).length < 2 ^ (prefixWord ++ tailWord_513159).sum := by decide
  have hdescent : baseEnd_513159 < baseStart_513159 := by decide
  rcases family_descends (prefixWord ++ tailWord_513159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513176 : List Nat := [2, 1, 2, 4, 2, 2, 1, 3, 5]
def baseStart_513176 : Nat := 118140960795 + 513176 * 2 ^ 59
def prefixEnd_513176 : Nat := 4983230072969 + 3 ^ 40 * 513176 * 2
def baseEnd_513176 : Nat := 58556877411508762275545

theorem tailTrace_513176 : CollatzResearch.WordTrace tailWord_513176 prefixEnd_513176 58556877411508762275545 := by
  unfold tailWord_513176
  simp only [CollatzResearch.WordTrace]
  refine ⟨9358533194429235164127691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12478044259238980218836921 9358533194429235164127691)
  ·
    refine ⟨14037799791643852746191537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9358533194429235164127691 14037799791643852746191537)
    ·
      refine ⟨10528349843732889559643653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14037799791643852746191537 10528349843732889559643653)
      ·
        refine ⟨1974065595699916792433185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10528349843732889559643653 1974065595699916792433185)
        ·
          refine ⟨1480549196774937594324889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1974065595699916792433185 1480549196774937594324889)
          ·
            refine ⟨1110411897581203195743667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1480549196774937594324889 1110411897581203195743667)
            ·
              refine ⟨1665617846371804793615501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1110411897581203195743667 1665617846371804793615501)
              ·
                refine ⟨624606692389426797605813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1665617846371804793615501 624606692389426797605813)
                ·
                  refine ⟨58556877411508762275545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 624606692389426797605813 58556877411508762275545)
                  ·
                    rfl

theorem cell22_513176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 3, 5].length) (baseStart_513176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_513176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_513176 prefixEnd_513176 := by exact prefixLift 513176
  have htrace : WordTrace (prefixWord ++ tailWord_513176) baseStart_513176 baseEnd_513176 := by
    simpa [prefixWord, tailWord_513176, baseEnd_513176] using wordTrace_append hprefix tailTrace_513176
  have hstable : (prefixWord ++ tailWord_513176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513176).length < 2 ^ (prefixWord ++ tailWord_513176).sum := by decide
  have hdescent : baseEnd_513176 < baseStart_513176 := by decide
  rcases family_descends (prefixWord ++ tailWord_513176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513255 : List Nat := [1, 1, 5, 3, 2, 1, 2, 3, 4]
def baseStart_513255 : Nat := 118140960795 + 513255 * 2 ^ 59
def prefixEnd_513255 : Nat := 4983230072969 + 3 ^ 40 * 513255 * 2
def baseEnd_513255 : Nat := 58565891849665471367131

theorem tailTrace_513255 : CollatzResearch.WordTrace tailWord_513255 prefixEnd_513255 58565891849665471367131 := by
  unfold tailWord_513255
  simp only [CollatzResearch.WordTrace]
  refine ⟨18719947755572266820381219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12479965170381511213587479 18719947755572266820381219)
  ·
    refine ⟨28079921633358400230571829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18719947755572266820381219 28079921633358400230571829)
    ·
      refine ⟨2632492653127350021616109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28079921633358400230571829 2632492653127350021616109)
      ·
        refine ⟨987184744922756258106041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2632492653127350021616109 987184744922756258106041)
        ·
          refine ⟨740388558692067193579531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 987184744922756258106041 740388558692067193579531)
          ·
            refine ⟨1110582838038100790369297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 740388558692067193579531 1110582838038100790369297)
            ·
              refine ⟨832937128528575592776973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1110582838038100790369297 832937128528575592776973)
              ·
                refine ⟨312351423198215847291365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 832937128528575592776973 312351423198215847291365)
                ·
                  refine ⟨58565891849665471367131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 312351423198215847291365 58565891849665471367131)
                  ·
                    rfl

theorem cell22_513255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 3, 4].length) (baseStart_513255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_513255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_513255 prefixEnd_513255 := by exact prefixLift 513255
  have htrace : WordTrace (prefixWord ++ tailWord_513255) baseStart_513255 baseEnd_513255 := by
    simpa [prefixWord, tailWord_513255, baseEnd_513255] using wordTrace_append hprefix tailTrace_513255
  have hstable : (prefixWord ++ tailWord_513255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513255).length < 2 ^ (prefixWord ++ tailWord_513255).sum := by decide
  have hdescent : baseEnd_513255 < baseStart_513255 := by decide
  rcases family_descends (prefixWord ++ tailWord_513255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513266 : List Nat := [3, 2, 1, 3, 3, 1, 9]
def baseStart_513266 : Nat := 118140960795 + 513266 * 2 ^ 59
def prefixEnd_513266 : Nat := 4983230072969 + 3 ^ 40 * 513266 * 2
def baseEnd_513266 : Nat := 6507460780510964891717

theorem tailTrace_513266 : CollatzResearch.WordTrace tailWord_513266 prefixEnd_513266 6507460780510964891717 := by
  unfold tailWord_513266
  simp only [CollatzResearch.WordTrace]
  refine ⟨4680087239633103924757913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12480232639021610466021101 4680087239633103924757913)
  ·
    refine ⟨3510065429724827943568435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4680087239633103924757913 3510065429724827943568435)
    ·
      refine ⟨5265098144587241915352653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3510065429724827943568435 5265098144587241915352653)
      ·
        refine ⟨1974411804220215718257245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5265098144587241915352653 1974411804220215718257245)
        ·
          refine ⟨740404426582580894346467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1974411804220215718257245 740404426582580894346467)
          ·
            refine ⟨1110606639873871341519701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 740404426582580894346467 1110606639873871341519701)
            ·
              refine ⟨6507460780510964891717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1110606639873871341519701 6507460780510964891717)
              ·
                rfl

theorem cell22_513266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 9].length) (baseStart_513266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_513266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_513266 prefixEnd_513266 := by exact prefixLift 513266
  have htrace : WordTrace (prefixWord ++ tailWord_513266) baseStart_513266 baseEnd_513266 := by
    simpa [prefixWord, tailWord_513266, baseEnd_513266] using wordTrace_append hprefix tailTrace_513266
  have hstable : (prefixWord ++ tailWord_513266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513266).length < 2 ^ (prefixWord ++ tailWord_513266).sum := by decide
  have hdescent : baseEnd_513266 < baseStart_513266 := by decide
  rcases family_descends (prefixWord ++ tailWord_513266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513315 : List Nat := [1, 1, 1, 4, 2, 3, 3, 3, 1, 3]
def baseStart_513315 : Nat := 118140960795 + 513315 * 2 ^ 59
def prefixEnd_513315 : Nat := 4983230072969 + 3 ^ 40 * 513315 * 2
def baseEnd_513315 : Nat := 175718214775176257601209

theorem tailTrace_513315 : CollatzResearch.WordTrace tailWord_513315 prefixEnd_513315 175718214775176257601209 := by
  unfold tailWord_513315
  simp only [CollatzResearch.WordTrace]
  refine ⟨18722136135354897067565399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12481424090236598045043599 18722136135354897067565399)
  ·
    refine ⟨28083204203032345601348099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18722136135354897067565399 28083204203032345601348099)
    ·
      refine ⟨42124806304548518402022149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28083204203032345601348099 42124806304548518402022149)
      ·
        refine ⟨7898401182102847200379153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42124806304548518402022149 7898401182102847200379153)
        ·
          refine ⟨5923800886577135400284365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7898401182102847200379153 5923800886577135400284365)
          ·
            refine ⟨2221425332466425775106637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5923800886577135400284365 2221425332466425775106637)
            ·
              refine ⟨833034499674909665664989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2221425332466425775106637 833034499674909665664989)
              ·
                refine ⟨312387937378091124624371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 833034499674909665664989 312387937378091124624371)
                ·
                  refine ⟨468581906067136686936557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 312387937378091124624371 468581906067136686936557)
                  ·
                    refine ⟨175718214775176257601209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 468581906067136686936557 175718214775176257601209)
                    ·
                      rfl

theorem cell22_513315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 3, 1, 3].length) (baseStart_513315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_513315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_513315 prefixEnd_513315 := by exact prefixLift 513315
  have htrace : WordTrace (prefixWord ++ tailWord_513315) baseStart_513315 baseEnd_513315 := by
    simpa [prefixWord, tailWord_513315, baseEnd_513315] using wordTrace_append hprefix tailTrace_513315
  have hstable : (prefixWord ++ tailWord_513315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513315).length < 2 ^ (prefixWord ++ tailWord_513315).sum := by decide
  have hdescent : baseEnd_513315 < baseStart_513315 := by decide
  rcases family_descends (prefixWord ++ tailWord_513315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513345 : List Nat := [1, 2, 5, 2, 1, 1, 4, 1, 5]
def baseStart_513345 : Nat := 118140960795 + 513345 * 2 ^ 59
def prefixEnd_513345 : Nat := 4983230072969 + 3 ^ 40 * 513345 * 2
def baseEnd_513345 : Nat := 58576161462755393117039

theorem tailTrace_513345 : CollatzResearch.WordTrace tailWord_513345 prefixEnd_513345 58576161462755393117039 := by
  unfold tailWord_513345
  simp only [CollatzResearch.WordTrace]
  refine ⟨18723230325246212191157489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12482153550164141460771659 18723230325246212191157489)
  ·
    refine ⟨14042422743934659143368117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18723230325246212191157489 14042422743934659143368117)
    ·
      refine ⟨1316477132243874294690761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14042422743934659143368117 1316477132243874294690761)
      ·
        refine ⟨987357849182905721018071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1316477132243874294690761 987357849182905721018071)
        ·
          refine ⟨1481036773774358581527107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 987357849182905721018071 1481036773774358581527107)
          ·
            refine ⟨2221555160661537872290661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1481036773774358581527107 2221555160661537872290661)
            ·
              refine ⟨416541592624038351054499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2221555160661537872290661 416541592624038351054499)
              ·
                refine ⟨624812388936057526581749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 416541592624038351054499 624812388936057526581749)
                ·
                  refine ⟨58576161462755393117039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 624812388936057526581749 58576161462755393117039)
                  ·
                    rfl

theorem cell22_513345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 4, 1, 5].length) (baseStart_513345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_513345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_513345 prefixEnd_513345 := by exact prefixLift 513345
  have htrace : WordTrace (prefixWord ++ tailWord_513345) baseStart_513345 baseEnd_513345 := by
    simpa [prefixWord, tailWord_513345, baseEnd_513345] using wordTrace_append hprefix tailTrace_513345
  have hstable : (prefixWord ++ tailWord_513345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513345).length < 2 ^ (prefixWord ++ tailWord_513345).sum := by decide
  have hdescent : baseEnd_513345 < baseStart_513345 := by decide
  rcases family_descends (prefixWord ++ tailWord_513345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513401 : List Nat := [1, 2, 1, 3, 2, 1, 5, 7]
def baseStart_513401 : Nat := 118140960795 + 513401 * 2 ^ 59
def prefixEnd_513401 : Nat := 4983230072969 + 3 ^ 40 * 513401 * 2
def baseEnd_513401 : Nat := 19527517148077855550105

theorem tailTrace_513401 : CollatzResearch.WordTrace tailWord_513401 prefixEnd_513401 19527517148077855550105 := by
  unfold tailWord_513401
  simp only [CollatzResearch.WordTrace]
  refine ⟨18725272813043333755196057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12483515208695555836797371 18725272813043333755196057)
  ·
    refine ⟨14043954609782500316397043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18725272813043333755196057 14043954609782500316397043)
    ·
      refine ⟨21065931914673750474595565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14043954609782500316397043 21065931914673750474595565)
      ·
        refine ⟨7899724468002656427973337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21065931914673750474595565 7899724468002656427973337)
        ·
          refine ⟨5924793351001992320980003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7899724468002656427973337 5924793351001992320980003)
          ·
            refine ⟨8887190026502988481470005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5924793351001992320980003 8887190026502988481470005)
            ·
              refine ⟨833174064984655170137813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8887190026502988481470005 833174064984655170137813)
              ·
                refine ⟨19527517148077855550105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 833174064984655170137813 19527517148077855550105)
                ·
                  rfl

theorem cell22_513401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 7].length) (baseStart_513401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_513401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_513401 prefixEnd_513401 := by exact prefixLift 513401
  have htrace : WordTrace (prefixWord ++ tailWord_513401) baseStart_513401 baseEnd_513401 := by
    simpa [prefixWord, tailWord_513401, baseEnd_513401] using wordTrace_append hprefix tailTrace_513401
  have hstable : (prefixWord ++ tailWord_513401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513401).length < 2 ^ (prefixWord ++ tailWord_513401).sum := by decide
  have hdescent : baseEnd_513401 < baseStart_513401 := by decide
  rcases family_descends (prefixWord ++ tailWord_513401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513426 : List Nat := [3, 2, 3, 3, 2, 1, 2, 1, 1, 4]
def baseStart_513426 : Nat := 118140960795 + 513426 * 2 ^ 59
def prefixEnd_513426 : Nat := 4983230072969 + 3 ^ 40 * 513426 * 2
def baseEnd_513426 : Nat := 175756212343608968075869

theorem tailTrace_513426 : CollatzResearch.WordTrace tailWord_513426 prefixEnd_513426 175756212343608968075869 := by
  unfold tailWord_513426
  simp only [CollatzResearch.WordTrace]
  refine ⟨4681546159488190756214033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12484123091968508683237421 4681546159488190756214033)
  ·
    refine ⟨3511159619616143067160525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4681546159488190756214033 3511159619616143067160525)
    ·
      refine ⟨1316684857356053650185197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3511159619616143067160525 1316684857356053650185197)
      ·
        refine ⟨493756821508520118819449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1316684857356053650185197 493756821508520118819449)
        ·
          refine ⟨370317616131390089114587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 493756821508520118819449 370317616131390089114587)
          ·
            refine ⟨555476424197085133671881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370317616131390089114587 555476424197085133671881)
            ·
              refine ⟨416607318147813850253911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 555476424197085133671881 416607318147813850253911)
              ·
                refine ⟨624910977221720775380867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 416607318147813850253911 624910977221720775380867)
                ·
                  refine ⟨937366465832581163071301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 624910977221720775380867 937366465832581163071301)
                  ·
                    refine ⟨175756212343608968075869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 937366465832581163071301 175756212343608968075869)
                    ·
                      rfl

theorem cell22_513426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_513426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_513426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_513426 prefixEnd_513426 := by exact prefixLift 513426
  have htrace : WordTrace (prefixWord ++ tailWord_513426) baseStart_513426 baseEnd_513426 := by
    simpa [prefixWord, tailWord_513426, baseEnd_513426] using wordTrace_append hprefix tailTrace_513426
  have hstable : (prefixWord ++ tailWord_513426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513426).length < 2 ^ (prefixWord ++ tailWord_513426).sum := by decide
  have hdescent : baseEnd_513426 < baseStart_513426 := by decide
  rcases family_descends (prefixWord ++ tailWord_513426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513484 : List Nat := [2, 2, 1, 4, 2, 3, 1, 3, 1, 3]
def baseStart_513484 : Nat := 118140960795 + 513484 * 2 ^ 59
def prefixEnd_513484 : Nat := 4983230072969 + 3 ^ 40 * 513484 * 2
def baseEnd_513484 : Nat := 175776066928916150125691

theorem tailTrace_513484 : CollatzResearch.WordTrace tailWord_513484 prefixEnd_513484 175776066928916150125691 := by
  unfold tailWord_513484
  simp only [CollatzResearch.WordTrace]
  refine ⟨9364150035871319465233753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12485533381161759286978337 9364150035871319465233753)
  ·
    refine ⟨7023112526903489598925315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9364150035871319465233753 7023112526903489598925315)
    ·
      refine ⟨10534668790355234398387973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7023112526903489598925315 10534668790355234398387973)
      ·
        refine ⟨1975250398191606449697745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10534668790355234398387973 1975250398191606449697745)
        ·
          refine ⟨1481437798643704837273309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1975250398191606449697745 1481437798643704837273309)
          ·
            refine ⟨555539174491389313977491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1481437798643704837273309 555539174491389313977491)
            ·
              refine ⟨833308761737083970966237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 555539174491389313977491 833308761737083970966237)
              ·
                refine ⟨312490785651406489112339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 833308761737083970966237 312490785651406489112339)
                ·
                  refine ⟨468736178477109733668509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 312490785651406489112339 468736178477109733668509)
                  ·
                    refine ⟨175776066928916150125691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 468736178477109733668509 175776066928916150125691)
                    ·
                      rfl

theorem cell22_513484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 3, 1, 3].length) (baseStart_513484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_513484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_513484 prefixEnd_513484 := by exact prefixLift 513484
  have htrace : WordTrace (prefixWord ++ tailWord_513484) baseStart_513484 baseEnd_513484 := by
    simpa [prefixWord, tailWord_513484, baseEnd_513484] using wordTrace_append hprefix tailTrace_513484
  have hstable : (prefixWord ++ tailWord_513484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513484).length < 2 ^ (prefixWord ++ tailWord_513484).sum := by decide
  have hdescent : baseEnd_513484 < baseStart_513484 := by decide
  rcases family_descends (prefixWord ++ tailWord_513484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513514 : List Nat := [3, 1, 3, 1, 5, 1, 2, 1, 5]
def baseStart_513514 : Nat := 118140960795 + 513514 * 2 ^ 59
def prefixEnd_513514 : Nat := 4983230072969 + 3 ^ 40 * 513514 * 2
def baseEnd_513514 : Nat := 58595445514002023958533

theorem tailTrace_513514 : CollatzResearch.WordTrace tailWord_513514 prefixEnd_513514 58595445514002023958533 := by
  unfold tailWord_513514
  simp only [CollatzResearch.WordTrace]
  refine ⟨4682348565408488513514899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12486262841089302702706397 4682348565408488513514899)
  ·
    refine ⟨7023522848112732770272349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4682348565408488513514899 7023522848112732770272349)
    ·
      refine ⟨2633821068042274788852131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7023522848112732770272349 2633821068042274788852131)
      ·
        refine ⟨3950731602063412183278197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2633821068042274788852131 3950731602063412183278197)
        ·
          refine ⟨370381087693444892182331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3950731602063412183278197 370381087693444892182331)
          ·
            refine ⟨555571631540167338273497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370381087693444892182331 555571631540167338273497)
            ·
              refine ⟨416678723655125503705123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 555571631540167338273497 416678723655125503705123)
              ·
                refine ⟨625018085482688255557685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 416678723655125503705123 625018085482688255557685)
                ·
                  refine ⟨58595445514002023958533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 625018085482688255557685 58595445514002023958533)
                  ·
                    rfl

theorem cell22_513514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 2, 1, 5].length) (baseStart_513514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_513514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_513514 prefixEnd_513514 := by exact prefixLift 513514
  have htrace : WordTrace (prefixWord ++ tailWord_513514) baseStart_513514 baseEnd_513514 := by
    simpa [prefixWord, tailWord_513514, baseEnd_513514] using wordTrace_append hprefix tailTrace_513514
  have hstable : (prefixWord ++ tailWord_513514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513514).length < 2 ^ (prefixWord ++ tailWord_513514).sum := by decide
  have hdescent : baseEnd_513514 < baseStart_513514 := by decide
  rcases family_descends (prefixWord ++ tailWord_513514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513523 : List Nat := [1, 1, 1, 2, 2, 2, 2, 2, 6, 3]
def baseStart_513523 : Nat := 118140960795 + 513523 * 2 ^ 59
def prefixEnd_513523 : Nat := 4983230072969 + 3 ^ 40 * 513523 * 2
def baseEnd_513523 : Nat := 175789417425933048400571

theorem tailTrace_513523 : CollatzResearch.WordTrace tailWord_513523 prefixEnd_513523 175789417425933048400571 := by
  unfold tailWord_513523
  simp only [CollatzResearch.WordTrace]
  refine ⟨18729722518601348591137223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12486481679067565727424815 18729722518601348591137223)
  ·
    refine ⟨28094583777902022886705835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18729722518601348591137223 28094583777902022886705835)
    ·
      refine ⟨42141875666853034330058753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28094583777902022886705835 42141875666853034330058753)
      ·
        refine ⟨31606406750139775747544065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42141875666853034330058753 31606406750139775747544065)
        ·
          refine ⟨23704805062604831810658049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31606406750139775747544065 23704805062604831810658049)
          ·
            refine ⟨17778603796953623857993537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23704805062604831810658049 17778603796953623857993537)
            ·
              refine ⟨13333952847715217893495153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17778603796953623857993537 13333952847715217893495153)
              ·
                refine ⟨10000464635786413420121365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13333952847715217893495153 10000464635786413420121365)
                ·
                  refine ⟨468771779802488129068189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10000464635786413420121365 468771779802488129068189)
                  ·
                    refine ⟨175789417425933048400571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 468771779802488129068189 175789417425933048400571)
                    ·
                      rfl

theorem cell22_513523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 6, 3].length) (baseStart_513523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_513523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_513523 prefixEnd_513523 := by exact prefixLift 513523
  have htrace : WordTrace (prefixWord ++ tailWord_513523) baseStart_513523 baseEnd_513523 := by
    simpa [prefixWord, tailWord_513523, baseEnd_513523] using wordTrace_append hprefix tailTrace_513523
  have hstable : (prefixWord ++ tailWord_513523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513523).length < 2 ^ (prefixWord ++ tailWord_513523).sum := by decide
  have hdescent : baseEnd_513523 < baseStart_513523 := by decide
  rcases family_descends (prefixWord ++ tailWord_513523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513557 : List Nat := [1, 3, 2, 1, 3, 3, 2, 2, 2, 3]
def baseStart_513557 : Nat := 118140960795 + 513557 * 2 ^ 59
def prefixEnd_513557 : Nat := 4983230072969 + 3 ^ 40 * 513557 * 2
def baseEnd_513557 : Nat := 175801056320768293050467

theorem tailTrace_513557 : CollatzResearch.WordTrace tailWord_513557 prefixEnd_513557 175801056320768293050467 := by
  unfold tailWord_513557
  simp only [CollatzResearch.WordTrace]
  refine ⟨18730962600478172397874925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12487308400318781598583283 18730962600478172397874925)
  ·
    refine ⟨7024110975179314649203097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18730962600478172397874925 7024110975179314649203097)
    ·
      refine ⟨5268083231384485986902323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7024110975179314649203097 5268083231384485986902323)
      ·
        refine ⟨7902124847076728980353485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5268083231384485986902323 7902124847076728980353485)
        ·
          refine ⟨2963296817653773367632557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7902124847076728980353485 2963296817653773367632557)
          ·
            refine ⟨1111236306620165012862209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2963296817653773367632557 1111236306620165012862209)
            ·
              refine ⟨833427229965123759646657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1111236306620165012862209 833427229965123759646657)
              ·
                refine ⟨625070422473842819734993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 833427229965123759646657 625070422473842819734993)
                ·
                  refine ⟨468802816855382114801245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 625070422473842819734993 468802816855382114801245)
                  ·
                    refine ⟨175801056320768293050467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 468802816855382114801245 175801056320768293050467)
                    ·
                      rfl

theorem cell22_513557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 2, 2, 3].length) (baseStart_513557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_513557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_513557 prefixEnd_513557 := by exact prefixLift 513557
  have htrace : WordTrace (prefixWord ++ tailWord_513557) baseStart_513557 baseEnd_513557 := by
    simpa [prefixWord, tailWord_513557, baseEnd_513557] using wordTrace_append hprefix tailTrace_513557
  have hstable : (prefixWord ++ tailWord_513557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513557).length < 2 ^ (prefixWord ++ tailWord_513557).sum := by decide
  have hdescent : baseEnd_513557 < baseStart_513557 := by decide
  rcases family_descends (prefixWord ++ tailWord_513557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513675 : List Nat := [1, 1, 1, 1, 4, 1, 3, 3, 4, 3]
def baseStart_513675 : Nat := 118140960795 + 513675 * 2 ^ 59
def prefixEnd_513675 : Nat := 4983230072969 + 3 ^ 40 * 513675 * 2
def baseEnd_513675 : Nat := 175841450132255318600105

theorem tailTrace_513675 : CollatzResearch.WordTrace tailWord_513675 prefixEnd_513675 175841450132255318600105 := by
  unfold tailWord_513675
  simp only [CollatzResearch.WordTrace]
  refine ⟨18735266414050678550670479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12490177609367119033780319 18735266414050678550670479)
  ·
    refine ⟨28102899621076017826005719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18735266414050678550670479 28102899621076017826005719)
    ·
      refine ⟨42154349431614026739008579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28102899621076017826005719 42154349431614026739008579)
      ·
        refine ⟨63231524147421040108512869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42154349431614026739008579 63231524147421040108512869)
        ·
          refine ⟨11855910777641445020346163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63231524147421040108512869 11855910777641445020346163)
          ·
            refine ⟨17783866166462167530519245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11855910777641445020346163 17783866166462167530519245)
            ·
              refine ⟨6668949812423312823944717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17783866166462167530519245 6668949812423312823944717)
              ·
                refine ⟨2500856179658742308979269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6668949812423312823944717 2500856179658742308979269)
                ·
                  refine ⟨468910533686014182933613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2500856179658742308979269 468910533686014182933613)
                  ·
                    refine ⟨175841450132255318600105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 468910533686014182933613 175841450132255318600105)
                    ·
                      rfl

theorem cell22_513675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 4, 3].length) (baseStart_513675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_513675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_513675 prefixEnd_513675 := by exact prefixLift 513675
  have htrace : WordTrace (prefixWord ++ tailWord_513675) baseStart_513675 baseEnd_513675 := by
    simpa [prefixWord, tailWord_513675, baseEnd_513675] using wordTrace_append hprefix tailTrace_513675
  have hstable : (prefixWord ++ tailWord_513675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513675).length < 2 ^ (prefixWord ++ tailWord_513675).sum := by decide
  have hdescent : baseEnd_513675 < baseStart_513675 := by decide
  rcases family_descends (prefixWord ++ tailWord_513675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513765 : List Nat := [1, 3, 1, 4, 1, 1, 1, 2, 1, 7]
def baseStart_513765 : Nat := 118140960795 + 513765 * 2 ^ 59
def prefixEnd_513765 : Nat := 4983230072969 + 3 ^ 40 * 513765 * 2
def baseEnd_513765 : Nat := 175872258971525083849829

theorem tailTrace_513765 : CollatzResearch.WordTrace tailWord_513765 prefixEnd_513765 175872258971525083849829 := by
  unfold tailWord_513765
  simp only [CollatzResearch.WordTrace]
  refine ⟨18738548983724623921446749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12492365989149749280964499 18738548983724623921446749)
  ·
    refine ⟨7026955868896733970542531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18738548983724623921446749 7026955868896733970542531)
    ·
      refine ⟨10540433803345100955813797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7026955868896733970542531 10540433803345100955813797)
      ·
        refine ⟨1976331338127206429215087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10540433803345100955813797 1976331338127206429215087)
        ·
          refine ⟨2964497007190809643822631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1976331338127206429215087 2964497007190809643822631)
          ·
            refine ⟨4446745510786214465733947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2964497007190809643822631 4446745510786214465733947)
            ·
              refine ⟨6670118266179321698600921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4446745510786214465733947 6670118266179321698600921)
              ·
                refine ⟨5002588699634491273950691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6670118266179321698600921 5002588699634491273950691)
                ·
                  refine ⟨7503883049451736910926037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5002588699634491273950691 7503883049451736910926037)
                  ·
                    refine ⟨175872258971525083849829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7503883049451736910926037 175872258971525083849829)
                    ·
                      rfl

theorem cell22_513765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 7].length) (baseStart_513765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_513765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_513765 prefixEnd_513765 := by exact prefixLift 513765
  have htrace : WordTrace (prefixWord ++ tailWord_513765) baseStart_513765 baseEnd_513765 := by
    simpa [prefixWord, tailWord_513765, baseEnd_513765] using wordTrace_append hprefix tailTrace_513765
  have hstable : (prefixWord ++ tailWord_513765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513765).length < 2 ^ (prefixWord ++ tailWord_513765).sum := by decide
  have hdescent : baseEnd_513765 < baseStart_513765 := by decide
  rcases family_descends (prefixWord ++ tailWord_513765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513782 : List Nat := [5, 1, 1, 1, 1, 3, 1, 2, 2, 5]
def baseStart_513782 : Nat := 118140960795 + 513782 * 2 ^ 59
def prefixEnd_513782 : Nat := 4983230072969 + 3 ^ 40 * 513782 * 2
def baseEnd_513782 : Nat := 175878078418942706174777

theorem tailTrace_513782 : CollatzResearch.WordTrace tailWord_513782 prefixEnd_513782 175878078418942706174777 := by
  unfold tailWord_513782
  simp only [CollatzResearch.WordTrace]
  refine ⟨1171198064041439739050975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12492779349775357216543733 1171198064041439739050975)
  ·
    refine ⟨1756797096062159608576463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1171198064041439739050975 1756797096062159608576463)
    ·
      refine ⟨2635195644093239412864695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1756797096062159608576463 2635195644093239412864695)
      ·
        refine ⟨3952793466139859119297043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2635195644093239412864695 3952793466139859119297043)
        ·
          refine ⟨5929190199209788678945565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3952793466139859119297043 5929190199209788678945565)
          ·
            refine ⟨2223446324703670754604587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5929190199209788678945565 2223446324703670754604587)
            ·
              refine ⟨3335169487055506131906881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2223446324703670754604587 3335169487055506131906881)
              ·
                refine ⟨2501377115291629598930161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3335169487055506131906881 2501377115291629598930161)
                ·
                  refine ⟨1876032836468722199197621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2501377115291629598930161 1876032836468722199197621)
                  ·
                    refine ⟨175878078418942706174777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1876032836468722199197621 175878078418942706174777)
                    ·
                      rfl

theorem cell22_513782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_513782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_513782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_513782 prefixEnd_513782 := by exact prefixLift 513782
  have htrace : WordTrace (prefixWord ++ tailWord_513782) baseStart_513782 baseEnd_513782 := by
    simpa [prefixWord, tailWord_513782, baseEnd_513782] using wordTrace_append hprefix tailTrace_513782
  have hstable : (prefixWord ++ tailWord_513782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513782).length < 2 ^ (prefixWord ++ tailWord_513782).sum := by decide
  have hdescent : baseEnd_513782 < baseStart_513782 := by decide
  rcases family_descends (prefixWord ++ tailWord_513782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513795 : List Nat := [1, 1, 1, 3, 2, 2, 3, 3, 6]
def baseStart_513795 : Nat := 118140960795 + 513795 * 2 ^ 59
def prefixEnd_513795 : Nat := 4983230072969 + 3 ^ 40 * 513795 * 2
def baseEnd_513795 : Nat := 58627509528205001866579

theorem tailTrace_513795 : CollatzResearch.WordTrace tailWord_513795 prefixEnd_513795 58627509528205001866579 := by
  unfold tailWord_513795
  simp only [CollatzResearch.WordTrace]
  refine ⟨18739643173615939045038839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12493095449077292696692559 18739643173615939045038839)
  ·
    refine ⟨28109464760423908567558259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18739643173615939045038839 28109464760423908567558259)
    ·
      refine ⟨42164197140635862851337389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28109464760423908567558259 42164197140635862851337389)
      ·
        refine ⟨15811573927738448569251521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42164197140635862851337389 15811573927738448569251521)
        ·
          refine ⟨11858680445803836426938641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15811573927738448569251521 11858680445803836426938641)
          ·
            refine ⟨8894010334352877320203981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11858680445803836426938641 8894010334352877320203981)
            ·
              refine ⟨3335253875382328995076493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8894010334352877320203981 3335253875382328995076493)
              ·
                refine ⟨1250720203268373373153685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3335253875382328995076493 1250720203268373373153685)
                ·
                  refine ⟨58627509528205001866579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1250720203268373373153685 58627509528205001866579)
                  ·
                    rfl

theorem cell22_513795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 3, 6].length) (baseStart_513795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_513795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_513795 prefixEnd_513795 := by exact prefixLift 513795
  have htrace : WordTrace (prefixWord ++ tailWord_513795) baseStart_513795 baseEnd_513795 := by
    simpa [prefixWord, tailWord_513795, baseEnd_513795] using wordTrace_append hprefix tailTrace_513795
  have hstable : (prefixWord ++ tailWord_513795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513795).length < 2 ^ (prefixWord ++ tailWord_513795).sum := by decide
  have hdescent : baseEnd_513795 < baseStart_513795 := by decide
  rcases family_descends (prefixWord ++ tailWord_513795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513822 : List Nat := [4, 3, 2, 2, 1, 2, 1, 3, 1, 3]
def baseStart_513822 : Nat := 118140960795 + 513822 * 2 ^ 59
def prefixEnd_513822 : Nat := 4983230072969 + 3 ^ 40 * 513822 * 2
def baseEnd_513822 : Nat := 175891771236395935174655

theorem tailTrace_513822 : CollatzResearch.WordTrace tailWord_513822 prefixEnd_513822 175891771236395935174655 := by
  unfold tailWord_513822
  simp only [CollatzResearch.WordTrace]
  refine ⟨2342578493064765332033965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12493751963012081770847813 2342578493064765332033965)
  ·
    refine ⟨878466934899286999512737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2342578493064765332033965 878466934899286999512737)
    ·
      refine ⟨658850201174465249634553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 878466934899286999512737 658850201174465249634553)
      ·
        refine ⟨494137650880848937225915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 658850201174465249634553 494137650880848937225915)
        ·
          refine ⟨741206476321273405838873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494137650880848937225915 741206476321273405838873)
          ·
            refine ⟨555904857240955054379155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 741206476321273405838873 555904857240955054379155)
            ·
              refine ⟨833857285861432581568733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 555904857240955054379155 833857285861432581568733)
              ·
                refine ⟨312696482198037218088275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 833857285861432581568733 312696482198037218088275)
                ·
                  refine ⟨469044723297055827132413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 312696482198037218088275 469044723297055827132413)
                  ·
                    refine ⟨175891771236395935174655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 469044723297055827132413 175891771236395935174655)
                    ·
                      rfl

theorem cell22_513822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_513822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_513822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_513822 prefixEnd_513822 := by exact prefixLift 513822
  have htrace : WordTrace (prefixWord ++ tailWord_513822) baseStart_513822 baseEnd_513822 := by
    simpa [prefixWord, tailWord_513822, baseEnd_513822] using wordTrace_append hprefix tailTrace_513822
  have hstable : (prefixWord ++ tailWord_513822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513822).length < 2 ^ (prefixWord ++ tailWord_513822).sum := by decide
  have hdescent : baseEnd_513822 < baseStart_513822 := by decide
  rcases family_descends (prefixWord ++ tailWord_513822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513827 : List Nat := [1, 1, 1, 4, 2, 1, 3, 2, 4, 3]
def baseStart_513827 : Nat := 118140960795 + 513827 * 2 ^ 59
def prefixEnd_513827 : Nat := 4983230072969 + 3 ^ 40 * 513827 * 2
def baseEnd_513827 : Nat := 175893482838577588799639

theorem tailTrace_513827 : CollatzResearch.WordTrace tailWord_513827 prefixEnd_513827 175893482838577588799639 := by
  unfold tailWord_513827
  simp only [CollatzResearch.WordTrace]
  refine ⟨18740810309500008510203735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12493873539666672340135823 18740810309500008510203735)
  ·
    refine ⟨28111215464250012765305603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18740810309500008510203735 28111215464250012765305603)
    ·
      refine ⟨42166823196375019147958405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28111215464250012765305603 42166823196375019147958405)
      ·
        refine ⟨7906279349320316090242201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42166823196375019147958405 7906279349320316090242201)
        ·
          refine ⟨5929709511990237067681651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7906279349320316090242201 5929709511990237067681651)
          ·
            refine ⟨8894564267985355601522477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5929709511990237067681651 8894564267985355601522477)
            ·
              refine ⟨3335461600494508350570929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8894564267985355601522477 3335461600494508350570929)
              ·
                refine ⟨2501596200370881262928197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3335461600494508350570929 2501596200370881262928197)
                ·
                  refine ⟨469049287569540236799037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2501596200370881262928197 469049287569540236799037)
                  ·
                    refine ⟨175893482838577588799639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 469049287569540236799037 175893482838577588799639)
                    ·
                      rfl

theorem cell22_513827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 4, 3].length) (baseStart_513827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_513827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_513827 prefixEnd_513827 := by exact prefixLift 513827
  have htrace : WordTrace (prefixWord ++ tailWord_513827) baseStart_513827 baseEnd_513827 := by
    simpa [prefixWord, tailWord_513827, baseEnd_513827] using wordTrace_append hprefix tailTrace_513827
  have hstable : (prefixWord ++ tailWord_513827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513827).length < 2 ^ (prefixWord ++ tailWord_513827).sum := by decide
  have hdescent : baseEnd_513827 < baseStart_513827 := by decide
  rcases family_descends (prefixWord ++ tailWord_513827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513829 : List Nat := [1, 3, 1, 2, 3, 2, 3, 3, 4]
def baseStart_513829 : Nat := 118140960795 + 513829 * 2 ^ 59
def prefixEnd_513829 : Nat := 4983230072969 + 3 ^ 40 * 513829 * 2
def baseEnd_513829 : Nat := 58631389159816750083211

theorem tailTrace_513829 : CollatzResearch.WordTrace tailWord_513829 prefixEnd_513829 58631389159816750083211 := by
  unfold tailWord_513829
  simp only [CollatzResearch.WordTrace]
  refine ⟨18740883255492762851776541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12493922170328508567851027 18740883255492762851776541)
  ·
    refine ⟨7027831220809786069416203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18740883255492762851776541 7027831220809786069416203)
    ·
      refine ⟨10541746831214679104124305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7027831220809786069416203 10541746831214679104124305)
      ·
        refine ⟨7906310123411009328093229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10541746831214679104124305 7906310123411009328093229)
        ·
          refine ⟨2964866296279128498034961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7906310123411009328093229 2964866296279128498034961)
          ·
            refine ⟨2223649722209346373526221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2964866296279128498034961 2223649722209346373526221)
            ·
              refine ⟨833868645828504890072333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2223649722209346373526221 833868645828504890072333)
              ·
                refine ⟨312700742185689333777125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 833868645828504890072333 312700742185689333777125)
                ·
                  refine ⟨58631389159816750083211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 312700742185689333777125 58631389159816750083211)
                  ·
                    rfl

theorem cell22_513829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 3, 4].length) (baseStart_513829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_513829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_513829 prefixEnd_513829 := by exact prefixLift 513829
  have htrace : WordTrace (prefixWord ++ tailWord_513829) baseStart_513829 baseEnd_513829 := by
    simpa [prefixWord, tailWord_513829, baseEnd_513829] using wordTrace_append hprefix tailTrace_513829
  have hstable : (prefixWord ++ tailWord_513829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513829).length < 2 ^ (prefixWord ++ tailWord_513829).sum := by decide
  have hdescent : baseEnd_513829 < baseStart_513829 := by decide
  rcases family_descends (prefixWord ++ tailWord_513829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513842 : List Nat := [3, 2, 1, 1, 3, 2, 1, 1, 4, 4]
def baseStart_513842 : Nat := 118140960795 + 513842 * 2 ^ 59
def prefixEnd_513842 : Nat := 4983230072969 + 3 ^ 40 * 513842 * 2
def baseEnd_513842 : Nat := 175898617645122549674593

theorem tailTrace_513842 : CollatzResearch.WordTrace tailWord_513842 prefixEnd_513842 175898617645122549674593 := by
  unfold tailWord_513842
  simp only [CollatzResearch.WordTrace]
  refine ⟨4685339351111416517999945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12494238269630444047999853 4685339351111416517999945)
  ·
    refine ⟨3514004513333562388499959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4685339351111416517999945 3514004513333562388499959)
    ·
      refine ⟨5271006770000343582749939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3514004513333562388499959 5271006770000343582749939)
      ·
        refine ⟨7906510155000515374124909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5271006770000343582749939 7906510155000515374124909)
        ·
          refine ⟨2964941308125193265296841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7906510155000515374124909 2964941308125193265296841)
          ·
            refine ⟨2223705981093894948972631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2964941308125193265296841 2223705981093894948972631)
            ·
              refine ⟨3335558971640842423458947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2223705981093894948972631 3335558971640842423458947)
              ·
                refine ⟨5003338457461263635188421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3335558971640842423458947 5003338457461263635188421)
                ·
                  refine ⟨938125960773986931597829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5003338457461263635188421 938125960773986931597829)
                  ·
                    refine ⟨175898617645122549674593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 938125960773986931597829 175898617645122549674593)
                    ·
                      rfl

theorem cell22_513842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 4, 4].length) (baseStart_513842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_513842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_513842 prefixEnd_513842 := by exact prefixLift 513842
  have htrace : WordTrace (prefixWord ++ tailWord_513842) baseStart_513842 baseEnd_513842 := by
    simpa [prefixWord, tailWord_513842, baseEnd_513842] using wordTrace_append hprefix tailTrace_513842
  have hstable : (prefixWord ++ tailWord_513842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513842).length < 2 ^ (prefixWord ++ tailWord_513842).sum := by decide
  have hdescent : baseEnd_513842 < baseStart_513842 := by decide
  rcases family_descends (prefixWord ++ tailWord_513842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513846 : List Nat := [5, 1, 2, 2, 1, 3, 1, 1, 6]
def baseStart_513846 : Nat := 118140960795 + 513846 * 2 ^ 59
def prefixEnd_513846 : Nat := 4983230072969 + 3 ^ 40 * 513846 * 2
def baseEnd_513846 : Nat := 58633328975622624191527

theorem tailTrace_513846 : CollatzResearch.WordTrace tailWord_513846 prefixEnd_513846 58633328975622624191527 := by
  unfold tailWord_513846
  simp only [CollatzResearch.WordTrace]
  refine ⟨1171343956026948422196587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12494335530954116503430261 1171343956026948422196587)
  ·
    refine ⟨1757015934040422633294881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1171343956026948422196587 1757015934040422633294881)
    ·
      refine ⟨1317761950530316974971161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1757015934040422633294881 1317761950530316974971161)
      ·
        refine ⟨988321462897737731228371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1317761950530316974971161 988321462897737731228371)
        ·
          refine ⟨1482482194346606596842557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 988321462897737731228371 1482482194346606596842557)
          ·
            refine ⟨555930822879977473815959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1482482194346606596842557 555930822879977473815959)
            ·
              refine ⟨833896234319966210723939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 555930822879977473815959 833896234319966210723939)
              ·
                refine ⟨1250844351479949316085909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 833896234319966210723939 1250844351479949316085909)
                ·
                  refine ⟨58633328975622624191527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1250844351479949316085909 58633328975622624191527)
                  ·
                    rfl

theorem cell22_513846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 1, 6].length) (baseStart_513846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_513846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_513846 prefixEnd_513846 := by exact prefixLift 513846
  have htrace : WordTrace (prefixWord ++ tailWord_513846) baseStart_513846 baseEnd_513846 := by
    simpa [prefixWord, tailWord_513846, baseEnd_513846] using wordTrace_append hprefix tailTrace_513846
  have hstable : (prefixWord ++ tailWord_513846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513846).length < 2 ^ (prefixWord ++ tailWord_513846).sum := by decide
  have hdescent : baseEnd_513846 < baseStart_513846 := by decide
  rcases family_descends (prefixWord ++ tailWord_513846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513872 : List Nat := [2, 1, 1, 1, 1, 4, 1, 3, 5, 3]
def baseStart_513872 : Nat := 118140960795 + 513872 * 2 ^ 59
def prefixEnd_513872 : Nat := 4983230072969 + 3 ^ 40 * 513872 * 2
def baseEnd_513872 : Nat := 175908887258212471424501

theorem tailTrace_513872 : CollatzResearch.WordTrace tailWord_513872 prefixEnd_513872 175908887258212471424501 := by
  unfold tailWord_513872
  simp only [CollatzResearch.WordTrace]
  refine ⟨9371225797168490597795935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12494967729557987463727913 9371225797168490597795935)
  ·
    refine ⟨14056838695752735896693903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9371225797168490597795935 14056838695752735896693903)
    ·
      refine ⟨21085258043629103845040855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14056838695752735896693903 21085258043629103845040855)
      ·
        refine ⟨31627887065443655767561283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21085258043629103845040855 31627887065443655767561283)
        ·
          refine ⟨47441830598165483651341925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31627887065443655767561283 47441830598165483651341925)
          ·
            refine ⟨8895343237156028184626611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47441830598165483651341925 8895343237156028184626611)
            ·
              refine ⟨13343014855734042276939917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8895343237156028184626611 13343014855734042276939917)
              ·
                refine ⟨5003630570900265853852469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13343014855734042276939917 5003630570900265853852469)
                ·
                  refine ⟨469090366021899923798669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5003630570900265853852469 469090366021899923798669)
                  ·
                    refine ⟨175908887258212471424501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 469090366021899923798669 175908887258212471424501)
                    ·
                      rfl

theorem cell22_513872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 5, 3].length) (baseStart_513872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_513872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_513872 prefixEnd_513872 := by exact prefixLift 513872
  have htrace : WordTrace (prefixWord ++ tailWord_513872) baseStart_513872 baseEnd_513872 := by
    simpa [prefixWord, tailWord_513872, baseEnd_513872] using wordTrace_append hprefix tailTrace_513872
  have hstable : (prefixWord ++ tailWord_513872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513872).length < 2 ^ (prefixWord ++ tailWord_513872).sum := by decide
  have hdescent : baseEnd_513872 < baseStart_513872 := by decide
  rcases family_descends (prefixWord ++ tailWord_513872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513953 : List Nat := [1, 2, 3, 4, 3, 1, 1, 2, 5]
def baseStart_513953 : Nat := 118140960795 + 513953 * 2 ^ 59
def prefixEnd_513953 : Nat := 4983230072969 + 3 ^ 40 * 513953 * 2
def baseEnd_513953 : Nat := 58645538404518420049751

theorem tailTrace_513953 : CollatzResearch.WordTrace tailWord_513953 prefixEnd_513953 58645538404518420049751 := by
  unfold tailWord_513953
  simp only [CollatzResearch.WordTrace]
  refine ⟨18745405907043532029290513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12496937271362354686193675 18745405907043532029290513)
  ·
    refine ⟨14059054430282649021967885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18745405907043532029290513 14059054430282649021967885)
    ·
      refine ⟨5272145411355993383237957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14059054430282649021967885 5272145411355993383237957)
      ·
        refine ⟨988527264629248759357117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5272145411355993383237957 988527264629248759357117)
        ·
          refine ⟨370697724235968284758919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 988527264629248759357117 370697724235968284758919)
          ·
            refine ⟨556046586353952427138379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370697724235968284758919 556046586353952427138379)
            ·
              refine ⟨834069879530928640707569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 556046586353952427138379 834069879530928640707569)
              ·
                refine ⟨625552409648196480530677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 834069879530928640707569 625552409648196480530677)
                ·
                  refine ⟨58645538404518420049751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 625552409648196480530677 58645538404518420049751)
                  ·
                    rfl

theorem cell22_513953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 2, 5].length) (baseStart_513953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_513953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_513953 prefixEnd_513953 := by exact prefixLift 513953
  have htrace : WordTrace (prefixWord ++ tailWord_513953) baseStart_513953 baseEnd_513953 := by
    simpa [prefixWord, tailWord_513953, baseEnd_513953] using wordTrace_append hprefix tailTrace_513953
  have hstable : (prefixWord ++ tailWord_513953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513953).length < 2 ^ (prefixWord ++ tailWord_513953).sum := by decide
  have hdescent : baseEnd_513953 < baseStart_513953 := by decide
  rcases family_descends (prefixWord ++ tailWord_513953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513977 : List Nat := [1, 2, 1, 4, 2, 1, 1, 1, 3, 6]
def baseStart_513977 : Nat := 118140960795 + 513977 * 2 ^ 59
def prefixEnd_513977 : Nat := 4983230072969 + 3 ^ 40 * 513977 * 2
def baseEnd_513977 : Nat := 175944830904027197549179

theorem tailTrace_513977 : CollatzResearch.WordTrace tailWord_513977 prefixEnd_513977 175944830904027197549179 := by
  unfold tailWord_513977
  simp only [CollatzResearch.WordTrace]
  refine ⟨18746281258956584128164185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12497520839304389418776123 18746281258956584128164185)
  ·
    refine ⟨14059710944217438096123139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18746281258956584128164185 14059710944217438096123139)
    ·
      refine ⟨21089566416326157144184709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14059710944217438096123139 21089566416326157144184709)
      ·
        refine ⟨3954293703061154464534633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21089566416326157144184709 3954293703061154464534633)
        ·
          refine ⟨2965720277295865848400975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3954293703061154464534633 2965720277295865848400975)
          ·
            refine ⟨4448580415943798772601463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2965720277295865848400975 4448580415943798772601463)
            ·
              refine ⟨6672870623915698158902195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4448580415943798772601463 6672870623915698158902195)
              ·
                refine ⟨10009305935873547238353293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6672870623915698158902195 10009305935873547238353293)
                ·
                  refine ⟨3753489725952580214382485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10009305935873547238353293 3753489725952580214382485)
                  ·
                    refine ⟨175944830904027197549179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3753489725952580214382485 175944830904027197549179)
                    ·
                      rfl

theorem cell22_513977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 6].length) (baseStart_513977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_513977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_513977 prefixEnd_513977 := by exact prefixLift 513977
  have htrace : WordTrace (prefixWord ++ tailWord_513977) baseStart_513977 baseEnd_513977 := by
    simpa [prefixWord, tailWord_513977, baseEnd_513977] using wordTrace_append hprefix tailTrace_513977
  have hstable : (prefixWord ++ tailWord_513977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513977).length < 2 ^ (prefixWord ++ tailWord_513977).sum := by decide
  have hdescent : baseEnd_513977 < baseStart_513977 := by decide
  rcases family_descends (prefixWord ++ tailWord_513977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514009 : List Nat := [1, 2, 1, 2, 6, 2, 8]
def baseStart_514009 : Nat := 118140960795 + 514009 * 2 ^ 59
def prefixEnd_514009 : Nat := 4983230072969 + 3 ^ 40 * 514009 * 2
def baseEnd_514009 : Nat := 6516880931777399287003

theorem tailTrace_514009 : CollatzResearch.WordTrace tailWord_514009 prefixEnd_514009 6516880931777399287003 := by
  unfold tailWord_514009
  simp only [CollatzResearch.WordTrace]
  refine ⟨18747448394840653593329081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12498298929893769062219387 18747448394840653593329081)
  ·
    refine ⟨14060586296130490194996811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18747448394840653593329081 14060586296130490194996811)
    ·
      refine ⟨21090879444195735292495217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14060586296130490194996811 21090879444195735292495217)
      ·
        refine ⟨15818159583146801469371413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21090879444195735292495217 15818159583146801469371413)
        ·
          refine ⟨741476230460006318876785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15818159583146801469371413 741476230460006318876785)
          ·
            refine ⟨556107172845004739157589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 741476230460006318876785 556107172845004739157589)
            ·
              refine ⟨6516880931777399287003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 556107172845004739157589 6516880931777399287003)
              ·
                rfl

theorem cell22_514009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 8].length) (baseStart_514009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_514009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_514009 prefixEnd_514009 := by exact prefixLift 514009
  have htrace : WordTrace (prefixWord ++ tailWord_514009) baseStart_514009 baseEnd_514009 := by
    simpa [prefixWord, tailWord_514009, baseEnd_514009] using wordTrace_append hprefix tailTrace_514009
  have hstable : (prefixWord ++ tailWord_514009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514009).length < 2 ^ (prefixWord ++ tailWord_514009).sum := by decide
  have hdescent : baseEnd_514009 < baseStart_514009 := by decide
  rcases family_descends (prefixWord ++ tailWord_514009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514030 : List Nat := [4, 1, 2, 1, 3, 3, 2, 1, 2, 3]
def baseStart_514030 : Nat := 118140960795 + 514030 * 2 ^ 59
def prefixEnd_514030 : Nat := 4983230072969 + 3 ^ 40 * 514030 * 2
def baseEnd_514030 : Nat := 175962973887152725974017

theorem tailTrace_514030 : CollatzResearch.WordTrace tailWord_514030 prefixEnd_514030 175962973887152725974017 := by
  unfold tailWord_514030
  simp only [CollatzResearch.WordTrace]
  refine ⟨2343526790970571772480443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12498809551843049453229029 2343526790970571772480443)
  ·
    refine ⟨3515290186455857658720665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2343526790970571772480443 3515290186455857658720665)
    ·
      refine ⟨2636467639841893244040499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3515290186455857658720665 2636467639841893244040499)
      ·
        refine ⟨3954701459762839866060749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2636467639841893244040499 3954701459762839866060749)
        ·
          refine ⟨1483013047411064949772781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3954701459762839866060749 1483013047411064949772781)
          ·
            refine ⟨556129892779149356164793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1483013047411064949772781 556129892779149356164793)
            ·
              refine ⟨417097419584362017123595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 556129892779149356164793 417097419584362017123595)
              ·
                refine ⟨625646129376543025685393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 417097419584362017123595 625646129376543025685393)
                ·
                  refine ⟨469234597032407269264045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 625646129376543025685393 469234597032407269264045)
                  ·
                    refine ⟨175962973887152725974017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 469234597032407269264045 175962973887152725974017)
                    ·
                      rfl

theorem cell22_514030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 2, 1, 2, 3].length) (baseStart_514030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_514030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_514030 prefixEnd_514030 := by exact prefixLift 514030
  have htrace : WordTrace (prefixWord ++ tailWord_514030) baseStart_514030 baseEnd_514030 := by
    simpa [prefixWord, tailWord_514030, baseEnd_514030] using wordTrace_append hprefix tailTrace_514030
  have hstable : (prefixWord ++ tailWord_514030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514030).length < 2 ^ (prefixWord ++ tailWord_514030).sum := by decide
  have hdescent : baseEnd_514030 < baseStart_514030 := by decide
  rcases family_descends (prefixWord ++ tailWord_514030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514129 : List Nat := [1, 2, 2, 1, 3, 1, 1, 3, 4, 4]
def baseStart_514129 : Nat := 118140960795 + 514129 * 2 ^ 59
def prefixEnd_514129 : Nat := 4983230072969 + 3 ^ 40 * 514129 * 2
def baseEnd_514129 : Nat := 175996863610349467748713

theorem tailTrace_514129 : CollatzResearch.WordTrace tailWord_514129 prefixEnd_514129 175996863610349467748713 := by
  unfold tailWord_514129
  simp only [CollatzResearch.WordTrace]
  refine ⟨18751825154405914087697441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12501216769603942725131627 18751825154405914087697441)
  ·
    refine ⟨14063868865804435565773081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18751825154405914087697441 14063868865804435565773081)
    ·
      refine ⟨10547901649353326674329811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14063868865804435565773081 10547901649353326674329811)
      ·
        refine ⟨15821852474029990011494717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10547901649353326674329811 15821852474029990011494717)
        ·
          refine ⟨5933194677761246254310519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15821852474029990011494717 5933194677761246254310519)
          ·
            refine ⟨8899792016641869381465779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5933194677761246254310519 8899792016641869381465779)
            ·
              refine ⟨13349688024962804072198669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8899792016641869381465779 13349688024962804072198669)
              ·
                refine ⟨5006133009361051527074501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13349688024962804072198669 5006133009361051527074501)
                ·
                  refine ⟨938649939255197161326469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5006133009361051527074501 938649939255197161326469)
                  ·
                    refine ⟨175996863610349467748713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 938649939255197161326469 175996863610349467748713)
                    ·
                      rfl

theorem cell22_514129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 4, 4].length) (baseStart_514129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_514129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_514129 prefixEnd_514129 := by exact prefixLift 514129
  have htrace : WordTrace (prefixWord ++ tailWord_514129) baseStart_514129 baseEnd_514129 := by
    simpa [prefixWord, tailWord_514129, baseEnd_514129] using wordTrace_append hprefix tailTrace_514129
  have hstable : (prefixWord ++ tailWord_514129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514129).length < 2 ^ (prefixWord ++ tailWord_514129).sum := by decide
  have hdescent : baseEnd_514129 < baseStart_514129 := by decide
  rcases family_descends (prefixWord ++ tailWord_514129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514244 : List Nat := [2, 3, 3, 1, 2, 3, 2, 2, 1, 3]
def baseStart_514244 : Nat := 118140960795 + 514244 * 2 ^ 59
def prefixEnd_514244 : Nat := 4983230072969 + 3 ^ 40 * 514244 * 2
def baseEnd_514244 : Nat := 176036230460527501123361

theorem tailTrace_514244 : CollatzResearch.WordTrace tailWord_514244 prefixEnd_514244 176036230460527501123361 := by
  unfold tailWord_514244
  simp only [CollatzResearch.WordTrace]
  refine ⟨9378009774494644364066893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12504013032659525818755857 9378009774494644364066893)
  ·
    refine ⟨3516753665435491636525085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9378009774494644364066893 3516753665435491636525085)
    ·
      refine ⟨1318782624538309363696907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3516753665435491636525085 1318782624538309363696907)
      ·
        refine ⟨1978173936807464045545361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1318782624538309363696907 1978173936807464045545361)
        ·
          refine ⟨1483630452605598034159021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1978173936807464045545361 1483630452605598034159021)
          ·
            refine ⟨556361419727099262809633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1483630452605598034159021 556361419727099262809633)
            ·
              refine ⟨417271064795324447107225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 556361419727099262809633 417271064795324447107225)
              ·
                refine ⟨312953298596493335330419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 417271064795324447107225 312953298596493335330419)
                ·
                  refine ⟨469429947894740002995629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 312953298596493335330419 469429947894740002995629)
                  ·
                    refine ⟨176036230460527501123361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 469429947894740002995629 176036230460527501123361)
                    ·
                      rfl

theorem cell22_514244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_514244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_514244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_514244 prefixEnd_514244 := by exact prefixLift 514244
  have htrace : WordTrace (prefixWord ++ tailWord_514244) baseStart_514244 baseEnd_514244 := by
    simpa [prefixWord, tailWord_514244, baseEnd_514244] using wordTrace_append hprefix tailTrace_514244
  have hstable : (prefixWord ++ tailWord_514244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514244).length < 2 ^ (prefixWord ++ tailWord_514244).sum := by decide
  have hdescent : baseEnd_514244 < baseStart_514244 := by decide
  rcases family_descends (prefixWord ++ tailWord_514244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514266 : List Nat := [3, 1, 1, 2, 2, 1, 3, 3, 1, 5]
def baseStart_514266 : Nat := 118140960795 + 514266 * 2 ^ 59
def prefixEnd_514266 : Nat := 4983230072969 + 3 ^ 40 * 514266 * 2
def baseEnd_514266 : Nat := 176043761510126777073293

theorem tailTrace_514266 : CollatzResearch.WordTrace tailWord_514266 prefixEnd_514266 176043761510126777073293 := by
  unfold tailWord_514266
  simp only [CollatzResearch.WordTrace]
  refine ⟨4689205488727396621358663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12504547969939724323623101 4689205488727396621358663)
  ·
    refine ⟨7033808233091094932037995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4689205488727396621358663 7033808233091094932037995)
    ·
      refine ⟨10550712349636642398056993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7033808233091094932037995 10550712349636642398056993)
      ·
        refine ⟨7913034262227481798542745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10550712349636642398056993 7913034262227481798542745)
        ·
          refine ⟨5934775696670611348907059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7913034262227481798542745 5934775696670611348907059)
          ·
            refine ⟨8902163545005917023360589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5934775696670611348907059 8902163545005917023360589)
            ·
              refine ⟨3338311329377218883760221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8902163545005917023360589 3338311329377218883760221)
              ·
                refine ⟨1251866748516457081410083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3338311329377218883760221 1251866748516457081410083)
                ·
                  refine ⟨1877800122774685622115125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1251866748516457081410083 1877800122774685622115125)
                  ·
                    refine ⟨176043761510126777073293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1877800122774685622115125 176043761510126777073293)
                    ·
                      rfl

theorem cell22_514266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 3, 1, 5].length) (baseStart_514266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_514266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_514266 prefixEnd_514266 := by exact prefixLift 514266
  have htrace : WordTrace (prefixWord ++ tailWord_514266) baseStart_514266 baseEnd_514266 := by
    simpa [prefixWord, tailWord_514266, baseEnd_514266] using wordTrace_append hprefix tailTrace_514266
  have hstable : (prefixWord ++ tailWord_514266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514266).length < 2 ^ (prefixWord ++ tailWord_514266).sum := by decide
  have hdescent : baseEnd_514266 < baseStart_514266 := by decide
  rcases family_descends (prefixWord ++ tailWord_514266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514300 : List Nat := [2, 2, 2, 1, 4, 1, 3, 2, 2, 3]
def baseStart_514300 : Nat := 118140960795 + 514300 * 2 ^ 59
def prefixEnd_514300 : Nat := 4983230072969 + 3 ^ 40 * 514300 * 2
def baseEnd_514300 : Nat := 176055400404962021723189

theorem tailTrace_514300 : CollatzResearch.WordTrace tailWord_514300 prefixEnd_514300 176055400404962021723189 := by
  unfold tailWord_514300
  simp only [CollatzResearch.WordTrace]
  refine ⟨9379031018393205146086177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12505374691190940194781569 9379031018393205146086177)
  ·
    refine ⟨7034273263794903859564633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9379031018393205146086177 7034273263794903859564633)
    ·
      refine ⟨5275704947846177894673475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7034273263794903859564633 5275704947846177894673475)
      ·
        refine ⟨7913557421769266842010213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5275704947846177894673475 7913557421769266842010213)
        ·
          refine ⟨1483792016581737532876915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7913557421769266842010213 1483792016581737532876915)
          ·
            refine ⟨2225688024872606299315373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1483792016581737532876915 2225688024872606299315373)
            ·
              refine ⟨834633009327227362243265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2225688024872606299315373 834633009327227362243265)
              ·
                refine ⟨625974756995420521682449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 834633009327227362243265 625974756995420521682449)
                ·
                  refine ⟨469481067746565391261837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 625974756995420521682449 469481067746565391261837)
                  ·
                    refine ⟨176055400404962021723189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 469481067746565391261837 176055400404962021723189)
                    ·
                      rfl

theorem cell22_514300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 2, 2, 3].length) (baseStart_514300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_514300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_514300 prefixEnd_514300 := by exact prefixLift 514300
  have htrace : WordTrace (prefixWord ++ tailWord_514300) baseStart_514300 baseEnd_514300 := by
    simpa [prefixWord, tailWord_514300, baseEnd_514300] using wordTrace_append hprefix tailTrace_514300
  have hstable : (prefixWord ++ tailWord_514300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514300).length < 2 ^ (prefixWord ++ tailWord_514300).sum := by decide
  have hdescent : baseEnd_514300 < baseStart_514300 := by decide
  rcases family_descends (prefixWord ++ tailWord_514300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514328 : List Nat := [2, 1, 2, 3, 1, 2, 1, 4, 3, 3]
def baseStart_514328 : Nat := 118140960795 + 514328 * 2 ^ 59
def prefixEnd_514328 : Nat := 4983230072969 + 3 ^ 40 * 514328 * 2
def baseEnd_514328 : Nat := 176064985377179282023103

theorem tailTrace_514328 : CollatzResearch.WordTrace tailWord_514328 prefixEnd_514328 176064985377179282023103 := by
  unfold tailWord_514328
  simp only [CollatzResearch.WordTrace]
  refine ⟨9379541640342485537095819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12506055520456647382794425 9379541640342485537095819)
  ·
    refine ⟨14069312460513728305643729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9379541640342485537095819 14069312460513728305643729)
    ·
      refine ⟨10551984345385296229232797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14069312460513728305643729 10551984345385296229232797)
      ·
        refine ⟨3956994129519486085962299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10551984345385296229232797 3956994129519486085962299)
        ·
          refine ⟨5935491194279229128943449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3956994129519486085962299 5935491194279229128943449)
          ·
            refine ⟨4451618395709421846707587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5935491194279229128943449 4451618395709421846707587)
            ·
              refine ⟨6677427593564132770061381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4451618395709421846707587 6677427593564132770061381)
              ·
                refine ⟨1252017673793274894386509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6677427593564132770061381 1252017673793274894386509)
                ·
                  refine ⟨469506627672478085394941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1252017673793274894386509 469506627672478085394941)
                  ·
                    refine ⟨176064985377179282023103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 469506627672478085394941 176064985377179282023103)
                    ·
                      rfl

theorem cell22_514328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 4, 3, 3].length) (baseStart_514328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_514328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_514328 prefixEnd_514328 := by exact prefixLift 514328
  have htrace : WordTrace (prefixWord ++ tailWord_514328) baseStart_514328 baseEnd_514328 := by
    simpa [prefixWord, tailWord_514328, baseEnd_514328] using wordTrace_append hprefix tailTrace_514328
  have hstable : (prefixWord ++ tailWord_514328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514328).length < 2 ^ (prefixWord ++ tailWord_514328).sum := by decide
  have hdescent : baseEnd_514328 < baseStart_514328 := by decide
  rcases family_descends (prefixWord ++ tailWord_514328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514330 : List Nat := [3, 1, 1, 3, 4, 2, 2, 6]
def baseStart_514330 : Nat := 118140960795 + 514330 * 2 ^ 59
def prefixEnd_514330 : Nat := 4983230072969 + 3 ^ 40 * 514330 * 2
def baseEnd_514330 : Nat := 19562852224227993719233

theorem tailTrace_514330 : CollatzResearch.WordTrace tailWord_514330 prefixEnd_514330 19562852224227993719233 := by
  unfold tailWord_514330
  simp only [CollatzResearch.WordTrace]
  refine ⟨4689789056669431353941111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12506104151118483610509629 4689789056669431353941111)
  ·
    refine ⟨7034683585004147030911667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4689789056669431353941111 7034683585004147030911667)
    ·
      refine ⟨10552025377506220546367501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7034683585004147030911667 10552025377506220546367501)
      ·
        refine ⟨3957009516564832704887813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10552025377506220546367501 3957009516564832704887813)
        ·
          refine ⟨741939284355906132166465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3957009516564832704887813 741939284355906132166465)
          ·
            refine ⟨556454463266929599124849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 741939284355906132166465 556454463266929599124849)
            ·
              refine ⟨417340847450197199343637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 556454463266929599124849 417340847450197199343637)
              ·
                refine ⟨19562852224227993719233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 417340847450197199343637 19562852224227993719233)
                ·
                  rfl

theorem cell22_514330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 2, 6].length) (baseStart_514330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_514330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_514330 prefixEnd_514330 := by exact prefixLift 514330
  have htrace : WordTrace (prefixWord ++ tailWord_514330) baseStart_514330 baseEnd_514330 := by
    simpa [prefixWord, tailWord_514330, baseEnd_514330] using wordTrace_append hprefix tailTrace_514330
  have hstable : (prefixWord ++ tailWord_514330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514330).length < 2 ^ (prefixWord ++ tailWord_514330).sum := by decide
  have hdescent : baseEnd_514330 < baseStart_514330 := by decide
  rcases family_descends (prefixWord ++ tailWord_514330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514435 : List Nat := [1, 1, 1, 3, 6, 1, 2, 1, 1, 5]
def baseStart_514435 : Nat := 118140960795 + 514435 * 2 ^ 59
def prefixEnd_514435 : Nat := 4983230072969 + 3 ^ 40 * 514435 * 2
def baseEnd_514435 : Nat := 176101613663866669597775

theorem tailTrace_514435 : CollatzResearch.WordTrace tailWord_514435 prefixEnd_514435 176101613663866669597775 := by
  unfold tailWord_514435
  simp only [CollatzResearch.WordTrace]
  refine ⟨18762985891297328348336759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12508657260864885565557839 18762985891297328348336759)
  ·
    refine ⟨28144478836945992522505139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18762985891297328348336759 28144478836945992522505139)
    ·
      refine ⟨42216718255418988783757709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28144478836945992522505139 42216718255418988783757709)
      ·
        refine ⟨15831269345782120793909141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42216718255418988783757709 15831269345782120793909141)
        ·
          refine ⟨742090750583536912214491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15831269345782120793909141 742090750583536912214491)
          ·
            refine ⟨1113136125875305368321737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 742090750583536912214491 1113136125875305368321737)
            ·
              refine ⟨834852094406479026241303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1113136125875305368321737 834852094406479026241303)
              ·
                refine ⟨1252278141609718539361955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 834852094406479026241303 1252278141609718539361955)
                ·
                  refine ⟨1878417212414577809042933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1252278141609718539361955 1878417212414577809042933)
                  ·
                    refine ⟨176101613663866669597775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1878417212414577809042933 176101613663866669597775)
                    ·
                      rfl

theorem cell22_514435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 1, 1, 5].length) (baseStart_514435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_514435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_514435 prefixEnd_514435 := by exact prefixLift 514435
  have htrace : WordTrace (prefixWord ++ tailWord_514435) baseStart_514435 baseEnd_514435 := by
    simpa [prefixWord, tailWord_514435, baseEnd_514435] using wordTrace_append hprefix tailTrace_514435
  have hstable : (prefixWord ++ tailWord_514435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514435).length < 2 ^ (prefixWord ++ tailWord_514435).sum := by decide
  have hdescent : baseEnd_514435 < baseStart_514435 := by decide
  rcases family_descends (prefixWord ++ tailWord_514435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514465 : List Nat := [1, 2, 3, 5, 1, 1, 9]
def baseStart_514465 : Nat := 118140960795 + 514465 * 2 ^ 59
def prefixEnd_514465 : Nat := 4983230072969 + 3 ^ 40 * 514465 * 2
def baseEnd_514465 : Nat := 6522662343590984864729

theorem tailTrace_514465 : CollatzResearch.WordTrace tailWord_514465 prefixEnd_514465 6522662343590984864729 := by
  unfold tailWord_514465
  simp only [CollatzResearch.WordTrace]
  refine ⟨18764080081188643471928849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12509386720792428981285899 18764080081188643471928849)
  ·
    refine ⟨14073060060891482603946637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18764080081188643471928849 14073060060891482603946637)
    ·
      refine ⟨5277397522834305976479989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14073060060891482603946637 5277397522834305976479989)
      ·
        refine ⟨494756017765716185294999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5277397522834305976479989 494756017765716185294999)
        ·
          refine ⟨742134026648574277942499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494756017765716185294999 742134026648574277942499)
          ·
            refine ⟨1113201039972861416913749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 742134026648574277942499 1113201039972861416913749)
            ·
              refine ⟨6522662343590984864729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1113201039972861416913749 6522662343590984864729)
              ·
                rfl

theorem cell22_514465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 9].length) (baseStart_514465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_514465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_514465 prefixEnd_514465 := by exact prefixLift 514465
  have htrace : WordTrace (prefixWord ++ tailWord_514465) baseStart_514465 baseEnd_514465 := by
    simpa [prefixWord, tailWord_514465, baseEnd_514465] using wordTrace_append hprefix tailTrace_514465
  have hstable : (prefixWord ++ tailWord_514465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514465).length < 2 ^ (prefixWord ++ tailWord_514465).sum := by decide
  have hdescent : baseEnd_514465 < baseStart_514465 := by decide
  rcases family_descends (prefixWord ++ tailWord_514465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514531 : List Nat := [1, 1, 1, 6, 3, 1, 3, 2, 1, 3]
def baseStart_514531 : Nat := 118140960795 + 514531 * 2 ^ 59
def prefixEnd_514531 : Nat := 4983230072969 + 3 ^ 40 * 514531 * 2
def baseEnd_514531 : Nat := 176134476425754419197481

theorem tailTrace_514531 : CollatzResearch.WordTrace tailWord_514531 prefixEnd_514531 176134476425754419197481 := by
  unfold tailWord_514531
  simp only [CollatzResearch.WordTrace]
  refine ⟨18766487298949536743831447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12510991532633024495887631 18766487298949536743831447)
  ·
    refine ⟨28149730948424305115747171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18766487298949536743831447 28149730948424305115747171)
    ·
      refine ⟨42224596422636457673620757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28149730948424305115747171 42224596422636457673620757)
      ·
        refine ⟨1979277957311083953450973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 42224596422636457673620757 1979277957311083953450973)
        ·
          refine ⟨742229233991656482544115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1979277957311083953450973 742229233991656482544115)
          ·
            refine ⟨1113343850987484723816173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 742229233991656482544115 1113343850987484723816173)
            ·
              refine ⟨417503944120306771431065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1113343850987484723816173 417503944120306771431065)
              ·
                refine ⟨313127958090230078573299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 417503944120306771431065 313127958090230078573299)
                ·
                  refine ⟨469691937135345117859949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 313127958090230078573299 469691937135345117859949)
                  ·
                    refine ⟨176134476425754419197481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 469691937135345117859949 176134476425754419197481)
                    ·
                      rfl

theorem cell22_514531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 3, 2, 1, 3].length) (baseStart_514531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_514531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_514531 prefixEnd_514531 := by exact prefixLift 514531
  have htrace : WordTrace (prefixWord ++ tailWord_514531) baseStart_514531 baseEnd_514531 := by
    simpa [prefixWord, tailWord_514531, baseEnd_514531] using wordTrace_append hprefix tailTrace_514531
  have hstable : (prefixWord ++ tailWord_514531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514531).length < 2 ^ (prefixWord ++ tailWord_514531).sum := by decide
  have hdescent : baseEnd_514531 < baseStart_514531 := by decide
  rcases family_descends (prefixWord ++ tailWord_514531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514570 : List Nat := [3, 1, 2, 2, 2, 1, 3, 2, 1, 5]
def baseStart_514570 : Nat := 118140960795 + 514570 * 2 ^ 59
def prefixEnd_514570 : Nat := 4983230072969 + 3 ^ 40 * 514570 * 2
def baseEnd_514570 : Nat := 176147826922771317472361

theorem tailTrace_514570 : CollatzResearch.WordTrace tailWord_514570 prefixEnd_514570 176147826922771317472361 := by
  unfold tailWord_514570
  simp only [CollatzResearch.WordTrace]
  refine ⟨4691977436452061601125291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12511939830538830936334109 4691977436452061601125291)
  ·
    refine ⟨7037966154678092401687937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4691977436452061601125291 7037966154678092401687937)
    ·
      refine ⟨5278474616008569301265953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7037966154678092401687937 5278474616008569301265953)
      ·
        refine ⟨3958855962006426975949465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5278474616008569301265953 3958855962006426975949465)
        ·
          refine ⟨2969141971504820231962099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3958855962006426975949465 2969141971504820231962099)
          ·
            refine ⟨4453712957257230347943149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2969141971504820231962099 4453712957257230347943149)
            ·
              refine ⟨1670142358971461380478681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4453712957257230347943149 1670142358971461380478681)
              ·
                refine ⟨1252606769228596035359011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1670142358971461380478681 1252606769228596035359011)
                ·
                  refine ⟨1878910153842894053038517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1252606769228596035359011 1878910153842894053038517)
                  ·
                    refine ⟨176147826922771317472361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1878910153842894053038517 176147826922771317472361)
                    ·
                      rfl

theorem cell22_514570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 2, 1, 5].length) (baseStart_514570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_514570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_514570 prefixEnd_514570 := by exact prefixLift 514570
  have htrace : WordTrace (prefixWord ++ tailWord_514570) baseStart_514570 baseEnd_514570 := by
    simpa [prefixWord, tailWord_514570, baseEnd_514570] using wordTrace_append hprefix tailTrace_514570
  have hstable : (prefixWord ++ tailWord_514570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514570).length < 2 ^ (prefixWord ++ tailWord_514570).sum := by decide
  have hdescent : baseEnd_514570 < baseStart_514570 := by decide
  rcases family_descends (prefixWord ++ tailWord_514570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514574 : List Nat := [4, 1, 1, 2, 3, 2, 3, 1, 1, 4]
def baseStart_514574 : Nat := 118140960795 + 514574 * 2 ^ 59
def prefixEnd_514574 : Nat := 4983230072969 + 3 ^ 40 * 514574 * 2
def baseEnd_514574 : Nat := 176149196204516640372349

theorem tailTrace_514574 : CollatzResearch.WordTrace tailWord_514574 prefixEnd_514574 176149196204516640372349 := by
  unfold tailWord_514574
  simp only [CollatzResearch.WordTrace]
  refine ⟨2346006954724219385955847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12512037091862503391764517 2346006954724219385955847)
  ·
    refine ⟨3519010432086329078933771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2346006954724219385955847 3519010432086329078933771)
    ·
      refine ⟨5278515648129493618400657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3519010432086329078933771 5278515648129493618400657)
      ·
        refine ⟨3958886736097120213800493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5278515648129493618400657 3958886736097120213800493)
        ·
          refine ⟨1484582526036420080175185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3958886736097120213800493 1484582526036420080175185)
          ·
            refine ⟨1113436894527315060131389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1484582526036420080175185 1113436894527315060131389)
            ·
              refine ⟨417538835447743147549271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1113436894527315060131389 417538835447743147549271)
              ·
                refine ⟨626308253171614721323907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 417538835447743147549271 626308253171614721323907)
                ·
                  refine ⟨939462379757422081985861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 626308253171614721323907 939462379757422081985861)
                  ·
                    refine ⟨176149196204516640372349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 939462379757422081985861 176149196204516640372349)
                    ·
                      rfl

theorem cell22_514574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 3, 1, 1, 4].length) (baseStart_514574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_514574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_514574 prefixEnd_514574 := by exact prefixLift 514574
  have htrace : WordTrace (prefixWord ++ tailWord_514574) baseStart_514574 baseEnd_514574 := by
    simpa [prefixWord, tailWord_514574, baseEnd_514574] using wordTrace_append hprefix tailTrace_514574
  have hstable : (prefixWord ++ tailWord_514574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514574).length < 2 ^ (prefixWord ++ tailWord_514574).sum := by decide
  have hdescent : baseEnd_514574 < baseStart_514574 := by decide
  rcases family_descends (prefixWord ++ tailWord_514574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514589 : List Nat := [1, 4, 2, 2, 1, 2, 4, 2, 4]
def baseStart_514589 : Nat := 118140960795 + 514589 * 2 ^ 59
def prefixEnd_514589 : Nat := 4983230072969 + 3 ^ 40 * 514589 * 2
def baseEnd_514589 : Nat := 58718110337020533749101

theorem tailTrace_514589 : CollatzResearch.WordTrace tailWord_514589 prefixEnd_514589 58718110337020533749101 := by
  unfold tailWord_514589
  simp only [CollatzResearch.WordTrace]
  refine ⟨18768602732739412649442821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12512401821826275099628547 18768602732739412649442821)
  ·
    refine ⟨3519113012388639871770529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18768602732739412649442821 3519113012388639871770529)
    ·
      refine ⟨2639334759291479903827897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3519113012388639871770529 2639334759291479903827897)
      ·
        refine ⟨1979501069468609927870923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2639334759291479903827897 1979501069468609927870923)
        ·
          refine ⟨2969251604202914891806385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1979501069468609927870923 2969251604202914891806385)
          ·
            refine ⟨2226938703152186168854789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2969251604202914891806385 2226938703152186168854789)
            ·
              refine ⟨417551006841034906660273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2226938703152186168854789 417551006841034906660273)
              ·
                refine ⟨313163255130776179995205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 417551006841034906660273 313163255130776179995205)
                ·
                  refine ⟨58718110337020533749101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 313163255130776179995205 58718110337020533749101)
                  ·
                    rfl

theorem cell22_514589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 4, 2, 4].length) (baseStart_514589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_514589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_514589 prefixEnd_514589 := by exact prefixLift 514589
  have htrace : WordTrace (prefixWord ++ tailWord_514589) baseStart_514589 baseEnd_514589 := by
    simpa [prefixWord, tailWord_514589, baseEnd_514589] using wordTrace_append hprefix tailTrace_514589
  have hstable : (prefixWord ++ tailWord_514589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514589).length < 2 ^ (prefixWord ++ tailWord_514589).sum := by decide
  have hdescent : baseEnd_514589 < baseStart_514589 := by decide
  rcases family_descends (prefixWord ++ tailWord_514589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514660 : List Nat := [2, 3, 1, 1, 2, 2, 1, 3, 2, 5]
def baseStart_514660 : Nat := 118140960795 + 514660 * 2 ^ 59
def prefixEnd_514660 : Nat := 4983230072969 + 3 ^ 40 * 514660 * 2
def baseEnd_514660 : Nat := 176178635762041082722085

theorem tailTrace_514660 : CollatzResearch.WordTrace tailWord_514660 prefixEnd_514660 176178635762041082722085 := by
  unfold tailWord_514660
  simp only [CollatzResearch.WordTrace]
  refine ⟨9385596157741095887638717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12514128210321461183518289 9385596157741095887638717)
  ·
    refine ⟨3519598559152910957864519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9385596157741095887638717 3519598559152910957864519)
    ·
      refine ⟨5279397838729366436796779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3519598559152910957864519 5279397838729366436796779)
      ·
        refine ⟨7919096758094049655195169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5279397838729366436796779 7919096758094049655195169)
        ·
          refine ⟨5939322568570537241396377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7919096758094049655195169 5939322568570537241396377)
          ·
            refine ⟨4454491926427902931047283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5939322568570537241396377 4454491926427902931047283)
            ·
              refine ⟨6681737889641854396570925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4454491926427902931047283 6681737889641854396570925)
              ·
                refine ⟨2505651708615695398714097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6681737889641854396570925 2505651708615695398714097)
                ·
                  refine ⟨1879238781461771549035573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2505651708615695398714097 1879238781461771549035573)
                  ·
                    refine ⟨176178635762041082722085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1879238781461771549035573 176178635762041082722085)
                    ·
                      rfl

theorem cell22_514660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_514660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_514660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_514660 prefixEnd_514660 := by exact prefixLift 514660
  have htrace : WordTrace (prefixWord ++ tailWord_514660) baseStart_514660 baseEnd_514660 := by
    simpa [prefixWord, tailWord_514660, baseEnd_514660] using wordTrace_append hprefix tailTrace_514660
  have hstable : (prefixWord ++ tailWord_514660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514660).length < 2 ^ (prefixWord ++ tailWord_514660).sum := by decide
  have hdescent : baseEnd_514660 < baseStart_514660 := by decide
  rcases family_descends (prefixWord ++ tailWord_514660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514735 : List Nat := [1, 1, 2, 1, 2, 5, 2, 8]
def baseStart_514735 : Nat := 118140960795 + 514735 * 2 ^ 59
def prefixEnd_514735 : Nat := 4983230072969 + 3 ^ 40 * 514735 * 2
def baseEnd_514735 : Nat := 19578256643862876344095

theorem tailTrace_514735 : CollatzResearch.WordTrace tailWord_514735 prefixEnd_514735 19578256643862876344095 := by
  unfold tailWord_514735
  simp only [CollatzResearch.WordTrace]
  refine ⟨18773927790210479584257659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12515951860140319722838439 18773927790210479584257659)
  ·
    refine ⟨28160891685315719376386489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18773927790210479584257659 28160891685315719376386489)
    ·
      refine ⟨21120668763986789532289867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28160891685315719376386489 21120668763986789532289867)
      ·
        refine ⟨31681003145980184298434801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21120668763986789532289867 31681003145980184298434801)
        ·
          refine ⟨23760752359485138223826101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31681003145980184298434801 23760752359485138223826101)
          ·
            refine ⟨2227570533701731708483697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23760752359485138223826101 2227570533701731708483697)
            ·
              refine ⟨1670677900276298781362773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2227570533701731708483697 1670677900276298781362773)
              ·
                refine ⟨19578256643862876344095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1670677900276298781362773 19578256643862876344095)
                ·
                  rfl

theorem cell22_514735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 8].length) (baseStart_514735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_514735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_514735 prefixEnd_514735 := by exact prefixLift 514735
  have htrace : WordTrace (prefixWord ++ tailWord_514735) baseStart_514735 baseEnd_514735 := by
    simpa [prefixWord, tailWord_514735, baseEnd_514735] using wordTrace_append hprefix tailTrace_514735
  have hstable : (prefixWord ++ tailWord_514735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514735).length < 2 ^ (prefixWord ++ tailWord_514735).sum := by decide
  have hdescent : baseEnd_514735 < baseStart_514735 := by decide
  rcases family_descends (prefixWord ++ tailWord_514735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514756 : List Nat := [2, 3, 3, 1, 1, 3, 2, 2, 2, 3]
def baseStart_514756 : Nat := 118140960795 + 514756 * 2 ^ 59
def prefixEnd_514756 : Nat := 4983230072969 + 3 ^ 40 * 514756 * 2
def baseEnd_514756 : Nat := 176211498523928832321791

theorem tailTrace_514756 : CollatzResearch.WordTrace tailWord_514756 prefixEnd_514756 176211498523928832321791 := by
  unfold tailWord_514756
  simp only [CollatzResearch.WordTrace]
  refine ⟨9387346861567200085386061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12516462482089600113848081 9387346861567200085386061)
  ·
    refine ⟨3520255073087700032019773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9387346861567200085386061 3520255073087700032019773)
    ·
      refine ⟨1320095652407887512007415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3520255073087700032019773 1320095652407887512007415)
      ·
        refine ⟨1980143478611831268011123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1320095652407887512007415 1980143478611831268011123)
        ·
          refine ⟨2970215217917746902016685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1980143478611831268011123 2970215217917746902016685)
          ·
            refine ⟨1113830706719155088256257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2970215217917746902016685 1113830706719155088256257)
            ·
              refine ⟨835373030039366316192193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1113830706719155088256257 835373030039366316192193)
              ·
                refine ⟨626529772529524737144145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 835373030039366316192193 626529772529524737144145)
                ·
                  refine ⟨469897329397143552858109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 626529772529524737144145 469897329397143552858109)
                  ·
                    refine ⟨176211498523928832321791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 469897329397143552858109 176211498523928832321791)
                    ·
                      rfl

theorem cell22_514756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_514756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_514756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_514756 prefixEnd_514756 := by exact prefixLift 514756
  have htrace : WordTrace (prefixWord ++ tailWord_514756) baseStart_514756 baseEnd_514756 := by
    simpa [prefixWord, tailWord_514756, baseEnd_514756] using wordTrace_append hprefix tailTrace_514756
  have hstable : (prefixWord ++ tailWord_514756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514756).length < 2 ^ (prefixWord ++ tailWord_514756).sum := by decide
  have hdescent : baseEnd_514756 < baseStart_514756 := by decide
  rcases family_descends (prefixWord ++ tailWord_514756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514795 : List Nat := [1, 1, 1, 1, 2, 4, 1, 1, 3, 7]
def baseStart_514795 : Nat := 118140960795 + 514795 * 2 ^ 59
def prefixEnd_514795 : Nat := 4983230072969 + 3 ^ 40 * 514795 * 2
def baseEnd_514795 : Nat := 176224849020945730596671

theorem tailTrace_514795 : CollatzResearch.WordTrace tailWord_514795 prefixEnd_514795 176224849020945730596671 := by
  unfold tailWord_514795
  simp only [CollatzResearch.WordTrace]
  refine ⟨18776116169993109831441839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12517410779995406554294559 18776116169993109831441839)
  ·
    refine ⟨28164174254989664747162759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18776116169993109831441839 28164174254989664747162759)
    ·
      refine ⟨42246261382484497120744139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28164174254989664747162759 42246261382484497120744139)
      ·
        refine ⟨63369392073726745681116209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42246261382484497120744139 63369392073726745681116209)
        ·
          refine ⟨47527044055295059260837157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63369392073726745681116209 47527044055295059260837157)
          ·
            refine ⟨8911320760367823611406967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47527044055295059260837157 8911320760367823611406967)
            ·
              refine ⟨13366981140551735417110451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8911320760367823611406967 13366981140551735417110451)
              ·
                refine ⟨20050471710827603125665677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13366981140551735417110451 20050471710827603125665677)
                ·
                  refine ⟨7518926891560351172124629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20050471710827603125665677 7518926891560351172124629)
                  ·
                    refine ⟨176224849020945730596671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7518926891560351172124629 176224849020945730596671)
                    ·
                      rfl

theorem cell22_514795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 7].length) (baseStart_514795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_514795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_514795 prefixEnd_514795 := by exact prefixLift 514795
  have htrace : WordTrace (prefixWord ++ tailWord_514795) baseStart_514795 baseEnd_514795 := by
    simpa [prefixWord, tailWord_514795, baseEnd_514795] using wordTrace_append hprefix tailTrace_514795
  have hstable : (prefixWord ++ tailWord_514795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514795).length < 2 ^ (prefixWord ++ tailWord_514795).sum := by decide
  have hdescent : baseEnd_514795 < baseStart_514795 := by decide
  rcases family_descends (prefixWord ++ tailWord_514795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514797 : List Nat := [1, 5, 1, 2, 1, 1, 2, 2, 7]
def baseStart_514797 : Nat := 118140960795 + 514797 * 2 ^ 59
def prefixEnd_514797 : Nat := 4983230072969 + 3 ^ 40 * 514797 * 2
def baseEnd_514797 : Nat := 58741844553939464015555

theorem tailTrace_514797 : CollatzResearch.WordTrace tailWord_514797 prefixEnd_514797 58741844553939464015555 := by
  unfold tailWord_514797
  simp only [CollatzResearch.WordTrace]
  refine ⟨18776189115985864173014645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12517459410657242782009763 18776189115985864173014645)
  ·
    refine ⟨1760267729623674766220123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18776189115985864173014645 1760267729623674766220123)
    ·
      refine ⟨2640401594435512149330185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1760267729623674766220123 2640401594435512149330185)
      ·
        refine ⟨1980301195826634111997639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2640401594435512149330185 1980301195826634111997639)
        ·
          refine ⟨2970451793739951167996459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1980301195826634111997639 2970451793739951167996459)
          ·
            refine ⟨4455677690609926751994689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2970451793739951167996459 4455677690609926751994689)
            ·
              refine ⟨3341758267957445063996017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4455677690609926751994689 3341758267957445063996017)
              ·
                refine ⟨2506318700968083797997013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3341758267957445063996017 2506318700968083797997013)
                ·
                  refine ⟨58741844553939464015555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2506318700968083797997013 58741844553939464015555)
                  ·
                    rfl

theorem cell22_514797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_514797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_514797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_514797 prefixEnd_514797 := by exact prefixLift 514797
  have htrace : WordTrace (prefixWord ++ tailWord_514797) baseStart_514797 baseEnd_514797 := by
    simpa [prefixWord, tailWord_514797, baseEnd_514797] using wordTrace_append hprefix tailTrace_514797
  have hstable : (prefixWord ++ tailWord_514797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514797).length < 2 ^ (prefixWord ++ tailWord_514797).sum := by decide
  have hdescent : baseEnd_514797 < baseStart_514797 := by decide
  rcases family_descends (prefixWord ++ tailWord_514797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514801 : List Nat := [1, 2, 2, 2, 2, 2, 4, 3, 1, 3]
def baseStart_514801 : Nat := 118140960795 + 514801 * 2 ^ 59
def prefixEnd_514801 : Nat := 4983230072969 + 3 ^ 40 * 514801 * 2
def baseEnd_514801 : Nat := 176226902943563714946653

theorem tailTrace_514801 : CollatzResearch.WordTrace tailWord_514801 prefixEnd_514801 176226902943563714946653 := by
  unfold tailWord_514801
  simp only [CollatzResearch.WordTrace]
  refine ⟨18776335007971372856160257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12517556671980915237440171 18776335007971372856160257)
  ·
    refine ⟨14082251255978529642120193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18776335007971372856160257 14082251255978529642120193)
    ·
      refine ⟨10561688441983897231590145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14082251255978529642120193 10561688441983897231590145)
      ·
        refine ⟨7921266331487922923692609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10561688441983897231590145 7921266331487922923692609)
        ·
          refine ⟨5940949748615942192769457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7921266331487922923692609 5940949748615942192769457)
          ·
            refine ⟨4455712311461956644577093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5940949748615942192769457 4455712311461956644577093)
            ·
              refine ⟨835446058399116870858205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4455712311461956644577093 835446058399116870858205)
              ·
                refine ⟨313292271899668826571827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 835446058399116870858205 313292271899668826571827)
                ·
                  refine ⟨469938407849503239857741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 313292271899668826571827 469938407849503239857741)
                  ·
                    refine ⟨176226902943563714946653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 469938407849503239857741 176226902943563714946653)
                    ·
                      rfl

theorem cell22_514801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 3, 1, 3].length) (baseStart_514801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_514801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_514801 prefixEnd_514801 := by exact prefixLift 514801
  have htrace : WordTrace (prefixWord ++ tailWord_514801) baseStart_514801 baseEnd_514801 := by
    simpa [prefixWord, tailWord_514801, baseEnd_514801] using wordTrace_append hprefix tailTrace_514801
  have hstable : (prefixWord ++ tailWord_514801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514801).length < 2 ^ (prefixWord ++ tailWord_514801).sum := by decide
  have hdescent : baseEnd_514801 < baseStart_514801 := by decide
  rcases family_descends (prefixWord ++ tailWord_514801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514812 : List Nat := [2, 2, 2, 1, 3, 2, 1, 2, 2, 5]
def baseStart_514812 : Nat := 118140960795 + 514812 * 2 ^ 59
def prefixEnd_514812 : Nat := 4983230072969 + 3 ^ 40 * 514812 * 2
def baseEnd_514812 : Nat := 176230668468363352921619

theorem tailTrace_514812 : CollatzResearch.WordTrace tailWord_514812 prefixEnd_514812 176230668468363352921619 := by
  unfold tailWord_514812
  simp only [CollatzResearch.WordTrace]
  refine ⟨9388368105465760867405345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12517824140621014489873793 9388368105465760867405345)
  ·
    refine ⟨7041276079099320650554009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9388368105465760867405345 7041276079099320650554009)
    ·
      refine ⟨5280957059324490487915507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7041276079099320650554009 5280957059324490487915507)
      ·
        refine ⟨7921435588986735731873261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5280957059324490487915507 7921435588986735731873261)
        ·
          refine ⟨2970538345870025899452473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7921435588986735731873261 2970538345870025899452473)
          ·
            refine ⟨2227903759402519424589355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2970538345870025899452473 2227903759402519424589355)
            ·
              refine ⟨3341855639103779136884033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2227903759402519424589355 3341855639103779136884033)
              ·
                refine ⟨2506391729327834352663025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3341855639103779136884033 2506391729327834352663025)
                ·
                  refine ⟨1879793796995875764497269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2506391729327834352663025 1879793796995875764497269)
                  ·
                    refine ⟨176230668468363352921619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1879793796995875764497269 176230668468363352921619)
                    ·
                      rfl

theorem cell22_514812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_514812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_514812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_514812 prefixEnd_514812 := by exact prefixLift 514812
  have htrace : WordTrace (prefixWord ++ tailWord_514812) baseStart_514812 baseEnd_514812 := by
    simpa [prefixWord, tailWord_514812, baseEnd_514812] using wordTrace_append hprefix tailTrace_514812
  have hstable : (prefixWord ++ tailWord_514812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514812).length < 2 ^ (prefixWord ++ tailWord_514812).sum := by decide
  have hdescent : baseEnd_514812 < baseStart_514812 := by decide
  rcases family_descends (prefixWord ++ tailWord_514812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514814 : List Nat := [4, 2, 2, 1, 2, 2, 1, 1, 7]
def baseStart_514814 : Nat := 118140960795 + 514814 * 2 ^ 59
def prefixEnd_514814 : Nat := 4983230072969 + 3 ^ 40 * 514814 * 2
def baseEnd_514814 : Nat := 58743784369745338123871

theorem tailTrace_514814 : CollatzResearch.WordTrace tailWord_514814 prefixEnd_514814 58743784369745338123871 := by
  unfold tailWord_514814
  simp only [CollatzResearch.WordTrace]
  refine ⟨2347101144615534509547937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12517872771282850717588997 2347101144615534509547937)
  ·
    refine ⟨1760325858461650882160953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2347101144615534509547937 1760325858461650882160953)
    ·
      refine ⟨1320244393846238161620715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1760325858461650882160953 1320244393846238161620715)
      ·
        refine ⟨1980366590769357242431073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1320244393846238161620715 1980366590769357242431073)
        ·
          refine ⟨1485274943077017931823305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1980366590769357242431073 1485274943077017931823305)
          ·
            refine ⟨1113956207307763448867479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1485274943077017931823305 1113956207307763448867479)
            ·
              refine ⟨1670934310961645173301219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1113956207307763448867479 1670934310961645173301219)
              ·
                refine ⟨2506401466442467759951829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1670934310961645173301219 2506401466442467759951829)
                ·
                  refine ⟨58743784369745338123871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2506401466442467759951829 58743784369745338123871)
                  ·
                    rfl

theorem cell22_514814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_514814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_514814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_514814 prefixEnd_514814 := by exact prefixLift 514814
  have htrace : WordTrace (prefixWord ++ tailWord_514814) baseStart_514814 baseEnd_514814 := by
    simpa [prefixWord, tailWord_514814, baseEnd_514814] using wordTrace_append hprefix tailTrace_514814
  have hstable : (prefixWord ++ tailWord_514814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514814).length < 2 ^ (prefixWord ++ tailWord_514814).sum := by decide
  have hdescent : baseEnd_514814 < baseStart_514814 := by decide
  rcases family_descends (prefixWord ++ tailWord_514814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514818 : List Nat := [3, 4, 1, 1, 1, 2, 2, 4, 1, 3]
def baseStart_514818 : Nat := 118140960795 + 514818 * 2 ^ 59
def prefixEnd_514818 : Nat := 4983230072969 + 3 ^ 40 * 514818 * 2
def baseEnd_514818 : Nat := 176232722390981337271601

theorem tailTrace_514818 : CollatzResearch.WordTrace tailWord_514818 prefixEnd_514818 176232722390981337271601 := by
  unfold tailWord_514818
  simp only [CollatzResearch.WordTrace]
  refine ⟨4694238762227446189882277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12517970032606523173019405 4694238762227446189882277)
  ·
    refine ⟨880169767917646160602927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4694238762227446189882277 880169767917646160602927)
    ·
      refine ⟨1320254651876469240904391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 880169767917646160602927 1320254651876469240904391)
      ·
        refine ⟨1980381977814703861356587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1320254651876469240904391 1980381977814703861356587)
        ·
          refine ⟨2970572966722055792034881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1980381977814703861356587 2970572966722055792034881)
          ·
            refine ⟨2227929725041541844026161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2970572966722055792034881 2227929725041541844026161)
            ·
              refine ⟨1670947293781156383019621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2227929725041541844026161 1670947293781156383019621)
              ·
                refine ⟨313302617583966821816179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1670947293781156383019621 313302617583966821816179)
                ·
                  refine ⟨469953926375950232724269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 313302617583966821816179 469953926375950232724269)
                  ·
                    refine ⟨176232722390981337271601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 469953926375950232724269 176232722390981337271601)
                    ·
                      rfl

theorem cell22_514818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_514818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_514818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_514818 prefixEnd_514818 := by exact prefixLift 514818
  have htrace : WordTrace (prefixWord ++ tailWord_514818) baseStart_514818 baseEnd_514818 := by
    simpa [prefixWord, tailWord_514818, baseEnd_514818] using wordTrace_append hprefix tailTrace_514818
  have hstable : (prefixWord ++ tailWord_514818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514818).length < 2 ^ (prefixWord ++ tailWord_514818).sum := by decide
  have hdescent : baseEnd_514818 < baseStart_514818 := by decide
  rcases family_descends (prefixWord ++ tailWord_514818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514842 : List Nat := [3, 1, 1, 3, 2, 1, 1, 4, 6]
def baseStart_514842 : Nat := 118140960795 + 514842 * 2 ^ 59
def prefixEnd_514842 : Nat := 4983230072969 + 3 ^ 40 * 514842 * 2
def baseEnd_514842 : Nat := 58746979360484424890509

theorem tailTrace_514842 : CollatzResearch.WordTrace tailWord_514842 prefixEnd_514842 58746979360484424890509 := by
  unfold tailWord_514842
  simp only [CollatzResearch.WordTrace]
  refine ⟨4694457600205709214600695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12518553600548557905601853 4694457600205709214600695)
  ·
    refine ⟨7041686400308563821901043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4694457600205709214600695 7041686400308563821901043)
    ·
      refine ⟨10562529600462845732851565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7041686400308563821901043 10562529600462845732851565)
      ·
        refine ⟨3960948600173567149819337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10562529600462845732851565 3960948600173567149819337)
        ·
          refine ⟨2970711450130175362364503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3960948600173567149819337 2970711450130175362364503)
          ·
            refine ⟨4456067175195263043546755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2970711450130175362364503 4456067175195263043546755)
            ·
              refine ⟨6684100762792894565320133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4456067175195263043546755 6684100762792894565320133)
              ·
                refine ⟨1253268893023667730997525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6684100762792894565320133 1253268893023667730997525)
                ·
                  refine ⟨58746979360484424890509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1253268893023667730997525 58746979360484424890509)
                  ·
                    rfl

theorem cell22_514842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 4, 6].length) (baseStart_514842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_514842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_514842 prefixEnd_514842 := by exact prefixLift 514842
  have htrace : WordTrace (prefixWord ++ tailWord_514842) baseStart_514842 baseEnd_514842 := by
    simpa [prefixWord, tailWord_514842, baseEnd_514842] using wordTrace_append hprefix tailTrace_514842
  have hstable : (prefixWord ++ tailWord_514842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514842).length < 2 ^ (prefixWord ++ tailWord_514842).sum := by decide
  have hdescent : baseEnd_514842 < baseStart_514842 := by decide
  rcases family_descends (prefixWord ++ tailWord_514842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514844 : List Nat := [2, 2, 3, 1, 1, 3, 1, 4, 1, 4]
def baseStart_514844 : Nat := 118140960795 + 514844 * 2 ^ 59
def prefixEnd_514844 : Nat := 4983230072969 + 3 ^ 40 * 514844 * 2
def baseEnd_514844 : Nat := 176241622722325936121521

theorem tailTrace_514844 : CollatzResearch.WordTrace tailWord_514844 prefixEnd_514844 176241622722325936121521 := by
  unfold tailWord_514844
  simp only [CollatzResearch.WordTrace]
  refine ⟨9388951673407795599987793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12518602231210394133317057 9388951673407795599987793)
  ·
    refine ⟨7041713755055846699990845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9388951673407795599987793 7041713755055846699990845)
    ·
      refine ⟨2640642658145942512496567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7041713755055846699990845 2640642658145942512496567)
      ·
        refine ⟨3960963987218913768744851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2640642658145942512496567 3960963987218913768744851)
        ·
          refine ⟨5941445980828370653117277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3960963987218913768744851 5941445980828370653117277)
          ·
            refine ⟨2228042242810638994918979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5941445980828370653117277 2228042242810638994918979)
            ·
              refine ⟨3342063364215958492378469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2228042242810638994918979 3342063364215958492378469)
              ·
                refine ⟨626636880790492217320963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3342063364215958492378469 626636880790492217320963)
                ·
                  refine ⟨939955321185738325981445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 626636880790492217320963 939955321185738325981445)
                  ·
                    refine ⟨176241622722325936121521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 939955321185738325981445 176241622722325936121521)
                    ·
                      rfl

theorem cell22_514844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_514844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_514844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_514844 prefixEnd_514844 := by exact prefixLift 514844
  have htrace : WordTrace (prefixWord ++ tailWord_514844) baseStart_514844 baseEnd_514844 := by
    simpa [prefixWord, tailWord_514844, baseEnd_514844] using wordTrace_append hprefix tailTrace_514844
  have hstable : (prefixWord ++ tailWord_514844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514844).length < 2 ^ (prefixWord ++ tailWord_514844).sum := by decide
  have hdescent : baseEnd_514844 < baseStart_514844 := by decide
  rcases family_descends (prefixWord ++ tailWord_514844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514949 : List Nat := [1, 3, 1, 1, 3, 3, 2, 3, 5]
def baseStart_514949 : Nat := 118140960795 + 514949 * 2 ^ 59
def prefixEnd_514949 : Nat := 4983230072969 + 3 ^ 40 * 514949 * 2
def baseEnd_514949 : Nat := 58759188789380220748733

theorem tailTrace_514949 : CollatzResearch.WordTrace tailWord_514949 prefixEnd_514949 58759188789380220748733 := by
  unfold tailWord_514949
  simp only [CollatzResearch.WordTrace]
  refine ⟨18781733011435194132547901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12521155340956796088365267 18781733011435194132547901)
  ·
    refine ⟨7043149879288197799705463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18781733011435194132547901 7043149879288197799705463)
    ·
      refine ⟨10564724818932296699558195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7043149879288197799705463 10564724818932296699558195)
      ·
        refine ⟨15847087228398445049337293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10564724818932296699558195 15847087228398445049337293)
        ·
          refine ⟨5942657710649416893501485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15847087228398445049337293 5942657710649416893501485)
          ·
            refine ⟨2228496641493531335063057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5942657710649416893501485 2228496641493531335063057)
            ·
              refine ⟨1671372481120148501297293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2228496641493531335063057 1671372481120148501297293)
              ·
                refine ⟨626764680420055687986485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1671372481120148501297293 626764680420055687986485)
                ·
                  refine ⟨58759188789380220748733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 626764680420055687986485 58759188789380220748733)
                  ·
                    rfl

theorem cell22_514949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 3, 5].length) (baseStart_514949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_514949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_514949 prefixEnd_514949 := by exact prefixLift 514949
  have htrace : WordTrace (prefixWord ++ tailWord_514949) baseStart_514949 baseEnd_514949 := by
    simpa [prefixWord, tailWord_514949, baseEnd_514949] using wordTrace_append hprefix tailTrace_514949
  have hstable : (prefixWord ++ tailWord_514949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514949).length < 2 ^ (prefixWord ++ tailWord_514949).sum := by decide
  have hdescent : baseEnd_514949 < baseStart_514949 := by decide
  rcases family_descends (prefixWord ++ tailWord_514949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514964 : List Nat := [2, 4, 2, 1, 1, 1, 1, 2, 1, 7]
def baseStart_514964 : Nat := 118140960795 + 514964 * 2 ^ 59
def prefixEnd_514964 : Nat := 4983230072969 + 3 ^ 40 * 514964 * 2
def baseEnd_514964 : Nat := 176282701174685623121153

theorem tailTrace_514964 : CollatzResearch.WordTrace tailWord_514964 prefixEnd_514964 176282701174685623121153 := by
  unfold tailWord_514964
  simp only [CollatzResearch.WordTrace]
  refine ⟨9391140053190425847171973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12521520070920567796229297 9391140053190425847171973)
  ·
    refine ⟨1760838759973204846344745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9391140053190425847171973 1760838759973204846344745)
    ·
      refine ⟨1320629069979903634758559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1760838759973204846344745 1320629069979903634758559)
      ·
        refine ⟨1980943604969855452137839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1320629069979903634758559 1980943604969855452137839)
        ·
          refine ⟨2971415407454783178206759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1980943604969855452137839 2971415407454783178206759)
          ·
            refine ⟨4457123111182174767310139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2971415407454783178206759 4457123111182174767310139)
            ·
              refine ⟨6685684666773262150965209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4457123111182174767310139 6685684666773262150965209)
              ·
                refine ⟨5014263500079946613223907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6685684666773262150965209 5014263500079946613223907)
                ·
                  refine ⟨7521395250119919919835861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5014263500079946613223907 7521395250119919919835861)
                  ·
                    refine ⟨176282701174685623121153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7521395250119919919835861 176282701174685623121153)
                    ·
                      rfl

theorem cell22_514964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_514964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_514964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_514964 prefixEnd_514964 := by exact prefixLift 514964
  have htrace : WordTrace (prefixWord ++ tailWord_514964) baseStart_514964 baseEnd_514964 := by
    simpa [prefixWord, tailWord_514964, baseEnd_514964] using wordTrace_append hprefix tailTrace_514964
  have hstable : (prefixWord ++ tailWord_514964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514964).length < 2 ^ (prefixWord ++ tailWord_514964).sum := by decide
  have hdescent : baseEnd_514964 < baseStart_514964 := by decide
  rcases family_descends (prefixWord ++ tailWord_514964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514970 : List Nat := [3, 1, 1, 4, 3, 1, 2, 3, 1, 3]
def baseStart_514970 : Nat := 118140960795 + 514970 * 2 ^ 59
def prefixEnd_514970 : Nat := 4983230072969 + 3 ^ 40 * 514970 * 2
def baseEnd_514970 : Nat := 176284755097303607471135

theorem tailTrace_514970 : CollatzResearch.WordTrace tailWord_514970 prefixEnd_514970 176284755097303607471135 := by
  unfold tailWord_514970
  simp only [CollatzResearch.WordTrace]
  refine ⟨4695624736089778679765591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12521665962906076479374909 4695624736089778679765591)
  ·
    refine ⟨7043437104134668019648387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4695624736089778679765591 7043437104134668019648387)
    ·
      refine ⟨10565155656202002029472581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7043437104134668019648387 10565155656202002029472581)
      ·
        refine ⟨1980966685537875380526109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10565155656202002029472581 1980966685537875380526109)
        ·
          refine ⟨742862507076703267697291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1980966685537875380526109 742862507076703267697291)
          ·
            refine ⟨1114293760615054901545937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 742862507076703267697291 1114293760615054901545937)
            ·
              refine ⟨835720320461291176159453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1114293760615054901545937 835720320461291176159453)
              ·
                refine ⟨313395120172984191059795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 835720320461291176159453 313395120172984191059795)
                ·
                  refine ⟨470092680259476286589693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 313395120172984191059795 470092680259476286589693)
                  ·
                    refine ⟨176284755097303607471135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 470092680259476286589693 176284755097303607471135)
                    ·
                      rfl

theorem cell22_514970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 3, 1, 3].length) (baseStart_514970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_514970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_514970 prefixEnd_514970 := by exact prefixLift 514970
  have htrace : WordTrace (prefixWord ++ tailWord_514970) baseStart_514970 baseEnd_514970 := by
    simpa [prefixWord, tailWord_514970, baseEnd_514970] using wordTrace_append hprefix tailTrace_514970
  have hstable : (prefixWord ++ tailWord_514970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514970).length < 2 ^ (prefixWord ++ tailWord_514970).sum := by decide
  have hdescent : baseEnd_514970 < baseStart_514970 := by decide
  rcases family_descends (prefixWord ++ tailWord_514970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514983 : List Nat := [1, 1, 6, 1, 3, 2, 1, 2, 5]
def baseStart_514983 : Nat := 118140960795 + 514983 * 2 ^ 59
def prefixEnd_514983 : Nat := 4983230072969 + 3 ^ 40 * 514983 * 2
def baseEnd_514983 : Nat := 58763068420991968965365

theorem tailTrace_514983 : CollatzResearch.WordTrace tailWord_514983 prefixEnd_514983 58763068420991968965365 := by
  unfold tailWord_514983
  simp only [CollatzResearch.WordTrace]
  refine ⟨18782973093312017939285603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12521982062208011959523735 18782973093312017939285603)
  ·
    refine ⟨28174459639968026908928405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18782973093312017939285603 28174459639968026908928405)
    ·
      refine ⟨1320677795623501261356019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 28174459639968026908928405 1320677795623501261356019)
      ·
        refine ⟨1981016693435251892034029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1320677795623501261356019 1981016693435251892034029)
        ·
          refine ⟨742881260038219459512761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1981016693435251892034029 742881260038219459512761)
          ·
            refine ⟨557160945028664594634571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 742881260038219459512761 557160945028664594634571)
            ·
              refine ⟨835741417542996891951857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 557160945028664594634571 835741417542996891951857)
              ·
                refine ⟨626806063157247668963893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 835741417542996891951857 626806063157247668963893)
                ·
                  refine ⟨58763068420991968965365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 626806063157247668963893 58763068420991968965365)
                  ·
                    rfl

theorem cell22_514983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 2, 5].length) (baseStart_514983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_514983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_514983 prefixEnd_514983 := by exact prefixLift 514983
  have htrace : WordTrace (prefixWord ++ tailWord_514983) baseStart_514983 baseEnd_514983 := by
    simpa [prefixWord, tailWord_514983, baseEnd_514983] using wordTrace_append hprefix tailTrace_514983
  have hstable : (prefixWord ++ tailWord_514983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514983).length < 2 ^ (prefixWord ++ tailWord_514983).sum := by decide
  have hdescent : baseEnd_514983 < baseStart_514983 := by decide
  rcases family_descends (prefixWord ++ tailWord_514983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514992 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 1, 11]
def baseStart_514992 : Nat := 118140960795 + 514992 * 2 ^ 59
def prefixEnd_514992 : Nat := 4983230072969 + 3 ^ 40 * 514992 * 2
def baseEnd_514992 : Nat := 176292286146902883421067

theorem tailTrace_514992 : CollatzResearch.WordTrace tailWord_514992 prefixEnd_514992 176292286146902883421067 := by
  unfold tailWord_514992
  simp only [CollatzResearch.WordTrace]
  refine ⟨9391650675139706238181615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12522200900186274984242153 9391650675139706238181615)
  ·
    refine ⟨14087476012709559357272423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9391650675139706238181615 14087476012709559357272423)
    ·
      refine ⟨21131214019064339035908635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14087476012709559357272423 21131214019064339035908635)
      ·
        refine ⟨31696821028596508553862953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21131214019064339035908635 31696821028596508553862953)
        ·
          refine ⟨23772615771447381415397215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31696821028596508553862953 23772615771447381415397215)
          ·
            refine ⟨35658923657171072123095823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23772615771447381415397215 35658923657171072123095823)
            ·
              refine ⟨53488385485756608184643735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35658923657171072123095823 53488385485756608184643735)
              ·
                refine ⟨80232578228634912276965603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53488385485756608184643735 80232578228634912276965603)
                ·
                  refine ⟨120348867342952368415448405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80232578228634912276965603 120348867342952368415448405)
                  ·
                    refine ⟨176292286146902883421067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 120348867342952368415448405 176292286146902883421067)
                    ·
                      rfl

theorem cell22_514992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 11].length) (baseStart_514992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_514992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_514992 prefixEnd_514992 := by exact prefixLift 514992
  have htrace : WordTrace (prefixWord ++ tailWord_514992) baseStart_514992 baseEnd_514992 := by
    simpa [prefixWord, tailWord_514992, baseEnd_514992] using wordTrace_append hprefix tailTrace_514992
  have hstable : (prefixWord ++ tailWord_514992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514992).length < 2 ^ (prefixWord ++ tailWord_514992).sum := by decide
  have hdescent : baseEnd_514992 < baseStart_514992 := by decide
  rcases family_descends (prefixWord ++ tailWord_514992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515021 : List Nat := [1, 6, 3, 1, 1, 2, 1, 3, 1, 3]
def baseStart_515021 : Nat := 118140960795 + 515021 * 2 ^ 59
def prefixEnd_515021 : Nat := 4983230072969 + 3 ^ 40 * 515021 * 2
def baseEnd_515021 : Nat := 176302213439556474445979

theorem tailTrace_515021 : CollatzResearch.WordTrace tailWord_515021 prefixEnd_515021 176302213439556474445979 := by
  unfold tailWord_515021
  simp only [CollatzResearch.WordTrace]
  refine ⟨18784359067174350429168917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12522906044782900286112611 18784359067174350429168917)
  ·
    refine ⟨880516831273797676367293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18784359067174350429168917 880516831273797676367293)
    ·
      refine ⟨330193811727674128637735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 880516831273797676367293 330193811727674128637735)
      ·
        refine ⟨495290717591511192956603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330193811727674128637735 495290717591511192956603)
        ·
          refine ⟨742936076387266789434905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 495290717591511192956603 742936076387266789434905)
          ·
            refine ⟨557202057290450092076179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 742936076387266789434905 557202057290450092076179)
            ·
              refine ⟨835803085935675138114269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 557202057290450092076179 835803085935675138114269)
              ·
                refine ⟨313426157225878176792851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 835803085935675138114269 313426157225878176792851)
                ·
                  refine ⟨470139235838817265189277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 313426157225878176792851 470139235838817265189277)
                  ·
                    refine ⟨176302213439556474445979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 470139235838817265189277 176302213439556474445979)
                    ·
                      rfl

theorem cell22_515021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_515021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_515021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_515021 prefixEnd_515021 := by exact prefixLift 515021
  have htrace : WordTrace (prefixWord ++ tailWord_515021) baseStart_515021 baseEnd_515021 := by
    simpa [prefixWord, tailWord_515021, baseEnd_515021] using wordTrace_append hprefix tailTrace_515021
  have hstable : (prefixWord ++ tailWord_515021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515021).length < 2 ^ (prefixWord ++ tailWord_515021).sum := by decide
  have hdescent : baseEnd_515021 < baseStart_515021 := by decide
  rcases family_descends (prefixWord ++ tailWord_515021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515024 : List Nat := [2, 1, 1, 1, 1, 2, 3, 5, 2, 4]
def baseStart_515024 : Nat := 118140960795 + 515024 * 2 ^ 59
def prefixEnd_515024 : Nat := 4983230072969 + 3 ^ 40 * 515024 * 2
def baseEnd_515024 : Nat := 176303240400865466620969

theorem tailTrace_515024 : CollatzResearch.WordTrace tailWord_515024 prefixEnd_515024 176303240400865466620969 := by
  unfold tailWord_515024
  simp only [CollatzResearch.WordTrace]
  refine ⟨9392234243081740970764063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12522978990775654627685417 9392234243081740970764063)
  ·
    refine ⟨14088351364622611456146095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9392234243081740970764063 14088351364622611456146095)
    ·
      refine ⟨21132527046933917184219143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14088351364622611456146095 21132527046933917184219143)
      ·
        refine ⟨31698790570400875776328715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21132527046933917184219143 31698790570400875776328715)
        ·
          refine ⟨47548185855601313664493073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31698790570400875776328715 47548185855601313664493073)
          ·
            refine ⟨35661139391700985248369805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47548185855601313664493073 35661139391700985248369805)
            ·
              refine ⟨13372927271887869468138677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35661139391700985248369805 13372927271887869468138677)
              ·
                refine ⟨1253711931739487762638001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13372927271887869468138677 1253711931739487762638001)
                ·
                  refine ⟨940283948804615821978501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1253711931739487762638001 940283948804615821978501)
                  ·
                    refine ⟨176303240400865466620969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 940283948804615821978501 176303240400865466620969)
                    ·
                      rfl

theorem cell22_515024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 5, 2, 4].length) (baseStart_515024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_515024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_515024 prefixEnd_515024 := by exact prefixLift 515024
  have htrace : WordTrace (prefixWord ++ tailWord_515024) baseStart_515024 baseEnd_515024 := by
    simpa [prefixWord, tailWord_515024, baseEnd_515024] using wordTrace_append hprefix tailTrace_515024
  have hstable : (prefixWord ++ tailWord_515024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515024).length < 2 ^ (prefixWord ++ tailWord_515024).sum := by decide
  have hdescent : baseEnd_515024 < baseStart_515024 := by decide
  rcases family_descends (prefixWord ++ tailWord_515024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515028 : List Nat := [2, 4, 1, 2, 1, 2, 3, 3, 4]
def baseStart_515028 : Nat := 118140960795 + 515028 * 2 ^ 59
def prefixEnd_515028 : Nat := 4983230072969 + 3 ^ 40 * 515028 * 2
def baseEnd_515028 : Nat := 58768203227536929840319

theorem tailTrace_515028 : CollatzResearch.WordTrace tailWord_515028 prefixEnd_515028 58768203227536929840319 := by
  unfold tailWord_515028
  simp only [CollatzResearch.WordTrace]
  refine ⟨9392307189074495312336869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12523076252099327083115825 9392307189074495312336869)
  ·
    refine ⟨1761057597951467871063163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9392307189074495312336869 1761057597951467871063163)
    ·
      refine ⟨2641586396927201806594745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1761057597951467871063163 2641586396927201806594745)
      ·
        refine ⟨1981189797695401354946059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2641586396927201806594745 1981189797695401354946059)
        ·
          refine ⟨2971784696543102032419089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1981189797695401354946059 2971784696543102032419089)
          ·
            refine ⟨2228838522407326524314317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2971784696543102032419089 2228838522407326524314317)
            ·
              refine ⟨835814445902747446617869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2228838522407326524314317 835814445902747446617869)
              ·
                refine ⟨313430417213530292481701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 835814445902747446617869 313430417213530292481701)
                ·
                  refine ⟨58768203227536929840319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 313430417213530292481701 58768203227536929840319)
                  ·
                    rfl

theorem cell22_515028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 3, 4].length) (baseStart_515028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_515028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_515028 prefixEnd_515028 := by exact prefixLift 515028
  have htrace : WordTrace (prefixWord ++ tailWord_515028) baseStart_515028 baseEnd_515028 := by
    simpa [prefixWord, tailWord_515028, baseEnd_515028] using wordTrace_append hprefix tailTrace_515028
  have hstable : (prefixWord ++ tailWord_515028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515028).length < 2 ^ (prefixWord ++ tailWord_515028).sum := by decide
  have hdescent : baseEnd_515028 < baseStart_515028 := by decide
  rcases family_descends (prefixWord ++ tailWord_515028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515045 : List Nat := [1, 3, 1, 6, 2, 1, 1, 1, 6]
def baseStart_515045 : Nat := 118140960795 + 515045 * 2 ^ 59
def prefixEnd_515045 : Nat := 4983230072969 + 3 ^ 40 * 515045 * 2
def baseEnd_515045 : Nat := 58770143043342803948635

theorem tailTrace_515045 : CollatzResearch.WordTrace tailWord_515045 prefixEnd_515045 58770143043342803948635 := by
  unfold tailWord_515045
  simp only [CollatzResearch.WordTrace]
  refine ⟨18785234419087402528042589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12523489612724935018695059 18785234419087402528042589)
  ·
    refine ⟨7044462907157775948015971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18785234419087402528042589 7044462907157775948015971)
    ·
      refine ⟨10566694360736663922023957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7044462907157775948015971 10566694360736663922023957)
      ·
        refine ⟨495313798159531121344873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 10566694360736663922023957 495313798159531121344873)
        ·
          refine ⟨371485348619648341008655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 495313798159531121344873 371485348619648341008655)
          ·
            refine ⟨557228022929472511512983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371485348619648341008655 557228022929472511512983)
            ·
              refine ⟨835842034394208767269475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 557228022929472511512983 835842034394208767269475)
              ·
                refine ⟨1253763051591313150904213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 835842034394208767269475 1253763051591313150904213)
                ·
                  refine ⟨58770143043342803948635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1253763051591313150904213 58770143043342803948635)
                  ·
                    rfl

theorem cell22_515045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 1, 6].length) (baseStart_515045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_515045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_515045 prefixEnd_515045 := by exact prefixLift 515045
  have htrace : WordTrace (prefixWord ++ tailWord_515045) baseStart_515045 baseEnd_515045 := by
    simpa [prefixWord, tailWord_515045, baseEnd_515045] using wordTrace_append hprefix tailTrace_515045
  have hstable : (prefixWord ++ tailWord_515045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515045).length < 2 ^ (prefixWord ++ tailWord_515045).sum := by decide
  have hdescent : baseEnd_515045 < baseStart_515045 := by decide
  rcases family_descends (prefixWord ++ tailWord_515045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515090 : List Nat := [3, 2, 5, 1, 2, 9]
def baseStart_515090 : Nat := 118140960795 + 515090 * 2 ^ 59
def prefixEnd_515090 : Nat := 4983230072969 + 3 ^ 40 * 515090 * 2
def baseEnd_515090 : Nat := 2176862142588435734207

theorem tailTrace_515090 : CollatzResearch.WordTrace tailWord_515090 prefixEnd_515090 2176862142588435734207 := by
  unfold tailWord_515090
  simp only [CollatzResearch.WordTrace]
  refine ⟨4696718925981093803357681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12524583802616250142287149 4696718925981093803357681)
  ·
    refine ⟨3522539194485820352518261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4696718925981093803357681 3522539194485820352518261)
    ·
      refine ⟨330238049483045658048587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3522539194485820352518261 330238049483045658048587)
      ·
        refine ⟨495357074224568487072881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330238049483045658048587 495357074224568487072881)
        ·
          refine ⟨371517805668426365304661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 495357074224568487072881 371517805668426365304661)
          ·
            refine ⟨2176862142588435734207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 371517805668426365304661 2176862142588435734207)
            ·
              rfl

theorem cell22_515090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 9].length) (baseStart_515090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_515090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_515090 prefixEnd_515090 := by exact prefixLift 515090
  have htrace : WordTrace (prefixWord ++ tailWord_515090) baseStart_515090 baseEnd_515090 := by
    simpa [prefixWord, tailWord_515090, baseEnd_515090] using wordTrace_append hprefix tailTrace_515090
  have hstable : (prefixWord ++ tailWord_515090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515090).length < 2 ^ (prefixWord ++ tailWord_515090).sum := by decide
  have hdescent : baseEnd_515090 < baseStart_515090 := by decide
  rcases family_descends (prefixWord ++ tailWord_515090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515105 : List Nat := [1, 2, 3, 2, 3, 2, 1, 4, 1, 3]
def baseStart_515105 : Nat := 118140960795 + 515105 * 2 ^ 59
def prefixEnd_515105 : Nat := 4983230072969 + 3 ^ 40 * 515105 * 2
def baseEnd_515105 : Nat := 176330968356208255345721

theorem tailTrace_515105 : CollatzResearch.WordTrace tailWord_515105 prefixEnd_515105 176330968356208255345721 := by
  unfold tailWord_515105
  simp only [CollatzResearch.WordTrace]
  refine ⟨18787422798870032775226769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12524948532580021850151179 18787422798870032775226769)
  ·
    refine ⟨14090567099152524581420077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18787422798870032775226769 14090567099152524581420077)
    ·
      refine ⟨5283962662182196718032529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14090567099152524581420077 5283962662182196718032529)
      ·
        refine ⟨3962971996636647538524397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5283962662182196718032529 3962971996636647538524397)
        ·
          refine ⟨1486114498738742826946649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3962971996636647538524397 1486114498738742826946649)
          ·
            refine ⟨1114585874054057120209987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1486114498738742826946649 1114585874054057120209987)
            ·
              refine ⟨1671878811081085680314981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1114585874054057120209987 1671878811081085680314981)
              ·
                refine ⟨313477277077703565059059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1671878811081085680314981 313477277077703565059059)
                ·
                  refine ⟨470215915616555347588589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 313477277077703565059059 470215915616555347588589)
                  ·
                    refine ⟨176330968356208255345721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 470215915616555347588589 176330968356208255345721)
                    ·
                      rfl

theorem cell22_515105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 4, 1, 3].length) (baseStart_515105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_515105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_515105 prefixEnd_515105 := by exact prefixLift 515105
  have htrace : WordTrace (prefixWord ++ tailWord_515105) baseStart_515105 baseEnd_515105 := by
    simpa [prefixWord, tailWord_515105, baseEnd_515105] using wordTrace_append hprefix tailTrace_515105
  have hstable : (prefixWord ++ tailWord_515105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515105).length < 2 ^ (prefixWord ++ tailWord_515105).sum := by decide
  have hdescent : baseEnd_515105 < baseStart_515105 := by decide
  rcases family_descends (prefixWord ++ tailWord_515105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515178 : List Nat := [3, 1, 3, 2, 2, 1, 3, 1, 1, 5]
def baseStart_515178 : Nat := 118140960795 + 515178 * 2 ^ 59
def prefixEnd_515178 : Nat := 4983230072969 + 3 ^ 40 * 515178 * 2
def baseEnd_515178 : Nat := 176355957748060398270497

theorem tailTrace_515178 : CollatzResearch.WordTrace tailWord_515178 prefixEnd_515178 176355957748060398270497 := by
  unfold tailWord_515178
  simp only [CollatzResearch.WordTrace]
  refine ⟨4697521331901391560658547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12526723551737044161756125 4697521331901391560658547)
  ·
    refine ⟨7046281997852087340987821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4697521331901391560658547 7046281997852087340987821)
    ·
      refine ⟨2642355749194532752870433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7046281997852087340987821 2642355749194532752870433)
      ·
        refine ⟨1981766811895899564652825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2642355749194532752870433 1981766811895899564652825)
        ·
          refine ⟨1486325108921924673489619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1981766811895899564652825 1486325108921924673489619)
          ·
            refine ⟨2229487663382887010234429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1486325108921924673489619 2229487663382887010234429)
            ·
              refine ⟨836057873768582628837911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2229487663382887010234429 836057873768582628837911)
              ·
                refine ⟨1254086810652873943256867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 836057873768582628837911 1254086810652873943256867)
                ·
                  refine ⟨1881130215979310914885301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1254086810652873943256867 1881130215979310914885301)
                  ·
                    refine ⟨176355957748060398270497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1881130215979310914885301 176355957748060398270497)
                    ·
                      rfl

theorem cell22_515178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_515178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_515178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_515178 prefixEnd_515178 := by exact prefixLift 515178
  have htrace : WordTrace (prefixWord ++ tailWord_515178) baseStart_515178 baseEnd_515178 := by
    simpa [prefixWord, tailWord_515178, baseEnd_515178] using wordTrace_append hprefix tailTrace_515178
  have hstable : (prefixWord ++ tailWord_515178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515178).length < 2 ^ (prefixWord ++ tailWord_515178).sum := by decide
  have hdescent : baseEnd_515178 < baseStart_515178 := by decide
  rcases family_descends (prefixWord ++ tailWord_515178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515208 : List Nat := [2, 1, 3, 4, 2, 2, 8]
def baseStart_515208 : Nat := 118140960795 + 515208 * 2 ^ 59
def prefixEnd_515208 : Nat := 4983230072969 + 3 ^ 40 * 515208 * 2
def baseEnd_515208 : Nat := 6532082494857419260015

theorem tailTrace_515208 : CollatzResearch.WordTrace tailWord_515208 prefixEnd_515208 6532082494857419260015 := by
  unfold tailWord_515208
  simp only [CollatzResearch.WordTrace]
  refine ⟨9395589758748440683113139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12527453011664587577484185 9395589758748440683113139)
  ·
    refine ⟨14093384638122661024669709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9395589758748440683113139 14093384638122661024669709)
    ·
      refine ⟨5285019239295997884251141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14093384638122661024669709 5285019239295997884251141)
      ·
        refine ⟨990941107367999603297089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5285019239295997884251141 990941107367999603297089)
        ·
          refine ⟨743205830525999702472817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 990941107367999603297089 743205830525999702472817)
          ·
            refine ⟨557404372894499776854613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 743205830525999702472817 557404372894499776854613)
            ·
              refine ⟨6532082494857419260015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 557404372894499776854613 6532082494857419260015)
              ·
                rfl

theorem cell22_515208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 8].length) (baseStart_515208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_515208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_515208 prefixEnd_515208 := by exact prefixLift 515208
  have htrace : WordTrace (prefixWord ++ tailWord_515208) baseStart_515208 baseEnd_515208 := by
    simpa [prefixWord, tailWord_515208, baseEnd_515208] using wordTrace_append hprefix tailTrace_515208
  have hstable : (prefixWord ++ tailWord_515208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515208).length < 2 ^ (prefixWord ++ tailWord_515208).sum := by decide
  have hdescent : baseEnd_515208 < baseStart_515208 := by decide
  rcases family_descends (prefixWord ++ tailWord_515208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515274 : List Nat := [3, 1, 2, 1, 3, 4, 2, 2, 1, 3]
def baseStart_515274 : Nat := 118140960795 + 515274 * 2 ^ 59
def prefixEnd_515274 : Nat := 4983230072969 + 3 ^ 40 * 515274 * 2
def baseEnd_515274 : Nat := 176388820509948147870203

theorem tailTrace_515274 : CollatzResearch.WordTrace tailWord_515274 prefixEnd_515274 176388820509948147870203 := by
  unfold tailWord_515274
  simp only [CollatzResearch.WordTrace]
  refine ⟨4698396683814443659532219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12529057823505183092085917 4698396683814443659532219)
  ·
    refine ⟨7047595025721665489298329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4698396683814443659532219 7047595025721665489298329)
    ·
      refine ⟨5285696269291249116973747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7047595025721665489298329 5285696269291249116973747)
      ·
        refine ⟨7928544403936873675460621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5285696269291249116973747 7928544403936873675460621)
        ·
          refine ⟨2973204151476327628297733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7928544403936873675460621 2973204151476327628297733)
          ·
            refine ⟨557475778401811430305825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2973204151476327628297733 557475778401811430305825)
            ·
              refine ⟨418106833801358572729369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 557475778401811430305825 418106833801358572729369)
              ·
                refine ⟨313580125351018929547027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 418106833801358572729369 313580125351018929547027)
                ·
                  refine ⟨470370188026528394320541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 313580125351018929547027 470370188026528394320541)
                  ·
                    refine ⟨176388820509948147870203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 470370188026528394320541 176388820509948147870203)
                    ·
                      rfl

theorem cell22_515274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 2, 2, 1, 3].length) (baseStart_515274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_515274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_515274 prefixEnd_515274 := by exact prefixLift 515274
  have htrace : WordTrace (prefixWord ++ tailWord_515274) baseStart_515274 baseEnd_515274 := by
    simpa [prefixWord, tailWord_515274, baseEnd_515274] using wordTrace_append hprefix tailTrace_515274
  have hstable : (prefixWord ++ tailWord_515274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515274).length < 2 ^ (prefixWord ++ tailWord_515274).sum := by decide
  have hdescent : baseEnd_515274 < baseStart_515274 := by decide
  rcases family_descends (prefixWord ++ tailWord_515274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515281 : List Nat := [1, 2, 2, 1, 2, 2, 1, 5, 6]
def baseStart_515281 : Nat := 118140960795 + 515281 * 2 ^ 59
def prefixEnd_515281 : Nat := 4983230072969 + 3 ^ 40 * 515281 * 2
def baseEnd_515281 : Nat := 58797072251000820981727

theorem tailTrace_515281 : CollatzResearch.WordTrace tailWord_515281 prefixEnd_515281 58797072251000820981727 := by
  unfold tailWord_515281
  simp only [CollatzResearch.WordTrace]
  refine ⟨18793842046232414833633697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12529228030821609889089131 18793842046232414833633697)
  ·
    refine ⟨14095381534674311125225273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18793842046232414833633697 14095381534674311125225273)
    ·
      refine ⟨10571536151005733343918955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14095381534674311125225273 10571536151005733343918955)
      ·
        refine ⟨15857304226508600015878433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10571536151005733343918955 15857304226508600015878433)
        ·
          refine ⟨11892978169881450011908825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15857304226508600015878433 11892978169881450011908825)
          ·
            refine ⟨8919733627411087508931619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11892978169881450011908825 8919733627411087508931619)
            ·
              refine ⟨13379600441116631263397429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8919733627411087508931619 13379600441116631263397429)
              ·
                refine ⟨1254337541354684180943509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13379600441116631263397429 1254337541354684180943509)
                ·
                  refine ⟨58797072251000820981727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1254337541354684180943509 58797072251000820981727)
                  ·
                    rfl

theorem cell22_515281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 5, 6].length) (baseStart_515281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_515281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_515281 prefixEnd_515281 := by exact prefixLift 515281
  have htrace : WordTrace (prefixWord ++ tailWord_515281) baseStart_515281 baseEnd_515281 := by
    simpa [prefixWord, tailWord_515281, baseEnd_515281] using wordTrace_append hprefix tailTrace_515281
  have hstable : (prefixWord ++ tailWord_515281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515281).length < 2 ^ (prefixWord ++ tailWord_515281).sum := by decide
  have hdescent : baseEnd_515281 < baseStart_515281 := by decide
  rcases family_descends (prefixWord ++ tailWord_515281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515313 : List Nat := [1, 2, 2, 2, 2, 1, 1, 4, 4, 3]
def baseStart_515313 : Nat := 118140960795 + 515313 * 2 ^ 59
def prefixEnd_515313 : Nat := 4983230072969 + 3 ^ 40 * 515313 * 2
def baseEnd_515313 : Nat := 176402171006965046145083

theorem tailTrace_515313 : CollatzResearch.WordTrace tailWord_515313 prefixEnd_515313 176402171006965046145083 := by
  unfold tailWord_515313
  simp only [CollatzResearch.WordTrace]
  refine ⟨18795009182116484298798593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12530006121410989532532395 18795009182116484298798593)
  ·
    refine ⟨14096256886587363224098945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18795009182116484298798593 14096256886587363224098945)
    ·
      refine ⟨10572192664940522418074209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14096256886587363224098945 10572192664940522418074209)
      ·
        refine ⟨7929144498705391813555657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10572192664940522418074209 7929144498705391813555657)
        ·
          refine ⟨5946858374029043860166743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7929144498705391813555657 5946858374029043860166743)
          ·
            refine ⟨8920287561043565790250115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5946858374029043860166743 8920287561043565790250115)
            ·
              refine ⟨13380431341565348685375173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8920287561043565790250115 13380431341565348685375173)
              ·
                refine ⟨2508830876543502878507845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13380431341565348685375173 2508830876543502878507845)
                ·
                  refine ⟨470405789351906789720221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2508830876543502878507845 470405789351906789720221)
                  ·
                    refine ⟨176402171006965046145083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 470405789351906789720221 176402171006965046145083)
                    ·
                      rfl

theorem cell22_515313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 4, 3].length) (baseStart_515313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_515313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_515313 prefixEnd_515313 := by exact prefixLift 515313
  have htrace : WordTrace (prefixWord ++ tailWord_515313) baseStart_515313 baseEnd_515313 := by
    simpa [prefixWord, tailWord_515313, baseEnd_515313] using wordTrace_append hprefix tailTrace_515313
  have hstable : (prefixWord ++ tailWord_515313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515313).length < 2 ^ (prefixWord ++ tailWord_515313).sum := by decide
  have hdescent : baseEnd_515313 < baseStart_515313 := by decide
  rcases family_descends (prefixWord ++ tailWord_515313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515315 : List Nat := [1, 1, 1, 2, 2, 6, 2, 3, 4]
def baseStart_515315 : Nat := 118140960795 + 515315 * 2 ^ 59
def prefixEnd_515315 : Nat := 4983230072969 + 3 ^ 40 * 515315 * 2
def baseEnd_515315 : Nat := 58800951882612569198359

theorem tailTrace_515315 : CollatzResearch.WordTrace tailWord_515315 prefixEnd_515315 58800951882612569198359 := by
  unfold tailWord_515315
  simp only [CollatzResearch.WordTrace]
  refine ⟨18795082128109238640371399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12530054752072825760247599 18795082128109238640371399)
  ·
    refine ⟨28192623192163857960557099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18795082128109238640371399 28192623192163857960557099)
    ·
      refine ⟨42288934788245786940835649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28192623192163857960557099 42288934788245786940835649)
      ·
        refine ⟨31716701091184340205626737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42288934788245786940835649 31716701091184340205626737)
        ·
          refine ⟨23787525818388255154220053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31716701091184340205626737 23787525818388255154220053)
          ·
            refine ⟨1115040272736949460354065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 23787525818388255154220053 1115040272736949460354065)
            ·
              refine ⟨836280204552712095265549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1115040272736949460354065 836280204552712095265549)
              ·
                refine ⟨313605076707267035724581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 836280204552712095265549 313605076707267035724581)
                ·
                  refine ⟨58800951882612569198359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 313605076707267035724581 58800951882612569198359)
                  ·
                    rfl

theorem cell22_515315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 3, 4].length) (baseStart_515315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_515315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_515315 prefixEnd_515315 := by exact prefixLift 515315
  have htrace : WordTrace (prefixWord ++ tailWord_515315) baseStart_515315 baseEnd_515315 := by
    simpa [prefixWord, tailWord_515315, baseEnd_515315] using wordTrace_append hprefix tailTrace_515315
  have hstable : (prefixWord ++ tailWord_515315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515315).length < 2 ^ (prefixWord ++ tailWord_515315).sum := by decide
  have hdescent : baseEnd_515315 < baseStart_515315 := by decide
  rcases family_descends (prefixWord ++ tailWord_515315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515388 : List Nat := [2, 2, 2, 2, 1, 3, 2, 1, 7]
def baseStart_515388 : Nat := 118140960795 + 515388 * 2 ^ 59
def prefixEnd_515388 : Nat := 4983230072969 + 3 ^ 40 * 515388 * 2
def baseEnd_515388 : Nat := 58809281679896616839951

theorem tailTrace_515388 : CollatzResearch.WordTrace tailWord_515388 prefixEnd_515388 58809281679896616839951 := by
  unfold tailWord_515388
  simp only [CollatzResearch.WordTrace]
  refine ⟨9398872328422386053889409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12531829771229848071852545 9398872328422386053889409)
  ·
    refine ⟨7049154246316789540417057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9398872328422386053889409 7049154246316789540417057)
    ·
      refine ⟨5286865684737592155312793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7049154246316789540417057 5286865684737592155312793)
      ·
        refine ⟨3965149263553194116484595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5286865684737592155312793 3965149263553194116484595)
        ·
          refine ⟨5947723895329791174726893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3965149263553194116484595 5947723895329791174726893)
          ·
            refine ⟨2230396460748671690522585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5947723895329791174726893 2230396460748671690522585)
            ·
              refine ⟨1672797345561503767891939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2230396460748671690522585 1672797345561503767891939)
              ·
                refine ⟨2509196018342255651837909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1672797345561503767891939 2509196018342255651837909)
                ·
                  refine ⟨58809281679896616839951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2509196018342255651837909 58809281679896616839951)
                  ·
                    rfl

theorem cell22_515388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 7].length) (baseStart_515388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_515388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_515388 prefixEnd_515388 := by exact prefixLift 515388
  have htrace : WordTrace (prefixWord ++ tailWord_515388) baseStart_515388 baseEnd_515388 := by
    simpa [prefixWord, tailWord_515388, baseEnd_515388] using wordTrace_append hprefix tailTrace_515388
  have hstable : (prefixWord ++ tailWord_515388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515388).length < 2 ^ (prefixWord ++ tailWord_515388).sum := by decide
  have hdescent : baseEnd_515388 < baseStart_515388 := by decide
  rcases family_descends (prefixWord ++ tailWord_515388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515450 : List Nat := [3, 1, 1, 1, 1, 1, 2, 8, 4]
def baseStart_515450 : Nat := 118140960795 + 515450 * 2 ^ 59
def prefixEnd_515450 : Nat := 4983230072969 + 3 ^ 40 * 515450 * 2
def baseEnd_515450 : Nat := 58816356302247451823221

theorem tailTrace_515450 : CollatzResearch.WordTrace tailWord_515450 prefixEnd_515450 58816356302247451823221 := by
  unfold tailWord_515450
  simp only [CollatzResearch.WordTrace]
  refine ⟨4700001495655039174133951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12533337321746771131023869 4700001495655039174133951)
  ·
    refine ⟨7050002243482558761200927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4700001495655039174133951 7050002243482558761200927)
    ·
      refine ⟨10575003365223838141801391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7050002243482558761200927 10575003365223838141801391)
      ·
        refine ⟨15862505047835757212702087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10575003365223838141801391 15862505047835757212702087)
        ·
          refine ⟨23793757571753635819053131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15862505047835757212702087 23793757571753635819053131)
          ·
            refine ⟨35690636357630453728579697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23793757571753635819053131 35690636357630453728579697)
            ·
              refine ⟨26767977268222840296434773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35690636357630453728579697 26767977268222840296434773)
              ·
                refine ⟨313687233611986409723845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 26767977268222840296434773 313687233611986409723845)
                ·
                  refine ⟨58816356302247451823221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 313687233611986409723845 58816356302247451823221)
                  ·
                    rfl

theorem cell22_515450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 8, 4].length) (baseStart_515450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_515450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_515450 prefixEnd_515450 := by exact prefixLift 515450
  have htrace : WordTrace (prefixWord ++ tailWord_515450) baseStart_515450 baseEnd_515450 := by
    simpa [prefixWord, tailWord_515450, baseEnd_515450] using wordTrace_append hprefix tailTrace_515450
  have hstable : (prefixWord ++ tailWord_515450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515450).length < 2 ^ (prefixWord ++ tailWord_515450).sum := by decide
  have hdescent : baseEnd_515450 < baseStart_515450 := by decide
  rcases family_descends (prefixWord ++ tailWord_515450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515454 : List Nat := [4, 2, 3, 2, 1, 1, 1, 1, 2, 5]
def baseStart_515454 : Nat := 118140960795 + 515454 * 2 ^ 59
def prefixEnd_515454 : Nat := 4983230072969 + 3 ^ 40 * 515454 * 2
def baseEnd_515454 : Nat := 176450438188487678369651

theorem tailTrace_515454 : CollatzResearch.WordTrace tailWord_515454 prefixEnd_515454 176450438188487678369651 := by
  unfold tailWord_515454
  simp only [CollatzResearch.WordTrace]
  refine ⟨2350018984325708172460177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12533434583070443586454277 2350018984325708172460177)
  ·
    refine ⟨1762514238244281129345133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2350018984325708172460177 1762514238244281129345133)
    ·
      refine ⟨660942839341605423504425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1762514238244281129345133 660942839341605423504425)
      ·
        refine ⟨495707129506204067628319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 660942839341605423504425 495707129506204067628319)
        ·
          refine ⟨743560694259306101442479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 495707129506204067628319 743560694259306101442479)
          ·
            refine ⟨1115341041388959152163719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 743560694259306101442479 1115341041388959152163719)
            ·
              refine ⟨1673011562083438728245579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1115341041388959152163719 1673011562083438728245579)
              ·
                refine ⟨2509517343125158092368369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1673011562083438728245579 2509517343125158092368369)
                ·
                  refine ⟨1882138007343868569276277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2509517343125158092368369 1882138007343868569276277)
                  ·
                    refine ⟨176450438188487678369651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1882138007343868569276277 176450438188487678369651)
                    ·
                      rfl

theorem cell22_515454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_515454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_515454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_515454 prefixEnd_515454 := by exact prefixLift 515454
  have htrace : WordTrace (prefixWord ++ tailWord_515454) baseStart_515454 baseEnd_515454 := by
    simpa [prefixWord, tailWord_515454, baseEnd_515454] using wordTrace_append hprefix tailTrace_515454
  have hstable : (prefixWord ++ tailWord_515454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515454).length < 2 ^ (prefixWord ++ tailWord_515454).sum := by decide
  have hdescent : baseEnd_515454 < baseStart_515454 := by decide
  rcases family_descends (prefixWord ++ tailWord_515454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515516 : List Nat := [2, 2, 2, 4, 2, 1, 3, 1, 2, 3]
def baseStart_515516 : Nat := 118140960795 + 515516 * 2 ^ 59
def prefixEnd_515516 : Nat := 4983230072969 + 3 ^ 40 * 515516 * 2
def baseEnd_515516 : Nat := 176471662055540183319461

theorem tailTrace_515516 : CollatzResearch.WordTrace tailWord_515516 prefixEnd_515516 176471662055540183319461 := by
  unfold tailWord_515516
  simp only [CollatzResearch.WordTrace]
  refine ⟨9401206600190524984219201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12534942133587366645625601 9401206600190524984219201)
  ·
    refine ⟨7050904950142893738164401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9401206600190524984219201 7050904950142893738164401)
    ·
      refine ⟨5288178712607170303623301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7050904950142893738164401 5288178712607170303623301)
      ·
        refine ⟨991533508613844431929369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5288178712607170303623301 991533508613844431929369)
        ·
          refine ⟨743650131460383323947027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 991533508613844431929369 743650131460383323947027)
          ·
            refine ⟨1115475197190574985920541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 743650131460383323947027 1115475197190574985920541)
            ·
              refine ⟨418303198946465619720203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1115475197190574985920541 418303198946465619720203)
              ·
                refine ⟨627454798419698429580305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 418303198946465619720203 627454798419698429580305)
                ·
                  refine ⟨470591098814773822185229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 627454798419698429580305 470591098814773822185229)
                  ·
                    refine ⟨176471662055540183319461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 470591098814773822185229 176471662055540183319461)
                    ·
                      rfl

theorem cell22_515516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 3, 1, 2, 3].length) (baseStart_515516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_515516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_515516 prefixEnd_515516 := by exact prefixLift 515516
  have htrace : WordTrace (prefixWord ++ tailWord_515516) baseStart_515516 baseEnd_515516 := by
    simpa [prefixWord, tailWord_515516, baseEnd_515516] using wordTrace_append hprefix tailTrace_515516
  have hstable : (prefixWord ++ tailWord_515516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515516).length < 2 ^ (prefixWord ++ tailWord_515516).sum := by decide
  have hdescent : baseEnd_515516 < baseStart_515516 := by decide
  rcases family_descends (prefixWord ++ tailWord_515516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515544 : List Nat := [2, 1, 2, 2, 2, 1, 5, 3, 1, 3]
def baseStart_515544 : Nat := 118140960795 + 515544 * 2 ^ 59
def prefixEnd_515544 : Nat := 4983230072969 + 3 ^ 40 * 515544 * 2
def baseEnd_515544 : Nat := 176481247027757443619375

theorem tailTrace_515544 : CollatzResearch.WordTrace tailWord_515544 prefixEnd_515544 176481247027757443619375 := by
  unfold tailWord_515544
  simp only [CollatzResearch.WordTrace]
  refine ⟨9401717222139805375228843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12535622962853073833638457 9401717222139805375228843)
  ·
    refine ⟨14102575833209708062843265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9401717222139805375228843 14102575833209708062843265)
    ·
      refine ⟨10576931874907281047132449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14102575833209708062843265 10576931874907281047132449)
      ·
        refine ⟨7932698906180460785349337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10576931874907281047132449 7932698906180460785349337)
        ·
          refine ⟨5949524179635345589012003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7932698906180460785349337 5949524179635345589012003)
          ·
            refine ⟨8924286269453018383518005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5949524179635345589012003 8924286269453018383518005)
            ·
              refine ⟨836651837761220473454813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8924286269453018383518005 836651837761220473454813)
              ·
                refine ⟨313744439160457677545555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 836651837761220473454813 313744439160457677545555)
                ·
                  refine ⟨470616658740686516318333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 313744439160457677545555 470616658740686516318333)
                  ·
                    refine ⟨176481247027757443619375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 470616658740686516318333 176481247027757443619375)
                    ·
                      rfl

theorem cell22_515544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 3, 1, 3].length) (baseStart_515544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_515544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_515544 prefixEnd_515544 := by exact prefixLift 515544
  have htrace : WordTrace (prefixWord ++ tailWord_515544) baseStart_515544 baseEnd_515544 := by
    simpa [prefixWord, tailWord_515544, baseEnd_515544] using wordTrace_append hprefix tailTrace_515544
  have hstable : (prefixWord ++ tailWord_515544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515544).length < 2 ^ (prefixWord ++ tailWord_515544).sum := by decide
  have hdescent : baseEnd_515544 < baseStart_515544 := by decide
  rcases family_descends (prefixWord ++ tailWord_515544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515574 : List Nat := [5, 1, 1, 1, 2, 2, 4, 1, 5]
def baseStart_515574 : Nat := 118140960795 + 515574 * 2 ^ 59
def prefixEnd_515574 : Nat := 4983230072969 + 3 ^ 40 * 515574 * 2
def baseEnd_515574 : Nat := 58830505546949121789761

theorem tailTrace_515574 : CollatzResearch.WordTrace tailWord_515574 prefixEnd_515574 58830505546949121789761 := by
  unfold tailWord_515574
  simp only [CollatzResearch.WordTrace]
  refine ⟨1175283039635682867128111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12536352422780617249366517 1175283039635682867128111)
  ·
    refine ⟨1762924559453524300692167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1175283039635682867128111 1762924559453524300692167)
    ·
      refine ⟨2644386839180286451038251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1762924559453524300692167 2644386839180286451038251)
      ·
        refine ⟨3966580258770429676557377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2644386839180286451038251 3966580258770429676557377)
        ·
          refine ⟨2974935194077822257418033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3966580258770429676557377 2974935194077822257418033)
          ·
            refine ⟨2231201395558366693063525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2974935194077822257418033 2231201395558366693063525)
            ·
              refine ⟨418350261667193754949411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2231201395558366693063525 418350261667193754949411)
              ·
                refine ⟨627525392500790632424117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 418350261667193754949411 627525392500790632424117)
                ·
                  refine ⟨58830505546949121789761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 627525392500790632424117 58830505546949121789761)
                  ·
                    rfl

theorem cell22_515574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 4, 1, 5].length) (baseStart_515574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_515574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_515574 prefixEnd_515574 := by exact prefixLift 515574
  have htrace : WordTrace (prefixWord ++ tailWord_515574) baseStart_515574 baseEnd_515574 := by
    simpa [prefixWord, tailWord_515574, baseEnd_515574] using wordTrace_append hprefix tailTrace_515574
  have hstable : (prefixWord ++ tailWord_515574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515574).length < 2 ^ (prefixWord ++ tailWord_515574).sum := by decide
  have hdescent : baseEnd_515574 < baseStart_515574 := by decide
  rcases family_descends (prefixWord ++ tailWord_515574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515619 : List Nat := [1, 1, 1, 4, 5, 1, 1, 4, 4]
def baseStart_515619 : Nat := 118140960795 + 515619 * 2 ^ 59
def prefixEnd_515619 : Nat := 4983230072969 + 3 ^ 40 * 515619 * 2
def baseEnd_515619 : Nat := 58835640353494082664715

theorem tailTrace_515619 : CollatzResearch.WordTrace tailWord_515619 prefixEnd_515619 58835640353494082664715 := by
  unfold tailWord_515619
  simp only [CollatzResearch.WordTrace]
  refine ⟨18806169919007898559437911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12537446612671932372958607 18806169919007898559437911)
  ·
    refine ⟨28209254878511847839156867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18806169919007898559437911 28209254878511847839156867)
    ·
      refine ⟨42313882317767771758735301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28209254878511847839156867 42313882317767771758735301)
      ·
        refine ⟨7933852934581457204762869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42313882317767771758735301 7933852934581457204762869)
        ·
          refine ⟨743798712617011612946519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7933852934581457204762869 743798712617011612946519)
          ·
            refine ⟨1115698068925517419419779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 743798712617011612946519 1115698068925517419419779)
            ·
              refine ⟨1673547103388276129129669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1115698068925517419419779 1673547103388276129129669)
              ·
                refine ⟨313790081885301774211813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1673547103388276129129669 313790081885301774211813)
                ·
                  refine ⟨58835640353494082664715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 313790081885301774211813 58835640353494082664715)
                  ·
                    rfl

theorem cell22_515619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 4, 4].length) (baseStart_515619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_515619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_515619 prefixEnd_515619 := by exact prefixLift 515619
  have htrace : WordTrace (prefixWord ++ tailWord_515619) baseStart_515619 baseEnd_515619 := by
    simpa [prefixWord, tailWord_515619, baseEnd_515619] using wordTrace_append hprefix tailTrace_515619
  have hstable : (prefixWord ++ tailWord_515619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515619).length < 2 ^ (prefixWord ++ tailWord_515619).sum := by decide
  have hdescent : baseEnd_515619 < baseStart_515619 := by decide
  rcases family_descends (prefixWord ++ tailWord_515619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515647 : List Nat := [1, 1, 2, 2, 3, 4, 3, 6]
def baseStart_515647 : Nat := 118140960795 + 515647 * 2 ^ 59
def prefixEnd_515647 : Nat := 4983230072969 + 3 ^ 40 * 515647 * 2
def baseEnd_515647 : Nat := 19612945114744389810451

theorem tailTrace_515647 : CollatzResearch.WordTrace tailWord_515647 prefixEnd_515647 19612945114744389810451 := by
  unfold tailWord_515647
  simp only [CollatzResearch.WordTrace]
  refine ⟨18807191162906459341457195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12538127441937639560971463 18807191162906459341457195)
  ·
    refine ⟨28210786744359689012185793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18807191162906459341457195 28210786744359689012185793)
    ·
      refine ⟨21158090058269766759139345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28210786744359689012185793 21158090058269766759139345)
      ·
        refine ⟨15868567543702325069354509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21158090058269766759139345 15868567543702325069354509)
        ·
          refine ⟨5950712828888371901007941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15868567543702325069354509 5950712828888371901007941)
          ·
            refine ⟨1115758655416569731438989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5950712828888371901007941 1115758655416569731438989)
            ·
              refine ⟨418409495781213649289621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1115758655416569731438989 418409495781213649289621)
              ·
                refine ⟨19612945114744389810451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 418409495781213649289621 19612945114744389810451)
                ·
                  rfl

theorem cell22_515647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 3, 6].length) (baseStart_515647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_515647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_515647 prefixEnd_515647 := by exact prefixLift 515647
  have htrace : WordTrace (prefixWord ++ tailWord_515647) baseStart_515647 baseEnd_515647 := by
    simpa [prefixWord, tailWord_515647, baseEnd_515647] using wordTrace_append hprefix tailTrace_515647
  have hstable : (prefixWord ++ tailWord_515647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515647).length < 2 ^ (prefixWord ++ tailWord_515647).sum := by decide
  have hdescent : baseEnd_515647 < baseStart_515647 := by decide
  rcases family_descends (prefixWord ++ tailWord_515647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515662 : List Nat := [4, 1, 1, 1, 1, 2, 1, 1, 7, 3]
def baseStart_515662 : Nat := 118140960795 + 515662 * 2 ^ 59
def prefixEnd_515662 : Nat := 4983230072969 + 3 ^ 40 * 515662 * 2
def baseEnd_515662 : Nat := 176521640839244469169013

theorem tailTrace_515662 : CollatzResearch.WordTrace tailWord_515662 prefixEnd_515662 176521640839244469169013 := by
  unfold tailWord_515662
  simp only [CollatzResearch.WordTrace]
  refine ⟨2350967282231514612906655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12538492171901411268835493 2350967282231514612906655)
  ·
    refine ⟨3526450923347271919359983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2350967282231514612906655 3526450923347271919359983)
    ·
      refine ⟨5289676385020907879039975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3526450923347271919359983 5289676385020907879039975)
      ·
        refine ⟨7934514577531361818559963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5289676385020907879039975 7934514577531361818559963)
        ·
          refine ⟨11901771866297042727839945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7934514577531361818559963 11901771866297042727839945)
          ·
            refine ⟨8926328899722782045879959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11901771866297042727839945 8926328899722782045879959)
            ·
              refine ⟨13389493349584173068819939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8926328899722782045879959 13389493349584173068819939)
              ·
                refine ⟨20084240024376259603229909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13389493349584173068819939 20084240024376259603229909)
                ·
                  refine ⟨470724375571318584450701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20084240024376259603229909 470724375571318584450701)
                  ·
                    refine ⟨176521640839244469169013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 470724375571318584450701 176521640839244469169013)
                    ·
                      rfl

theorem cell22_515662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 7, 3].length) (baseStart_515662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_515662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_515662 prefixEnd_515662 := by exact prefixLift 515662
  have htrace : WordTrace (prefixWord ++ tailWord_515662) baseStart_515662 baseEnd_515662 := by
    simpa [prefixWord, tailWord_515662, baseEnd_515662] using wordTrace_append hprefix tailTrace_515662
  have hstable : (prefixWord ++ tailWord_515662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515662).length < 2 ^ (prefixWord ++ tailWord_515662).sum := by decide
  have hdescent : baseEnd_515662 < baseStart_515662 := by decide
  rcases family_descends (prefixWord ++ tailWord_515662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515713 : List Nat := [1, 2, 4, 2, 1, 4, 1, 3, 1, 3]
def baseStart_515713 : Nat := 118140960795 + 515713 * 2 ^ 59
def prefixEnd_515713 : Nat := 4983230072969 + 3 ^ 40 * 515713 * 2
def baseEnd_515713 : Nat := 176539099181497336143857

theorem tailTrace_515713 : CollatzResearch.WordTrace tailWord_515713 prefixEnd_515713 176539099181497336143857 := by
  unfold tailWord_515713
  simp only [CollatzResearch.WordTrace]
  refine ⟨18809598380667352613359793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12539732253778235075573195 18809598380667352613359793)
  ·
    refine ⟨14107198785500514460019845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18809598380667352613359793 14107198785500514460019845)
    ·
      refine ⟨2645099772281346461253721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14107198785500514460019845 2645099772281346461253721)
      ·
        refine ⟨1983824829211009845940291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2645099772281346461253721 1983824829211009845940291)
        ·
          refine ⟨2975737243816514768910437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1983824829211009845940291 2975737243816514768910437)
          ·
            refine ⟨557950733215596519170707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2975737243816514768910437 557950733215596519170707)
            ·
              refine ⟨836926099823394778756061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 557950733215596519170707 836926099823394778756061)
              ·
                refine ⟨313847287433773042033523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 836926099823394778756061 313847287433773042033523)
                ·
                  refine ⟨470770931150659563050285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 313847287433773042033523 470770931150659563050285)
                  ·
                    refine ⟨176539099181497336143857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 470770931150659563050285 176539099181497336143857)
                    ·
                      rfl

theorem cell22_515713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 3, 1, 3].length) (baseStart_515713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_515713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_515713 prefixEnd_515713 := by exact prefixLift 515713
  have htrace : WordTrace (prefixWord ++ tailWord_515713) baseStart_515713 baseEnd_515713 := by
    simpa [prefixWord, tailWord_515713, baseEnd_515713] using wordTrace_append hprefix tailTrace_515713
  have hstable : (prefixWord ++ tailWord_515713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515713).length < 2 ^ (prefixWord ++ tailWord_515713).sum := by decide
  have hdescent : baseEnd_515713 < baseStart_515713 := by decide
  rcases family_descends (prefixWord ++ tailWord_515713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515730 : List Nat := [3, 2, 3, 1, 3, 1, 3, 2, 1, 3]
def baseStart_515730 : Nat := 118140960795 + 515730 * 2 ^ 59
def prefixEnd_515730 : Nat := 4983230072969 + 3 ^ 40 * 515730 * 2
def baseEnd_515730 : Nat := 176544918628914958468805

theorem tailTrace_515730 : CollatzResearch.WordTrace tailWord_515730 prefixEnd_515730 176544918628914958468805 := by
  unfold tailWord_515730
  simp only [CollatzResearch.WordTrace]
  refine ⟨4702554605401441129182161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12540145614403843011152429 4702554605401441129182161)
  ·
    refine ⟨3526915954051080846886621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4702554605401441129182161 3526915954051080846886621)
    ·
      refine ⟨1322593482769155317582483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3526915954051080846886621 1322593482769155317582483)
      ·
        refine ⟨1983890224153732976373725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1322593482769155317582483 1983890224153732976373725)
        ·
          refine ⟨743958834057649866140147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1983890224153732976373725 743958834057649866140147)
          ·
            refine ⟨1115938251086474799210221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 743958834057649866140147 1115938251086474799210221)
            ·
              refine ⟨418476844157428049703833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1115938251086474799210221 418476844157428049703833)
              ·
                refine ⟨313857633118071037277875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 418476844157428049703833 313857633118071037277875)
                ·
                  refine ⟨470786449677106555916813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 313857633118071037277875 470786449677106555916813)
                  ·
                    refine ⟨176544918628914958468805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 470786449677106555916813 176544918628914958468805)
                    ·
                      rfl

theorem cell22_515730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_515730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_515730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_515730 prefixEnd_515730 := by exact prefixLift 515730
  have htrace : WordTrace (prefixWord ++ tailWord_515730) baseStart_515730 baseEnd_515730 := by
    simpa [prefixWord, tailWord_515730, baseEnd_515730] using wordTrace_append hprefix tailTrace_515730
  have hstable : (prefixWord ++ tailWord_515730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515730).length < 2 ^ (prefixWord ++ tailWord_515730).sum := by decide
  have hdescent : baseEnd_515730 < baseStart_515730 := by decide
  rcases family_descends (prefixWord ++ tailWord_515730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515743 : List Nat := [1, 1, 2, 7, 1, 2, 2, 1, 5]
def baseStart_515743 : Nat := 118140960795 + 515743 * 2 ^ 59
def prefixEnd_515743 : Nat := 4983230072969 + 3 ^ 40 * 515743 * 2
def baseEnd_515743 : Nat := 58849789598195752631255

theorem tailTrace_515743 : CollatzResearch.WordTrace tailWord_515743 prefixEnd_515743 58849789598195752631255 := by
  unfold tailWord_515743
  simp only [CollatzResearch.WordTrace]
  refine ⟨18810692570558667736951883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12540461713705778491301255 18810692570558667736951883)
  ·
    refine ⟨28216038855838001605427825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18810692570558667736951883 28216038855838001605427825)
    ·
      refine ⟨21162029141878501204070869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28216038855838001605427825 21162029141878501204070869)
      ·
        refine ⟨495985058012777371970411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 21162029141878501204070869 495985058012777371970411)
        ·
          refine ⟨743977587019166057955617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 495985058012777371970411 743977587019166057955617)
          ·
            refine ⟨557983190264374543466713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 743977587019166057955617 557983190264374543466713)
            ·
              refine ⟨418487392698280907600035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 557983190264374543466713 418487392698280907600035)
              ·
                refine ⟨627731089047421361400053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 418487392698280907600035 627731089047421361400053)
                ·
                  refine ⟨58849789598195752631255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 627731089047421361400053 58849789598195752631255)
                  ·
                    rfl

theorem cell22_515743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 2, 1, 5].length) (baseStart_515743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_515743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_515743 prefixEnd_515743 := by exact prefixLift 515743
  have htrace : WordTrace (prefixWord ++ tailWord_515743) baseStart_515743 baseEnd_515743 := by
    simpa [prefixWord, tailWord_515743, baseEnd_515743] using wordTrace_append hprefix tailTrace_515743
  have hstable : (prefixWord ++ tailWord_515743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515743).length < 2 ^ (prefixWord ++ tailWord_515743).sum := by decide
  have hdescent : baseEnd_515743 < baseStart_515743 := by decide
  rcases family_descends (prefixWord ++ tailWord_515743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515812 : List Nat := [2, 3, 1, 1, 1, 3, 1, 2, 2, 6]
def baseStart_515812 : Nat := 118140960795 + 515812 * 2 ^ 59
def prefixEnd_515812 : Nat := 4983230072969 + 3 ^ 40 * 515812 * 2
def baseEnd_515812 : Nat := 176572988904694077918553

theorem tailTrace_515812 : CollatzResearch.WordTrace tailWord_515812 prefixEnd_515812 176572988904694077918553 := by
  unfold tailWord_515812
  simp only [CollatzResearch.WordTrace]
  refine ⟨9406604603654346260606845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12542139471539128347475793 9406604603654346260606845)
  ·
    refine ⟨3527476726370379847727567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9406604603654346260606845 3527476726370379847727567)
    ·
      refine ⟨5291215089555569771591351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3527476726370379847727567 5291215089555569771591351)
      ·
        refine ⟨7936822634333354657387027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5291215089555569771591351 7936822634333354657387027)
        ·
          refine ⟨11905233951500031986080541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7936822634333354657387027 11905233951500031986080541)
          ·
            refine ⟨4464462731812511994780203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11905233951500031986080541 4464462731812511994780203)
            ·
              refine ⟨6696694097718767992170305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4464462731812511994780203 6696694097718767992170305)
              ·
                refine ⟨5022520573289075994127729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6696694097718767992170305 5022520573289075994127729)
                ·
                  refine ⟨3766890429966806995595797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5022520573289075994127729 3766890429966806995595797)
                  ·
                    refine ⟨176572988904694077918553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3766890429966806995595797 176572988904694077918553)
                    ·
                      rfl

theorem cell22_515812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_515812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_515812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_515812 prefixEnd_515812 := by exact prefixLift 515812
  have htrace : WordTrace (prefixWord ++ tailWord_515812) baseStart_515812 baseEnd_515812 := by
    simpa [prefixWord, tailWord_515812, baseEnd_515812] using wordTrace_append hprefix tailTrace_515812
  have hstable : (prefixWord ++ tailWord_515812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515812).length < 2 ^ (prefixWord ++ tailWord_515812).sum := by decide
  have hdescent : baseEnd_515812 < baseStart_515812 := by decide
  rcases family_descends (prefixWord ++ tailWord_515812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515831 : List Nat := [1, 1, 3, 1, 1, 1, 5, 5, 1, 3]
def baseStart_515831 : Nat := 118140960795 + 515831 * 2 ^ 59
def prefixEnd_515831 : Nat := 4983230072969 + 3 ^ 40 * 515831 * 2
def baseEnd_515831 : Nat := 176579492992984361693495

theorem tailTrace_515831 : CollatzResearch.WordTrace tailWord_515831 prefixEnd_515831 176579492992984361693495 := by
  unfold tailWord_515831
  simp only [CollatzResearch.WordTrace]
  refine ⟨18813902194239858766155347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12542601462826572510770231 18813902194239858766155347)
  ·
    refine ⟨28220853291359788149233021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18813902194239858766155347 28220853291359788149233021)
    ·
      refine ⟨10582819984259920555962383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28220853291359788149233021 10582819984259920555962383)
      ·
        refine ⟨15874229976389880833943575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10582819984259920555962383 15874229976389880833943575)
        ·
          refine ⟨23811344964584821250915363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15874229976389880833943575 23811344964584821250915363)
          ·
            refine ⟨35717017446877231876373045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23811344964584821250915363 35717017446877231876373045)
            ·
              refine ⟨3348470385644740488409973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35717017446877231876373045 3348470385644740488409973)
              ·
                refine ⟨313919098654194420788435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3348470385644740488409973 313919098654194420788435)
                ·
                  refine ⟨470878647981291631182653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 313919098654194420788435 470878647981291631182653)
                  ·
                    refine ⟨176579492992984361693495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 470878647981291631182653 176579492992984361693495)
                    ·
                      rfl

theorem cell22_515831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 5, 1, 3].length) (baseStart_515831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_515831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_515831 prefixEnd_515831 := by exact prefixLift 515831
  have htrace : WordTrace (prefixWord ++ tailWord_515831) baseStart_515831 baseEnd_515831 := by
    simpa [prefixWord, tailWord_515831, baseEnd_515831] using wordTrace_append hprefix tailTrace_515831
  have hstable : (prefixWord ++ tailWord_515831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515831).length < 2 ^ (prefixWord ++ tailWord_515831).sum := by decide
  have hdescent : baseEnd_515831 < baseStart_515831 := by decide
  rcases family_descends (prefixWord ++ tailWord_515831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515844 : List Nat := [2, 3, 2, 2, 1, 3, 1, 1, 7]
def baseStart_515844 : Nat := 118140960795 + 515844 * 2 ^ 59
def prefixEnd_515844 : Nat := 4983230072969 + 3 ^ 40 * 515844 * 2
def baseEnd_515844 : Nat := 58861314386218887039485

theorem tailTrace_515844 : CollatzResearch.WordTrace tailWord_515844 prefixEnd_515844 58861314386218887039485 := by
  unfold tailWord_515844
  simp only [CollatzResearch.WordTrace]
  refine ⟨9407188171596380993189293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12542917562128507990919057 9407188171596380993189293)
  ·
    refine ⟨3527695564348642872445985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9407188171596380993189293 3527695564348642872445985)
    ·
      refine ⟨2645771673261482154334489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3527695564348642872445985 2645771673261482154334489)
      ·
        refine ⟨1984328754946111615750867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2645771673261482154334489 1984328754946111615750867)
        ·
          refine ⟨2976493132419167423626301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1984328754946111615750867 2976493132419167423626301)
          ·
            refine ⟨1116184924657187783859863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2976493132419167423626301 1116184924657187783859863)
            ·
              refine ⟨1674277386985781675789795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1116184924657187783859863 1674277386985781675789795)
              ·
                refine ⟨2511416080478672513684693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1674277386985781675789795 2511416080478672513684693)
                ·
                  refine ⟨58861314386218887039485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2511416080478672513684693 58861314386218887039485)
                  ·
                    rfl

theorem cell22_515844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 7].length) (baseStart_515844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_515844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_515844 prefixEnd_515844 := by exact prefixLift 515844
  have htrace : WordTrace (prefixWord ++ tailWord_515844) baseStart_515844 baseEnd_515844 := by
    simpa [prefixWord, tailWord_515844, baseEnd_515844] using wordTrace_append hprefix tailTrace_515844
  have hstable : (prefixWord ++ tailWord_515844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515844).length < 2 ^ (prefixWord ++ tailWord_515844).sum := by decide
  have hdescent : baseEnd_515844 < baseStart_515844 := by decide
  rcases family_descends (prefixWord ++ tailWord_515844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515861 : List Nat := [1, 3, 2, 1, 2, 4, 3, 1, 5]
def baseStart_515861 : Nat := 118140960795 + 515861 * 2 ^ 59
def prefixEnd_515861 : Nat := 4983230072969 + 3 ^ 40 * 515861 * 2
def baseEnd_515861 : Nat := 58863254202024761147801

theorem tailTrace_515861 : CollatzResearch.WordTrace tailWord_515861 prefixEnd_515861 58863254202024761147801 := by
  unfold tailWord_515861
  simp only [CollatzResearch.WordTrace]
  refine ⟨18814996384131173889747437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12543330922754115926498291 18814996384131173889747437)
  ·
    refine ⟨7055623644049190208655289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18814996384131173889747437 7055623644049190208655289)
    ·
      refine ⟨5291717733036892656491467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7055623644049190208655289 5291717733036892656491467)
      ·
        refine ⟨7937576599555338984737201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5291717733036892656491467 7937576599555338984737201)
        ·
          refine ⟨5953182449666504238552901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7937576599555338984737201 5953182449666504238552901)
          ·
            refine ⟨1116221709312469544728669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5953182449666504238552901 1116221709312469544728669)
            ·
              refine ⟨418583140992176079273251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1116221709312469544728669 418583140992176079273251)
              ·
                refine ⟨627874711488264118909877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 418583140992176079273251 627874711488264118909877)
                ·
                  refine ⟨58863254202024761147801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 627874711488264118909877 58863254202024761147801)
                  ·
                    rfl

theorem cell22_515861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 3, 1, 5].length) (baseStart_515861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_515861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_515861 prefixEnd_515861 := by exact prefixLift 515861
  have htrace : WordTrace (prefixWord ++ tailWord_515861) baseStart_515861 baseEnd_515861 := by
    simpa [prefixWord, tailWord_515861, baseEnd_515861] using wordTrace_append hprefix tailTrace_515861
  have hstable : (prefixWord ++ tailWord_515861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515861).length < 2 ^ (prefixWord ++ tailWord_515861).sum := by decide
  have hdescent : baseEnd_515861 < baseStart_515861 := by decide
  rcases family_descends (prefixWord ++ tailWord_515861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515936 : List Nat := [2, 1, 1, 3, 3, 3, 2, 1, 2, 4]
def baseStart_515936 : Nat := 118140960795 + 515936 * 2 ^ 59
def prefixEnd_515936 : Nat := 4983230072969 + 3 ^ 40 * 515936 * 2
def baseEnd_515936 : Nat := 176615436638799087818173

theorem tailTrace_515936 : CollatzResearch.WordTrace tailWord_515936 prefixEnd_515936 176615436638799087818173 := by
  unfold tailWord_515936
  simp only [CollatzResearch.WordTrace]
  refine ⟨9408865929429730849363831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12545154572572974465818441 9408865929429730849363831)
  ·
    refine ⟨14113298894144596274045747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9408865929429730849363831 14113298894144596274045747)
    ·
      refine ⟨21169948341216894411068621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14113298894144596274045747 21169948341216894411068621)
      ·
        refine ⟨7938730627956335404150733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21169948341216894411068621 7938730627956335404150733)
        ·
          refine ⟨2977023985483625776556525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7938730627956335404150733 2977023985483625776556525)
          ·
            refine ⟨1116383994556359666208697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2977023985483625776556525 1116383994556359666208697)
            ·
              refine ⟨837287995917269749656523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1116383994556359666208697 837287995917269749656523)
              ·
                refine ⟨1255931993875904624484785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 837287995917269749656523 1255931993875904624484785)
                ·
                  refine ⟨941948995406928468363589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1255931993875904624484785 941948995406928468363589)
                  ·
                    refine ⟨176615436638799087818173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 941948995406928468363589 176615436638799087818173)
                    ·
                      rfl

theorem cell22_515936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 1, 2, 4].length) (baseStart_515936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_515936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_515936 prefixEnd_515936 := by exact prefixLift 515936
  have htrace : WordTrace (prefixWord ++ tailWord_515936) baseStart_515936 baseEnd_515936 := by
    simpa [prefixWord, tailWord_515936, baseEnd_515936] using wordTrace_append hprefix tailTrace_515936
  have hstable : (prefixWord ++ tailWord_515936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515936).length < 2 ^ (prefixWord ++ tailWord_515936).sum := by decide
  have hdescent : baseEnd_515936 < baseStart_515936 := by decide
  rcases family_descends (prefixWord ++ tailWord_515936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516009 : List Nat := [1, 2, 1, 1, 1, 1, 4, 2, 5, 4]
def baseStart_516009 : Nat := 118140960795 + 516009 * 2 ^ 59
def prefixEnd_516009 : Nat := 4983230072969 + 3 ^ 40 * 516009 * 2
def baseEnd_516009 : Nat := 176640426030651230742949

theorem tailTrace_516009 : CollatzResearch.WordTrace tailWord_516009 prefixEnd_516009 176640426030651230742949 := by
  unfold tailWord_516009
  simp only [CollatzResearch.WordTrace]
  refine ⟨18820394387594995166135081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12546929591729996777423387 18820394387594995166135081)
  ·
    refine ⟨14115295790696246374601311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18820394387594995166135081 14115295790696246374601311)
    ·
      refine ⟨21172943686044369561901967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14115295790696246374601311 21172943686044369561901967)
      ·
        refine ⟨31759415529066554342852951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21172943686044369561901967 31759415529066554342852951)
        ·
          refine ⟨47639123293599831514279427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31759415529066554342852951 47639123293599831514279427)
          ·
            refine ⟨71458684940399747271419141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47639123293599831514279427 71458684940399747271419141)
            ·
              refine ⟨13398503426324952613391089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71458684940399747271419141 13398503426324952613391089)
              ·
                refine ⟨10048877569743714460043317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13398503426324952613391089 10048877569743714460043317)
                ·
                  refine ⟨942082272163473230629061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10048877569743714460043317 942082272163473230629061)
                  ·
                    refine ⟨176640426030651230742949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 942082272163473230629061 176640426030651230742949)
                    ·
                      rfl

theorem cell22_516009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 5, 4].length) (baseStart_516009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_516009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_516009 prefixEnd_516009 := by exact prefixLift 516009
  have htrace : WordTrace (prefixWord ++ tailWord_516009) baseStart_516009 baseEnd_516009 := by
    simpa [prefixWord, tailWord_516009, baseEnd_516009] using wordTrace_append hprefix tailTrace_516009
  have hstable : (prefixWord ++ tailWord_516009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516009).length < 2 ^ (prefixWord ++ tailWord_516009).sum := by decide
  have hdescent : baseEnd_516009 < baseStart_516009 := by decide
  rcases family_descends (prefixWord ++ tailWord_516009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516056 : List Nat := [2, 1, 2, 2, 2, 2, 1, 1, 6, 3]
def baseStart_516056 : Nat := 118140960795 + 516056 * 2 ^ 59
def prefixEnd_516056 : Nat := 4983230072969 + 3 ^ 40 * 516056 * 2
def baseEnd_516056 : Nat := 176656515091158774817805

theorem tailTrace_516056 : CollatzResearch.WordTrace tailWord_516056 prefixEnd_516056 176656515091158774817805 := by
  unfold tailWord_516056
  simp only [CollatzResearch.WordTrace]
  refine ⟨9411054309212361096548011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12548072412283148128730681 9411054309212361096548011)
  ·
    refine ⟨14116581463818541644822017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9411054309212361096548011 14116581463818541644822017)
    ·
      refine ⟨10587436097863906233616513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14116581463818541644822017 10587436097863906233616513)
      ·
        refine ⟨7940577073397929675212385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10587436097863906233616513 7940577073397929675212385)
        ·
          refine ⟨5955432805048447256409289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7940577073397929675212385 5955432805048447256409289)
          ·
            refine ⟨4466574603786335442306967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5955432805048447256409289 4466574603786335442306967)
            ·
              refine ⟨6699861905679503163460451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4466574603786335442306967 6699861905679503163460451)
              ·
                refine ⟨10049792858519254745190677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6699861905679503163460451 10049792858519254745190677)
                ·
                  refine ⟨471084040243090066180813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10049792858519254745190677 471084040243090066180813)
                  ·
                    refine ⟨176656515091158774817805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 471084040243090066180813 176656515091158774817805)
                    ·
                      rfl

theorem cell22_516056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 6, 3].length) (baseStart_516056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_516056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_516056 prefixEnd_516056 := by exact prefixLift 516056
  have htrace : WordTrace (prefixWord ++ tailWord_516056) baseStart_516056 baseEnd_516056 := by
    simpa [prefixWord, tailWord_516056, baseEnd_516056] using wordTrace_append hprefix tailTrace_516056
  have hstable : (prefixWord ++ tailWord_516056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516056).length < 2 ^ (prefixWord ++ tailWord_516056).sum := by decide
  have hdescent : baseEnd_516056 < baseStart_516056 := by decide
  rcases family_descends (prefixWord ++ tailWord_516056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516146 : List Nat := [3, 2, 1, 1, 2, 3, 1, 1, 1, 7]
def baseStart_516146 : Nat := 118140960795 + 516146 * 2 ^ 59
def prefixEnd_516146 : Nat := 4983230072969 + 3 ^ 40 * 516146 * 2
def baseEnd_516146 : Nat := 176687323930428540067529

theorem tailTrace_516146 : CollatzResearch.WordTrace tailWord_516146 prefixEnd_516146 176687323930428540067529 := by
  unfold tailWord_516146
  simp only [CollatzResearch.WordTrace]
  refine ⟨4706347797024666890968073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12550260792065778375914861 4706347797024666890968073)
  ·
    refine ⟨3529760847768500168226055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4706347797024666890968073 3529760847768500168226055)
    ·
      refine ⟨5294641271652750252339083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3529760847768500168226055 5294641271652750252339083)
      ·
        refine ⟨7941961907479125378508625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5294641271652750252339083 7941961907479125378508625)
        ·
          refine ⟨5956471430609344033881469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7941961907479125378508625 5956471430609344033881469)
          ·
            refine ⟨2233676786478504012705551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5956471430609344033881469 2233676786478504012705551)
            ·
              refine ⟨3350515179717756019058327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2233676786478504012705551 3350515179717756019058327)
              ·
                refine ⟨5025772769576634028587491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3350515179717756019058327 5025772769576634028587491)
                ·
                  refine ⟨7538659154364951042881237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5025772769576634028587491 7538659154364951042881237)
                  ·
                    refine ⟨176687323930428540067529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7538659154364951042881237 176687323930428540067529)
                    ·
                      rfl

theorem cell22_516146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_516146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_516146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_516146 prefixEnd_516146 := by exact prefixLift 516146
  have htrace : WordTrace (prefixWord ++ tailWord_516146) baseStart_516146 baseEnd_516146 := by
    simpa [prefixWord, tailWord_516146, baseEnd_516146] using wordTrace_append hprefix tailTrace_516146
  have hstable : (prefixWord ++ tailWord_516146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516146).length < 2 ^ (prefixWord ++ tailWord_516146).sum := by decide
  have hdescent : baseEnd_516146 < baseStart_516146 := by decide
  rcases family_descends (prefixWord ++ tailWord_516146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516182 : List Nat := [5, 2, 2, 1, 1, 1, 3, 2, 5]
def baseStart_516182 : Nat := 118140960795 + 516182 * 2 ^ 59
def prefixEnd_516182 : Nat := 4983230072969 + 3 ^ 40 * 516182 * 2
def baseEnd_516182 : Nat := 58899882488712148722473

theorem tailTrace_516182 : CollatzResearch.WordTrace tailWord_516182 prefixEnd_516182 58899882488712148722473 := by
  unfold tailWord_516182
  simp only [CollatzResearch.WordTrace]
  refine ⟨1176669013498015357011425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12551136143978830474788533 1176669013498015357011425)
  ·
    refine ⟨882501760123511517758569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1176669013498015357011425 882501760123511517758569)
    ·
      refine ⟨661876320092633638318927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 882501760123511517758569 661876320092633638318927)
      ·
        refine ⟨992814480138950457478391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 661876320092633638318927 992814480138950457478391)
        ·
          refine ⟨1489221720208425686217587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 992814480138950457478391 1489221720208425686217587)
          ·
            refine ⟨2233832580312638529326381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1489221720208425686217587 2233832580312638529326381)
            ·
              refine ⟨837687217617239448497393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2233832580312638529326381 837687217617239448497393)
              ·
                refine ⟨628265413212929586373045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 837687217617239448497393 628265413212929586373045)
                ·
                  refine ⟨58899882488712148722473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 628265413212929586373045 58899882488712148722473)
                  ·
                    rfl

theorem cell22_516182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_516182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_516182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_516182 prefixEnd_516182 := by exact prefixLift 516182
  have htrace : WordTrace (prefixWord ++ tailWord_516182) baseStart_516182 baseEnd_516182 := by
    simpa [prefixWord, tailWord_516182, baseEnd_516182] using wordTrace_append hprefix tailTrace_516182
  have hstable : (prefixWord ++ tailWord_516182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516182).length < 2 ^ (prefixWord ++ tailWord_516182).sum := by decide
  have hdescent : baseEnd_516182 < baseStart_516182 := by decide
  rcases family_descends (prefixWord ++ tailWord_516182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516208 : List Nat := [2, 1, 1, 1, 5, 2, 3, 1, 1, 5]
def baseStart_516208 : Nat := 118140960795 + 516208 * 2 ^ 59
def prefixEnd_516208 : Nat := 4983230072969 + 3 ^ 40 * 516208 * 2
def baseEnd_516208 : Nat := 176708547797481045017339

theorem tailTrace_516208 : CollatzResearch.WordTrace tailWord_516208 prefixEnd_516208 176708547797481045017339 := by
  unfold tailWord_516208
  simp only [CollatzResearch.WordTrace]
  refine ⟨9413826256937026076314639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12551768342582701435086185 9413826256937026076314639)
  ·
    refine ⟨14120739385405539114471959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9413826256937026076314639 14120739385405539114471959)
    ·
      refine ⟨21181109078108308671707939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14120739385405539114471959 21181109078108308671707939)
      ·
        refine ⟨31771663617162463007561909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21181109078108308671707939 31771663617162463007561909)
        ·
          refine ⟨2978593464108980906958929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31771663617162463007561909 2978593464108980906958929)
          ·
            refine ⟨2233945098081735680219197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2978593464108980906958929 2233945098081735680219197)
            ·
              refine ⟨837729411780650880082199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2233945098081735680219197 837729411780650880082199)
              ·
                refine ⟨1256594117670976320123299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 837729411780650880082199 1256594117670976320123299)
                ·
                  refine ⟨1884891176506464480184949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1256594117670976320123299 1884891176506464480184949)
                  ·
                    refine ⟨176708547797481045017339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1884891176506464480184949 176708547797481045017339)
                    ·
                      rfl

theorem cell22_516208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 1, 1, 5].length) (baseStart_516208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_516208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_516208 prefixEnd_516208 := by exact prefixLift 516208
  have htrace : WordTrace (prefixWord ++ tailWord_516208) baseStart_516208 baseEnd_516208 := by
    simpa [prefixWord, tailWord_516208, baseEnd_516208] using wordTrace_append hprefix tailTrace_516208
  have hstable : (prefixWord ++ tailWord_516208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516208).length < 2 ^ (prefixWord ++ tailWord_516208).sum := by decide
  have hdescent : baseEnd_516208 < baseStart_516208 := by decide
  rcases family_descends (prefixWord ++ tailWord_516208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516244 : List Nat := [2, 4, 2, 3, 2, 1, 1, 1, 6]
def baseStart_516244 : Nat := 118140960795 + 516244 * 2 ^ 59
def prefixEnd_516244 : Nat := 4983230072969 + 3 ^ 40 * 516244 * 2
def baseEnd_516244 : Nat := 58906957111062983705743

theorem tailTrace_516244 : CollatzResearch.WordTrace tailWord_516244 prefixEnd_516244 58906957111062983705743 := by
  unfold tailWord_516244
  simp only [CollatzResearch.WordTrace]
  refine ⟨9414482770871815150469893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12552643694495753533959857 9414482770871815150469893)
  ·
    refine ⟨1765215519538465340713105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9414482770871815150469893 1765215519538465340713105)
    ·
      refine ⟨1323911639653849005534829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1765215519538465340713105 1323911639653849005534829)
      ·
        refine ⟨496466864870193377075561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1323911639653849005534829 496466864870193377075561)
        ·
          refine ⟨372350148652645032806671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 496466864870193377075561 372350148652645032806671)
          ·
            refine ⟨558525222978967549210007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372350148652645032806671 558525222978967549210007)
            ·
              refine ⟨837787834468451323815011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 558525222978967549210007 837787834468451323815011)
              ·
                refine ⟨1256681751702676985722517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 837787834468451323815011 1256681751702676985722517)
                ·
                  refine ⟨58906957111062983705743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1256681751702676985722517 58906957111062983705743)
                  ·
                    rfl

theorem cell22_516244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 1, 6].length) (baseStart_516244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_516244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_516244 prefixEnd_516244 := by exact prefixLift 516244
  have htrace : WordTrace (prefixWord ++ tailWord_516244) baseStart_516244 baseEnd_516244 := by
    simpa [prefixWord, tailWord_516244, baseEnd_516244] using wordTrace_append hprefix tailTrace_516244
  have hstable : (prefixWord ++ tailWord_516244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516244).length < 2 ^ (prefixWord ++ tailWord_516244).sum := by decide
  have hdescent : baseEnd_516244 < baseStart_516244 := by decide
  rcases family_descends (prefixWord ++ tailWord_516244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516298 : List Nat := [3, 1, 2, 1, 3, 1, 2, 2, 2, 5]
def baseStart_516298 : Nat := 118140960795 + 516298 * 2 ^ 59
def prefixEnd_516298 : Nat := 4983230072969 + 3 ^ 40 * 516298 * 2
def baseEnd_516298 : Nat := 176739356636750810267063

theorem tailTrace_516298 : CollatzResearch.WordTrace tailWord_516298 prefixEnd_516298 176739356636750810267063 := by
  unfold tailWord_516298
  simp only [CollatzResearch.WordTrace]
  refine ⟨4707733770886999380851387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12553956722365331682270365 4707733770886999380851387)
  ·
    refine ⟨7061600656330499071277081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4707733770886999380851387 7061600656330499071277081)
    ·
      refine ⟨5296200492247874303457811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7061600656330499071277081 5296200492247874303457811)
      ·
        refine ⟨7944300738371811455186717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5296200492247874303457811 7944300738371811455186717)
        ·
          refine ⟨2979112776889429295695019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7944300738371811455186717 2979112776889429295695019)
          ·
            refine ⟨4468669165334143943542529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2979112776889429295695019 4468669165334143943542529)
            ·
              refine ⟨3351501874000607957656897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4468669165334143943542529 3351501874000607957656897)
              ·
                refine ⟨2513626405500455968242673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3351501874000607957656897 2513626405500455968242673)
                ·
                  refine ⟨1885219804125341976182005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2513626405500455968242673 1885219804125341976182005)
                  ·
                    refine ⟨176739356636750810267063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1885219804125341976182005 176739356636750810267063)
                    ·
                      rfl

theorem cell22_516298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_516298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_516298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_516298 prefixEnd_516298 := by exact prefixLift 516298
  have htrace : WordTrace (prefixWord ++ tailWord_516298) baseStart_516298 baseEnd_516298 := by
    simpa [prefixWord, tailWord_516298, baseEnd_516298] using wordTrace_append hprefix tailTrace_516298
  have hstable : (prefixWord ++ tailWord_516298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516298).length < 2 ^ (prefixWord ++ tailWord_516298).sum := by decide
  have hdescent : baseEnd_516298 < baseStart_516298 := by decide
  rcases family_descends (prefixWord ++ tailWord_516298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516313 : List Nat := [1, 2, 1, 2, 3, 1, 3, 2, 3, 4]
def baseStart_516313 : Nat := 118140960795 + 516313 * 2 ^ 59
def prefixEnd_516313 : Nat := 4983230072969 + 3 ^ 40 * 516313 * 2
def baseEnd_516313 : Nat := 176744491443295771142017

theorem tailTrace_516313 : CollatzResearch.WordTrace tailWord_516313 prefixEnd_516313 176744491443295771142017 := by
  unfold tailWord_516313
  simp only [CollatzResearch.WordTrace]
  refine ⟨18831482178493655085201593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12554321452329103390134395 18831482178493655085201593)
  ·
    refine ⟨14123611633870241313901195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18831482178493655085201593 14123611633870241313901195)
    ·
      refine ⟨21185417450805361970851793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14123611633870241313901195 21185417450805361970851793)
      ·
        refine ⟨15889063088104021478138845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21185417450805361970851793 15889063088104021478138845)
        ·
          refine ⟨5958398658039008054302067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15889063088104021478138845 5958398658039008054302067)
          ·
            refine ⟨8937597987058512081453101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5958398658039008054302067 8937597987058512081453101)
            ·
              refine ⟨3351599245146942030544913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8937597987058512081453101 3351599245146942030544913)
              ·
                refine ⟨2513699433860206522908685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3351599245146942030544913 2513699433860206522908685)
                ·
                  refine ⟨942637287697577446090757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2513699433860206522908685 942637287697577446090757)
                  ·
                    refine ⟨176744491443295771142017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 942637287697577446090757 176744491443295771142017)
                    ·
                      rfl

theorem cell22_516313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 3, 4].length) (baseStart_516313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_516313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_516313 prefixEnd_516313 := by exact prefixLift 516313
  have htrace : WordTrace (prefixWord ++ tailWord_516313) baseStart_516313 baseEnd_516313 := by
    simpa [prefixWord, tailWord_516313, baseEnd_516313] using wordTrace_append hprefix tailTrace_516313
  have hstable : (prefixWord ++ tailWord_516313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516313).length < 2 ^ (prefixWord ++ tailWord_516313).sum := by decide
  have hdescent : baseEnd_516313 < baseStart_516313 := by decide
  rcases family_descends (prefixWord ++ tailWord_516313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516328 : List Nat := [2, 1, 4, 1, 2, 2, 1, 1, 8]
def baseStart_516328 : Nat := 118140960795 + 516328 * 2 ^ 59
def prefixEnd_516328 : Nat := 4983230072969 + 3 ^ 40 * 516328 * 2
def baseEnd_516328 : Nat := 58916542083280244005657

theorem tailTrace_516328 : CollatzResearch.WordTrace tailWord_516328 prefixEnd_516328 58916542083280244005657 := by
  unfold tailWord_516328
  simp only [CollatzResearch.WordTrace]
  refine ⟨9416014636719656323498819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12554686182292875097998425 9416014636719656323498819)
  ·
    refine ⟨14124021955079484485248229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9416014636719656323498819 14124021955079484485248229)
    ·
      refine ⟨2648254116577403340984043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14124021955079484485248229 2648254116577403340984043)
      ·
        refine ⟨3972381174866105011476065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2648254116577403340984043 3972381174866105011476065)
        ·
          refine ⟨2979285881149578758607049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3972381174866105011476065 2979285881149578758607049)
          ·
            refine ⟨2234464410862184068955287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2979285881149578758607049 2234464410862184068955287)
            ·
              refine ⟨3351696616293276103432931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2234464410862184068955287 3351696616293276103432931)
              ·
                refine ⟨5027544924439914155149397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3351696616293276103432931 5027544924439914155149397)
                ·
                  refine ⟨58916542083280244005657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5027544924439914155149397 58916542083280244005657)
                  ·
                    rfl

theorem cell22_516328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 8].length) (baseStart_516328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_516328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_516328 prefixEnd_516328 := by exact prefixLift 516328
  have htrace : WordTrace (prefixWord ++ tailWord_516328) baseStart_516328 baseEnd_516328 := by
    simpa [prefixWord, tailWord_516328, baseEnd_516328] using wordTrace_append hprefix tailTrace_516328
  have hstable : (prefixWord ++ tailWord_516328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516328).length < 2 ^ (prefixWord ++ tailWord_516328).sum := by decide
  have hdescent : baseEnd_516328 < baseStart_516328 := by decide
  rcases family_descends (prefixWord ++ tailWord_516328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516330 : List Nat := [3, 1, 3, 1, 1, 2, 2, 4, 1, 4]
def baseStart_516330 : Nat := 118140960795 + 516330 * 2 ^ 59
def prefixEnd_516330 : Nat := 4983230072969 + 3 ^ 40 * 516330 * 2
def baseEnd_516330 : Nat := 176750310890713393466965

theorem tailTrace_516330 : CollatzResearch.WordTrace tailWord_516330 prefixEnd_516330 176750310890713393466965 := by
  unfold tailWord_516330
  simp only [CollatzResearch.WordTrace]
  refine ⟨4708025554858016747142611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12554734812954711325713629 4708025554858016747142611)
  ·
    refine ⟨7062038332287025120713917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4708025554858016747142611 7062038332287025120713917)
    ·
      refine ⟨2648264374607634420267719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7062038332287025120713917 2648264374607634420267719)
      ·
        refine ⟨3972396561911451630401579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2648264374607634420267719 3972396561911451630401579)
        ·
          refine ⟨5958594842867177445602369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3972396561911451630401579 5958594842867177445602369)
          ·
            refine ⟨4468946132150383084201777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5958594842867177445602369 4468946132150383084201777)
            ·
              refine ⟨3351709599112787313151333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4468946132150383084201777 3351709599112787313151333)
              ·
                refine ⟨628445549833647621215875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3351709599112787313151333 628445549833647621215875)
                ·
                  refine ⟨942668324750471431823813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 628445549833647621215875 942668324750471431823813)
                  ·
                    refine ⟨176750310890713393466965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 942668324750471431823813 176750310890713393466965)
                    ·
                      rfl

theorem cell22_516330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_516330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_516330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_516330 prefixEnd_516330 := by exact prefixLift 516330
  have htrace : WordTrace (prefixWord ++ tailWord_516330) baseStart_516330 baseEnd_516330 := by
    simpa [prefixWord, tailWord_516330, baseEnd_516330] using wordTrace_append hprefix tailTrace_516330
  have hstable : (prefixWord ++ tailWord_516330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516330).length < 2 ^ (prefixWord ++ tailWord_516330).sum := by decide
  have hdescent : baseEnd_516330 < baseStart_516330 := by decide
  rcases family_descends (prefixWord ++ tailWord_516330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516463 : List Nat := [1, 1, 2, 1, 3, 1, 2, 1, 10]
def baseStart_516463 : Nat := 118140960795 + 516463 * 2 ^ 59
def prefixEnd_516463 : Nat := 4983230072969 + 3 ^ 40 * 516463 * 2
def baseEnd_516463 : Nat := 58931946502915126630519

theorem tailTrace_516463 : CollatzResearch.WordTrace tailWord_516463 prefixEnd_516463 58931946502915126630519 := by
  unfold tailWord_516463
  simp only [CollatzResearch.WordTrace]
  refine ⟨18836953127950230703162043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12557968751966820468774695 18836953127950230703162043)
  ·
    refine ⟨28255429691925346054743065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18836953127950230703162043 28255429691925346054743065)
    ·
      refine ⟨21191572268944009541057299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28255429691925346054743065 21191572268944009541057299)
      ·
        refine ⟨31787358403416014311585949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21191572268944009541057299 31787358403416014311585949)
        ·
          refine ⟨11920259401281005366844731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31787358403416014311585949 11920259401281005366844731)
          ·
            refine ⟨17880389101921508050267097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11920259401281005366844731 17880389101921508050267097)
            ·
              refine ⟨13410291826441131037700323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17880389101921508050267097 13410291826441131037700323)
              ·
                refine ⟨20115437739661696556550485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13410291826441131037700323 20115437739661696556550485)
                ·
                  refine ⟨58931946502915126630519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 20115437739661696556550485 58931946502915126630519)
                  ·
                    rfl

theorem cell22_516463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 10].length) (baseStart_516463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_516463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_516463 prefixEnd_516463 := by exact prefixLift 516463
  have htrace : WordTrace (prefixWord ++ tailWord_516463) baseStart_516463 baseEnd_516463 := by
    simpa [prefixWord, tailWord_516463, baseEnd_516463] using wordTrace_append hprefix tailTrace_516463
  have hstable : (prefixWord ++ tailWord_516463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516463).length < 2 ^ (prefixWord ++ tailWord_516463).sum := by decide
  have hdescent : baseEnd_516463 < baseStart_516463 := by decide
  rcases family_descends (prefixWord ++ tailWord_516463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516514 : List Nat := [3, 3, 1, 2, 1, 1, 4, 3, 4]
def baseStart_516514 : Nat := 118140960795 + 516514 * 2 ^ 59
def prefixEnd_516514 : Nat := 4983230072969 + 3 ^ 40 * 516514 * 2
def baseEnd_516514 : Nat := 58937765950332748955467

theorem tailTrace_516514 : CollatzResearch.WordTrace tailWord_516514 prefixEnd_516514 58937765950332748955467 := by
  unfold tailWord_516514
  simp only [CollatzResearch.WordTrace]
  refine ⟨4709703312691366603317149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12559208833843644275512397 4709703312691366603317149)
  ·
    refine ⟨1766138742259262476243931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4709703312691366603317149 1766138742259262476243931)
    ·
      refine ⟨2649208113388893714365897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1766138742259262476243931 2649208113388893714365897)
      ·
        refine ⟨1986906085041670285774423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2649208113388893714365897 1986906085041670285774423)
        ·
          refine ⟨2980359127562505428661635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1986906085041670285774423 2980359127562505428661635)
          ·
            refine ⟨4470538691343758142992453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2980359127562505428661635 4470538691343758142992453)
            ·
              refine ⟨838226004626954651811085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4470538691343758142992453 838226004626954651811085)
              ·
                refine ⟨314334751735107994429157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 838226004626954651811085 314334751735107994429157)
                ·
                  refine ⟨58937765950332748955467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 314334751735107994429157 58937765950332748955467)
                  ·
                    rfl

theorem cell22_516514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 3, 4].length) (baseStart_516514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_516514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_516514 prefixEnd_516514 := by exact prefixLift 516514
  have htrace : WordTrace (prefixWord ++ tailWord_516514) baseStart_516514 baseEnd_516514 := by
    simpa [prefixWord, tailWord_516514, baseEnd_516514] using wordTrace_append hprefix tailTrace_516514
  have hstable : (prefixWord ++ tailWord_516514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516514).length < 2 ^ (prefixWord ++ tailWord_516514).sum := by decide
  have hdescent : baseEnd_516514 < baseStart_516514 := by decide
  rcases family_descends (prefixWord ++ tailWord_516514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516529 : List Nat := [1, 2, 2, 4, 1, 2, 3, 2, 2, 3]
def baseStart_516529 : Nat := 118140960795 + 516529 * 2 ^ 59
def prefixEnd_516529 : Nat := 4983230072969 + 3 ^ 40 * 516529 * 2
def baseEnd_516529 : Nat := 176818432657543207741355

theorem tailTrace_516529 : CollatzResearch.WordTrace tailWord_516529 prefixEnd_516529 176818432657543207741355 := by
  unfold tailWord_516529
  simp only [CollatzResearch.WordTrace]
  refine ⟨18839360345711123975064641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12559573563807415983376427 18839360345711123975064641)
  ·
    refine ⟨14129520259283342981298481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18839360345711123975064641 14129520259283342981298481)
    ·
      refine ⟨10597140194462507235973861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14129520259283342981298481 10597140194462507235973861)
      ·
        refine ⟨1986963786461720106745099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10597140194462507235973861 1986963786461720106745099)
        ·
          refine ⟨2980445679692580160117649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1986963786461720106745099 2980445679692580160117649)
          ·
            refine ⟨2235334259769435120088237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2980445679692580160117649 2235334259769435120088237)
            ·
              refine ⟨838250347413538170033089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2235334259769435120088237 838250347413538170033089)
              ·
                refine ⟨628687760560153627524817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 838250347413538170033089 628687760560153627524817)
                ·
                  refine ⟨471515820420115220643613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 628687760560153627524817 471515820420115220643613)
                  ·
                    refine ⟨176818432657543207741355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 471515820420115220643613 176818432657543207741355)
                    ·
                      rfl

theorem cell22_516529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 2, 2, 3].length) (baseStart_516529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_516529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_516529 prefixEnd_516529 := by exact prefixLift 516529
  have htrace : WordTrace (prefixWord ++ tailWord_516529) baseStart_516529 baseEnd_516529 := by
    simpa [prefixWord, tailWord_516529, baseEnd_516529] using wordTrace_append hprefix tailTrace_516529
  have hstable : (prefixWord ++ tailWord_516529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516529).length < 2 ^ (prefixWord ++ tailWord_516529).sum := by decide
  have hdescent : baseEnd_516529 < baseStart_516529 := by decide
  rcases family_descends (prefixWord ++ tailWord_516529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516570 : List Nat := [3, 1, 1, 2, 3, 1, 1, 1, 9]
def baseStart_516570 : Nat := 118140960795 + 516570 * 2 ^ 59
def prefixEnd_516570 : Nat := 4983230072969 + 3 ^ 40 * 516570 * 2
def baseEnd_516570 : Nat := 58944155931810922488743

theorem tailTrace_516570 : CollatzResearch.WordTrace tailWord_516570 prefixEnd_516570 58944155931810922488743 := by
  unfold tailWord_516570
  simp only [CollatzResearch.WordTrace]
  refine ⟨4710213934640646994326791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12560570492375058651538109 4710213934640646994326791)
  ·
    refine ⟨7065320901960970491490187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4710213934640646994326791 7065320901960970491490187)
    ·
      refine ⟨10597981352941455737235281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7065320901960970491490187 10597981352941455737235281)
      ·
        refine ⟨7948486014706091802926461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10597981352941455737235281 7948486014706091802926461)
        ·
          refine ⟨2980682255514784426097423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7948486014706091802926461 2980682255514784426097423)
          ·
            refine ⟨4471023383272176639146135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2980682255514784426097423 4471023383272176639146135)
            ·
              refine ⟨6706535074908264958719203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4471023383272176639146135 6706535074908264958719203)
              ·
                refine ⟨10059802612362397438078805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6706535074908264958719203 10059802612362397438078805)
                ·
                  refine ⟨58944155931810922488743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 10059802612362397438078805 58944155931810922488743)
                  ·
                    rfl

theorem cell22_516570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 9].length) (baseStart_516570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_516570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_516570 prefixEnd_516570 := by exact prefixLift 516570
  have htrace : WordTrace (prefixWord ++ tailWord_516570) baseStart_516570 baseEnd_516570 := by
    simpa [prefixWord, tailWord_516570, baseEnd_516570] using wordTrace_append hprefix tailTrace_516570
  have hstable : (prefixWord ++ tailWord_516570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516570).length < 2 ^ (prefixWord ++ tailWord_516570).sum := by decide
  have hdescent : baseEnd_516570 < baseStart_516570 := by decide
  rcases family_descends (prefixWord ++ tailWord_516570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516585 : List Nat := [1, 2, 1, 1, 1, 2, 1, 6, 2, 5]
def baseStart_516585 : Nat := 118140960795 + 516585 * 2 ^ 59
def prefixEnd_516585 : Nat := 4983230072969 + 3 ^ 40 * 516585 * 2
def baseEnd_516585 : Nat := 176837602601977728341183

theorem tailTrace_516585 : CollatzResearch.WordTrace tailWord_516585 prefixEnd_516585 176837602601977728341183 := by
  unfold tailWord_516585
  simp only [CollatzResearch.WordTrace]
  refine ⟨18841402833508245539103209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12560935222338830359402139 18841402833508245539103209)
  ·
    refine ⟨14131052125131184154327407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18841402833508245539103209 14131052125131184154327407)
    ·
      refine ⟨21196578187696776231491111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14131052125131184154327407 21196578187696776231491111)
      ·
        refine ⟨31794867281545164347236667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21196578187696776231491111 31794867281545164347236667)
        ·
          refine ⟨47692300922317746520855001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31794867281545164347236667 47692300922317746520855001)
          ·
            refine ⟨35769225691738309890641251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47692300922317746520855001 35769225691738309890641251)
            ·
              refine ⟨53653838537607464835961877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35769225691738309890641251 53653838537607464835961877)
              ·
                refine ⟨2515023681450349914185713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 53653838537607464835961877 2515023681450349914185713)
                ·
                  refine ⟨1886267761087762435639285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2515023681450349914185713 1886267761087762435639285)
                  ·
                    refine ⟨176837602601977728341183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1886267761087762435639285 176837602601977728341183)
                    ·
                      rfl

theorem cell22_516585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 2, 5].length) (baseStart_516585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_516585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_516585 prefixEnd_516585 := by exact prefixLift 516585
  have htrace : WordTrace (prefixWord ++ tailWord_516585) baseStart_516585 baseEnd_516585 := by
    simpa [prefixWord, tailWord_516585, baseEnd_516585] using wordTrace_append hprefix tailTrace_516585
  have hstable : (prefixWord ++ tailWord_516585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516585).length < 2 ^ (prefixWord ++ tailWord_516585).sum := by decide
  have hdescent : baseEnd_516585 < baseStart_516585 := by decide
  rcases family_descends (prefixWord ++ tailWord_516585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516617 : List Nat := [1, 2, 1, 1, 3, 1, 2, 6, 1, 4]
def baseStart_516617 : Nat := 118140960795 + 516617 * 2 ^ 59
def prefixEnd_516617 : Nat := 4983230072969 + 3 ^ 40 * 516617 * 2
def baseEnd_516617 : Nat := 176848556855940311541085

theorem tailTrace_516617 : CollatzResearch.WordTrace tailWord_516617 prefixEnd_516617 176848556855940311541085 := by
  unfold tailWord_516617
  simp only [CollatzResearch.WordTrace]
  refine ⟨18842569969392315004268105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12561713312928210002845403 18842569969392315004268105)
  ·
    refine ⟨14131927477044236253201079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18842569969392315004268105 14131927477044236253201079)
    ·
      refine ⟨21197891215566354379801619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14131927477044236253201079 21197891215566354379801619)
      ·
        refine ⟨31796836823349531569702429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21197891215566354379801619 31796836823349531569702429)
        ·
          refine ⟨11923813808756074338638411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31796836823349531569702429 11923813808756074338638411)
          ·
            refine ⟨17885720713134111507957617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11923813808756074338638411 17885720713134111507957617)
            ·
              refine ⟨13414290534850583630968213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17885720713134111507957617 13414290534850583630968213)
              ·
                refine ⟨628794868821121107701635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13414290534850583630968213 628794868821121107701635)
                ·
                  refine ⟨943192303231681661552453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 628794868821121107701635 943192303231681661552453)
                  ·
                    refine ⟨176848556855940311541085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 943192303231681661552453 176848556855940311541085)
                    ·
                      rfl

theorem cell22_516617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 6, 1, 4].length) (baseStart_516617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_516617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_516617 prefixEnd_516617 := by exact prefixLift 516617
  have htrace : WordTrace (prefixWord ++ tailWord_516617) baseStart_516617 baseEnd_516617 := by
    simpa [prefixWord, tailWord_516617, baseEnd_516617] using wordTrace_append hprefix tailTrace_516617
  have hstable : (prefixWord ++ tailWord_516617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516617).length < 2 ^ (prefixWord ++ tailWord_516617).sum := by decide
  have hdescent : baseEnd_516617 < baseStart_516617 := by decide
  rcases family_descends (prefixWord ++ tailWord_516617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516653 : List Nat := [1, 5, 4, 1, 1, 1, 1, 1, 2, 5]
def baseStart_516653 : Nat := 118140960795 + 516653 * 2 ^ 59
def prefixEnd_516653 : Nat := 4983230072969 + 3 ^ 40 * 516653 * 2
def baseEnd_516653 : Nat := 176860880391648217640975

theorem tailTrace_516653 : CollatzResearch.WordTrace tailWord_516653 prefixEnd_516653 176860880391648217640975 := by
  unfold tailWord_516653
  simp only [CollatzResearch.WordTrace]
  refine ⟨18843882997261893152578613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12562588664841262101719075 18843882997261893152578613)
  ·
    refine ⟨1766614030993302483054245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18843882997261893152578613 1766614030993302483054245)
    ·
      refine ⟨331240130811244215572671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1766614030993302483054245 331240130811244215572671)
      ·
        refine ⟨496860196216866323359007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331240130811244215572671 496860196216866323359007)
        ·
          refine ⟨745290294325299485038511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 496860196216866323359007 745290294325299485038511)
          ·
            refine ⟨1117935441487949227557767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 745290294325299485038511 1117935441487949227557767)
            ·
              refine ⟨1676903162231923841336651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1117935441487949227557767 1676903162231923841336651)
              ·
                refine ⟨2515354743347885762004977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1676903162231923841336651 2515354743347885762004977)
                ·
                  refine ⟨1886516057510914321503733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2515354743347885762004977 1886516057510914321503733)
                  ·
                    refine ⟨176860880391648217640975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1886516057510914321503733 176860880391648217640975)
                    ·
                      rfl

theorem cell22_516653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_516653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_516653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_516653 prefixEnd_516653 := by exact prefixLift 516653
  have htrace : WordTrace (prefixWord ++ tailWord_516653) baseStart_516653 baseEnd_516653 := by
    simpa [prefixWord, tailWord_516653, baseEnd_516653] using wordTrace_append hprefix tailTrace_516653
  have hstable : (prefixWord ++ tailWord_516653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516653).length < 2 ^ (prefixWord ++ tailWord_516653).sum := by decide
  have hdescent : baseEnd_516653 < baseStart_516653 := by decide
  rcases family_descends (prefixWord ++ tailWord_516653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516664 : List Nat := [2, 1, 2, 1, 4, 1, 1, 5, 2, 3]
def baseStart_516664 : Nat := 118140960795 + 516664 * 2 ^ 59
def prefixEnd_516664 : Nat := 4983230072969 + 3 ^ 40 * 516664 * 2
def baseEnd_516664 : Nat := 176864645916447855615941

theorem tailTrace_516664 : CollatzResearch.WordTrace tailWord_516664 prefixEnd_516664 176864645916447855615941 := by
  unfold tailWord_516664
  simp only [CollatzResearch.WordTrace]
  refine ⟨9422142100111021015614523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12562856133481361354152697 9422142100111021015614523)
  ·
    refine ⟨14133213150166531523421785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9422142100111021015614523 14133213150166531523421785)
    ·
      refine ⟨10599909862624898642566339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14133213150166531523421785 10599909862624898642566339)
      ·
        refine ⟨15899864793937347963849509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10599909862624898642566339 15899864793937347963849509)
        ·
          refine ⟨2981224648863252743221783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15899864793937347963849509 2981224648863252743221783)
          ·
            refine ⟨4471836973294879114832675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2981224648863252743221783 4471836973294879114832675)
            ·
              refine ⟨6707755459942318672249013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4471836973294879114832675 6707755459942318672249013)
              ·
                refine ⟨628852074369592375523345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6707755459942318672249013 628852074369592375523345)
                ·
                  refine ⟨471639055777194281642509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 628852074369592375523345 471639055777194281642509)
                  ·
                    refine ⟨176864645916447855615941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 471639055777194281642509 176864645916447855615941)
                    ·
                      rfl

theorem cell22_516664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 5, 2, 3].length) (baseStart_516664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_516664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_516664 prefixEnd_516664 := by exact prefixLift 516664
  have htrace : WordTrace (prefixWord ++ tailWord_516664) baseStart_516664 baseEnd_516664 := by
    simpa [prefixWord, tailWord_516664, baseEnd_516664] using wordTrace_append hprefix tailTrace_516664
  have hstable : (prefixWord ++ tailWord_516664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516664).length < 2 ^ (prefixWord ++ tailWord_516664).sum := by decide
  have hdescent : baseEnd_516664 < baseStart_516664 := by decide
  rcases family_descends (prefixWord ++ tailWord_516664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516679 : List Nat := [1, 1, 4, 1, 4, 1, 3, 1, 2, 4]
def baseStart_516679 : Nat := 118140960795 + 516679 * 2 ^ 59
def prefixEnd_516679 : Nat := 4983230072969 + 3 ^ 40 * 516679 * 2
def baseEnd_516679 : Nat := 176869780722992816490895

theorem tailTrace_516679 : CollatzResearch.WordTrace tailWord_516679 prefixEnd_516679 176869780722992816490895 := by
  unfold tailWord_516679
  simp only [CollatzResearch.WordTrace]
  refine ⟨18844831295167699593025091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12563220863445133062016727 18844831295167699593025091)
  ·
    refine ⟨28267246942751549389537637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18844831295167699593025091 28267246942751549389537637)
    ·
      refine ⟨5300108801765915510538307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28267246942751549389537637 5300108801765915510538307)
      ·
        refine ⟨7950163202648873265807461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5300108801765915510538307 7950163202648873265807461)
        ·
          refine ⟨1490655600496663737338899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7950163202648873265807461 1490655600496663737338899)
          ·
            refine ⟨2235983400744995606008349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1490655600496663737338899 2235983400744995606008349)
            ·
              refine ⟨838493775279373352253131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2235983400744995606008349 838493775279373352253131)
              ·
                refine ⟨1257740662919060028379697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 838493775279373352253131 1257740662919060028379697)
                ·
                  refine ⟨943305497189295021284773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1257740662919060028379697 943305497189295021284773)
                  ·
                    refine ⟨176869780722992816490895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 943305497189295021284773 176869780722992816490895)
                    ·
                      rfl

theorem cell22_516679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 1, 2, 4].length) (baseStart_516679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_516679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_516679 prefixEnd_516679 := by exact prefixLift 516679
  have htrace : WordTrace (prefixWord ++ tailWord_516679) baseStart_516679 baseEnd_516679 := by
    simpa [prefixWord, tailWord_516679, baseEnd_516679] using wordTrace_append hprefix tailTrace_516679
  have hstable : (prefixWord ++ tailWord_516679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516679).length < 2 ^ (prefixWord ++ tailWord_516679).sum := by decide
  have hdescent : baseEnd_516679 < baseStart_516679 := by decide
  rcases family_descends (prefixWord ++ tailWord_516679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516752 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 7, 4]
def baseStart_516752 : Nat := 118140960795 + 516752 * 2 ^ 59
def prefixEnd_516752 : Nat := 4983230072969 + 3 ^ 40 * 516752 * 2
def baseEnd_516752 : Nat := 176894770114844959415671

theorem tailTrace_516752 : CollatzResearch.WordTrace tailWord_516752 prefixEnd_516752 176894770114844959415671 := by
  unfold tailWord_516752
  simp only [CollatzResearch.WordTrace]
  refine ⟨9423746911951616530216255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12564995882602155373621673 9423746911951616530216255)
  ·
    refine ⟨14135620367927424795324383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9423746911951616530216255 14135620367927424795324383)
    ·
      refine ⟨21203430551891137192986575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14135620367927424795324383 21203430551891137192986575)
      ·
        refine ⟨31805145827836705789479863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21203430551891137192986575 31805145827836705789479863)
        ·
          refine ⟨47707718741755058684219795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31805145827836705789479863 47707718741755058684219795)
          ·
            refine ⟨71561578112632588026329693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47707718741755058684219795 71561578112632588026329693)
            ·
              refine ⟨26835591792237220509873635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71561578112632588026329693 26835591792237220509873635)
              ·
                refine ⟨40253387688355830764810453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26835591792237220509873635 40253387688355830764810453)
                ·
                  refine ⟨943438773945839783550245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 40253387688355830764810453 943438773945839783550245)
                  ·
                    refine ⟨176894770114844959415671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 943438773945839783550245 176894770114844959415671)
                    ·
                      rfl

theorem cell22_516752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 7, 4].length) (baseStart_516752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_516752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_516752 prefixEnd_516752 := by exact prefixLift 516752
  have htrace : WordTrace (prefixWord ++ tailWord_516752) baseStart_516752 baseEnd_516752 := by
    simpa [prefixWord, tailWord_516752, baseEnd_516752] using wordTrace_append hprefix tailTrace_516752
  have hstable : (prefixWord ++ tailWord_516752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516752).length < 2 ^ (prefixWord ++ tailWord_516752).sum := by decide
  have hdescent : baseEnd_516752 < baseStart_516752 := by decide
  rcases family_descends (prefixWord ++ tailWord_516752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516799 : List Nat := [1, 1, 2, 2, 2, 5, 1, 2, 1, 5]
def baseStart_516799 : Nat := 118140960795 + 516799 * 2 ^ 59
def prefixEnd_516799 : Nat := 4983230072969 + 3 ^ 40 * 516799 * 2
def baseEnd_516799 : Nat := 176910859175352503490527

theorem tailTrace_516799 : CollatzResearch.WordTrace tailWord_516799 prefixEnd_516799 176910859175352503490527 := by
  unfold tailWord_516799
  simp only [CollatzResearch.WordTrace]
  refine ⟨18849208054732960087393451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12566138703155306724928967 18849208054732960087393451)
  ·
    refine ⟨28273812082099440131090177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18849208054732960087393451 28273812082099440131090177)
    ·
      refine ⟨21205359061574580098317633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28273812082099440131090177 21205359061574580098317633)
      ·
        refine ⟨15904019296180935073738225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21205359061574580098317633 15904019296180935073738225)
        ·
          refine ⟨11928014472135701305303669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15904019296180935073738225 11928014472135701305303669)
          ·
            refine ⟨1118251356762721997372219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11928014472135701305303669 1118251356762721997372219)
            ·
              refine ⟨1677377035144082996058329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1118251356762721997372219 1677377035144082996058329)
              ·
                refine ⟨1258032776358062247043747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1677377035144082996058329 1258032776358062247043747)
                ·
                  refine ⟨1887049164537093370565621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1258032776358062247043747 1887049164537093370565621)
                  ·
                    refine ⟨176910859175352503490527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1887049164537093370565621 176910859175352503490527)
                    ·
                      rfl

theorem cell22_516799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 2, 1, 5].length) (baseStart_516799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_516799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_516799 prefixEnd_516799 := by exact prefixLift 516799
  have htrace : WordTrace (prefixWord ++ tailWord_516799) baseStart_516799 baseEnd_516799 := by
    simpa [prefixWord, tailWord_516799, baseEnd_516799] using wordTrace_append hprefix tailTrace_516799
  have hstable : (prefixWord ++ tailWord_516799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516799).length < 2 ^ (prefixWord ++ tailWord_516799).sum := by decide
  have hdescent : baseEnd_516799 < baseStart_516799 := by decide
  rcases family_descends (prefixWord ++ tailWord_516799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516818 : List Nat := [3, 2, 2, 2, 3, 1, 1, 4, 4]
def baseStart_516818 : Nat := 118140960795 + 516818 * 2 ^ 59
def prefixEnd_516818 : Nat := 4983230072969 + 3 ^ 40 * 516818 * 2
def baseEnd_516818 : Nat := 58972454421214262421823

theorem tailTrace_516818 : CollatzResearch.WordTrace tailWord_516818 prefixEnd_516818 58972454421214262421823 := by
  unfold tailWord_516818
  simp only [CollatzResearch.WordTrace]
  refine ⟨4712475260416031583083777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12566600694442750888223405 4712475260416031583083777)
  ·
    refine ⟨3534356445312023687312833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4712475260416031583083777 3534356445312023687312833)
    ·
      refine ⟨2650767333984017765484625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3534356445312023687312833 2650767333984017765484625)
      ·
        refine ⟨1988075500488013324113469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2650767333984017765484625 1988075500488013324113469)
        ·
          refine ⟨745528312683004996542551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1988075500488013324113469 745528312683004996542551)
          ·
            refine ⟨1118292469024507494813827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 745528312683004996542551 1118292469024507494813827)
            ·
              refine ⟨1677438703536761242220741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1118292469024507494813827 1677438703536761242220741)
              ·
                refine ⟨314519756913142732916389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1677438703536761242220741 314519756913142732916389)
                ·
                  refine ⟨58972454421214262421823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 314519756913142732916389 58972454421214262421823)
                  ·
                    rfl

theorem cell22_516818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 4, 4].length) (baseStart_516818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_516818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_516818 prefixEnd_516818 := by exact prefixLift 516818
  have htrace : WordTrace (prefixWord ++ tailWord_516818) baseStart_516818 baseEnd_516818 := by
    simpa [prefixWord, tailWord_516818, baseEnd_516818] using wordTrace_append hprefix tailTrace_516818
  have hstable : (prefixWord ++ tailWord_516818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516818).length < 2 ^ (prefixWord ++ tailWord_516818).sum := by decide
  have hdescent : baseEnd_516818 < baseStart_516818 := by decide
  rcases family_descends (prefixWord ++ tailWord_516818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516846 : List Nat := [4, 1, 2, 1, 1, 4, 3, 6]
def baseStart_516846 : Nat := 118140960795 + 516846 * 2 ^ 59
def prefixEnd_516846 : Nat := 4983230072969 + 3 ^ 40 * 516846 * 2
def baseEnd_516846 : Nat := 19658549803984449729487

theorem tailTrace_516846 : CollatzResearch.WordTrace tailWord_516846 prefixEnd_516846 19658549803984449729487 := by
  unfold tailWord_516846
  simp only [CollatzResearch.WordTrace]
  refine ⟨2356365285695335889294299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12567281523708458076236261 2356365285695335889294299)
  ·
    refine ⟨3534547928543003833941449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2356365285695335889294299 3534547928543003833941449)
    ·
      refine ⟨2650910946407252875456087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3534547928543003833941449 2650910946407252875456087)
      ·
        refine ⟨3976366419610879313184131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2650910946407252875456087 3976366419610879313184131)
        ·
          refine ⟨5964549629416318969776197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3976366419610879313184131 5964549629416318969776197)
          ·
            refine ⟨1118353055515559806833037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5964549629416318969776197 1118353055515559806833037)
            ·
              refine ⟨419382395818334927562389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1118353055515559806833037 419382395818334927562389)
              ·
                refine ⟨19658549803984449729487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 419382395818334927562389 19658549803984449729487)
                ·
                  rfl

theorem cell22_516846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 3, 6].length) (baseStart_516846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_516846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_516846 prefixEnd_516846 := by exact prefixLift 516846
  have htrace : WordTrace (prefixWord ++ tailWord_516846) baseStart_516846 baseEnd_516846 := by
    simpa [prefixWord, tailWord_516846, baseEnd_516846] using wordTrace_append hprefix tailTrace_516846
  have hstable : (prefixWord ++ tailWord_516846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516846).length < 2 ^ (prefixWord ++ tailWord_516846).sum := by decide
  have hdescent : baseEnd_516846 < baseStart_516846 := by decide
  rcases family_descends (prefixWord ++ tailWord_516846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516852 : List Nat := [2, 6, 1, 1, 2, 1, 2, 3, 4]
def baseStart_516852 : Nat := 118140960795 + 516852 * 2 ^ 59
def prefixEnd_516852 : Nat := 4983230072969 + 3 ^ 40 * 516852 * 2
def baseEnd_516852 : Nat := 58976334052826010638455

theorem tailTrace_516852 : CollatzResearch.WordTrace tailWord_516852 prefixEnd_516852 58976334052826010638455 := by
  unfold tailWord_516852
  simp only [CollatzResearch.WordTrace]
  refine ⟨9425570561770475069536405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12567427415693966759381873 9425570561770475069536405)
  ·
    refine ⟨441823620082991018884519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9425570561770475069536405 441823620082991018884519)
    ·
      refine ⟨662735430124486528326779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441823620082991018884519 662735430124486528326779)
      ·
        refine ⟨994103145186729792490169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 662735430124486528326779 994103145186729792490169)
        ·
          refine ⟨745577358890047344367627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 994103145186729792490169 745577358890047344367627)
          ·
            refine ⟨1118366038335071016551441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 745577358890047344367627 1118366038335071016551441)
            ·
              refine ⟨838774528751303262413581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1118366038335071016551441 838774528751303262413581)
              ·
                refine ⟨314540448281738723405093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 838774528751303262413581 314540448281738723405093)
                ·
                  refine ⟨58976334052826010638455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 314540448281738723405093 58976334052826010638455)
                  ·
                    rfl

theorem cell22_516852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_516852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_516852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_516852 prefixEnd_516852 := by exact prefixLift 516852
  have htrace : WordTrace (prefixWord ++ tailWord_516852) baseStart_516852 baseEnd_516852 := by
    simpa [prefixWord, tailWord_516852, baseEnd_516852] using wordTrace_append hprefix tailTrace_516852
  have hstable : (prefixWord ++ tailWord_516852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516852).length < 2 ^ (prefixWord ++ tailWord_516852).sum := by decide
  have hdescent : baseEnd_516852 < baseStart_516852 := by decide
  rcases family_descends (prefixWord ++ tailWord_516852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516874 : List Nat := [3, 1, 2, 2, 1, 2, 3, 1, 7]
def baseStart_516874 : Nat := 118140960795 + 516874 * 2 ^ 59
def prefixEnd_516874 : Nat := 4983230072969 + 3 ^ 40 * 516874 * 2
def baseEnd_516874 : Nat := 58978844402692435955099

theorem tailTrace_516874 : CollatzResearch.WordTrace tailWord_516874 prefixEnd_516874 58978844402692435955099 := by
  unfold tailWord_516874
  simp only [CollatzResearch.WordTrace]
  refine ⟨4712985882365311974093419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12567962352974165264249117 4712985882365311974093419)
  ·
    refine ⟨7069478823547967961140129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4712985882365311974093419 7069478823547967961140129)
    ·
      refine ⟨5302109117660975970855097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7069478823547967961140129 5302109117660975970855097)
      ·
        refine ⟨3976581838245731978141323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5302109117660975970855097 3976581838245731978141323)
        ·
          refine ⟨5964872757368597967211985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3976581838245731978141323 5964872757368597967211985)
          ·
            refine ⟨4473654568026448475408989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5964872757368597967211985 4473654568026448475408989)
            ·
              refine ⟨1677620463009918178278371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4473654568026448475408989 1677620463009918178278371)
              ·
                refine ⟨2516430694514877267417557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1677620463009918178278371 2516430694514877267417557)
                ·
                  refine ⟨58978844402692435955099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2516430694514877267417557 58978844402692435955099)
                  ·
                    rfl

theorem cell22_516874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 7].length) (baseStart_516874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_516874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_516874 prefixEnd_516874 := by exact prefixLift 516874
  have htrace : WordTrace (prefixWord ++ tailWord_516874) baseStart_516874 baseEnd_516874 := by
    simpa [prefixWord, tailWord_516874, baseEnd_516874] using wordTrace_append hprefix tailTrace_516874
  have hstable : (prefixWord ++ tailWord_516874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516874).length < 2 ^ (prefixWord ++ tailWord_516874).sum := by decide
  have hdescent : baseEnd_516874 < baseStart_516874 := by decide
  rcases family_descends (prefixWord ++ tailWord_516874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516929 : List Nat := [1, 2, 5, 3, 1, 1, 3, 2, 1, 3]
def baseStart_516929 : Nat := 118140960795 + 516929 * 2 ^ 59
def prefixEnd_516929 : Nat := 4983230072969 + 3 ^ 40 * 516929 * 2
def baseEnd_516929 : Nat := 176955360832075497740129

theorem tailTrace_516929 : CollatzResearch.WordTrace tailWord_516929 prefixEnd_516929 176955360832075497740129 := by
  unfold tailWord_516929
  simp only [CollatzResearch.WordTrace]
  refine ⟨18853949544261992289625841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12569299696174661526417227 18853949544261992289625841)
  ·
    refine ⟨14140462158196494217219381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18853949544261992289625841 14140462158196494217219381)
    ·
      refine ⟨1325668327330921332864317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14140462158196494217219381 1325668327330921332864317)
      ·
        refine ⟨497125622749095499824119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1325668327330921332864317 497125622749095499824119)
        ·
          refine ⟨745688434123643249736179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 497125622749095499824119 745688434123643249736179)
          ·
            refine ⟨1118532651185464874604269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 745688434123643249736179 1118532651185464874604269)
            ·
              refine ⟨419449744194549327976601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1118532651185464874604269 419449744194549327976601)
              ·
                refine ⟨314587308145911995982451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 419449744194549327976601 314587308145911995982451)
                ·
                  refine ⟨471880962218867993973677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 314587308145911995982451 471880962218867993973677)
                  ·
                    refine ⟨176955360832075497740129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 471880962218867993973677 176955360832075497740129)
                    ·
                      rfl

theorem cell22_516929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_516929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_516929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_516929 prefixEnd_516929 := by exact prefixLift 516929
  have htrace : WordTrace (prefixWord ++ tailWord_516929) baseStart_516929 baseEnd_516929 := by
    simpa [prefixWord, tailWord_516929, baseEnd_516929] using wordTrace_append hprefix tailTrace_516929
  have hstable : (prefixWord ++ tailWord_516929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516929).length < 2 ^ (prefixWord ++ tailWord_516929).sum := by decide
  have hdescent : baseEnd_516929 < baseStart_516929 := by decide
  rcases family_descends (prefixWord ++ tailWord_516929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517009 : List Nat := [1, 2, 2, 1, 1, 1, 3, 2, 9]
def baseStart_517009 : Nat := 118140960795 + 517009 * 2 ^ 59
def prefixEnd_517009 : Nat := 4983230072969 + 3 ^ 40 * 517009 * 2
def baseEnd_517009 : Nat := 58994248822327318579961

theorem tailTrace_517009 : CollatzResearch.WordTrace tailWord_517009 prefixEnd_517009 58994248822327318579961 := by
  unfold tailWord_517009
  simp only [CollatzResearch.WordTrace]
  refine ⟨18856867383972165952538081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12571244922648110635025387 18856867383972165952538081)
  ·
    refine ⟨14142650537979124464403561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18856867383972165952538081 14142650537979124464403561)
    ·
      refine ⟨10606987903484343348302671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14142650537979124464403561 10606987903484343348302671)
      ·
        refine ⟨15910481855226515022454007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10606987903484343348302671 15910481855226515022454007)
        ·
          refine ⟨23865722782839772533681011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15910481855226515022454007 23865722782839772533681011)
          ·
            refine ⟨35798584174259658800521517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23865722782839772533681011 35798584174259658800521517)
            ·
              refine ⟨13424469065347372050195569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35798584174259658800521517 13424469065347372050195569)
              ·
                refine ⟨10068351799010529037646677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13424469065347372050195569 10068351799010529037646677)
                ·
                  refine ⟨58994248822327318579961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 10068351799010529037646677 58994248822327318579961)
                  ·
                    rfl

theorem cell22_517009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 9].length) (baseStart_517009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_517009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_517009 prefixEnd_517009 := by exact prefixLift 517009
  have htrace : WordTrace (prefixWord ++ tailWord_517009) baseStart_517009 baseEnd_517009 := by
    simpa [prefixWord, tailWord_517009, baseEnd_517009] using wordTrace_append hprefix tailTrace_517009
  have hstable : (prefixWord ++ tailWord_517009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517009).length < 2 ^ (prefixWord ++ tailWord_517009).sum := by decide
  have hdescent : baseEnd_517009 < baseStart_517009 := by decide
  rcases family_descends (prefixWord ++ tailWord_517009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517013 : List Nat := [1, 3, 2, 1, 1, 5, 1, 2, 3, 3]
def baseStart_517013 : Nat := 118140960795 + 517013 * 2 ^ 59
def prefixEnd_517013 : Nat := 4983230072969 + 3 ^ 40 * 517013 * 2
def baseEnd_517013 : Nat := 176984115748727278639871

theorem tailTrace_517013 : CollatzResearch.WordTrace tailWord_517013 prefixEnd_517013 176984115748727278639871 := by
  unfold tailWord_517013
  simp only [CollatzResearch.WordTrace]
  refine ⟨18857013275957674635683693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12571342183971783090455795 18857013275957674635683693)
  ·
    refine ⟨7071379978484127988381385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18857013275957674635683693 7071379978484127988381385)
    ·
      refine ⟨5303534983863095991286039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7071379978484127988381385 5303534983863095991286039)
      ·
        refine ⟨7955302475794643986929059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5303534983863095991286039 7955302475794643986929059)
        ·
          refine ⟨11932953713691965980393589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7955302475794643986929059 11932953713691965980393589)
          ·
            refine ⟨1118714410658621810661899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11932953713691965980393589 1118714410658621810661899)
            ·
              refine ⟨1678071615987932715992849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1118714410658621810661899 1678071615987932715992849)
              ·
                refine ⟨1258553711990949536994637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1678071615987932715992849 1258553711990949536994637)
                ·
                  refine ⟨471957641996606076372989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1258553711990949536994637 471957641996606076372989)
                  ·
                    refine ⟨176984115748727278639871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 471957641996606076372989 176984115748727278639871)
                    ·
                      rfl

theorem cell22_517013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 2, 3, 3].length) (baseStart_517013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_517013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_517013 prefixEnd_517013 := by exact prefixLift 517013
  have htrace : WordTrace (prefixWord ++ tailWord_517013) baseStart_517013 baseEnd_517013 := by
    simpa [prefixWord, tailWord_517013, baseEnd_517013] using wordTrace_append hprefix tailTrace_517013
  have hstable : (prefixWord ++ tailWord_517013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517013).length < 2 ^ (prefixWord ++ tailWord_517013).sum := by decide
  have hdescent : baseEnd_517013 < baseStart_517013 := by decide
  rcases family_descends (prefixWord ++ tailWord_517013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517071 : List Nat := [1, 1, 2, 1, 1, 6, 2, 2, 6]
def baseStart_517071 : Nat := 118140960795 + 517071 * 2 ^ 59
def prefixEnd_517071 : Nat := 4983230072969 + 3 ^ 40 * 517071 * 2
def baseEnd_517071 : Nat := 59001323444678153563231

theorem tailTrace_517071 : CollatzResearch.WordTrace tailWord_517071 prefixEnd_517071 59001323444678153563231 := by
  unfold tailWord_517071
  simp only [CollatzResearch.WordTrace]
  refine ⟨18859128709747550541295067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12572752473165033694196711 18859128709747550541295067)
  ·
    refine ⟨28288693064621325811942601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18859128709747550541295067 28288693064621325811942601)
    ·
      refine ⟨21216519798465994358956951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28288693064621325811942601 21216519798465994358956951)
      ·
        refine ⟨31824779697698991538435427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21216519798465994358956951 31824779697698991538435427)
        ·
          refine ⟨47737169546548487307653141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31824779697698991538435427 47737169546548487307653141)
          ·
            refine ⟨2237679822494460342546241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 47737169546548487307653141 2237679822494460342546241)
            ·
              refine ⟨1678259866870845256909681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2237679822494460342546241 1678259866870845256909681)
              ·
                refine ⟨1258694900153133942682261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1678259866870845256909681 1258694900153133942682261)
                ·
                  refine ⟨59001323444678153563231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1258694900153133942682261 59001323444678153563231)
                  ·
                    rfl

theorem cell22_517071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 2, 6].length) (baseStart_517071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_517071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_517071 prefixEnd_517071 := by exact prefixLift 517071
  have htrace : WordTrace (prefixWord ++ tailWord_517071) baseStart_517071 baseEnd_517071 := by
    simpa [prefixWord, tailWord_517071, baseEnd_517071] using wordTrace_append hprefix tailTrace_517071
  have hstable : (prefixWord ++ tailWord_517071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517071).length < 2 ^ (prefixWord ++ tailWord_517071).sum := by decide
  have hdescent : baseEnd_517071 < baseStart_517071 := by decide
  rcases family_descends (prefixWord ++ tailWord_517071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517073 : List Nat := [1, 2, 2, 1, 2, 1, 6, 2, 1, 4]
def baseStart_517073 : Nat := 118140960795 + 517073 * 2 ^ 59
def prefixEnd_517073 : Nat := 4983230072969 + 3 ^ 40 * 517073 * 2
def baseEnd_517073 : Nat := 177004654974907122139687

theorem tailTrace_517073 : CollatzResearch.WordTrace tailWord_517073 prefixEnd_517073 177004654974907122139687 := by
  unfold tailWord_517073
  simp only [CollatzResearch.WordTrace]
  refine ⟨18859201655740304882867873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12572801103826869921911915 18859201655740304882867873)
  ·
    refine ⟨14144401241805228662150905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18859201655740304882867873 14144401241805228662150905)
    ·
      refine ⟨10608300931353921496613179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14144401241805228662150905 10608300931353921496613179)
      ·
        refine ⟨15912451397030882244919769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10608300931353921496613179 15912451397030882244919769)
        ·
          refine ⟨11934338547773161683689827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15912451397030882244919769 11934338547773161683689827)
          ·
            refine ⟨17901507821659742525534741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11934338547773161683689827 17901507821659742525534741)
            ·
              refine ⟨839133179140300430884441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17901507821659742525534741 839133179140300430884441)
              ·
                refine ⟨629349884355225323163331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 839133179140300430884441 629349884355225323163331)
                ·
                  refine ⟨944024826532837984744997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 629349884355225323163331 944024826532837984744997)
                  ·
                    refine ⟨177004654974907122139687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 944024826532837984744997 177004654974907122139687)
                    ·
                      rfl

theorem cell22_517073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 2, 1, 4].length) (baseStart_517073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_517073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_517073 prefixEnd_517073 := by exact prefixLift 517073
  have htrace : WordTrace (prefixWord ++ tailWord_517073) baseStart_517073 baseEnd_517073 := by
    simpa [prefixWord, tailWord_517073, baseEnd_517073] using wordTrace_append hprefix tailTrace_517073
  have hstable : (prefixWord ++ tailWord_517073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517073).length < 2 ^ (prefixWord ++ tailWord_517073).sum := by decide
  have hdescent : baseEnd_517073 < baseStart_517073 := by decide
  rcases family_descends (prefixWord ++ tailWord_517073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517103 : List Nat := [1, 1, 2, 1, 4, 3, 2, 1, 4, 3]
def baseStart_517103 : Nat := 118140960795 + 517103 * 2 ^ 59
def prefixEnd_517103 : Nat := 4983230072969 + 3 ^ 40 * 517103 * 2
def baseEnd_517103 : Nat := 177014924587997043889595

theorem tailTrace_517103 : CollatzResearch.WordTrace tailWord_517103 prefixEnd_517103 177014924587997043889595 := by
  unfold tailWord_517103
  simp only [CollatzResearch.WordTrace]
  refine ⟨18860295845631620006459963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12573530563754413337639975 18860295845631620006459963)
  ·
    refine ⟨28290443768447430009689945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18860295845631620006459963 28290443768447430009689945)
    ·
      refine ⟨21217832826335572507267459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28290443768447430009689945 21217832826335572507267459)
      ·
        refine ⟨31826749239503358760901189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21217832826335572507267459 31826749239503358760901189)
        ·
          refine ⟨5967515482406879767668973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31826749239503358760901189 5967515482406879767668973)
          ·
            refine ⟨2237818305902579912875865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5967515482406879767668973 2237818305902579912875865)
            ·
              refine ⟨1678363729426934934656899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2237818305902579912875865 1678363729426934934656899)
              ·
                refine ⟨2517545594140402401985349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1678363729426934934656899 2517545594140402401985349)
                ·
                  refine ⟨472039798901325450372253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2517545594140402401985349 472039798901325450372253)
                  ·
                    refine ⟨177014924587997043889595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 472039798901325450372253 177014924587997043889595)
                    ·
                      rfl

theorem cell22_517103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 4, 3].length) (baseStart_517103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_517103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_517103 prefixEnd_517103 := by exact prefixLift 517103
  have htrace : WordTrace (prefixWord ++ tailWord_517103) baseStart_517103 baseEnd_517103 := by
    simpa [prefixWord, tailWord_517103, baseEnd_517103] using wordTrace_append hprefix tailTrace_517103
  have hstable : (prefixWord ++ tailWord_517103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517103).length < 2 ^ (prefixWord ++ tailWord_517103).sum := by decide
  have hdescent : baseEnd_517103 < baseStart_517103 := by decide
  rcases family_descends (prefixWord ++ tailWord_517103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517116 : List Nat := [2, 2, 2, 1, 2, 3, 1, 9]
def baseStart_517116 : Nat := 118140960795 + 517116 * 2 ^ 59
def prefixEnd_517116 : Nat := 4983230072969 + 3 ^ 40 * 517116 * 2
def baseEnd_517116 : Nat := 19668819417074371479395

theorem tailTrace_517116 : CollatzResearch.WordTrace tailWord_517116 prefixEnd_517116 19668819417074371479395 := by
  unfold tailWord_517116
  simp only [CollatzResearch.WordTrace]
  refine ⟨9430384997292261613341601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12573846663056348817788801 9430384997292261613341601)
  ·
    refine ⟨7072788747969196210006201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9430384997292261613341601 7072788747969196210006201)
    ·
      refine ⟨5304591560976897157504651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7072788747969196210006201 5304591560976897157504651)
      ·
        refine ⟨7956887341465345736256977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5304591560976897157504651 7956887341465345736256977)
        ·
          refine ⟨5967665506099009302192733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7956887341465345736256977 5967665506099009302192733)
          ·
            refine ⟨2237874564787128488322275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5967665506099009302192733 2237874564787128488322275)
            ·
              refine ⟨3356811847180692732483413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2237874564787128488322275 3356811847180692732483413)
              ·
                refine ⟨19668819417074371479395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3356811847180692732483413 19668819417074371479395)
                ·
                  rfl

theorem cell22_517116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 9].length) (baseStart_517116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_517116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_517116 prefixEnd_517116 := by exact prefixLift 517116
  have htrace : WordTrace (prefixWord ++ tailWord_517116) baseStart_517116 baseEnd_517116 := by
    simpa [prefixWord, tailWord_517116, baseEnd_517116] using wordTrace_append hprefix tailTrace_517116
  have hstable : (prefixWord ++ tailWord_517116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517116).length < 2 ^ (prefixWord ++ tailWord_517116).sum := by decide
  have hdescent : baseEnd_517116 < baseStart_517116 := by decide
  rcases family_descends (prefixWord ++ tailWord_517116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517178 : List Nat := [3, 1, 1, 1, 3, 1, 4, 3, 5]
def baseStart_517178 : Nat := 118140960795 + 517178 * 2 ^ 59
def prefixEnd_517178 : Nat := 4983230072969 + 3 ^ 40 * 517178 * 2
def baseEnd_517178 : Nat := 59013532873573949421455

theorem tailTrace_517178 : CollatzResearch.WordTrace tailWord_517178 prefixEnd_517178 59013532873573949421455 := by
  unfold tailWord_517178
  simp only [CollatzResearch.WordTrace]
  refine ⟨4715757830089976953860047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12575354213573271876960125 4715757830089976953860047)
  ·
    refine ⟨7073636745134965430790071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4715757830089976953860047 7073636745134965430790071)
    ·
      refine ⟨10610455117702448146185107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7073636745134965430790071 10610455117702448146185107)
      ·
        refine ⟨15915682676553672219277661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10610455117702448146185107 15915682676553672219277661)
        ·
          refine ⟨5968381003707627082229123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15915682676553672219277661 5968381003707627082229123)
          ·
            refine ⟨8952571505561440623343685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5968381003707627082229123 8952571505561440623343685)
            ·
              refine ⟨1678607157292770116876941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8952571505561440623343685 1678607157292770116876941)
              ·
                refine ⟨629477683984788793828853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1678607157292770116876941 629477683984788793828853)
                ·
                  refine ⟨59013532873573949421455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 629477683984788793828853 59013532873573949421455)
                  ·
                    rfl

theorem cell22_517178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 3, 5].length) (baseStart_517178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_517178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_517178 prefixEnd_517178 := by exact prefixLift 517178
  have htrace : WordTrace (prefixWord ++ tailWord_517178) baseStart_517178 baseEnd_517178 := by
    simpa [prefixWord, tailWord_517178, baseEnd_517178] using wordTrace_append hprefix tailTrace_517178
  have hstable : (prefixWord ++ tailWord_517178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517178).length < 2 ^ (prefixWord ++ tailWord_517178).sum := by decide
  have hdescent : baseEnd_517178 < baseStart_517178 := by decide
  rcases family_descends (prefixWord ++ tailWord_517178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517182 : List Nat := [4, 2, 1, 3, 1, 2, 1, 2, 3, 3]
def baseStart_517182 : Nat := 118140960795 + 517182 * 2 ^ 59
def prefixEnd_517182 : Nat := 4983230072969 + 3 ^ 40 * 517182 * 2
def baseEnd_517182 : Nat := 177041967902467171164353

theorem tailTrace_517182 : CollatzResearch.WordTrace tailWord_517182 prefixEnd_517182 177041967902467171164353 := by
  unfold tailWord_517182
  simp only [CollatzResearch.WordTrace]
  refine ⟨2357897151543177062323225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12575451474896944332390533 2357897151543177062323225)
  ·
    refine ⟨1768422863657382796742419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2357897151543177062323225 1768422863657382796742419)
    ·
      refine ⟨2652634295486074195113629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1768422863657382796742419 2652634295486074195113629)
      ·
        refine ⟨994737860807277823167611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2652634295486074195113629 994737860807277823167611)
        ·
          refine ⟨1492106791210916734751417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 994737860807277823167611 1492106791210916734751417)
          ·
            refine ⟨1119080093408187551063563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1492106791210916734751417 1119080093408187551063563)
            ·
              refine ⟨1678620140112281326595345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1119080093408187551063563 1678620140112281326595345)
              ·
                refine ⟨1258965105084210994946509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1678620140112281326595345 1258965105084210994946509)
                ·
                  refine ⟨472111914406579123104941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1258965105084210994946509 472111914406579123104941)
                  ·
                    refine ⟨177041967902467171164353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 472111914406579123104941 177041967902467171164353)
                    ·
                      rfl

theorem cell22_517182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 2, 3, 3].length) (baseStart_517182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_517182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_517182 prefixEnd_517182 := by exact prefixLift 517182
  have htrace : WordTrace (prefixWord ++ tailWord_517182) baseStart_517182 baseEnd_517182 := by
    simpa [prefixWord, tailWord_517182, baseEnd_517182] using wordTrace_append hprefix tailTrace_517182
  have hstable : (prefixWord ++ tailWord_517182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517182).length < 2 ^ (prefixWord ++ tailWord_517182).sum := by decide
  have hdescent : baseEnd_517182 < baseStart_517182 := by decide
  rcases family_descends (prefixWord ++ tailWord_517182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517223 : List Nat := [1, 1, 5, 1, 1, 3, 1, 3, 6]
def baseStart_517223 : Nat := 118140960795 + 517223 * 2 ^ 59
def prefixEnd_517223 : Nat := 4983230072969 + 3 ^ 40 * 517223 * 2
def baseEnd_517223 : Nat := 59018667680118910296409

theorem tailTrace_517223 : CollatzResearch.WordTrace tailWord_517223 prefixEnd_517223 59018667680118910296409 := by
  unfold tailWord_517223
  simp only [CollatzResearch.WordTrace]
  refine ⟨18864672605196880500828323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12576448403464587000552215 18864672605196880500828323)
  ·
    refine ⟨28297008907795320751242485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18864672605196880500828323 28297008907795320751242485)
    ·
      refine ⟨2652844585105811320428983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28297008907795320751242485 2652844585105811320428983)
      ·
        refine ⟨3979266877658716980643475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2652844585105811320428983 3979266877658716980643475)
        ·
          refine ⟨5968900316488075470965213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3979266877658716980643475 5968900316488075470965213)
          ·
            refine ⟨2238337618683028301611955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5968900316488075470965213 2238337618683028301611955)
            ·
              refine ⟨3357506428024542452417933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2238337618683028301611955 3357506428024542452417933)
              ·
                refine ⟨1259064910509203419656725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3357506428024542452417933 1259064910509203419656725)
                ·
                  refine ⟨59018667680118910296409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1259064910509203419656725 59018667680118910296409)
                  ·
                    rfl

theorem cell22_517223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 3, 6].length) (baseStart_517223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_517223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_517223 prefixEnd_517223 := by exact prefixLift 517223
  have htrace : WordTrace (prefixWord ++ tailWord_517223) baseStart_517223 baseEnd_517223 := by
    simpa [prefixWord, tailWord_517223, baseEnd_517223] using wordTrace_append hprefix tailTrace_517223
  have hstable : (prefixWord ++ tailWord_517223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517223).length < 2 ^ (prefixWord ++ tailWord_517223).sum := by decide
  have hdescent : baseEnd_517223 < baseStart_517223 := by decide
  rcases family_descends (prefixWord ++ tailWord_517223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517257 : List Nat := [1, 2, 1, 1, 4, 5, 1, 3, 4]
def baseStart_517257 : Nat := 118140960795 + 517257 * 2 ^ 59
def prefixEnd_517257 : Nat := 4983230072969 + 3 ^ 40 * 517257 * 2
def baseEnd_517257 : Nat := 59022547311730658513041

theorem tailTrace_517257 : CollatzResearch.WordTrace tailWord_517257 prefixEnd_517257 59022547311730658513041 := by
  unfold tailWord_517257
  simp only [CollatzResearch.WordTrace]
  refine ⟨18865912687073704307566025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12577275124715802871710683 18865912687073704307566025)
  ·
    refine ⟨14149434515305278230674519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18865912687073704307566025 14149434515305278230674519)
    ·
      refine ⟨21224151772957917346011779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14149434515305278230674519 21224151772957917346011779)
      ·
        refine ⟨31836227659436876019017669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21224151772957917346011779 31836227659436876019017669)
        ·
          refine ⟨5969292686144414253565813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31836227659436876019017669 5969292686144414253565813)
          ·
            refine ⟨559621189326038836271795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5969292686144414253565813 559621189326038836271795)
            ·
              refine ⟨839431783989058254407693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 559621189326038836271795 839431783989058254407693)
              ·
                refine ⟨314786918995896845402885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 839431783989058254407693 314786918995896845402885)
                ·
                  refine ⟨59022547311730658513041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 314786918995896845402885 59022547311730658513041)
                  ·
                    rfl

theorem cell22_517257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 3, 4].length) (baseStart_517257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_517257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_517257 prefixEnd_517257 := by exact prefixLift 517257
  have htrace : WordTrace (prefixWord ++ tailWord_517257) baseStart_517257 baseEnd_517257 := by
    simpa [prefixWord, tailWord_517257, baseEnd_517257] using wordTrace_append hprefix tailTrace_517257
  have hstable : (prefixWord ++ tailWord_517257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517257).length < 2 ^ (prefixWord ++ tailWord_517257).sum := by decide
  have hdescent : baseEnd_517257 < baseStart_517257 := by decide
  rcases family_descends (prefixWord ++ tailWord_517257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517274 : List Nat := [3, 1, 1, 5, 1, 2, 3, 2, 4]
def baseStart_517274 : Nat := 118140960795 + 517274 * 2 ^ 59
def prefixEnd_517274 : Nat := 4983230072969 + 3 ^ 40 * 517274 * 2
def baseEnd_517274 : Nat := 59024487127536532621357

theorem tailTrace_517274 : CollatzResearch.WordTrace tailWord_517274 prefixEnd_517274 59024487127536532621357 := by
  unfold tailWord_517274
  simp only [CollatzResearch.WordTrace]
  refine ⟨4716633182003029052733719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12577688485341410807289917 4716633182003029052733719)
  ·
    refine ⟨7074949773004543579100579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4716633182003029052733719 7074949773004543579100579)
    ·
      refine ⟨10612424659506815368650869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7074949773004543579100579 10612424659506815368650869)
      ·
        refine ⟨994914811828763940811019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10612424659506815368650869 994914811828763940811019)
        ·
          refine ⟨1492372217743145911216529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 994914811828763940811019 1492372217743145911216529)
          ·
            refine ⟨1119279163307359433412397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1492372217743145911216529 1119279163307359433412397)
            ·
              refine ⟨419729686240259787529649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1119279163307359433412397 419729686240259787529649)
              ·
                refine ⟨314797264680194840647237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 419729686240259787529649 314797264680194840647237)
                ·
                  refine ⟨59024487127536532621357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 314797264680194840647237 59024487127536532621357)
                  ·
                    rfl

theorem cell22_517274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 3, 2, 4].length) (baseStart_517274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_517274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_517274 prefixEnd_517274 := by exact prefixLift 517274
  have htrace : WordTrace (prefixWord ++ tailWord_517274) baseStart_517274 baseEnd_517274 := by
    simpa [prefixWord, tailWord_517274, baseEnd_517274] using wordTrace_append hprefix tailTrace_517274
  have hstable : (prefixWord ++ tailWord_517274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517274).length < 2 ^ (prefixWord ++ tailWord_517274).sum := by decide
  have hdescent : baseEnd_517274 < baseStart_517274 := by decide
  rcases family_descends (prefixWord ++ tailWord_517274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517317 : List Nat := [1, 3, 1, 1, 1, 1, 3, 7, 1, 3]
def baseStart_517317 : Nat := 118140960795 + 517317 * 2 ^ 59
def prefixEnd_517317 : Nat := 4983230072969 + 3 ^ 40 * 517317 * 2
def baseEnd_517317 : Nat := 177088181161371819038939

theorem tailTrace_517317 : CollatzResearch.WordTrace tailWord_517317 prefixEnd_517317 177088181161371819038939 := by
  unfold tailWord_517317
  simp only [CollatzResearch.WordTrace]
  refine ⟨18868101066856334554750205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12578734044570889703166803 18868101066856334554750205)
  ·
    refine ⟨7075537900071125458031327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18868101066856334554750205 7075537900071125458031327)
    ·
      refine ⟨10613306850106688187046991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7075537900071125458031327 10613306850106688187046991)
      ·
        refine ⟨15919960275160032280570487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10613306850106688187046991 15919960275160032280570487)
        ·
          refine ⟨23879940412740048420855731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15919960275160032280570487 23879940412740048420855731)
          ·
            refine ⟨35819910619110072631283597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23879940412740048420855731 35819910619110072631283597)
            ·
              refine ⟨13432466482166277236731349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35819910619110072631283597 13432466482166277236731349)
              ·
                refine ⟨314823433175772122735891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 13432466482166277236731349 314823433175772122735891)
                ·
                  refine ⟨472235149763658184103837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 314823433175772122735891 472235149763658184103837)
                  ·
                    refine ⟨177088181161371819038939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 472235149763658184103837 177088181161371819038939)
                    ·
                      rfl

theorem cell22_517317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 7, 1, 3].length) (baseStart_517317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_517317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_517317 prefixEnd_517317 := by exact prefixLift 517317
  have htrace : WordTrace (prefixWord ++ tailWord_517317) baseStart_517317 baseEnd_517317 := by
    simpa [prefixWord, tailWord_517317, baseEnd_517317] using wordTrace_append hprefix tailTrace_517317
  have hstable : (prefixWord ++ tailWord_517317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517317).length < 2 ^ (prefixWord ++ tailWord_517317).sum := by decide
  have hdescent : baseEnd_517317 < baseStart_517317 := by decide
  rcases family_descends (prefixWord ++ tailWord_517317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517325 : List Nat := [1, 6, 2, 2, 2, 1, 2, 2, 4]
def baseStart_517325 : Nat := 118140960795 + 517325 * 2 ^ 59
def prefixEnd_517325 : Nat := 4983230072969 + 3 ^ 40 * 517325 * 2
def baseEnd_517325 : Nat := 59030306574954154946305

theorem tailTrace_517325 : CollatzResearch.WordTrace tailWord_517325 prefixEnd_517325 59030306574954154946305 := by
  unfold tailWord_517325
  simp only [CollatzResearch.WordTrace]
  refine ⟨18868392850827351921041429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12578928567218234614027619 18868392850827351921041429)
  ·
    refine ⟨884455914882532121298817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18868392850827351921041429 884455914882532121298817)
    ·
      refine ⟨663341936161899090974113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 884455914882532121298817 663341936161899090974113)
      ·
        refine ⟨497506452121424318230585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 663341936161899090974113 497506452121424318230585)
        ·
          refine ⟨373129839091068238672939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 497506452121424318230585 373129839091068238672939)
          ·
            refine ⟨559694758636602358009409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373129839091068238672939 559694758636602358009409)
            ·
              refine ⟨419771068977451768507057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 559694758636602358009409 419771068977451768507057)
              ·
                refine ⟨314828301733088826380293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 419771068977451768507057 314828301733088826380293)
                ·
                  refine ⟨59030306574954154946305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 314828301733088826380293 59030306574954154946305)
                  ·
                    rfl

theorem cell22_517325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_517325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_517325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_517325 prefixEnd_517325 := by exact prefixLift 517325
  have htrace : WordTrace (prefixWord ++ tailWord_517325) baseStart_517325 baseEnd_517325 := by
    simpa [prefixWord, tailWord_517325, baseEnd_517325] using wordTrace_append hprefix tailTrace_517325
  have hstable : (prefixWord ++ tailWord_517325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517325).length < 2 ^ (prefixWord ++ tailWord_517325).sum := by decide
  have hdescent : baseEnd_517325 < baseStart_517325 := by decide
  rcases family_descends (prefixWord ++ tailWord_517325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517345 : List Nat := [1, 2, 3, 1, 3, 3, 1, 1, 2, 5]
def baseStart_517345 : Nat := 118140960795 + 517345 * 2 ^ 59
def prefixEnd_517345 : Nat := 4983230072969 + 3 ^ 40 * 517345 * 2
def baseEnd_517345 : Nat := 177097766133589079338853

theorem tailTrace_517345 : CollatzResearch.WordTrace tailWord_517345 prefixEnd_517345 177097766133589079338853 := by
  unfold tailWord_517345
  simp only [CollatzResearch.WordTrace]
  refine ⟨18869122310754895336769489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12579414873836596891179659 18869122310754895336769489)
  ·
    refine ⟨14151841733066171502577117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18869122310754895336769489 14151841733066171502577117)
    ·
      refine ⟨5306940649899814313466419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14151841733066171502577117 5306940649899814313466419)
      ·
        refine ⟨7960410974849721470199629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5306940649899814313466419 7960410974849721470199629)
        ·
          refine ⟨2985154115568645551324861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7960410974849721470199629 2985154115568645551324861)
          ·
            refine ⟨1119432793338242081746823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2985154115568645551324861 1119432793338242081746823)
            ·
              refine ⟨1679149190007363122620235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1119432793338242081746823 1679149190007363122620235)
              ·
                refine ⟨2518723785011044683930353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1679149190007363122620235 2518723785011044683930353)
                ·
                  refine ⟨1889042838758283512947765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2518723785011044683930353 1889042838758283512947765)
                  ·
                    refine ⟨177097766133589079338853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1889042838758283512947765 177097766133589079338853)
                    ·
                      rfl

theorem cell22_517345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 2, 5].length) (baseStart_517345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_517345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_517345 prefixEnd_517345 := by exact prefixLift 517345
  have htrace : WordTrace (prefixWord ++ tailWord_517345) baseStart_517345 baseEnd_517345 := by
    simpa [prefixWord, tailWord_517345, baseEnd_517345] using wordTrace_append hprefix tailTrace_517345
  have hstable : (prefixWord ++ tailWord_517345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517345).length < 2 ^ (prefixWord ++ tailWord_517345).sum := by decide
  have hdescent : baseEnd_517345 < baseStart_517345 := by decide
  rcases family_descends (prefixWord ++ tailWord_517345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517377 : List Nat := [1, 2, 4, 1, 1, 4, 1, 3, 1, 4]
def baseStart_517377 : Nat := 118140960795 + 517377 * 2 ^ 59
def prefixEnd_517377 : Nat := 4983230072969 + 3 ^ 40 * 517377 * 2
def baseEnd_517377 : Nat := 177108720387551662538755

theorem tailTrace_517377 : CollatzResearch.WordTrace tailWord_517377 prefixEnd_517377 177108720387551662538755 := by
  unfold tailWord_517377
  simp only [CollatzResearch.WordTrace]
  refine ⟨18870289446638964801934385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12580192964425976534622923 18870289446638964801934385)
  ·
    refine ⟨14152717084979223601450789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18870289446638964801934385 14152717084979223601450789)
    ·
      refine ⟨2653634453433604425272023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14152717084979223601450789 2653634453433604425272023)
      ·
        refine ⟨3980451680150406637908035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2653634453433604425272023 3980451680150406637908035)
        ·
          refine ⟨5970677520225609956862053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3980451680150406637908035 5970677520225609956862053)
          ·
            refine ⟨1119502035042301866911635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5970677520225609956862053 1119502035042301866911635)
            ·
              refine ⟨1679253052563452800367453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1119502035042301866911635 1679253052563452800367453)
              ·
                refine ⟨629719894711294800137795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1679253052563452800367453 629719894711294800137795)
                ·
                  refine ⟨944579842066942200206693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 629719894711294800137795 944579842066942200206693)
                  ·
                    refine ⟨177108720387551662538755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 944579842066942200206693 177108720387551662538755)
                    ·
                      rfl

theorem cell22_517377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_517377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_517377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_517377 prefixEnd_517377 := by exact prefixLift 517377
  have htrace : WordTrace (prefixWord ++ tailWord_517377) baseStart_517377 baseEnd_517377 := by
    simpa [prefixWord, tailWord_517377, baseEnd_517377] using wordTrace_append hprefix tailTrace_517377
  have hstable : (prefixWord ++ tailWord_517377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517377).length < 2 ^ (prefixWord ++ tailWord_517377).sum := by decide
  have hdescent : baseEnd_517377 < baseStart_517377 := by decide
  rcases family_descends (prefixWord ++ tailWord_517377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517403 : List Nat := [1, 1, 1, 1, 1, 1, 5, 11]
def baseStart_517403 : Nat := 118140960795 + 517403 * 2 ^ 59
def prefixEnd_517403 : Nat := 4983230072969 + 3 ^ 40 * 517403 * 2
def baseEnd_517403 : Nat := 19679735635432917932075

theorem tailTrace_517403 : CollatzResearch.WordTrace tailWord_517403 prefixEnd_517403 19679735635432917932075 := by
  unfold tailWord_517403
  simp only [CollatzResearch.WordTrace]
  refine ⟨18871237744544771242380863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12580825163029847494920575 18871237744544771242380863)
  ·
    refine ⟨28306856616817156863571295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18871237744544771242380863 28306856616817156863571295)
    ·
      refine ⟨42460284925225735295356943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28306856616817156863571295 42460284925225735295356943)
      ·
        refine ⟨63690427387838602943035415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42460284925225735295356943 63690427387838602943035415)
        ·
          refine ⟨95535641081757904414553123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63690427387838602943035415 95535641081757904414553123)
          ·
            refine ⟨143303461622636856621829685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95535641081757904414553123 143303461622636856621829685)
            ·
              refine ⟨13434699527122205308296533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 143303461622636856621829685 13434699527122205308296533)
              ·
                refine ⟨19679735635432917932075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 13434699527122205308296533 19679735635432917932075)
                ·
                  rfl

theorem cell22_517403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 11].length) (baseStart_517403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_517403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_517403 prefixEnd_517403 := by exact prefixLift 517403
  have htrace : WordTrace (prefixWord ++ tailWord_517403) baseStart_517403 baseEnd_517403 := by
    simpa [prefixWord, tailWord_517403, baseEnd_517403] using wordTrace_append hprefix tailTrace_517403
  have hstable : (prefixWord ++ tailWord_517403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517403).length < 2 ^ (prefixWord ++ tailWord_517403).sum := by decide
  have hdescent : baseEnd_517403 < baseStart_517403 := by decide
  rcases family_descends (prefixWord ++ tailWord_517403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517462 : List Nat := [5, 2, 3, 1, 2, 1, 1, 2, 1, 4]
def baseStart_517462 : Nat := 118140960795 + 517462 * 2 ^ 59
def prefixEnd_517462 : Nat := 4983230072969 + 3 ^ 40 * 517462 * 2
def baseEnd_517462 : Nat := 177137817624639774163495

theorem tailTrace_517462 : CollatzResearch.WordTrace tailWord_517462 prefixEnd_517462 177137817624639774163495 := by
  unfold tailWord_517462
  simp only [CollatzResearch.WordTrace]
  refine ⟨1179586853208189019923665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12582259767554016212519093 1179586853208189019923665)
  ·
    refine ⟨884690139906141764942749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1179586853208189019923665 884690139906141764942749)
    ·
      refine ⟨331758802464803161853531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 884690139906141764942749 331758802464803161853531)
      ·
        refine ⟨497638203697204742780297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331758802464803161853531 497638203697204742780297)
        ·
          refine ⟨373228652772903557085223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 497638203697204742780297 373228652772903557085223)
          ·
            refine ⟨559842979159355335627835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373228652772903557085223 559842979159355335627835)
            ·
              refine ⟨839764468739033003441753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 559842979159355335627835 839764468739033003441753)
              ·
                refine ⟨629823351554274752581315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 839764468739033003441753 629823351554274752581315)
                ·
                  refine ⟨944735027331412128871973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 629823351554274752581315 944735027331412128871973)
                  ·
                    refine ⟨177137817624639774163495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 944735027331412128871973 177137817624639774163495)
                    ·
                      rfl

theorem cell22_517462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_517462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_517462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_517462 prefixEnd_517462 := by exact prefixLift 517462
  have htrace : WordTrace (prefixWord ++ tailWord_517462) baseStart_517462 baseEnd_517462 := by
    simpa [prefixWord, tailWord_517462, baseEnd_517462] using wordTrace_append hprefix tailTrace_517462
  have hstable : (prefixWord ++ tailWord_517462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517462).length < 2 ^ (prefixWord ++ tailWord_517462).sum := by decide
  have hdescent : baseEnd_517462 < baseStart_517462 := by decide
  rcases family_descends (prefixWord ++ tailWord_517462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517512 : List Nat := [2, 1, 3, 3, 1, 2, 1, 2, 3, 4]
def baseStart_517512 : Nat := 118140960795 + 517512 * 2 ^ 59
def prefixEnd_517512 : Nat := 4983230072969 + 3 ^ 40 * 517512 * 2
def baseEnd_517512 : Nat := 177154933646456310413341

theorem tailTrace_517512 : CollatzResearch.WordTrace tailWord_517512 prefixEnd_517512 177154933646456310413341 := by
  unfold tailWord_517512
  simp only [CollatzResearch.WordTrace]
  refine ⟨9437606650574941429049395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12583475534099921905399193 9437606650574941429049395)
  ·
    refine ⟨14156409975862412143574093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9437606650574941429049395 14156409975862412143574093)
    ·
      refine ⟨5308653740948404553840285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14156409975862412143574093 5308653740948404553840285)
      ·
        refine ⟨1990745152855651707690107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5308653740948404553840285 1990745152855651707690107)
        ·
          refine ⟨2986117729283477561535161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1990745152855651707690107 2986117729283477561535161)
          ·
            refine ⟨2239588296962608171151371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2986117729283477561535161 2239588296962608171151371)
            ·
              refine ⟨3359382445443912256727057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2239588296962608171151371 3359382445443912256727057)
              ·
                refine ⟨2519536834082934192545293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3359382445443912256727057 2519536834082934192545293)
                ·
                  refine ⟨944826312781100322204485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2519536834082934192545293 944826312781100322204485)
                  ·
                    refine ⟨177154933646456310413341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 944826312781100322204485 177154933646456310413341)
                    ·
                      rfl

theorem cell22_517512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 3, 4].length) (baseStart_517512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_517512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_517512 prefixEnd_517512 := by exact prefixLift 517512
  have htrace : WordTrace (prefixWord ++ tailWord_517512) baseStart_517512 baseEnd_517512 := by
    simpa [prefixWord, tailWord_517512, baseEnd_517512] using wordTrace_append hprefix tailTrace_517512
  have hstable : (prefixWord ++ tailWord_517512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517512).length < 2 ^ (prefixWord ++ tailWord_517512).sum := by decide
  have hdescent : baseEnd_517512 < baseStart_517512 := by decide
  rcases family_descends (prefixWord ++ tailWord_517512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517576 : List Nat := [2, 1, 3, 1, 3, 1, 5, 1, 2, 3]
def baseStart_517576 : Nat := 118140960795 + 517576 * 2 ^ 59
def prefixEnd_517576 : Nat := 4983230072969 + 3 ^ 40 * 517576 * 2
def baseEnd_517576 : Nat := 177176842154381476813145

theorem tailTrace_517576 : CollatzResearch.WordTrace tailWord_517576 prefixEnd_517576 177176842154381476813145 := by
  unfold tailWord_517576
  simp only [CollatzResearch.WordTrace]
  refine ⟨9438773786459010894214291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12585031715278681192285721 9438773786459010894214291)
  ·
    refine ⟨14158160679688516341321437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9438773786459010894214291 14158160679688516341321437)
    ·
      refine ⟨5309310254883193627995539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14158160679688516341321437 5309310254883193627995539)
      ·
        refine ⟨7963965382324790441993309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5309310254883193627995539 7963965382324790441993309)
        ·
          refine ⟨2986487018371796415747491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7963965382324790441993309 2986487018371796415747491)
          ·
            refine ⟨4479730527557694623621237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2986487018371796415747491 4479730527557694623621237)
            ·
              refine ⟨419974736958533870964491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4479730527557694623621237 419974736958533870964491)
              ·
                refine ⟨629962105437800806446737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 419974736958533870964491 629962105437800806446737)
                ·
                  refine ⟨472471579078350604835053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 629962105437800806446737 472471579078350604835053)
                  ·
                    refine ⟨177176842154381476813145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 472471579078350604835053 177176842154381476813145)
                    ·
                      rfl

theorem cell22_517576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 5, 1, 2, 3].length) (baseStart_517576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_517576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_517576 prefixEnd_517576 := by exact prefixLift 517576
  have htrace : WordTrace (prefixWord ++ tailWord_517576) baseStart_517576 baseEnd_517576 := by
    simpa [prefixWord, tailWord_517576, baseEnd_517576] using wordTrace_append hprefix tailTrace_517576
  have hstable : (prefixWord ++ tailWord_517576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517576).length < 2 ^ (prefixWord ++ tailWord_517576).sum := by decide
  have hdescent : baseEnd_517576 < baseStart_517576 := by decide
  rcases family_descends (prefixWord ++ tailWord_517576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517617 : List Nat := [1, 2, 2, 2, 3, 2, 2, 1, 7]
def baseStart_517617 : Nat := 118140960795 + 517617 * 2 ^ 59
def prefixEnd_517617 : Nat := 4983230072969 + 3 ^ 40 * 517617 * 2
def baseEnd_517617 : Nat := 59063625764090345512673

theorem tailTrace_517617 : CollatzResearch.WordTrace tailWord_517617 prefixEnd_517617 59063625764090345512673 := by
  unfold tailWord_517617
  simp only [CollatzResearch.WordTrace]
  refine ⟨18879042965769485790671105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12586028643846323860447403 18879042965769485790671105)
  ·
    refine ⟨14159282224327114343003329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18879042965769485790671105 14159282224327114343003329)
    ·
      refine ⟨10619461668245335757252497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14159282224327114343003329 10619461668245335757252497)
      ·
        refine ⟨7964596251184001817939373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10619461668245335757252497 7964596251184001817939373)
        ·
          refine ⟨2986723594194000681727265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7964596251184001817939373 2986723594194000681727265)
          ·
            refine ⟨2240042695645500511295449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2986723594194000681727265 2240042695645500511295449)
            ·
              refine ⟨1680032021734125383471587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2240042695645500511295449 1680032021734125383471587)
              ·
                refine ⟨2520048032601188075207381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1680032021734125383471587 2520048032601188075207381)
                ·
                  refine ⟨59063625764090345512673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2520048032601188075207381 59063625764090345512673)
                  ·
                    rfl

theorem cell22_517617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 7].length) (baseStart_517617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_517617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_517617 prefixEnd_517617 := by exact prefixLift 517617
  have htrace : WordTrace (prefixWord ++ tailWord_517617) baseStart_517617 baseEnd_517617 := by
    simpa [prefixWord, tailWord_517617, baseEnd_517617] using wordTrace_append hprefix tailTrace_517617
  have hstable : (prefixWord ++ tailWord_517617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517617).length < 2 ^ (prefixWord ++ tailWord_517617).sum := by decide
  have hdescent : baseEnd_517617 < baseStart_517617 := by decide
  rcases family_descends (prefixWord ++ tailWord_517617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517672 : List Nat := [2, 1, 5, 2, 2, 2, 2, 2, 1, 3]
def baseStart_517672 : Nat := 118140960795 + 517672 * 2 ^ 59
def prefixEnd_517672 : Nat := 4983230072969 + 3 ^ 40 * 517672 * 2
def baseEnd_517672 : Nat := 177209704916269226412851

theorem tailTrace_517672 : CollatzResearch.WordTrace tailWord_517672 prefixEnd_517672 177209704916269226412851 := by
  unfold tailWord_517672
  simp only [CollatzResearch.WordTrace]
  refine ⟨9440524490285115091961635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12587365987046820122615513 9440524490285115091961635)
  ·
    refine ⟨14160786735427672637942453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9440524490285115091961635 14160786735427672637942453)
    ·
      refine ⟨1327573756446344309807105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14160786735427672637942453 1327573756446344309807105)
      ·
        refine ⟨995680317334758232355329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1327573756446344309807105 995680317334758232355329)
        ·
          refine ⟨746760238001068674266497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 995680317334758232355329 746760238001068674266497)
          ·
            refine ⟨560070178500801505699873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 746760238001068674266497 560070178500801505699873)
            ·
              refine ⟨420052633875601129274905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 560070178500801505699873 420052633875601129274905)
              ·
                refine ⟨315039475406700846956179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 420052633875601129274905 315039475406700846956179)
                ·
                  refine ⟨472559213110051270434269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 315039475406700846956179 472559213110051270434269)
                  ·
                    refine ⟨177209704916269226412851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 472559213110051270434269 177209704916269226412851)
                    ·
                      rfl

theorem cell22_517672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_517672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_517672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_517672 prefixEnd_517672 := by exact prefixLift 517672
  have htrace : WordTrace (prefixWord ++ tailWord_517672) baseStart_517672 baseEnd_517672 := by
    simpa [prefixWord, tailWord_517672, baseEnd_517672] using wordTrace_append hprefix tailTrace_517672
  have hstable : (prefixWord ++ tailWord_517672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517672).length < 2 ^ (prefixWord ++ tailWord_517672).sum := by decide
  have hdescent : baseEnd_517672 < baseStart_517672 := by decide
  rcases family_descends (prefixWord ++ tailWord_517672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517722 : List Nat := [3, 1, 1, 2, 1, 1, 1, 2, 1, 9]
def baseStart_517722 : Nat := 118140960795 + 517722 * 2 ^ 59
def prefixEnd_517722 : Nat := 4983230072969 + 3 ^ 40 * 517722 * 2
def baseEnd_517722 : Nat := 177226820938085762662697

theorem tailTrace_517722 : CollatzResearch.WordTrace tailWord_517722 prefixEnd_517722 177226820938085762662697 := by
  unfold tailWord_517722
  simp only [CollatzResearch.WordTrace]
  refine ⟨4720718157597272180810855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12588581753592725815495613 4720718157597272180810855)
  ·
    refine ⟨7081077236395908271216283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4720718157597272180810855 7081077236395908271216283)
    ·
      refine ⟨10621615854593862406824425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7081077236395908271216283 10621615854593862406824425)
      ·
        refine ⟨7966211890945396805118319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10621615854593862406824425 7966211890945396805118319)
        ·
          refine ⟨11949317836418095207677479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7966211890945396805118319 11949317836418095207677479)
          ·
            refine ⟨17923976754627142811516219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11949317836418095207677479 17923976754627142811516219)
            ·
              refine ⟨26885965131940714217274329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17923976754627142811516219 26885965131940714217274329)
              ·
                refine ⟨20164473848955535662955747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26885965131940714217274329 20164473848955535662955747)
                ·
                  refine ⟨30246710773433303494433621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20164473848955535662955747 30246710773433303494433621)
                  ·
                    refine ⟨177226820938085762662697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 30246710773433303494433621 177226820938085762662697)
                    ·
                      rfl

theorem cell22_517722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 1, 9].length) (baseStart_517722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_517722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_517722 prefixEnd_517722 := by exact prefixLift 517722
  have htrace : WordTrace (prefixWord ++ tailWord_517722) baseStart_517722 baseEnd_517722 := by
    simpa [prefixWord, tailWord_517722, baseEnd_517722] using wordTrace_append hprefix tailTrace_517722
  have hstable : (prefixWord ++ tailWord_517722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517722).length < 2 ^ (prefixWord ++ tailWord_517722).sum := by decide
  have hdescent : baseEnd_517722 < baseStart_517722 := by decide
  rcases family_descends (prefixWord ++ tailWord_517722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517724 : List Nat := [2, 2, 4, 1, 2, 2, 9]
def baseStart_517724 : Nat := 118140960795 + 517724 * 2 ^ 59
def prefixEnd_517724 : Nat := 4983230072969 + 3 ^ 40 * 517724 * 2
def baseEnd_517724 : Nat := 6563981688109571263433

theorem tailTrace_517724 : CollatzResearch.WordTrace tailWord_517724 prefixEnd_517724 6563981688109571263433 := by
  unfold tailWord_517724
  simp only [CollatzResearch.WordTrace]
  refine ⟨9441472788190921532408113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12588630384254562043210817 9441472788190921532408113)
  ·
    refine ⟨7081104591143191149306085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9441472788190921532408113 7081104591143191149306085)
    ·
      refine ⟨1327707110839348340494891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7081104591143191149306085 1327707110839348340494891)
      ·
        refine ⟨1991560666259022510742337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1327707110839348340494891 1991560666259022510742337)
        ·
          refine ⟨1493670499694266883056753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1991560666259022510742337 1493670499694266883056753)
          ·
            refine ⟨1120252874770700162292565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1493670499694266883056753 1120252874770700162292565)
            ·
              refine ⟨6563981688109571263433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1120252874770700162292565 6563981688109571263433)
              ·
                rfl

theorem cell22_517724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 9].length) (baseStart_517724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_517724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_517724 prefixEnd_517724 := by exact prefixLift 517724
  have htrace : WordTrace (prefixWord ++ tailWord_517724) baseStart_517724 baseEnd_517724 := by
    simpa [prefixWord, tailWord_517724, baseEnd_517724] using wordTrace_append hprefix tailTrace_517724
  have hstable : (prefixWord ++ tailWord_517724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517724).length < 2 ^ (prefixWord ++ tailWord_517724).sum := by decide
  have hdescent : baseEnd_517724 < baseStart_517724 := by decide
  rcases family_descends (prefixWord ++ tailWord_517724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517737 : List Nat := [1, 2, 1, 1, 1, 4, 2, 1, 1, 8]
def baseStart_517737 : Nat := 118140960795 + 517737 * 2 ^ 59
def prefixEnd_517737 : Nat := 4983230072969 + 3 ^ 40 * 517737 * 2
def baseEnd_517737 : Nat := 177231955744630723537651

theorem tailTrace_517737 : CollatzResearch.WordTrace tailWord_517737 prefixEnd_517737 177231955744630723537651 := by
  unfold tailWord_517737
  simp only [CollatzResearch.WordTrace]
  refine ⟨18883419725334746285039465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12588946483556497523359643 18883419725334746285039465)
  ·
    refine ⟨14162564794001059713779599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18883419725334746285039465 14162564794001059713779599)
    ·
      refine ⟨21243847191001589570669399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14162564794001059713779599 21243847191001589570669399)
      ·
        refine ⟨31865770786502384356004099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21243847191001589570669399 31865770786502384356004099)
        ·
          refine ⟨47798656179753576534006149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31865770786502384356004099 47798656179753576534006149)
          ·
            refine ⟨8962248033703795600126153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47798656179753576534006149 8962248033703795600126153)
            ·
              refine ⟨6721686025277846700094615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8962248033703795600126153 6721686025277846700094615)
              ·
                refine ⟨10082529037916770050141923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6721686025277846700094615 10082529037916770050141923)
                ·
                  refine ⟨15123793556875155075212885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10082529037916770050141923 15123793556875155075212885)
                  ·
                    refine ⟨177231955744630723537651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 15123793556875155075212885 177231955744630723537651)
                    ·
                      rfl

theorem cell22_517737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 8].length) (baseStart_517737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_517737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_517737 prefixEnd_517737 := by exact prefixLift 517737
  have htrace : WordTrace (prefixWord ++ tailWord_517737) baseStart_517737 baseEnd_517737 := by
    simpa [prefixWord, tailWord_517737, baseEnd_517737] using wordTrace_append hprefix tailTrace_517737
  have hstable : (prefixWord ++ tailWord_517737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517737).length < 2 ^ (prefixWord ++ tailWord_517737).sum := by decide
  have hdescent : baseEnd_517737 < baseStart_517737 := by decide
  rcases family_descends (prefixWord ++ tailWord_517737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517752 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 11]
def baseStart_517752 : Nat := 118140960795 + 517752 * 2 ^ 59
def prefixEnd_517752 : Nat := 4983230072969 + 3 ^ 40 * 517752 * 2
def baseEnd_517752 : Nat := 59079030183725228137535

theorem tailTrace_517752 : CollatzResearch.WordTrace tailWord_517752 prefixEnd_517752 59079030183725228137535 := by
  unfold tailWord_517752
  simp only [CollatzResearch.WordTrace]
  refine ⟨9441983410140201923417755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12589311213520269231223673 9441983410140201923417755)
  ·
    refine ⟨14162975115210302885126633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9441983410140201923417755 14162975115210302885126633)
    ·
      refine ⟨10622231336407727163844975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14162975115210302885126633 10622231336407727163844975)
      ·
        refine ⟨15933347004611590745767463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10622231336407727163844975 15933347004611590745767463)
        ·
          refine ⟨23900020506917386118651195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15933347004611590745767463 23900020506917386118651195)
          ·
            refine ⟨35850030760376079177976793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23900020506917386118651195 35850030760376079177976793)
            ·
              refine ⟨26887523070282059383482595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35850030760376079177976793 26887523070282059383482595)
              ·
                refine ⟨40331284605423089075223893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26887523070282059383482595 40331284605423089075223893)
                ·
                  refine ⟨59079030183725228137535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 40331284605423089075223893 59079030183725228137535)
                  ·
                    rfl

theorem cell22_517752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 11].length) (baseStart_517752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_517752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_517752 prefixEnd_517752 := by exact prefixLift 517752
  have htrace : WordTrace (prefixWord ++ tailWord_517752) baseStart_517752 baseEnd_517752 := by
    simpa [prefixWord, tailWord_517752, baseEnd_517752] using wordTrace_append hprefix tailTrace_517752
  have hstable : (prefixWord ++ tailWord_517752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517752).length < 2 ^ (prefixWord ++ tailWord_517752).sum := by decide
  have hdescent : baseEnd_517752 < baseStart_517752 := by decide
  rcases family_descends (prefixWord ++ tailWord_517752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517790 : List Nat := [4, 3, 1, 1, 1, 4, 1, 1, 3, 3]
def baseStart_517790 : Nat := 118140960795 + 517790 * 2 ^ 59
def prefixEnd_517790 : Nat := 4983230072969 + 3 ^ 40 * 517790 * 2
def baseEnd_517790 : Nat := 177250098727756251962489

theorem tailTrace_517790 : CollatzResearch.WordTrace tailWord_517790 prefixEnd_517790 177250098727756251962489 := by
  unfold tailWord_517790
  simp only [CollatzResearch.WordTrace]
  refine ⟨2360669099267842042089853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12590235196095157557812549 2360669099267842042089853)
  ·
    refine ⟨885250912225440765783695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2360669099267842042089853 885250912225440765783695)
    ·
      refine ⟨1327876368338161148675543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 885250912225440765783695 1327876368338161148675543)
      ·
        refine ⟨1991814552507241723013315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1327876368338161148675543 1991814552507241723013315)
        ·
          refine ⟨2987721828760862584519973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1991814552507241723013315 2987721828760862584519973)
          ·
            refine ⟨560197842892661734597495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2987721828760862584519973 560197842892661734597495)
            ·
              refine ⟨840296764338992601896243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 560197842892661734597495 840296764338992601896243)
              ·
                refine ⟨1260445146508488902844365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 840296764338992601896243 1260445146508488902844365)
                ·
                  refine ⟨472666929940683338566637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1260445146508488902844365 472666929940683338566637)
                  ·
                    refine ⟨177250098727756251962489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 472666929940683338566637 177250098727756251962489)
                    ·
                      rfl

theorem cell22_517790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_517790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_517790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_517790 prefixEnd_517790 := by exact prefixLift 517790
  have htrace : WordTrace (prefixWord ++ tailWord_517790) baseStart_517790 baseEnd_517790 := by
    simpa [prefixWord, tailWord_517790, baseEnd_517790] using wordTrace_append hprefix tailTrace_517790
  have hstable : (prefixWord ++ tailWord_517790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517790).length < 2 ^ (prefixWord ++ tailWord_517790).sum := by decide
  have hdescent : baseEnd_517790 < baseStart_517790 := by decide
  rcases family_descends (prefixWord ++ tailWord_517790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517829 : List Nat := [1, 3, 1, 1, 1, 1, 2, 6, 1, 5]
def baseStart_517829 : Nat := 118140960795 + 517829 * 2 ^ 59
def prefixEnd_517829 : Nat := 4983230072969 + 3 ^ 40 * 517829 * 2
def baseEnd_517829 : Nat := 177263449224773150237369

theorem tailTrace_517829 : CollatzResearch.WordTrace tailWord_517829 prefixEnd_517829 177263449224773150237369 := by
  unfold tailWord_517829
  simp only [CollatzResearch.WordTrace]
  refine ⟨18886775241001445997388541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12591183494000963998259027 18886775241001445997388541)
  ·
    refine ⟨7082540715375542249020703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18886775241001445997388541 7082540715375542249020703)
    ·
      refine ⟨10623811073063313373531055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7082540715375542249020703 10623811073063313373531055)
      ·
        refine ⟨15935716609594970060296583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10623811073063313373531055 15935716609594970060296583)
        ·
          refine ⟨23903574914392455090444875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15935716609594970060296583 23903574914392455090444875)
          ·
            refine ⟨35855362371588682635667313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23903574914392455090444875 35855362371588682635667313)
            ·
              refine ⟨26891521778691511976750485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35855362371588682635667313 26891521778691511976750485)
              ·
                refine ⟨1260540083376164623910179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26891521778691511976750485 1260540083376164623910179)
                ·
                  refine ⟨1890810125064246935865269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1260540083376164623910179 1890810125064246935865269)
                  ·
                    refine ⟨177263449224773150237369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1890810125064246935865269 177263449224773150237369)
                    ·
                      rfl

theorem cell22_517829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 6, 1, 5].length) (baseStart_517829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_517829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_517829 prefixEnd_517829 := by exact prefixLift 517829
  have htrace : WordTrace (prefixWord ++ tailWord_517829) baseStart_517829 baseEnd_517829 := by
    simpa [prefixWord, tailWord_517829, baseEnd_517829] using wordTrace_append hprefix tailTrace_517829
  have hstable : (prefixWord ++ tailWord_517829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517829).length < 2 ^ (prefixWord ++ tailWord_517829).sum := by decide
  have hdescent : baseEnd_517829 < baseStart_517829 := by decide
  rcases family_descends (prefixWord ++ tailWord_517829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517831 : List Nat := [1, 1, 4, 1, 1, 1, 4, 5, 4]
def baseStart_517831 : Nat := 118140960795 + 517831 * 2 ^ 59
def prefixEnd_517831 : Nat := 4983230072969 + 3 ^ 40 * 517831 * 2
def baseEnd_517831 : Nat := 59088044621881937229121

theorem tailTrace_517831 : CollatzResearch.WordTrace tailWord_517831 prefixEnd_517831 59088044621881937229121 := by
  unfold tailWord_517831
  simp only [CollatzResearch.WordTrace]
  refine ⟨18886848186994200338961347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12591232124662800225974231 18886848186994200338961347)
  ·
    refine ⟨28330272280491300508442021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18886848186994200338961347 28330272280491300508442021)
    ·
      refine ⟨5311926052592118845332879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28330272280491300508442021 5311926052592118845332879)
      ·
        refine ⟨7967889078888178267999319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5311926052592118845332879 7967889078888178267999319)
        ·
          refine ⟨11951833618332267401998979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7967889078888178267999319 11951833618332267401998979)
          ·
            refine ⟨17927750427498401102998469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11951833618332267401998979 17927750427498401102998469)
            ·
              refine ⟨3361453205155950206812213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17927750427498401102998469 3361453205155950206812213)
              ·
                refine ⟨315136237983370331888645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3361453205155950206812213 315136237983370331888645)
                ·
                  refine ⟨59088044621881937229121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 315136237983370331888645 59088044621881937229121)
                  ·
                    rfl

theorem cell22_517831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 5, 4].length) (baseStart_517831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_517831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_517831 prefixEnd_517831 := by exact prefixLift 517831
  have htrace : WordTrace (prefixWord ++ tailWord_517831) baseStart_517831 baseEnd_517831 := by
    simpa [prefixWord, tailWord_517831, baseEnd_517831] using wordTrace_append hprefix tailTrace_517831
  have hstable : (prefixWord ++ tailWord_517831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517831).length < 2 ^ (prefixWord ++ tailWord_517831).sum := by decide
  have hdescent : baseEnd_517831 < baseStart_517831 := by decide
  rcases family_descends (prefixWord ++ tailWord_517831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517878 : List Nat := [5, 1, 1, 1, 1, 3, 3, 1, 2, 4]
def baseStart_517878 : Nat := 118140960795 + 517878 * 2 ^ 59
def prefixEnd_517878 : Nat := 4983230072969 + 3 ^ 40 * 517878 * 2
def baseEnd_517878 : Nat := 177280222926153355762219

theorem tailTrace_517878 : CollatzResearch.WordTrace tailWord_517878 prefixEnd_517878 177280222926153355762219 := by
  unfold tailWord_517878
  simp only [CollatzResearch.WordTrace]
  refine ⟨1180535151113995460370143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12592374945215951577281525 1180535151113995460370143)
  ·
    refine ⟨1770802726670993190555215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1180535151113995460370143 1770802726670993190555215)
    ·
      refine ⟨2656204090006489785832823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1770802726670993190555215 2656204090006489785832823)
      ·
        refine ⟨3984306135009734678749235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2656204090006489785832823 3984306135009734678749235)
        ·
          refine ⟨5976459202514602018123853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3984306135009734678749235 5976459202514602018123853)
          ·
            refine ⟨2241172200942975756796445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5976459202514602018123853 2241172200942975756796445)
            ·
              refine ⟨840439575353615908798667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2241172200942975756796445 840439575353615908798667)
              ·
                refine ⟨1260659363030423863198001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 840439575353615908798667 1260659363030423863198001)
                ·
                  refine ⟨945494522272817897398501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1260659363030423863198001 945494522272817897398501)
                  ·
                    refine ⟨177280222926153355762219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 945494522272817897398501 177280222926153355762219)
                    ·
                      rfl

theorem cell22_517878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_517878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_517878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_517878 prefixEnd_517878 := by exact prefixLift 517878
  have htrace : WordTrace (prefixWord ++ tailWord_517878) baseStart_517878 baseEnd_517878 := by
    simpa [prefixWord, tailWord_517878, baseEnd_517878] using wordTrace_append hprefix tailTrace_517878
  have hstable : (prefixWord ++ tailWord_517878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517878).length < 2 ^ (prefixWord ++ tailWord_517878).sum := by decide
  have hdescent : baseEnd_517878 < baseStart_517878 := by decide
  rcases family_descends (prefixWord ++ tailWord_517878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517998 : List Nat := [4, 1, 2, 3, 1, 1, 1, 1, 3, 5]
def baseStart_517998 : Nat := 118140960795 + 517998 * 2 ^ 59
def prefixEnd_517998 : Nat := 4983230072969 + 3 ^ 40 * 517998 * 2
def baseEnd_517998 : Nat := 177321301378513042761851

theorem tailTrace_517998 : CollatzResearch.WordTrace tailWord_517998 prefixEnd_517998 177321301378513042761851 := by
  unfold tailWord_517998
  simp only [CollatzResearch.WordTrace]
  refine ⟨2361617397173648482536331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12595292784926125240193765 2361617397173648482536331)
  ·
    refine ⟨3542426095760472723804497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2361617397173648482536331 3542426095760472723804497)
    ·
      refine ⟨2656819571820354542853373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3542426095760472723804497 2656819571820354542853373)
      ·
        refine ⟨996307339432632953570015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2656819571820354542853373 996307339432632953570015)
        ·
          refine ⟨1494461009148949430355023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 996307339432632953570015 1494461009148949430355023)
          ·
            refine ⟨2241691513723424145532535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1494461009148949430355023 2241691513723424145532535)
            ·
              refine ⟨3362537270585136218298803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2241691513723424145532535 3362537270585136218298803)
              ·
                refine ⟨5043805905877704327448205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3362537270585136218298803 5043805905877704327448205)
                ·
                  refine ⟨1891427214704139122793077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5043805905877704327448205 1891427214704139122793077)
                  ·
                    refine ⟨177321301378513042761851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1891427214704139122793077 177321301378513042761851)
                    ·
                      rfl

theorem cell22_517998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_517998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_517998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_517998 prefixEnd_517998 := by exact prefixLift 517998
  have htrace : WordTrace (prefixWord ++ tailWord_517998) baseStart_517998 baseEnd_517998 := by
    simpa [prefixWord, tailWord_517998, baseEnd_517998] using wordTrace_append hprefix tailTrace_517998
  have hstable : (prefixWord ++ tailWord_517998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517998).length < 2 ^ (prefixWord ++ tailWord_517998).sum := by decide
  have hdescent : baseEnd_517998 < baseStart_517998 := by decide
  rcases family_descends (prefixWord ++ tailWord_517998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518017 : List Nat := [1, 2, 4, 4, 1, 1, 1, 4, 4]
def baseStart_518017 : Nat := 118140960795 + 518017 * 2 ^ 59
def prefixEnd_518017 : Nat := 4983230072969 + 3 ^ 40 * 518017 * 2
def baseEnd_518017 : Nat := 59109268488934442178931

theorem tailTrace_518017 : CollatzResearch.WordTrace tailWord_518017 prefixEnd_518017 59109268488934442178931 := by
  unfold tailWord_518017
  simp only [CollatzResearch.WordTrace]
  refine ⟨18893632164320354105232305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12595754776213569403488203 18893632164320354105232305)
  ·
    refine ⟨14170224123240265578924229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18893632164320354105232305 14170224123240265578924229)
    ·
      refine ⟨2656917023107549796048293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14170224123240265578924229 2656917023107549796048293)
      ·
        refine ⟨498171941832665586759055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2656917023107549796048293 498171941832665586759055)
        ·
          refine ⟨747257912748998380138583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 498171941832665586759055 747257912748998380138583)
          ·
            refine ⟨1120886869123497570207875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 747257912748998380138583 1120886869123497570207875)
            ·
              refine ⟨1681330303685246355311813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1120886869123497570207875 1681330303685246355311813)
              ·
                refine ⟨315249431940983691620965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1681330303685246355311813 315249431940983691620965)
                ·
                  refine ⟨59109268488934442178931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 315249431940983691620965 59109268488934442178931)
                  ·
                    rfl

theorem cell22_518017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 4, 4].length) (baseStart_518017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_518017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_518017 prefixEnd_518017 := by exact prefixLift 518017
  have htrace : WordTrace (prefixWord ++ tailWord_518017) baseStart_518017 baseEnd_518017 := by
    simpa [prefixWord, tailWord_518017, baseEnd_518017] using wordTrace_append hprefix tailTrace_518017
  have hstable : (prefixWord ++ tailWord_518017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518017).length < 2 ^ (prefixWord ++ tailWord_518017).sum := by decide
  have hdescent : baseEnd_518017 < baseStart_518017 := by decide
  rcases family_descends (prefixWord ++ tailWord_518017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518047 : List Nat := [1, 1, 2, 5, 4, 1, 1, 1, 2, 4]
def baseStart_518047 : Nat := 118140960795 + 518047 * 2 ^ 59
def prefixEnd_518047 : Nat := 4983230072969 + 3 ^ 40 * 518047 * 2
def baseEnd_518047 : Nat := 177338075079893248286701

theorem tailTrace_518047 : CollatzResearch.WordTrace tailWord_518047 prefixEnd_518047 177338075079893248286701 := by
  unfold tailWord_518047
  simp only [CollatzResearch.WordTrace]
  refine ⟨18894726354211669228824395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12596484236141112819216263 18894726354211669228824395)
  ·
    refine ⟨28342089531317503843236593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18894726354211669228824395 28342089531317503843236593)
    ·
      refine ⟨21256567148488127882427445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28342089531317503843236593 21256567148488127882427445)
      ·
        refine ⟨1992803170170761988977573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21256567148488127882427445 1992803170170761988977573)
        ·
          refine ⟨373650594407017872933295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1992803170170761988977573 373650594407017872933295)
          ·
            refine ⟨560475891610526809399943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373650594407017872933295 560475891610526809399943)
            ·
              refine ⟨840713837415790214099915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 560475891610526809399943 840713837415790214099915)
              ·
                refine ⟨1261070756123685321149873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 840713837415790214099915 1261070756123685321149873)
                ·
                  refine ⟨945803067092763990862405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1261070756123685321149873 945803067092763990862405)
                  ·
                    refine ⟨177338075079893248286701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 945803067092763990862405 177338075079893248286701)
                    ·
                      rfl

theorem cell22_518047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 1, 2, 4].length) (baseStart_518047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_518047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_518047 prefixEnd_518047 := by exact prefixLift 518047
  have htrace : WordTrace (prefixWord ++ tailWord_518047) baseStart_518047 baseEnd_518047 := by
    simpa [prefixWord, tailWord_518047, baseEnd_518047] using wordTrace_append hprefix tailTrace_518047
  have hstable : (prefixWord ++ tailWord_518047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518047).length < 2 ^ (prefixWord ++ tailWord_518047).sum := by decide
  have hdescent : baseEnd_518047 < baseStart_518047 := by decide
  rcases family_descends (prefixWord ++ tailWord_518047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518062 : List Nat := [4, 1, 5, 1, 1, 1, 9]
def baseStart_518062 : Nat := 118140960795 + 518062 * 2 ^ 59
def prefixEnd_518062 : Nat := 4983230072969 + 3 ^ 40 * 518062 * 2
def baseEnd_518062 : Nat := 6568267032831044783765

theorem tailTrace_518062 : CollatzResearch.WordTrace tailWord_518062 prefixEnd_518062 6568267032831044783765 := by
  unfold tailWord_518062
  simp only [CollatzResearch.WordTrace]
  refine ⟨2361909181144665848827555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12596848966104884527080293 2361909181144665848827555)
  ·
    refine ⟨3542863771716998773241333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2361909181144665848827555 3542863771716998773241333)
    ·
      refine ⟨332143478598468634991375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3542863771716998773241333 332143478598468634991375)
      ·
        refine ⟨498215217897702952487063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332143478598468634991375 498215217897702952487063)
        ·
          refine ⟨747322826846554428730595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 498215217897702952487063 747322826846554428730595)
          ·
            refine ⟨1120984240269831643095893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 747322826846554428730595 1120984240269831643095893)
            ·
              refine ⟨6568267032831044783765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1120984240269831643095893 6568267032831044783765)
              ·
                rfl

theorem cell22_518062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 9].length) (baseStart_518062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_518062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_518062 prefixEnd_518062 := by exact prefixLift 518062
  have htrace : WordTrace (prefixWord ++ tailWord_518062) baseStart_518062 baseEnd_518062 := by
    simpa [prefixWord, tailWord_518062, baseEnd_518062] using wordTrace_append hprefix tailTrace_518062
  have hstable : (prefixWord ++ tailWord_518062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518062).length < 2 ^ (prefixWord ++ tailWord_518062).sum := by decide
  have hdescent : baseEnd_518062 < baseStart_518062 := by decide
  rcases family_descends (prefixWord ++ tailWord_518062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518077 : List Nat := [1, 4, 1, 2, 3, 1, 2, 4, 1, 3]
def baseStart_518077 : Nat := 118140960795 + 518077 * 2 ^ 59
def prefixEnd_518077 : Nat := 4983230072969 + 3 ^ 40 * 518077 * 2
def baseEnd_518077 : Nat := 177348344692983170036609

theorem tailTrace_518077 : CollatzResearch.WordTrace tailWord_518077 prefixEnd_518077 177348344692983170036609 := by
  unfold tailWord_518077
  simp only [CollatzResearch.WordTrace]
  refine ⟨18895820544102984352416485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12597213696068656234944323 18895820544102984352416485)
  ·
    refine ⟨3542966352019309566078091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18895820544102984352416485 3542966352019309566078091)
    ·
      refine ⟨5314449528028964349117137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3542966352019309566078091 5314449528028964349117137)
      ·
        refine ⟨3985837146021723261837853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5314449528028964349117137 3985837146021723261837853)
        ·
          refine ⟨1494688929758146223189195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3985837146021723261837853 1494688929758146223189195)
          ·
            refine ⟨2242033394637219334783793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1494688929758146223189195 2242033394637219334783793)
            ·
              refine ⟨1681525045977914501087845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2242033394637219334783793 1681525045977914501087845)
              ·
                refine ⟨315285946120858968953971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1681525045977914501087845 315285946120858968953971)
                ·
                  refine ⟨472928919181288453430957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 315285946120858968953971 472928919181288453430957)
                  ·
                    refine ⟨177348344692983170036609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 472928919181288453430957 177348344692983170036609)
                    ·
                      rfl

theorem cell22_518077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 4, 1, 3].length) (baseStart_518077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_518077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_518077 prefixEnd_518077 := by exact prefixLift 518077
  have htrace : WordTrace (prefixWord ++ tailWord_518077) baseStart_518077 baseEnd_518077 := by
    simpa [prefixWord, tailWord_518077, baseEnd_518077] using wordTrace_append hprefix tailTrace_518077
  have hstable : (prefixWord ++ tailWord_518077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518077).length < 2 ^ (prefixWord ++ tailWord_518077).sum := by decide
  have hdescent : baseEnd_518077 < baseStart_518077 := by decide
  rcases family_descends (prefixWord ++ tailWord_518077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518088 : List Nat := [2, 1, 3, 1, 4, 1, 2, 1, 2, 5]
def baseStart_518088 : Nat := 118140960795 + 518088 * 2 ^ 59
def prefixEnd_518088 : Nat := 4983230072969 + 3 ^ 40 * 518088 * 2
def baseEnd_518088 : Nat := 177352110217782808011575

theorem tailTrace_518088 : CollatzResearch.WordTrace tailWord_518088 prefixEnd_518088 177352110217782808011575 := by
  unfold tailWord_518088
  simp only [CollatzResearch.WordTrace]
  refine ⟨9448110873531566615533459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12597481164708755487377945 9448110873531566615533459)
  ·
    refine ⟨14172166310297349923300189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9448110873531566615533459 14172166310297349923300189)
    ·
      refine ⟨5314562366361506221237571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14172166310297349923300189 5314562366361506221237571)
      ·
        refine ⟨7971843549542259331856357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5314562366361506221237571 7971843549542259331856357)
        ·
          refine ⟨1494720665539173624723067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7971843549542259331856357 1494720665539173624723067)
          ·
            refine ⟨2242080998308760437084601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1494720665539173624723067 2242080998308760437084601)
            ·
              refine ⟨1681560748731570327813451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2242080998308760437084601 1681560748731570327813451)
              ·
                refine ⟨2522341123097355491720177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1681560748731570327813451 2522341123097355491720177)
                ·
                  refine ⟨1891755842323016618790133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2522341123097355491720177 1891755842323016618790133)
                  ·
                    refine ⟨177352110217782808011575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1891755842323016618790133 177352110217782808011575)
                    ·
                      rfl

theorem cell22_518088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 2, 5].length) (baseStart_518088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_518088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_518088 prefixEnd_518088 := by exact prefixLift 518088
  have htrace : WordTrace (prefixWord ++ tailWord_518088) baseStart_518088 baseEnd_518088 := by
    simpa [prefixWord, tailWord_518088, baseEnd_518088] using wordTrace_append hprefix tailTrace_518088
  have hstable : (prefixWord ++ tailWord_518088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518088).length < 2 ^ (prefixWord ++ tailWord_518088).sum := by decide
  have hdescent : baseEnd_518088 < baseStart_518088 := by decide
  rcases family_descends (prefixWord ++ tailWord_518088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518154 : List Nat := [3, 1, 2, 2, 5, 1, 1, 2, 1, 4]
def baseStart_518154 : Nat := 118140960795 + 518154 * 2 ^ 59
def prefixEnd_518154 : Nat := 4983230072969 + 3 ^ 40 * 518154 * 2
def baseEnd_518154 : Nat := 177374703366580635861373

theorem tailTrace_518154 : CollatzResearch.WordTrace tailWord_518154 prefixEnd_518154 177374703366580635861373 := by
  unfold tailWord_518154
  simp only [CollatzResearch.WordTrace]
  refine ⟨4724657241206006625742379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12599085976549351001979677 4724657241206006625742379)
  ·
    refine ⟨7086985861809009938613569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4724657241206006625742379 7086985861809009938613569)
    ·
      refine ⟨5315239396356757453960177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7086985861809009938613569 5315239396356757453960177)
      ·
        refine ⟨3986429547267568090470133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5315239396356757453960177 3986429547267568090470133)
        ·
          refine ⟨373727770056334508481575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3986429547267568090470133 373727770056334508481575)
          ·
            refine ⟨560591655084501762722363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373727770056334508481575 560591655084501762722363)
            ·
              refine ⟨840887482626752644083545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 560591655084501762722363 840887482626752644083545)
              ·
                refine ⟨630665611970064483062659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 840887482626752644083545 630665611970064483062659)
                ·
                  refine ⟨945998417955096724593989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 630665611970064483062659 945998417955096724593989)
                  ·
                    refine ⟨177374703366580635861373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 945998417955096724593989 177374703366580635861373)
                    ·
                      rfl

theorem cell22_518154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 2, 1, 4].length) (baseStart_518154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_518154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_518154 prefixEnd_518154 := by exact prefixLift 518154
  have htrace : WordTrace (prefixWord ++ tailWord_518154) baseStart_518154 baseEnd_518154 := by
    simpa [prefixWord, tailWord_518154, baseEnd_518154] using wordTrace_append hprefix tailTrace_518154
  have hstable : (prefixWord ++ tailWord_518154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518154).length < 2 ^ (prefixWord ++ tailWord_518154).sum := by decide
  have hdescent : baseEnd_518154 < baseStart_518154 := by decide
  rcases family_descends (prefixWord ++ tailWord_518154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518180 : List Nat := [2, 3, 1, 4, 3, 9]
def baseStart_518180 : Nat := 118140960795 + 518180 * 2 ^ 59
def prefixEnd_518180 : Nat := 4983230072969 + 3 ^ 40 * 518180 * 2
def baseEnd_518180 : Nat := 2189921033307718947053

theorem tailTrace_518180 : CollatzResearch.WordTrace tailWord_518180 prefixEnd_518180 2189921033307718947053 := by
  unfold tailWord_518180
  simp only [CollatzResearch.WordTrace]
  refine ⟨9449788631364916471707997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12599718175153221962277329 9449788631364916471707997)
  ·
    refine ⟨3543670736761843676890499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9449788631364916471707997 3543670736761843676890499)
    ·
      refine ⟨5315506105142765515335749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3543670736761843676890499 5315506105142765515335749)
      ·
        refine ⟨996657394714268534125453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5315506105142765515335749 996657394714268534125453)
        ·
          refine ⟨373746523017850700297045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 996657394714268534125453 373746523017850700297045)
          ·
            refine ⟨2189921033307718947053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 373746523017850700297045 2189921033307718947053)
            ·
              rfl

theorem cell22_518180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 9].length) (baseStart_518180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_518180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_518180 prefixEnd_518180 := by exact prefixLift 518180
  have htrace : WordTrace (prefixWord ++ tailWord_518180) baseStart_518180 baseEnd_518180 := by
    simpa [prefixWord, tailWord_518180, baseEnd_518180] using wordTrace_append hprefix tailTrace_518180
  have hstable : (prefixWord ++ tailWord_518180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518180).length < 2 ^ (prefixWord ++ tailWord_518180).sum := by decide
  have hdescent : baseEnd_518180 < baseStart_518180 := by decide
  rcases family_descends (prefixWord ++ tailWord_518180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518193 : List Nat := [1, 2, 2, 3, 1, 3, 1, 1, 2, 6]
def baseStart_518193 : Nat := 118140960795 + 518193 * 2 ^ 59
def prefixEnd_518193 : Nat := 4983230072969 + 3 ^ 40 * 518193 * 2
def baseEnd_518193 : Nat := 177388053863597534136253

theorem tailTrace_518193 : CollatzResearch.WordTrace tailWord_518193 prefixEnd_518193 177388053863597534136253 := by
  unfold tailWord_518193
  simp only [CollatzResearch.WordTrace]
  refine ⟨18900051411682736163639233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12600034274455157442426155 18900051411682736163639233)
  ·
    refine ⟨14175038558762052122729425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18900051411682736163639233 14175038558762052122729425)
    ·
      refine ⟨10631278919071539092047069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14175038558762052122729425 10631278919071539092047069)
      ·
        refine ⟨3986729594651827159517651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10631278919071539092047069 3986729594651827159517651)
        ·
          refine ⟨5980094391977740739276477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3986729594651827159517651 5980094391977740739276477)
          ·
            refine ⟨2242535396991652777228679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5980094391977740739276477 2242535396991652777228679)
            ·
              refine ⟨3363803095487479165843019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2242535396991652777228679 3363803095487479165843019)
              ·
                refine ⟨5045704643231218748764529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3363803095487479165843019 5045704643231218748764529)
                ·
                  refine ⟨3784278482423414061573397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5045704643231218748764529 3784278482423414061573397)
                  ·
                    refine ⟨177388053863597534136253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3784278482423414061573397 177388053863597534136253)
                    ·
                      rfl

theorem cell22_518193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 6].length) (baseStart_518193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_518193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_518193 prefixEnd_518193 := by exact prefixLift 518193
  have htrace : WordTrace (prefixWord ++ tailWord_518193) baseStart_518193 baseEnd_518193 := by
    simpa [prefixWord, tailWord_518193, baseEnd_518193] using wordTrace_append hprefix tailTrace_518193
  have hstable : (prefixWord ++ tailWord_518193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518193).length < 2 ^ (prefixWord ++ tailWord_518193).sum := by decide
  have hdescent : baseEnd_518193 < baseStart_518193 := by decide
  rcases family_descends (prefixWord ++ tailWord_518193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518229 : List Nat := [1, 3, 2, 2, 1, 4, 2, 3, 1, 3]
def baseStart_518229 : Nat := 118140960795 + 518229 * 2 ^ 59
def prefixEnd_518229 : Nat := 4983230072969 + 3 ^ 40 * 518229 * 2
def baseEnd_518229 : Nat := 177400377399305440236143

theorem tailTrace_518229 : CollatzResearch.WordTrace tailWord_518229 prefixEnd_518229 177400377399305440236143 := by
  unfold tailWord_518229
  simp only [CollatzResearch.WordTrace]
  refine ⟨18901364439552314311949741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12600909626368209541299827 18901364439552314311949741)
  ·
    refine ⟨7088011664832117866981153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18901364439552314311949741 7088011664832117866981153)
    ·
      refine ⟨5316008748624088400235865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7088011664832117866981153 5316008748624088400235865)
      ·
        refine ⟨3987006561468066300176899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5316008748624088400235865 3987006561468066300176899)
        ·
          refine ⟨5980509842202099450265349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3987006561468066300176899 5980509842202099450265349)
          ·
            refine ⟨1121345595412893646924753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5980509842202099450265349 1121345595412893646924753)
            ·
              refine ⟨841009196559670235193565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1121345595412893646924753 841009196559670235193565)
              ·
                refine ⟨315378448709876338197587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 841009196559670235193565 315378448709876338197587)
                ·
                  refine ⟨473067673064814507296381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 315378448709876338197587 473067673064814507296381)
                  ·
                    refine ⟨177400377399305440236143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 473067673064814507296381 177400377399305440236143)
                    ·
                      rfl

theorem cell22_518229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 3, 1, 3].length) (baseStart_518229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_518229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_518229 prefixEnd_518229 := by exact prefixLift 518229
  have htrace : WordTrace (prefixWord ++ tailWord_518229) baseStart_518229 baseEnd_518229 := by
    simpa [prefixWord, tailWord_518229, baseEnd_518229] using wordTrace_append hprefix tailTrace_518229
  have hstable : (prefixWord ++ tailWord_518229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518229).length < 2 ^ (prefixWord ++ tailWord_518229).sum := by decide
  have hdescent : baseEnd_518229 < baseStart_518229 := by decide
  rcases family_descends (prefixWord ++ tailWord_518229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518242 : List Nat := [3, 3, 2, 2, 2, 1, 1, 1, 7]
def baseStart_518242 : Nat := 118140960795 + 518242 * 2 ^ 59
def prefixEnd_518242 : Nat := 4983230072969 + 3 ^ 40 * 518242 * 2
def baseEnd_518242 : Nat := 59134942521659246553701

theorem tailTrace_518242 : CollatzResearch.WordTrace tailWord_518242 prefixEnd_518242 59134942521659246553701 := by
  unfold tailWord_518242
  simp only [CollatzResearch.WordTrace]
  refine ⟨4725459647126304383043245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12601225725670145021448653 4725459647126304383043245)
  ·
    refine ⟨1772047367672364143641217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4725459647126304383043245 1772047367672364143641217)
    ·
      refine ⟨1329035525754273107730913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1772047367672364143641217 1329035525754273107730913)
      ·
        refine ⟨996776644315704830798185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1329035525754273107730913 996776644315704830798185)
        ·
          refine ⟨747582483236778623098639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 996776644315704830798185 747582483236778623098639)
          ·
            refine ⟨1121373724855167934647959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 747582483236778623098639 1121373724855167934647959)
            ·
              refine ⟨1682060587282751901971939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1121373724855167934647959 1682060587282751901971939)
              ·
                refine ⟨2523090880924127852957909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1682060587282751901971939 2523090880924127852957909)
                ·
                  refine ⟨59134942521659246553701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2523090880924127852957909 59134942521659246553701)
                  ·
                    rfl

theorem cell22_518242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_518242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_518242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_518242 prefixEnd_518242 := by exact prefixLift 518242
  have htrace : WordTrace (prefixWord ++ tailWord_518242) baseStart_518242 baseEnd_518242 := by
    simpa [prefixWord, tailWord_518242, baseEnd_518242] using wordTrace_append hprefix tailTrace_518242
  have hstable : (prefixWord ++ tailWord_518242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518242).length < 2 ^ (prefixWord ++ tailWord_518242).sum := by decide
  have hdescent : baseEnd_518242 < baseStart_518242 := by decide
  rcases family_descends (prefixWord ++ tailWord_518242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518304 : List Nat := [2, 1, 1, 4, 2, 3, 3, 2, 4]
def baseStart_518304 : Nat := 118140960795 + 518304 * 2 ^ 59
def prefixEnd_518304 : Nat := 4983230072969 + 3 ^ 40 * 518304 * 2
def baseEnd_518304 : Nat := 59142017144010081536971

theorem tailTrace_518304 : CollatzResearch.WordTrace tailWord_518304 prefixEnd_518304 59142017144010081536971 := by
  unfold tailWord_518304
  simp only [CollatzResearch.WordTrace]
  refine ⟨9452049957140301060464983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12602733276187068080619977 9452049957140301060464983)
  ·
    refine ⟨14178074935710451590697475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9452049957140301060464983 14178074935710451590697475)
    ·
      refine ⟨21267112403565677386046213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14178074935710451590697475 21267112403565677386046213)
      ·
        refine ⟨3987583575668564509883665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21267112403565677386046213 3987583575668564509883665)
        ·
          refine ⟨2990687681751423382412749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3987583575668564509883665 2990687681751423382412749)
          ·
            refine ⟨1121507880656783768404781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2990687681751423382412749 1121507880656783768404781)
            ·
              refine ⟨420565455246293913151793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1121507880656783768404781 420565455246293913151793)
              ·
                refine ⟨315424091434720434863845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 420565455246293913151793 315424091434720434863845)
                ·
                  refine ⟨59142017144010081536971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 315424091434720434863845 59142017144010081536971)
                  ·
                    rfl

theorem cell22_518304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 3, 2, 4].length) (baseStart_518304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_518304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_518304 prefixEnd_518304 := by exact prefixLift 518304
  have htrace : WordTrace (prefixWord ++ tailWord_518304) baseStart_518304 baseEnd_518304 := by
    simpa [prefixWord, tailWord_518304, baseEnd_518304] using wordTrace_append hprefix tailTrace_518304
  have hstable : (prefixWord ++ tailWord_518304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518304).length < 2 ^ (prefixWord ++ tailWord_518304).sum := by decide
  have hdescent : baseEnd_518304 < baseStart_518304 := by decide
  rcases family_descends (prefixWord ++ tailWord_518304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518334 : List Nat := [4, 2, 1, 1, 4, 1, 2, 1, 2, 4]
def baseStart_518334 : Nat := 118140960795 + 518334 * 2 ^ 59
def prefixEnd_518334 : Nat := 4983230072969 + 3 ^ 40 * 518334 * 2
def baseEnd_518334 : Nat := 177436321045120166360821

theorem tailTrace_518334 : CollatzResearch.WordTrace tailWord_518334 prefixEnd_518334 177436321045120166360821 := by
  unfold tailWord_518334
  simp only [CollatzResearch.WordTrace]
  refine ⟨2363149263021489655565257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12603462736114611496348037 2363149263021489655565257)
  ·
    refine ⟨1772361947266117241673943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2363149263021489655565257 1772361947266117241673943)
    ·
      refine ⟨2658542920899175862510915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1772361947266117241673943 2658542920899175862510915)
      ·
        refine ⟨3987814381348763793766373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2658542920899175862510915 3987814381348763793766373)
        ·
          refine ⟨747715196502893211331195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3987814381348763793766373 747715196502893211331195)
          ·
            refine ⟨1121572794754339816996793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 747715196502893211331195 1121572794754339816996793)
            ·
              refine ⟨841179596065754862747595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1121572794754339816996793 841179596065754862747595)
              ·
                refine ⟨1261769394098632294121393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 841179596065754862747595 1261769394098632294121393)
                ·
                  refine ⟨946327045573974220591045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1261769394098632294121393 946327045573974220591045)
                  ·
                    refine ⟨177436321045120166360821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 946327045573974220591045 177436321045120166360821)
                    ·
                      rfl

theorem cell22_518334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_518334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_518334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_518334 prefixEnd_518334 := by exact prefixLift 518334
  have htrace : WordTrace (prefixWord ++ tailWord_518334) baseStart_518334 baseEnd_518334 := by
    simpa [prefixWord, tailWord_518334, baseEnd_518334] using wordTrace_append hprefix tailTrace_518334
  have hstable : (prefixWord ++ tailWord_518334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518334).length < 2 ^ (prefixWord ++ tailWord_518334).sum := by decide
  have hdescent : baseEnd_518334 < baseStart_518334 := by decide
  rcases family_descends (prefixWord ++ tailWord_518334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518435 : List Nat := [1, 1, 1, 4, 2, 2, 1, 1, 3, 6]
def baseStart_518435 : Nat := 118140960795 + 518435 * 2 ^ 59
def prefixEnd_518435 : Nat := 4983230072969 + 3 ^ 40 * 518435 * 2
def baseEnd_518435 : Nat := 177470895409189569585511

theorem tailTrace_518435 : CollatzResearch.WordTrace tailWord_518435 prefixEnd_518435 177470895409189569585511 := by
  unfold tailWord_518435
  simp only [CollatzResearch.WordTrace]
  refine ⟨18908877876806011493948759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12605918584537340995965839 18908877876806011493948759)
  ·
    refine ⟨28363316815209017240923139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18908877876806011493948759 28363316815209017240923139)
    ·
      refine ⟨42544975222813525861384709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28363316815209017240923139 42544975222813525861384709)
      ·
        refine ⟨7977182854277536099009633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42544975222813525861384709 7977182854277536099009633)
        ·
          refine ⟨5982887140708152074257225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7977182854277536099009633 5982887140708152074257225)
          ·
            refine ⟨4487165355531114055692919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5982887140708152074257225 4487165355531114055692919)
            ·
              refine ⟨6730748033296671083539379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4487165355531114055692919 6730748033296671083539379)
              ·
                refine ⟨10096122049945006625309069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6730748033296671083539379 10096122049945006625309069)
                ·
                  refine ⟨3786045768729377484490901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10096122049945006625309069 3786045768729377484490901)
                  ·
                    refine ⟨177470895409189569585511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3786045768729377484490901 177470895409189569585511)
                    ·
                      rfl

theorem cell22_518435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 6].length) (baseStart_518435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_518435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_518435 prefixEnd_518435 := by exact prefixLift 518435
  have htrace : WordTrace (prefixWord ++ tailWord_518435) baseStart_518435 baseEnd_518435 := by
    simpa [prefixWord, tailWord_518435, baseEnd_518435] using wordTrace_append hprefix tailTrace_518435
  have hstable : (prefixWord ++ tailWord_518435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518435).length < 2 ^ (prefixWord ++ tailWord_518435).sum := by decide
  have hdescent : baseEnd_518435 < baseStart_518435 := by decide
  rcases family_descends (prefixWord ++ tailWord_518435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518529 : List Nat := [1, 2, 4, 3, 1, 1, 1, 4, 5]
def baseStart_518529 : Nat := 118140960795 + 518529 * 2 ^ 59
def prefixEnd_518529 : Nat := 4983230072969 + 3 ^ 40 * 518529 * 2
def baseEnd_518529 : Nat := 59167691176734885911741

theorem tailTrace_518529 : CollatzResearch.WordTrace tailWord_518529 prefixEnd_518529 59167691176734885911741 := by
  unfold tailWord_518529
  simp only [CollatzResearch.WordTrace]
  refine ⟨18912306338465465547870641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12608204225643643698580427 18912306338465465547870641)
  ·
    refine ⟨14184229753849099160902981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18912306338465465547870641 14184229753849099160902981)
    ·
      refine ⟨2659543078846706092669309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14184229753849099160902981 2659543078846706092669309)
      ·
        refine ⟨997328654567514784750991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2659543078846706092669309 997328654567514784750991)
        ·
          refine ⟨1495992981851272177126487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 997328654567514784750991 1495992981851272177126487)
          ·
            refine ⟨2243989472776908265689731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1495992981851272177126487 2243989472776908265689731)
            ·
              refine ⟨3365984209165362398534597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2243989472776908265689731 3365984209165362398534597)
              ·
                refine ⟨631122039218505449725237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3365984209165362398534597 631122039218505449725237)
                ·
                  refine ⟨59167691176734885911741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 631122039218505449725237 59167691176734885911741)
                  ·
                    rfl

theorem cell22_518529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 4, 5].length) (baseStart_518529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_518529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_518529 prefixEnd_518529 := by exact prefixLift 518529
  have htrace : WordTrace (prefixWord ++ tailWord_518529) baseStart_518529 baseEnd_518529 := by
    simpa [prefixWord, tailWord_518529, baseEnd_518529] using wordTrace_append hprefix tailTrace_518529
  have hstable : (prefixWord ++ tailWord_518529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518529).length < 2 ^ (prefixWord ++ tailWord_518529).sum := by decide
  have hdescent : baseEnd_518529 < baseStart_518529 := by decide
  rcases family_descends (prefixWord ++ tailWord_518529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518559 : List Nat := [1, 1, 2, 5, 1, 1, 2, 4, 1, 4]
def baseStart_518559 : Nat := 118140960795 + 518559 * 2 ^ 59
def prefixEnd_518559 : Nat := 4983230072969 + 3 ^ 40 * 518559 * 2
def baseEnd_518559 : Nat := 177513343143294579485131

theorem tailTrace_518559 : CollatzResearch.WordTrace tailWord_518559 prefixEnd_518559 177513343143294579485131 := by
  unfold tailWord_518559
  simp only [CollatzResearch.WordTrace]
  refine ⟨18913400528356780671462731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12608933685571187114308487 18913400528356780671462731)
  ·
    refine ⟨28370100792535171007194097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18913400528356780671462731 28370100792535171007194097)
    ·
      refine ⟨21277575594401378255395573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28370100792535171007194097 21277575594401378255395573)
      ·
        refine ⟨1994772711975129211443335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21277575594401378255395573 1994772711975129211443335)
        ·
          refine ⟨2992159067962693817165003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1994772711975129211443335 2992159067962693817165003)
          ·
            refine ⟨4488238601944040725747505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2992159067962693817165003 4488238601944040725747505)
            ·
              refine ⟨3366178951458030544310629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4488238601944040725747505 3366178951458030544310629)
              ·
                refine ⟨631158553398380727058243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3366178951458030544310629 631158553398380727058243)
                ·
                  refine ⟨946737830097571090587365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 631158553398380727058243 946737830097571090587365)
                  ·
                    refine ⟨177513343143294579485131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 946737830097571090587365 177513343143294579485131)
                    ·
                      rfl

theorem cell22_518559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 4, 1, 4].length) (baseStart_518559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_518559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_518559 prefixEnd_518559 := by exact prefixLift 518559
  have htrace : WordTrace (prefixWord ++ tailWord_518559) baseStart_518559 baseEnd_518559 := by
    simpa [prefixWord, tailWord_518559, baseEnd_518559] using wordTrace_append hprefix tailTrace_518559
  have hstable : (prefixWord ++ tailWord_518559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518559).length < 2 ^ (prefixWord ++ tailWord_518559).sum := by decide
  have hdescent : baseEnd_518559 < baseStart_518559 := by decide
  rcases family_descends (prefixWord ++ tailWord_518559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518580 : List Nat := [2, 5, 2, 2, 1, 2, 1, 2, 5]
def baseStart_518580 : Nat := 118140960795 + 518580 * 2 ^ 59
def prefixEnd_518580 : Nat := 4983230072969 + 3 ^ 40 * 518580 * 2
def baseEnd_518580 : Nat := 59173510624152508236689

theorem tailTrace_518580 : CollatzResearch.WordTrace tailWord_518580 prefixEnd_518580 59173510624152508236689 := by
  unfold tailWord_518580
  simp only [CollatzResearch.WordTrace]
  refine ⟨9457083230640350628988597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12609444307520467505318129 9457083230640350628988597)
  ·
    refine ⟨886601552872532871467681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9457083230640350628988597 886601552872532871467681)
    ·
      refine ⟨664951164654399653600761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 886601552872532871467681 664951164654399653600761)
      ·
        refine ⟨498713373490799740200571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 664951164654399653600761 498713373490799740200571)
        ·
          refine ⟨748070060236199610300857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 498713373490799740200571 748070060236199610300857)
          ·
            refine ⟨561052545177149707725643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 748070060236199610300857 561052545177149707725643)
            ·
              refine ⟨841578817765724561588465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 561052545177149707725643 841578817765724561588465)
              ·
                refine ⟨631184113324293421191349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 841578817765724561588465 631184113324293421191349)
                ·
                  refine ⟨59173510624152508236689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 631184113324293421191349 59173510624152508236689)
                  ·
                    rfl

theorem cell22_518580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_518580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_518580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_518580 prefixEnd_518580 := by exact prefixLift 518580
  have htrace : WordTrace (prefixWord ++ tailWord_518580) baseStart_518580 baseEnd_518580 := by
    simpa [prefixWord, tailWord_518580, baseEnd_518580] using wordTrace_append hprefix tailTrace_518580
  have hstable : (prefixWord ++ tailWord_518580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518580).length < 2 ^ (prefixWord ++ tailWord_518580).sum := by decide
  have hdescent : baseEnd_518580 < baseStart_518580 := by decide
  rcases family_descends (prefixWord ++ tailWord_518580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518602 : List Nat := [3, 1, 2, 1, 2, 2, 2, 9]
def baseStart_518602 : Nat := 118140960795 + 518602 * 2 ^ 59
def prefixEnd_518602 : Nat := 4983230072969 + 3 ^ 40 * 518602 * 2
def baseEnd_518602 : Nat := 19725340324672977851111

theorem tailTrace_518602 : CollatzResearch.WordTrace tailWord_518602 prefixEnd_518602 19725340324672977851111 := by
  unfold tailWord_518602
  simp only [CollatzResearch.WordTrace]
  refine ⟨4728742216800249753819515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12609979244800666010185373 4728742216800249753819515)
  ·
    refine ⟨7093113325200374630729273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4728742216800249753819515 7093113325200374630729273)
    ·
      refine ⟨5319834993900280973046955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7093113325200374630729273 5319834993900280973046955)
      ·
        refine ⟨7979752490850421459570433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5319834993900280973046955 7979752490850421459570433)
        ·
          refine ⟨5984814368137816094677825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7979752490850421459570433 5984814368137816094677825)
          ·
            refine ⟨4488610776103362071008369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5984814368137816094677825 4488610776103362071008369)
            ·
              refine ⟨3366458082077521553256277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4488610776103362071008369 3366458082077521553256277)
              ·
                refine ⟨19725340324672977851111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3366458082077521553256277 19725340324672977851111)
                ·
                  rfl

theorem cell22_518602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 9].length) (baseStart_518602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_518602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_518602 prefixEnd_518602 := by exact prefixLift 518602
  have htrace : WordTrace (prefixWord ++ tailWord_518602) baseStart_518602 baseEnd_518602 := by
    simpa [prefixWord, tailWord_518602, baseEnd_518602] using wordTrace_append hprefix tailTrace_518602
  have hstable : (prefixWord ++ tailWord_518602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518602).length < 2 ^ (prefixWord ++ tailWord_518602).sum := by decide
  have hdescent : baseEnd_518602 < baseStart_518602 := by decide
  rcases family_descends (prefixWord ++ tailWord_518602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518617 : List Nat := [1, 2, 1, 2, 4, 1, 1, 1, 2, 7]
def baseStart_518617 : Nat := 118140960795 + 518617 * 2 ^ 59
def prefixEnd_518617 : Nat := 4983230072969 + 3 ^ 40 * 518617 * 2
def baseEnd_518617 : Nat := 177533197728601761534953

theorem tailTrace_518617 : CollatzResearch.WordTrace tailWord_518617 prefixEnd_518617 177533197728601761534953 := by
  unfold tailWord_518617
  simp only [CollatzResearch.WordTrace]
  refine ⟨18915515962146656577074105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12610343974764437718049403 18915515962146656577074105)
  ·
    refine ⟨14186636971609992432805579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18915515962146656577074105 14186636971609992432805579)
    ·
      refine ⟨21279955457414988649208369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14186636971609992432805579 21279955457414988649208369)
      ·
        refine ⟨15959966593061241486906277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21279955457414988649208369 15959966593061241486906277)
        ·
          refine ⟨2992493736198982778794927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15959966593061241486906277 2992493736198982778794927)
          ·
            refine ⟨4488740604298474168192391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2992493736198982778794927 4488740604298474168192391)
            ·
              refine ⟨6733110906447711252288587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4488740604298474168192391 6733110906447711252288587)
              ·
                refine ⟨10099666359671566878432881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6733110906447711252288587 10099666359671566878432881)
                ·
                  refine ⟨7574749769753675158824661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10099666359671566878432881 7574749769753675158824661)
                  ·
                    refine ⟨177533197728601761534953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7574749769753675158824661 177533197728601761534953)
                    ·
                      rfl

theorem cell22_518617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 7].length) (baseStart_518617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_518617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_518617 prefixEnd_518617 := by exact prefixLift 518617
  have htrace : WordTrace (prefixWord ++ tailWord_518617) baseStart_518617 baseEnd_518617 := by
    simpa [prefixWord, tailWord_518617, baseEnd_518617] using wordTrace_append hprefix tailTrace_518617
  have hstable : (prefixWord ++ tailWord_518617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518617).length < 2 ^ (prefixWord ++ tailWord_518617).sum := by decide
  have hdescent : baseEnd_518617 < baseStart_518617 := by decide
  rcases family_descends (prefixWord ++ tailWord_518617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518709 : List Nat := [1, 3, 3, 1, 1, 2, 2, 3, 6]
def baseStart_518709 : Nat := 118140960795 + 518709 * 2 ^ 59
def prefixEnd_518709 : Nat := 4983230072969 + 3 ^ 40 * 518709 * 2
def baseEnd_518709 : Nat := 59188230402914729411557

theorem tailTrace_518709 : CollatzResearch.WordTrace tailWord_518709 prefixEnd_518709 59188230402914729411557 := by
  unfold tailWord_518709
  simp only [CollatzResearch.WordTrace]
  refine ⟨18918871477813356289423181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12612580985208904192948787 18918871477813356289423181)
  ·
    refine ⟨7094576804180008608533693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18918871477813356289423181 7094576804180008608533693)
    ·
      refine ⟨2660466301567503228200135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7094576804180008608533693 2660466301567503228200135)
      ·
        refine ⟨3990699452351254842300203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2660466301567503228200135 3990699452351254842300203)
        ·
          refine ⟨5986049178526882263450305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3990699452351254842300203 5986049178526882263450305)
          ·
            refine ⟨4489536883895161697587729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5986049178526882263450305 4489536883895161697587729)
            ·
              refine ⟨3367152662921371273190797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4489536883895161697587729 3367152662921371273190797)
              ·
                refine ⟨1262682248595514227446549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3367152662921371273190797 1262682248595514227446549)
                ·
                  refine ⟨59188230402914729411557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1262682248595514227446549 59188230402914729411557)
                  ·
                    rfl

theorem cell22_518709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 3, 6].length) (baseStart_518709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_518709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_518709 prefixEnd_518709 := by exact prefixLift 518709
  have htrace : WordTrace (prefixWord ++ tailWord_518709) baseStart_518709 baseEnd_518709 := by
    simpa [prefixWord, tailWord_518709, baseEnd_518709] using wordTrace_append hprefix tailTrace_518709
  have hstable : (prefixWord ++ tailWord_518709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518709).length < 2 ^ (prefixWord ++ tailWord_518709).sum := by decide
  have hdescent : baseEnd_518709 < baseStart_518709 := by decide
  rcases family_descends (prefixWord ++ tailWord_518709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518788 : List Nat := [2, 3, 2, 1, 3, 3, 2, 6]
def baseStart_518788 : Nat := 118140960795 + 518788 * 2 ^ 59
def prefixEnd_518788 : Nat := 4983230072969 + 3 ^ 40 * 518788 * 2
def baseEnd_518788 : Nat := 19732414947023812834381

theorem tailTrace_518788 : CollatzResearch.WordTrace tailWord_518788 prefixEnd_518788 19732414947023812834381 := by
  unfold tailWord_518788
  simp only [CollatzResearch.WordTrace]
  refine ⟨9460876422263576390774509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12614501896351435187699345 9460876422263576390774509)
  ·
    refine ⟨3547828658348841146540441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9460876422263576390774509 3547828658348841146540441)
    ·
      refine ⟨2660871493761630859905331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3547828658348841146540441 2660871493761630859905331)
      ·
        refine ⟨3991307240642446289857997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2660871493761630859905331 3991307240642446289857997)
        ·
          refine ⟨1496740215240917358696749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3991307240642446289857997 1496740215240917358696749)
          ·
            refine ⟨561277580715344009511281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1496740215240917358696749 561277580715344009511281)
            ·
              refine ⟨420958185536508007133461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 561277580715344009511281 420958185536508007133461)
              ·
                refine ⟨19732414947023812834381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 420958185536508007133461 19732414947023812834381)
                ·
                  rfl

theorem cell22_518788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 2, 6].length) (baseStart_518788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_518788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_518788 prefixEnd_518788 := by exact prefixLift 518788
  have htrace : WordTrace (prefixWord ++ tailWord_518788) baseStart_518788 baseEnd_518788 := by
    simpa [prefixWord, tailWord_518788, baseEnd_518788] using wordTrace_append hprefix tailTrace_518788
  have hstable : (prefixWord ++ tailWord_518788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518788).length < 2 ^ (prefixWord ++ tailWord_518788).sum := by decide
  have hdescent : baseEnd_518788 < baseStart_518788 := by decide
  rcases family_descends (prefixWord ++ tailWord_518788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518826 : List Nat := [3, 1, 5, 2, 2, 1, 2, 1, 2, 3]
def baseStart_518826 : Nat := 118140960795 + 518826 * 2 ^ 59
def prefixEnd_518826 : Nat := 4983230072969 + 3 ^ 40 * 518826 * 2
def baseEnd_518826 : Nat := 177604742699794883059313

theorem tailTrace_518826 : CollatzResearch.WordTrace tailWord_518826 prefixEnd_518826 177604742699794883059313 := by
  unfold tailWord_518826
  simp only [CollatzResearch.WordTrace]
  refine ⟨4730784704597371317858083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12615425878926323514288221 4730784704597371317858083)
  ·
    refine ⟨7096177056896056976787125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4730784704597371317858083 7096177056896056976787125)
    ·
      refine ⟨665266599084005341573793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7096177056896056976787125 665266599084005341573793)
      ·
        refine ⟨498949949313004006180345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 665266599084005341573793 498949949313004006180345)
        ·
          refine ⟨374212461984753004635259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 498949949313004006180345 374212461984753004635259)
          ·
            refine ⟨561318692977129506952889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374212461984753004635259 561318692977129506952889)
            ·
              refine ⟨420989019732847130214667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 561318692977129506952889 420989019732847130214667)
              ·
                refine ⟨631483529599270695322001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 420989019732847130214667 631483529599270695322001)
                ·
                  refine ⟨473612647199453021491501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 631483529599270695322001 473612647199453021491501)
                  ·
                    refine ⟨177604742699794883059313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 473612647199453021491501 177604742699794883059313)
                    ·
                      rfl

theorem cell22_518826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_518826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_518826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_518826 prefixEnd_518826 := by exact prefixLift 518826
  have htrace : WordTrace (prefixWord ++ tailWord_518826) baseStart_518826 baseEnd_518826 := by
    simpa [prefixWord, tailWord_518826, baseEnd_518826] using wordTrace_append hprefix tailTrace_518826
  have hstable : (prefixWord ++ tailWord_518826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518826).length < 2 ^ (prefixWord ++ tailWord_518826).sum := by decide
  have hdescent : baseEnd_518826 < baseStart_518826 := by decide
  rcases family_descends (prefixWord ++ tailWord_518826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518893 : List Nat := [1, 5, 1, 2, 1, 1, 4, 1, 1, 5]
def baseStart_518893 : Nat := 118140960795 + 518893 * 2 ^ 59
def prefixEnd_518893 : Nat := 4983230072969 + 3 ^ 40 * 518893 * 2
def baseEnd_518893 : Nat := 177627678169029041634107

theorem tailTrace_518893 : CollatzResearch.WordTrace tailWord_518893 prefixEnd_518893 177627678169029041634107 := by
  unfold tailWord_518893
  simp only [CollatzResearch.WordTrace]
  refine ⟨18925582509146755714121333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12617055006097837142747555 18925582509146755714121333)
  ·
    refine ⟨1774273360232508348198875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18925582509146755714121333 1774273360232508348198875)
    ·
      refine ⟨2661410040348762522298313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1774273360232508348198875 2661410040348762522298313)
      ·
        refine ⟨1996057530261571891723735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2661410040348762522298313 1996057530261571891723735)
        ·
          refine ⟨2994086295392357837585603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1996057530261571891723735 2994086295392357837585603)
          ·
            refine ⟨4491129443088536756378405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2994086295392357837585603 4491129443088536756378405)
            ·
              refine ⟨842086770579100641820951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4491129443088536756378405 842086770579100641820951)
              ·
                refine ⟨1263130155868650962731427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 842086770579100641820951 1263130155868650962731427)
                ·
                  refine ⟨1894695233802976444097141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1263130155868650962731427 1894695233802976444097141)
                  ·
                    refine ⟨177627678169029041634107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1894695233802976444097141 177627678169029041634107)
                    ·
                      rfl

theorem cell22_518893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_518893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_518893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_518893 prefixEnd_518893 := by exact prefixLift 518893
  have htrace : WordTrace (prefixWord ++ tailWord_518893) baseStart_518893 baseEnd_518893 := by
    simpa [prefixWord, tailWord_518893, baseEnd_518893] using wordTrace_append hprefix tailTrace_518893
  have hstable : (prefixWord ++ tailWord_518893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518893).length < 2 ^ (prefixWord ++ tailWord_518893).sum := by decide
  have hdescent : baseEnd_518893 < baseStart_518893 := by decide
  rcases family_descends (prefixWord ++ tailWord_518893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518908 : List Nat := [2, 2, 2, 1, 3, 2, 3, 1, 2, 4]
def baseStart_518908 : Nat := 118140960795 + 518908 * 2 ^ 59
def prefixEnd_518908 : Nat := 4983230072969 + 3 ^ 40 * 518908 * 2
def baseEnd_518908 : Nat := 177632812975574002509061

theorem tailTrace_518908 : CollatzResearch.WordTrace tailWord_518908 prefixEnd_518908 177632812975574002509061 := by
  unfold tailWord_518908
  simp only [CollatzResearch.WordTrace]
  refine ⟨9463064802046206637958689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12617419736061608850611585 9463064802046206637958689)
  ·
    refine ⟨7097298601534654978469017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9463064802046206637958689 7097298601534654978469017)
    ·
      refine ⟨5322973951150991233851763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7097298601534654978469017 5322973951150991233851763)
      ·
        refine ⟨7984460926726486850777645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5322973951150991233851763 7984460926726486850777645)
        ·
          refine ⟨2994172847522432569041617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7984460926726486850777645 2994172847522432569041617)
          ·
            refine ⟨2245629635641824426781213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2994172847522432569041617 2245629635641824426781213)
            ·
              refine ⟨842111113365684160042955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2245629635641824426781213 842111113365684160042955)
              ·
                refine ⟨1263166670048526240064433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 842111113365684160042955 1263166670048526240064433)
                ·
                  refine ⟨947375002536394680048325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1263166670048526240064433 947375002536394680048325)
                  ·
                    refine ⟨177632812975574002509061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 947375002536394680048325 177632812975574002509061)
                    ·
                      rfl

theorem cell22_518908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 1, 2, 4].length) (baseStart_518908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_518908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_518908 prefixEnd_518908 := by exact prefixLift 518908
  have htrace : WordTrace (prefixWord ++ tailWord_518908) baseStart_518908 baseEnd_518908 := by
    simpa [prefixWord, tailWord_518908, baseEnd_518908] using wordTrace_append hprefix tailTrace_518908
  have hstable : (prefixWord ++ tailWord_518908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518908).length < 2 ^ (prefixWord ++ tailWord_518908).sum := by decide
  have hdescent : baseEnd_518908 < baseStart_518908 := by decide
  rcases family_descends (prefixWord ++ tailWord_518908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518989 : List Nat := [1, 6, 1, 2, 2, 2, 1, 1, 3, 3]
def baseStart_518989 : Nat := 118140960795 + 518989 * 2 ^ 59
def prefixEnd_518989 : Nat := 4983230072969 + 3 ^ 40 * 518989 * 2
def baseEnd_518989 : Nat := 177660540930916791233813

theorem tailTrace_518989 : CollatzResearch.WordTrace tailWord_518989 prefixEnd_518989 177660540930916791233813 := by
  unfold tailWord_518989
  simp only [CollatzResearch.WordTrace]
  refine ⟨18929083916798964109616021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12619389277865976073077347 18929083916798964109616021)
  ·
    refine ⟨887300808599951442638251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18929083916798964109616021 887300808599951442638251)
    ·
      refine ⟨1330951212899927163957377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 887300808599951442638251 1330951212899927163957377)
      ·
        refine ⟨998213409674945372968033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1330951212899927163957377 998213409674945372968033)
        ·
          refine ⟨748660057256209029726025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 998213409674945372968033 748660057256209029726025)
          ·
            refine ⟨561495042942156772294519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 748660057256209029726025 561495042942156772294519)
            ·
              refine ⟨842242564413235158441779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 561495042942156772294519 842242564413235158441779)
              ·
                refine ⟨1263363846619852737662669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 842242564413235158441779 1263363846619852737662669)
                ·
                  refine ⟨473761442482444776623501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1263363846619852737662669 473761442482444776623501)
                  ·
                    refine ⟨177660540930916791233813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 473761442482444776623501 177660540930916791233813)
                    ·
                      rfl

theorem cell22_518989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_518989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_518989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_518989 prefixEnd_518989 := by exact prefixLift 518989
  have htrace : WordTrace (prefixWord ++ tailWord_518989) baseStart_518989 baseEnd_518989 := by
    simpa [prefixWord, tailWord_518989, baseEnd_518989] using wordTrace_append hprefix tailTrace_518989
  have hstable : (prefixWord ++ tailWord_518989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518989).length < 2 ^ (prefixWord ++ tailWord_518989).sum := by decide
  have hdescent : baseEnd_518989 < baseStart_518989 := by decide
  rcases family_descends (prefixWord ++ tailWord_518989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519015 : List Nat := [1, 1, 5, 1, 2, 2, 3, 2, 1, 4]
def baseStart_519015 : Nat := 118140960795 + 519015 * 2 ^ 59
def prefixEnd_519015 : Nat := 4983230072969 + 3 ^ 40 * 519015 * 2
def baseEnd_519015 : Nat := 177669441262261390083733

theorem tailTrace_519015 : CollatzResearch.WordTrace tailWord_519015 prefixEnd_519015 177669441262261390083733 := by
  unfold tailWord_519015
  simp only [CollatzResearch.WordTrace]
  refine ⟨18930032214704770550062499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12620021476469847033374999 18930032214704770550062499)
  ·
    refine ⟨28395048322057155825093749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18930032214704770550062499 28395048322057155825093749)
    ·
      refine ⟨2662035780192858358602539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28395048322057155825093749 2662035780192858358602539)
      ·
        refine ⟨3993053670289287537903809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2662035780192858358602539 3993053670289287537903809)
        ·
          refine ⟨2994790252716965653427857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3993053670289287537903809 2994790252716965653427857)
          ·
            refine ⟨2246092689537724240070893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2994790252716965653427857 2246092689537724240070893)
            ·
              refine ⟨842284758576646590026585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2246092689537724240070893 842284758576646590026585)
              ·
                refine ⟨631713568932484942519939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 842284758576646590026585 631713568932484942519939)
                ·
                  refine ⟨947570353398727413779909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 631713568932484942519939 947570353398727413779909)
                  ·
                    refine ⟨177669441262261390083733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 947570353398727413779909 177669441262261390083733)
                    ·
                      rfl

theorem cell22_519015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_519015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_519015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_519015 prefixEnd_519015 := by exact prefixLift 519015
  have htrace : WordTrace (prefixWord ++ tailWord_519015) baseStart_519015 baseEnd_519015 := by
    simpa [prefixWord, tailWord_519015, baseEnd_519015] using wordTrace_append hprefix tailTrace_519015
  have hstable : (prefixWord ++ tailWord_519015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519015).length < 2 ^ (prefixWord ++ tailWord_519015).sum := by decide
  have hdescent : baseEnd_519015 < baseStart_519015 := by decide
  rcases family_descends (prefixWord ++ tailWord_519015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519041 : List Nat := [1, 2, 4, 15]
def baseStart_519041 : Nat := 118140960795 + 519041 * 2 ^ 59
def prefixEnd_519041 : Nat := 4983230072969 + 3 ^ 40 * 519041 * 2
def baseEnd_519041 : Nat := 243728863640063084957

theorem tailTrace_519041 : CollatzResearch.WordTrace tailWord_519041 prefixEnd_519041 243728863640063084957 := by
  unfold tailWord_519041
  simp only [CollatzResearch.WordTrace]
  refine ⟨18930980512610576990508977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12620653675073717993672651 18930980512610576990508977)
  ·
    refine ⟨14198235384457932742881733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18930980512610576990508977 14198235384457932742881733)
    ·
      refine ⟨2662169134585862389290325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14198235384457932742881733 2662169134585862389290325)
      ·
        refine ⟨243728863640063084957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 15 2662169134585862389290325 243728863640063084957)
        ·
          rfl

theorem cell22_519041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 15].length) (baseStart_519041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_519041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_519041 prefixEnd_519041 := by exact prefixLift 519041
  have htrace : WordTrace (prefixWord ++ tailWord_519041) baseStart_519041 baseEnd_519041 := by
    simpa [prefixWord, tailWord_519041, baseEnd_519041] using wordTrace_append hprefix tailTrace_519041
  have hstable : (prefixWord ++ tailWord_519041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519041).length < 2 ^ (prefixWord ++ tailWord_519041).sum := by decide
  have hdescent : baseEnd_519041 < baseStart_519041 := by decide
  rcases family_descends (prefixWord ++ tailWord_519041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519043 : List Nat := [1, 1, 1, 3, 4, 1, 1, 4, 2, 4]
def baseStart_519043 : Nat := 118140960795 + 519043 * 2 ^ 59
def prefixEnd_519043 : Nat := 4983230072969 + 3 ^ 40 * 519043 * 2
def baseEnd_519043 : Nat := 177679026234478650383647

theorem tailTrace_519043 : CollatzResearch.WordTrace tailWord_519043 prefixEnd_519043 177679026234478650383647 := by
  unfold tailWord_519043
  simp only [CollatzResearch.WordTrace]
  refine ⟨18931053458603331332081783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12620702305735554221387855 18931053458603331332081783)
  ·
    refine ⟨28396580187904996998122675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18931053458603331332081783 28396580187904996998122675)
    ·
      refine ⟨42594870281857495497184013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28396580187904996998122675 42594870281857495497184013)
      ·
        refine ⟨15973076355696560811444005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42594870281857495497184013 15973076355696560811444005)
        ·
          refine ⟨2994951816693105152145751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15973076355696560811444005 2994951816693105152145751)
          ·
            refine ⟨4492427725039657728218627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2994951816693105152145751 4492427725039657728218627)
            ·
              refine ⟨6738641587559486592327941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4492427725039657728218627 6738641587559486592327941)
              ·
                refine ⟨1263495297667403736061489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6738641587559486592327941 1263495297667403736061489)
                ·
                  refine ⟨947621473250552802046117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1263495297667403736061489 947621473250552802046117)
                  ·
                    refine ⟨177679026234478650383647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 947621473250552802046117 177679026234478650383647)
                    ·
                      rfl

theorem cell22_519043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 4, 2, 4].length) (baseStart_519043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_519043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_519043 prefixEnd_519043 := by exact prefixLift 519043
  have htrace : WordTrace (prefixWord ++ tailWord_519043) baseStart_519043 baseEnd_519043 := by
    simpa [prefixWord, tailWord_519043, baseEnd_519043] using wordTrace_append hprefix tailTrace_519043
  have hstable : (prefixWord ++ tailWord_519043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519043).length < 2 ^ (prefixWord ++ tailWord_519043).sum := by decide
  have hdescent : baseEnd_519043 < baseStart_519043 := by decide
  rcases family_descends (prefixWord ++ tailWord_519043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519045 : List Nat := [1, 3, 1, 1, 3, 3, 1, 4, 2, 3]
def baseStart_519045 : Nat := 118140960795 + 519045 * 2 ^ 59
def prefixEnd_519045 : Nat := 4983230072969 + 3 ^ 40 * 519045 * 2
def baseEnd_519045 : Nat := 177679710875351311833641

theorem tailTrace_519045 : CollatzResearch.WordTrace tailWord_519045 prefixEnd_519045 177679710875351311833641 := by
  unfold tailWord_519045
  simp only [CollatzResearch.WordTrace]
  refine ⟨18931126404596085673654589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12620750936397390449103059 18931126404596085673654589)
  ·
    refine ⟨7099172401723532127620471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18931126404596085673654589 7099172401723532127620471)
    ·
      refine ⟨10648758602585298191430707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7099172401723532127620471 10648758602585298191430707)
      ·
        refine ⟨15973137903877947287146061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10648758602585298191430707 15973137903877947287146061)
        ·
          refine ⟨5989926713954230232679773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15973137903877947287146061 5989926713954230232679773)
          ·
            refine ⟨2246222517732836337254915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5989926713954230232679773 2246222517732836337254915)
            ·
              refine ⟨3369333776599254505882373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2246222517732836337254915 3369333776599254505882373)
              ·
                refine ⟨631750083112360219852945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3369333776599254505882373 631750083112360219852945)
                ·
                  refine ⟨473812562334270164889709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 631750083112360219852945 473812562334270164889709)
                  ·
                    refine ⟨177679710875351311833641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 473812562334270164889709 177679710875351311833641)
                    ·
                      rfl

theorem cell22_519045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 4, 2, 3].length) (baseStart_519045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_519045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_519045 prefixEnd_519045 := by exact prefixLift 519045
  have htrace : WordTrace (prefixWord ++ tailWord_519045) baseStart_519045 baseEnd_519045 := by
    simpa [prefixWord, tailWord_519045, baseEnd_519045] using wordTrace_append hprefix tailTrace_519045
  have hstable : (prefixWord ++ tailWord_519045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519045).length < 2 ^ (prefixWord ++ tailWord_519045).sum := by decide
  have hdescent : baseEnd_519045 < baseStart_519045 := by decide
  rcases family_descends (prefixWord ++ tailWord_519045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519047 : List Nat := [1, 1, 4, 2, 3, 1, 4, 2, 4]
def baseStart_519047 : Nat := 118140960795 + 519047 * 2 ^ 59
def prefixEnd_519047 : Nat := 4983230072969 + 3 ^ 40 * 519047 * 2
def baseEnd_519047 : Nat := 59226798505407991094545

theorem tailTrace_519047 : CollatzResearch.WordTrace tailWord_519047 prefixEnd_519047 59226798505407991094545 := by
  unfold tailWord_519047
  simp only [CollatzResearch.WordTrace]
  refine ⟨18931199350588840015227395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12620799567059226676818263 18931199350588840015227395)
  ·
    refine ⟨28396799025883260022841093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18931199350588840015227395 28396799025883260022841093)
    ·
      refine ⟨5324399817353111254282705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28396799025883260022841093 5324399817353111254282705)
      ·
        refine ⟨3993299863014833440712029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5324399817353111254282705 3993299863014833440712029)
        ·
          refine ⟨1497487448630562540267011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3993299863014833440712029 1497487448630562540267011)
          ·
            refine ⟨2246231172945843810400517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1497487448630562540267011 2246231172945843810400517)
            ·
              refine ⟨421168344927345714450097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2246231172945843810400517 421168344927345714450097)
              ·
                refine ⟨315876258695509285837573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 421168344927345714450097 315876258695509285837573)
                ·
                  refine ⟨59226798505407991094545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 315876258695509285837573 59226798505407991094545)
                  ·
                    rfl

theorem cell22_519047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 4, 2, 4].length) (baseStart_519047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_519047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_519047 prefixEnd_519047 := by exact prefixLift 519047
  have htrace : WordTrace (prefixWord ++ tailWord_519047) baseStart_519047 baseEnd_519047 := by
    simpa [prefixWord, tailWord_519047, baseEnd_519047] using wordTrace_append hprefix tailTrace_519047
  have hstable : (prefixWord ++ tailWord_519047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519047).length < 2 ^ (prefixWord ++ tailWord_519047).sum := by decide
  have hdescent : baseEnd_519047 < baseStart_519047 := by decide
  rcases family_descends (prefixWord ++ tailWord_519047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519103 : List Nat := [1, 1, 2, 2, 2, 1, 2, 6, 5]
def baseStart_519103 : Nat := 118140960795 + 519103 * 2 ^ 59
def prefixEnd_519103 : Nat := 4983230072969 + 3 ^ 40 * 519103 * 2
def baseEnd_519103 : Nat := 59233188486886164627821

theorem tailTrace_519103 : CollatzResearch.WordTrace tailWord_519103 prefixEnd_519103 59233188486886164627821 := by
  unfold tailWord_519103
  simp only [CollatzResearch.WordTrace]
  refine ⟨18933241838385961579265963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12622161225590641052843975 18933241838385961579265963)
  ·
    refine ⟨28399862757578942368898945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18933241838385961579265963 28399862757578942368898945)
    ·
      refine ⟨21299897068184206776674209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28399862757578942368898945 21299897068184206776674209)
      ·
        refine ⟨15974922801138155082505657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21299897068184206776674209 15974922801138155082505657)
        ·
          refine ⟨11981192100853616311879243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15974922801138155082505657 11981192100853616311879243)
          ·
            refine ⟨17971788151280424467818865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11981192100853616311879243 17971788151280424467818865)
            ·
              refine ⟨13478841113460318350864149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17971788151280424467818865 13478841113460318350864149)
              ·
                refine ⟨631820677193452422696757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13478841113460318350864149 631820677193452422696757)
                ·
                  refine ⟨59233188486886164627821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 631820677193452422696757 59233188486886164627821)
                  ·
                    rfl

theorem cell22_519103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 6, 5].length) (baseStart_519103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_519103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_519103 prefixEnd_519103 := by exact prefixLift 519103
  have htrace : WordTrace (prefixWord ++ tailWord_519103) baseStart_519103 baseEnd_519103 := by
    simpa [prefixWord, tailWord_519103, baseEnd_519103] using wordTrace_append hprefix tailTrace_519103
  have hstable : (prefixWord ++ tailWord_519103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519103).length < 2 ^ (prefixWord ++ tailWord_519103).sum := by decide
  have hdescent : baseEnd_519103 < baseStart_519103 := by decide
  rcases family_descends (prefixWord ++ tailWord_519103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519193 : List Nat := [1, 2, 1, 2, 1, 1, 6, 8]
def baseStart_519193 : Nat := 118140960795 + 519193 * 2 ^ 59
def prefixEnd_519193 : Nat := 4983230072969 + 3 ^ 40 * 519193 * 2
def baseEnd_519193 : Nat := 19747819366658695459243

theorem tailTrace_519193 : CollatzResearch.WordTrace tailWord_519193 prefixEnd_519193 19747819366658695459243 := by
  unfold tailWord_519193
  simp only [CollatzResearch.WordTrace]
  refine ⟨18936524408059906950042233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12624349605373271300028155 18936524408059906950042233)
  ·
    refine ⟨14202393306044930212531675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18936524408059906950042233 14202393306044930212531675)
    ·
      refine ⟨21303589959067395318797513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14202393306044930212531675 21303589959067395318797513)
      ·
        refine ⟨15977692469300546489098135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21303589959067395318797513 15977692469300546489098135)
        ·
          refine ⟨23966538703950819733647203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15977692469300546489098135 23966538703950819733647203)
          ·
            refine ⟨35949808055926229600470805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23966538703950819733647203 35949808055926229600470805)
            ·
              refine ⟨1685147252621542012522069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35949808055926229600470805 1685147252621542012522069)
              ·
                refine ⟨19747819366658695459243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1685147252621542012522069 19747819366658695459243)
                ·
                  rfl

theorem cell22_519193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 8].length) (baseStart_519193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_519193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_519193 prefixEnd_519193 := by exact prefixLift 519193
  have htrace : WordTrace (prefixWord ++ tailWord_519193) baseStart_519193 baseEnd_519193 := by
    simpa [prefixWord, tailWord_519193, baseEnd_519193] using wordTrace_append hprefix tailTrace_519193
  have hstable : (prefixWord ++ tailWord_519193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519193).length < 2 ^ (prefixWord ++ tailWord_519193).sum := by decide
  have hdescent : baseEnd_519193 < baseStart_519193 := by decide
  rcases family_descends (prefixWord ++ tailWord_519193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519197 : List Nat := [1, 4, 2, 2, 3, 1, 1, 2, 1, 5]
def baseStart_519197 : Nat := 118140960795 + 519197 * 2 ^ 59
def prefixEnd_519197 : Nat := 4983230072969 + 3 ^ 40 * 519197 * 2
def baseEnd_519197 : Nat := 177731743581673582033175

theorem tailTrace_519197 : CollatzResearch.WordTrace tailWord_519197 prefixEnd_519197 177731743581673582033175 := by
  unfold tailWord_519197
  simp only [CollatzResearch.WordTrace]
  refine ⟨18936670300045415633187845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12624446866696943755458563 18936670300045415633187845)
  ·
    refine ⟨3550625681258515431222721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18936670300045415633187845 3550625681258515431222721)
    ·
      refine ⟨2662969260943886573417041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3550625681258515431222721 2662969260943886573417041)
      ·
        refine ⟨1997226945707914930062781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2662969260943886573417041 1997226945707914930062781)
        ·
          refine ⟨748960104640468098773543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1997226945707914930062781 748960104640468098773543)
          ·
            refine ⟨1123440156960702148160315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 748960104640468098773543 1123440156960702148160315)
            ·
              refine ⟨1685160235441053222240473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1123440156960702148160315 1685160235441053222240473)
              ·
                refine ⟨1263870176580789916680355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1685160235441053222240473 1263870176580789916680355)
                ·
                  refine ⟨1895805264871184875020533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1263870176580789916680355 1895805264871184875020533)
                  ·
                    refine ⟨177731743581673582033175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1895805264871184875020533 177731743581673582033175)
                    ·
                      rfl

theorem cell22_519197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_519197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_519197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_519197 prefixEnd_519197 := by exact prefixLift 519197
  have htrace : WordTrace (prefixWord ++ tailWord_519197) baseStart_519197 baseEnd_519197 := by
    simpa [prefixWord, tailWord_519197, baseEnd_519197] using wordTrace_append hprefix tailTrace_519197
  have hstable : (prefixWord ++ tailWord_519197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519197).length < 2 ^ (prefixWord ++ tailWord_519197).sum := by decide
  have hdescent : baseEnd_519197 < baseStart_519197 := by decide
  rcases family_descends (prefixWord ++ tailWord_519197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519210 : List Nat := [3, 1, 4, 1, 3, 10]
def baseStart_519210 : Nat := 118140960795 + 519210 * 2 ^ 59
def prefixEnd_519210 : Nat := 4983230072969 + 3 ^ 40 * 519210 * 2
def baseEnd_519210 : Nat := 2194273996880813351335

theorem tailTrace_519210 : CollatzResearch.WordTrace tailWord_519210 prefixEnd_519210 2194273996880813351335 := by
  unfold tailWord_519210
  simp only [CollatzResearch.WordTrace]
  refine ⟨4734286112249579713352771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12624762965998879235607389 4734286112249579713352771)
  ·
    refine ⟨7101429168374369570029157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4734286112249579713352771 7101429168374369570029157)
    ·
      refine ⟨1331517969070194294380467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7101429168374369570029157 1331517969070194294380467)
      ·
        refine ⟨1997276953605291441570701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1331517969070194294380467 1997276953605291441570701)
        ·
          refine ⟨748978857601984290589013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1997276953605291441570701 748978857601984290589013)
          ·
            refine ⟨2194273996880813351335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 748978857601984290589013 2194273996880813351335)
            ·
              rfl

theorem cell22_519210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 10].length) (baseStart_519210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_519210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_519210 prefixEnd_519210 := by exact prefixLift 519210
  have htrace : WordTrace (prefixWord ++ tailWord_519210) baseStart_519210 baseEnd_519210 := by
    simpa [prefixWord, tailWord_519210, baseEnd_519210] using wordTrace_append hprefix tailTrace_519210
  have hstable : (prefixWord ++ tailWord_519210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519210).length < 2 ^ (prefixWord ++ tailWord_519210).sum := by decide
  have hdescent : baseEnd_519210 < baseStart_519210 := by decide
  rcases family_descends (prefixWord ++ tailWord_519210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519214 : List Nat := [4, 1, 3, 1, 1, 1, 4, 2, 2, 3]
def baseStart_519214 : Nat := 118140960795 + 519214 * 2 ^ 59
def prefixEnd_519214 : Nat := 4983230072969 + 3 ^ 40 * 519214 * 2
def baseEnd_519214 : Nat := 177737563029091204358123

theorem tailTrace_519214 : CollatzResearch.WordTrace tailWord_519214 prefixEnd_519214 177737563029091204358123 := by
  unfold tailWord_519214
  simp only [CollatzResearch.WordTrace]
  refine ⟨2367161292622978442069587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12624860227322551691037797 2367161292622978442069587)
  ·
    refine ⟨3550741938934467663104381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2367161292622978442069587 3550741938934467663104381)
    ·
      refine ⟨1331528227100425373664143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3550741938934467663104381 1331528227100425373664143)
      ·
        refine ⟨1997292340650638060496215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1331528227100425373664143 1997292340650638060496215)
        ·
          refine ⟨2995938510975957090744323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1997292340650638060496215 2995938510975957090744323)
          ·
            refine ⟨4493907766463935636116485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2995938510975957090744323 4493907766463935636116485)
            ·
              refine ⟨842607706211987931771841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4493907766463935636116485 842607706211987931771841)
              ·
                refine ⟨631955779658990948828881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 842607706211987931771841 631955779658990948828881)
                ·
                  refine ⟨473966834744243211621661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 631955779658990948828881 473966834744243211621661)
                  ·
                    refine ⟨177737563029091204358123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 473966834744243211621661 177737563029091204358123)
                    ·
                      rfl

theorem cell22_519214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_519214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_519214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_519214 prefixEnd_519214 := by exact prefixLift 519214
  have htrace : WordTrace (prefixWord ++ tailWord_519214) baseStart_519214 baseEnd_519214 := by
    simpa [prefixWord, tailWord_519214, baseEnd_519214] using wordTrace_append hprefix tailTrace_519214
  have hstable : (prefixWord ++ tailWord_519214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519214).length < 2 ^ (prefixWord ++ tailWord_519214).sum := by decide
  have hdescent : baseEnd_519214 < baseStart_519214 := by decide
  rcases family_descends (prefixWord ++ tailWord_519214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519289 : List Nat := [1, 2, 1, 3, 5, 1, 3, 1, 5]
def baseStart_519289 : Nat := 118140960795 + 519289 * 2 ^ 59
def prefixEnd_519289 : Nat := 4983230072969 + 3 ^ 40 * 519289 * 2
def baseEnd_519289 : Nat := 59254412353938669577631

theorem tailTrace_519289 : CollatzResearch.WordTrace tailWord_519289 prefixEnd_519289 59254412353938669577631 := by
  unfold tailWord_519289
  simp only [CollatzResearch.WordTrace]
  refine ⟨18940025815712115345536921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12626683877141410230357947 18940025815712115345536921)
  ·
    refine ⟨14205019361784086509152691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18940025815712115345536921 14205019361784086509152691)
    ·
      refine ⟨21307529042676129763729037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14205019361784086509152691 21307529042676129763729037)
      ·
        refine ⟨7990323391003548661398389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21307529042676129763729037 7990323391003548661398389)
        ·
          refine ⟨749092817906582687006099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7990323391003548661398389 749092817906582687006099)
          ·
            refine ⟨1123639226859874030509149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 749092817906582687006099 1123639226859874030509149)
            ·
              refine ⟨421364710072452761440931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1123639226859874030509149 421364710072452761440931)
              ·
                refine ⟨632047065108679142161397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 421364710072452761440931 632047065108679142161397)
                ·
                  refine ⟨59254412353938669577631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 632047065108679142161397 59254412353938669577631)
                  ·
                    rfl

theorem cell22_519289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 3, 1, 5].length) (baseStart_519289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_519289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_519289 prefixEnd_519289 := by exact prefixLift 519289
  have htrace : WordTrace (prefixWord ++ tailWord_519289) baseStart_519289 baseEnd_519289 := by
    simpa [prefixWord, tailWord_519289, baseEnd_519289] using wordTrace_append hprefix tailTrace_519289
  have hstable : (prefixWord ++ tailWord_519289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519289).length < 2 ^ (prefixWord ++ tailWord_519289).sum := by decide
  have hdescent : baseEnd_519289 < baseStart_519289 := by decide
  rcases family_descends (prefixWord ++ tailWord_519289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519315 : List Nat := [1, 1, 1, 2, 1, 2, 4, 4, 1, 5]
def baseStart_519315 : Nat := 118140960795 + 519315 * 2 ^ 59
def prefixEnd_519315 : Nat := 4983230072969 + 3 ^ 40 * 519315 * 2
def baseEnd_519315 : Nat := 177772137393160607582813

theorem tailTrace_519315 : CollatzResearch.WordTrace tailWord_519315 prefixEnd_519315 177772137393160607582813 := by
  unfold tailWord_519315
  simp only [CollatzResearch.WordTrace]
  refine ⟨18940974113617921785983399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12627316075745281190655599 18940974113617921785983399)
  ·
    refine ⟨28411461170426882678975099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18940974113617921785983399 28411461170426882678975099)
    ·
      refine ⟨42617191755640324018462649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28411461170426882678975099 42617191755640324018462649)
      ·
        refine ⟨31962893816730243013846987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42617191755640324018462649 31962893816730243013846987)
        ·
          refine ⟨47944340725095364520770481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31962893816730243013846987 47944340725095364520770481)
          ·
            refine ⟨35958255543821523390577861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47944340725095364520770481 35958255543821523390577861)
            ·
              refine ⟨6742172914466535635733349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35958255543821523390577861 6742172914466535635733349)
              ·
                refine ⟨1264157421462475431700003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6742172914466535635733349 1264157421462475431700003)
                ·
                  refine ⟨1896236132193713147550005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1264157421462475431700003 1896236132193713147550005)
                  ·
                    refine ⟨177772137393160607582813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1896236132193713147550005 177772137393160607582813)
                    ·
                      rfl

theorem cell22_519315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 4, 1, 5].length) (baseStart_519315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_519315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_519315 prefixEnd_519315 := by exact prefixLift 519315
  have htrace : WordTrace (prefixWord ++ tailWord_519315) baseStart_519315 baseEnd_519315 := by
    simpa [prefixWord, tailWord_519315, baseEnd_519315] using wordTrace_append hprefix tailTrace_519315
  have hstable : (prefixWord ++ tailWord_519315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519315).length < 2 ^ (prefixWord ++ tailWord_519315).sum := by decide
  have hdescent : baseEnd_519315 < baseStart_519315 := by decide
  rcases family_descends (prefixWord ++ tailWord_519315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519317 : List Nat := [1, 3, 2, 1, 1, 1, 2, 7, 4]
def baseStart_519317 : Nat := 118140960795 + 519317 * 2 ^ 59
def prefixEnd_519317 : Nat := 4983230072969 + 3 ^ 40 * 519317 * 2
def baseEnd_519317 : Nat := 59257607344677756344269

theorem tailTrace_519317 : CollatzResearch.WordTrace tailWord_519317 prefixEnd_519317 59257607344677756344269 := by
  unfold tailWord_519317
  simp only [CollatzResearch.WordTrace]
  refine ⟨18941047059610676127556205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12627364706407117418370803 18941047059610676127556205)
  ·
    refine ⟨7102892647354003547833577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18941047059610676127556205 7102892647354003547833577)
    ·
      refine ⟨5327169485515502660875183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7102892647354003547833577 5327169485515502660875183)
      ·
        refine ⟨7990754228273253991312775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5327169485515502660875183 7990754228273253991312775)
        ·
          refine ⟨11986131342409880986969163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7990754228273253991312775 11986131342409880986969163)
          ·
            refine ⟨17979197013614821480453745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11986131342409880986969163 17979197013614821480453745)
            ·
              refine ⟨13484397760211116110340309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17979197013614821480453745 13484397760211116110340309)
              ·
                refine ⟨316040572504948033836101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 13484397760211116110340309 316040572504948033836101)
                ·
                  refine ⟨59257607344677756344269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 316040572504948033836101 59257607344677756344269)
                  ·
                    rfl

theorem cell22_519317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 7, 4].length) (baseStart_519317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_519317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_519317 prefixEnd_519317 := by exact prefixLift 519317
  have htrace : WordTrace (prefixWord ++ tailWord_519317) baseStart_519317 baseEnd_519317 := by
    simpa [prefixWord, tailWord_519317, baseEnd_519317] using wordTrace_append hprefix tailTrace_519317
  have hstable : (prefixWord ++ tailWord_519317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519317).length < 2 ^ (prefixWord ++ tailWord_519317).sum := by decide
  have hdescent : baseEnd_519317 < baseStart_519317 := by decide
  rcases family_descends (prefixWord ++ tailWord_519317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519428 : List Nat := [2, 3, 2, 2, 2, 2, 2, 3, 1, 3]
def baseStart_519428 : Nat := 118140960795 + 519428 * 2 ^ 59
def prefixEnd_519428 : Nat := 4983230072969 + 3 ^ 40 * 519428 * 2
def baseEnd_519428 : Nat := 177810819602465979507467

theorem tailTrace_519428 : CollatzResearch.WordTrace tailWord_519428 prefixEnd_519428 177810819602465979507467 := by
  unfold tailWord_519428
  simp only [CollatzResearch.WordTrace]
  refine ⟨9472547781104271042423469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12630063708139028056564625 9472547781104271042423469)
  ·
    refine ⟨3552205417914101640908801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9472547781104271042423469 3552205417914101640908801)
    ·
      refine ⟨2664154063435576230681601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3552205417914101640908801 2664154063435576230681601)
      ·
        refine ⟨1998115547576682173011201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2664154063435576230681601 1998115547576682173011201)
        ·
          refine ⟨1498586660682511629758401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1998115547576682173011201 1498586660682511629758401)
          ·
            refine ⟨1123939995511883722318801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1498586660682511629758401 1123939995511883722318801)
            ·
              refine ⟨842954996633912791739101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1123939995511883722318801 842954996633912791739101)
              ·
                refine ⟨316108123737717296902163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 842954996633912791739101 316108123737717296902163)
                ·
                  refine ⟨474162185606575945353245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 316108123737717296902163 474162185606575945353245)
                  ·
                    refine ⟨177810819602465979507467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 474162185606575945353245 177810819602465979507467)
                    ·
                      rfl

theorem cell22_519428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 3, 1, 3].length) (baseStart_519428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_519428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_519428 prefixEnd_519428 := by exact prefixLift 519428
  have htrace : WordTrace (prefixWord ++ tailWord_519428) baseStart_519428 baseEnd_519428 := by
    simpa [prefixWord, tailWord_519428, baseEnd_519428] using wordTrace_append hprefix tailTrace_519428
  have hstable : (prefixWord ++ tailWord_519428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519428).length < 2 ^ (prefixWord ++ tailWord_519428).sum := by decide
  have hdescent : baseEnd_519428 < baseStart_519428 := by decide
  rcases family_descends (prefixWord ++ tailWord_519428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519452 : List Nat := [2, 2, 3, 1, 1, 1, 3, 3, 6]
def baseStart_519452 : Nat := 118140960795 + 519452 * 2 ^ 59
def prefixEnd_519452 : Nat := 4983230072969 + 3 ^ 40 * 519452 * 2
def baseEnd_519452 : Nat := 59273011764312638969131

theorem tailTrace_519452 : CollatzResearch.WordTrace tailWord_519452 prefixEnd_519452 59273011764312638969131 := by
  unfold tailWord_519452
  simp only [CollatzResearch.WordTrace]
  refine ⟨9472985457060797091860305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12630647276081062789147073 9472985457060797091860305)
  ·
    refine ⟨7104739092795597818895229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9472985457060797091860305 7104739092795597818895229)
    ·
      refine ⟨2664277159798349182085711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7104739092795597818895229 2664277159798349182085711)
      ·
        refine ⟨3996415739697523773128567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2664277159798349182085711 3996415739697523773128567)
        ·
          refine ⟨5994623609546285659692851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3996415739697523773128567 5994623609546285659692851)
          ·
            refine ⟨8991935414319428489539277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5994623609546285659692851 8991935414319428489539277)
            ·
              refine ⟨3371975780369785683577229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8991935414319428489539277 3371975780369785683577229)
              ·
                refine ⟨1264490917638669631341461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3371975780369785683577229 1264490917638669631341461)
                ·
                  refine ⟨59273011764312638969131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1264490917638669631341461 59273011764312638969131)
                  ·
                    rfl

theorem cell22_519452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 3, 6].length) (baseStart_519452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_519452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_519452 prefixEnd_519452 := by exact prefixLift 519452
  have htrace : WordTrace (prefixWord ++ tailWord_519452) baseStart_519452 baseEnd_519452 := by
    simpa [prefixWord, tailWord_519452, baseEnd_519452] using wordTrace_append hprefix tailTrace_519452
  have hstable : (prefixWord ++ tailWord_519452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519452).length < 2 ^ (prefixWord ++ tailWord_519452).sum := by decide
  have hdescent : baseEnd_519452 < baseStart_519452 := by decide
  rcases family_descends (prefixWord ++ tailWord_519452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519482 : List Nat := [3, 1, 1, 1, 4, 1, 1, 3, 1, 6]
def baseStart_519482 : Nat := 118140960795 + 519482 * 2 ^ 59
def prefixEnd_519482 : Nat := 4983230072969 + 3 ^ 40 * 519482 * 2
def baseEnd_519482 : Nat := 177829304906027838657301

theorem tailTrace_519482 : CollatzResearch.WordTrace tailWord_519482 prefixEnd_519482 177829304906027838657301 := by
  unfold tailWord_519482
  simp only [CollatzResearch.WordTrace]
  refine ⟨4736766276003227326828175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12631376736008606204875133 4736766276003227326828175)
  ·
    refine ⟨7105149414004840990242263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4736766276003227326828175 7105149414004840990242263)
    ·
      refine ⟨10657724121007261485363395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7105149414004840990242263 10657724121007261485363395)
      ·
        refine ⟨15986586181510892228045093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10657724121007261485363395 15986586181510892228045093)
        ·
          refine ⟨2997484909033292292758455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15986586181510892228045093 2997484909033292292758455)
          ·
            refine ⟨4496227363549938439137683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2997484909033292292758455 4496227363549938439137683)
            ·
              refine ⟨6744341045324907658706525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4496227363549938439137683 6744341045324907658706525)
              ·
                refine ⟨2529127891996840372014947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6744341045324907658706525 2529127891996840372014947)
                ·
                  refine ⟨3793691837995260558022421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2529127891996840372014947 3793691837995260558022421)
                  ·
                    refine ⟨177829304906027838657301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3793691837995260558022421 177829304906027838657301)
                    ·
                      rfl

theorem cell22_519482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 1, 6].length) (baseStart_519482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_519482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_519482 prefixEnd_519482 := by exact prefixLift 519482
  have htrace : WordTrace (prefixWord ++ tailWord_519482) baseStart_519482 baseEnd_519482 := by
    simpa [prefixWord, tailWord_519482, baseEnd_519482] using wordTrace_append hprefix tailTrace_519482
  have hstable : (prefixWord ++ tailWord_519482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519482).length < 2 ^ (prefixWord ++ tailWord_519482).sum := by decide
  have hdescent : baseEnd_519482 < baseStart_519482 := by decide
  rcases family_descends (prefixWord ++ tailWord_519482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519484 : List Nat := [2, 2, 2, 2, 1, 3, 1, 2, 4, 3]
def baseStart_519484 : Nat := 118140960795 + 519484 * 2 ^ 59
def prefixEnd_519484 : Nat := 4983230072969 + 3 ^ 40 * 519484 * 2
def baseEnd_519484 : Nat := 177829989546900500107295

theorem tailTrace_519484 : CollatzResearch.WordTrace tailWord_519484 prefixEnd_519484 177829989546900500107295 := by
  unfold tailWord_519484
  simp only [CollatzResearch.WordTrace]
  refine ⟨9473569025002831824442753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12631425366670442432590337 9473569025002831824442753)
  ·
    refine ⟨7105176768752123868332065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9473569025002831824442753 7105176768752123868332065)
    ·
      refine ⟨5328882576564092901249049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7105176768752123868332065 5328882576564092901249049)
      ·
        refine ⟨3996661932423069675936787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5328882576564092901249049 3996661932423069675936787)
        ·
          refine ⟨5994992898634604513905181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3996661932423069675936787 5994992898634604513905181)
          ·
            refine ⟨2248122336987976692714443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5994992898634604513905181 2248122336987976692714443)
            ·
              refine ⟨3372183505481965039071665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2248122336987976692714443 3372183505481965039071665)
              ·
                refine ⟨2529137629111473779303749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3372183505481965039071665 2529137629111473779303749)
                ·
                  refine ⟨474213305458401333619453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2529137629111473779303749 474213305458401333619453)
                  ·
                    refine ⟨177829989546900500107295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 474213305458401333619453 177829989546900500107295)
                    ·
                      rfl

theorem cell22_519484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 4, 3].length) (baseStart_519484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_519484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_519484 prefixEnd_519484 := by exact prefixLift 519484
  have htrace : WordTrace (prefixWord ++ tailWord_519484) baseStart_519484 baseEnd_519484 := by
    simpa [prefixWord, tailWord_519484, baseEnd_519484] using wordTrace_append hprefix tailTrace_519484
  have hstable : (prefixWord ++ tailWord_519484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519484).length < 2 ^ (prefixWord ++ tailWord_519484).sum := by decide
  have hdescent : baseEnd_519484 < baseStart_519484 := by decide
  rcases family_descends (prefixWord ++ tailWord_519484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519559 : List Nat := [1, 1, 4, 2, 2, 2, 1, 4, 5]
def baseStart_519559 : Nat := 118140960795 + 519559 * 2 ^ 59
def prefixEnd_519559 : Nat := 4983230072969 + 3 ^ 40 * 519559 * 2
def baseEnd_519559 : Nat := 59285221193208434827355

theorem tailTrace_519559 : CollatzResearch.WordTrace tailWord_519559 prefixEnd_519559 59285221193208434827355 := by
  unfold tailWord_519559
  simp only [CollatzResearch.WordTrace]
  refine ⟨18949873524733951457865731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12633249016489300971910487 18949873524733951457865731)
  ·
    refine ⟨28424810287100927186798597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18949873524733951457865731 28424810287100927186798597)
    ·
      refine ⟨5329651928831423847524737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28424810287100927186798597 5329651928831423847524737)
      ·
        refine ⟨3997238946623567885643553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5329651928831423847524737 3997238946623567885643553)
        ·
          refine ⟨2997929209967675914232665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3997238946623567885643553 2997929209967675914232665)
          ·
            refine ⟨2248446907475756935674499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2997929209967675914232665 2248446907475756935674499)
            ·
              refine ⟨3372670361213635403511749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2248446907475756935674499 3372670361213635403511749)
              ·
                refine ⟨632375692727556638158453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3372670361213635403511749 632375692727556638158453)
                ·
                  refine ⟨59285221193208434827355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 632375692727556638158453 59285221193208434827355)
                  ·
                    rfl

theorem cell22_519559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 4, 5].length) (baseStart_519559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_519559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_519559 prefixEnd_519559 := by exact prefixLift 519559
  have htrace : WordTrace (prefixWord ++ tailWord_519559) baseStart_519559 baseEnd_519559 := by
    simpa [prefixWord, tailWord_519559, baseEnd_519559] using wordTrace_append hprefix tailTrace_519559
  have hstable : (prefixWord ++ tailWord_519559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519559).length < 2 ^ (prefixWord ++ tailWord_519559).sum := by decide
  have hdescent : baseEnd_519559 < baseStart_519559 := by decide
  rcases family_descends (prefixWord ++ tailWord_519559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519649 : List Nat := [1, 2, 3, 1, 2, 4, 1, 8]
def baseStart_519649 : Nat := 118140960795 + 519649 * 2 ^ 59
def prefixEnd_519649 : Nat := 4983230072969 + 3 ^ 40 * 519649 * 2
def baseEnd_519649 : Nat := 19765163602099452192421

theorem tailTrace_519649 : CollatzResearch.WordTrace tailWord_519649 prefixEnd_519649 19765163602099452192421 := by
  unfold tailWord_519649
  simp only [CollatzResearch.WordTrace]
  refine ⟨18953156094407896828642001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12635437396271931219094667 18953156094407896828642001)
  ·
    refine ⟨14214867070805922621481501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18953156094407896828642001 14214867070805922621481501)
    ·
      refine ⟨5330575151552220983055563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14214867070805922621481501 5330575151552220983055563)
      ·
        refine ⟨7995862727328331474583345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5330575151552220983055563 7995862727328331474583345)
        ·
          refine ⟨5996897045496248605937509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7995862727328331474583345 5996897045496248605937509)
          ·
            refine ⟨1124418196030546613613283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5996897045496248605937509 1124418196030546613613283)
            ·
              refine ⟨1686627294045819920419925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1124418196030546613613283 1686627294045819920419925)
              ·
                refine ⟨19765163602099452192421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1686627294045819920419925 19765163602099452192421)
                ·
                  rfl

theorem cell22_519649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 8].length) (baseStart_519649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_519649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_519649 prefixEnd_519649 := by exact prefixLift 519649
  have htrace : WordTrace (prefixWord ++ tailWord_519649) baseStart_519649 baseEnd_519649 := by
    simpa [prefixWord, tailWord_519649, baseEnd_519649] using wordTrace_append hprefix tailTrace_519649
  have hstable : (prefixWord ++ tailWord_519649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519649).length < 2 ^ (prefixWord ++ tailWord_519649).sum := by decide
  have hdescent : baseEnd_519649 < baseStart_519649 := by decide
  rcases family_descends (prefixWord ++ tailWord_519649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519666 : List Nat := [3, 2, 1, 4, 1, 3, 8]
def baseStart_519666 : Nat := 118140960795 + 519666 * 2 ^ 59
def prefixEnd_519666 : Nat := 4983230072969 + 3 ^ 40 * 519666 * 2
def baseEnd_519666 : Nat := 6588603402456025631731

theorem tailTrace_519666 : CollatzResearch.WordTrace tailWord_519666 prefixEnd_519666 6588603402456025631731 := by
  unfold tailWord_519666
  simp only [CollatzResearch.WordTrace]
  refine ⟨4738444033836577183002713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12635850756897539154673901 4738444033836577183002713)
  ·
    refine ⟨3553833025377432887252035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4738444033836577183002713 3553833025377432887252035)
    ·
      refine ⟨5330749538066149330878053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3553833025377432887252035 5330749538066149330878053)
      ·
        refine ⟨999515538387402999539635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5330749538066149330878053 999515538387402999539635)
        ·
          refine ⟨1499273307581104499309453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 999515538387402999539635 1499273307581104499309453)
          ·
            refine ⟨562227490342914187241045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1499273307581104499309453 562227490342914187241045)
            ·
              refine ⟨6588603402456025631731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 562227490342914187241045 6588603402456025631731)
              ·
                rfl

theorem cell22_519666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 8].length) (baseStart_519666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_519666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_519666 prefixEnd_519666 := by exact prefixLift 519666
  have htrace : WordTrace (prefixWord ++ tailWord_519666) baseStart_519666 baseEnd_519666 := by
    simpa [prefixWord, tailWord_519666, baseEnd_519666] using wordTrace_append hprefix tailTrace_519666
  have hstable : (prefixWord ++ tailWord_519666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519666).length < 2 ^ (prefixWord ++ tailWord_519666).sum := by decide
  have hdescent : baseEnd_519666 < baseStart_519666 := by decide
  rcases family_descends (prefixWord ++ tailWord_519666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519756 : List Nat := [2, 2, 1, 3, 1, 4, 1, 2, 6]
def baseStart_519756 : Nat := 118140960795 + 519756 * 2 ^ 59
def prefixEnd_519756 : Nat := 4983230072969 + 3 ^ 40 * 519756 * 2
def baseEnd_519756 : Nat := 59307700235194152435487

theorem tailTrace_519756 : CollatzResearch.WordTrace tailWord_519756 prefixEnd_519756 59307700235194152435487 := by
  unfold tailWord_519756
  simp only [CollatzResearch.WordTrace]
  refine ⟨9478529352510127051393561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12638039136680169401858081 9478529352510127051393561)
  ·
    refine ⟨7108897014382595288545171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9478529352510127051393561 7108897014382595288545171)
    ·
      refine ⟨10663345521573892932817757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7108897014382595288545171 10663345521573892932817757)
      ·
        refine ⟨3998754570590209849806659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10663345521573892932817757 3998754570590209849806659)
        ·
          refine ⟨5998131855885314774709989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3998754570590209849806659 5998131855885314774709989)
          ·
            refine ⟨1124649722978496520258123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5998131855885314774709989 1124649722978496520258123)
            ·
              refine ⟨1686974584467744780387185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1124649722978496520258123 1686974584467744780387185)
              ·
                refine ⟨1265230938350808585290389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1686974584467744780387185 1265230938350808585290389)
                ·
                  refine ⟨59307700235194152435487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1265230938350808585290389 59307700235194152435487)
                  ·
                    rfl

theorem cell22_519756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 2, 6].length) (baseStart_519756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_519756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_519756 prefixEnd_519756 := by exact prefixLift 519756
  have htrace : WordTrace (prefixWord ++ tailWord_519756) baseStart_519756 baseEnd_519756 := by
    simpa [prefixWord, tailWord_519756, baseEnd_519756] using wordTrace_append hprefix tailTrace_519756
  have hstable : (prefixWord ++ tailWord_519756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519756).length < 2 ^ (prefixWord ++ tailWord_519756).sum := by decide
  have hdescent : baseEnd_519756 < baseStart_519756 := by decide
  rcases family_descends (prefixWord ++ tailWord_519756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519766 : List Nat := [5, 2, 2, 2, 1, 1, 2, 3, 1, 3]
def baseStart_519766 : Nat := 118140960795 + 519766 * 2 ^ 59
def prefixEnd_519766 : Nat := 4983230072969 + 3 ^ 40 * 519766 * 2
def baseEnd_519766 : Nat := 177926523909945764556431

theorem tailTrace_519766 : CollatzResearch.WordTrace tailWord_519766 prefixEnd_519766 177926523909945764556431 := by
  unfold tailWord_519766
  simp only [CollatzResearch.WordTrace]
  refine ⟨1184838964686501613165697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12638282289989350540434101 1184838964686501613165697)
  ·
    refine ⟨888629223514876209874273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1184838964686501613165697 888629223514876209874273)
    ·
      refine ⟨666471917636157157405705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 888629223514876209874273 666471917636157157405705)
      ·
        refine ⟨499853938227117868054279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 666471917636157157405705 499853938227117868054279)
        ·
          refine ⟨749780907340676802081419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 499853938227117868054279 749780907340676802081419)
          ·
            refine ⟨1124671361011015203122129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 749780907340676802081419 1124671361011015203122129)
            ·
              refine ⟨843503520758261402341597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1124671361011015203122129 843503520758261402341597)
              ·
                refine ⟨316313820284348025878099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 843503520758261402341597 316313820284348025878099)
                ·
                  refine ⟨474470730426522038817149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 316313820284348025878099 474470730426522038817149)
                  ·
                    refine ⟨177926523909945764556431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 474470730426522038817149 177926523909945764556431)
                    ·
                      rfl

theorem cell22_519766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_519766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_519766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_519766 prefixEnd_519766 := by exact prefixLift 519766
  have htrace : WordTrace (prefixWord ++ tailWord_519766) baseStart_519766 baseEnd_519766 := by
    simpa [prefixWord, tailWord_519766, baseEnd_519766] using wordTrace_append hprefix tailTrace_519766
  have hstable : (prefixWord ++ tailWord_519766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519766).length < 2 ^ (prefixWord ++ tailWord_519766).sum := by decide
  have hdescent : baseEnd_519766 < baseStart_519766 := by decide
  rcases family_descends (prefixWord ++ tailWord_519766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519818 : List Nat := [3, 1, 2, 3, 2, 1, 4, 6]
def baseStart_519818 : Nat := 118140960795 + 519818 * 2 ^ 59
def prefixEnd_519818 : Nat := 4983230072969 + 3 ^ 40 * 519818 * 2
def baseEnd_519818 : Nat := 19771591619181662472919

theorem tailTrace_519818 : CollatzResearch.WordTrace tailWord_519818 prefixEnd_519818 19771591619181662472919 := by
  unfold tailWord_519818
  simp only [CollatzResearch.WordTrace]
  refine ⟨4739830007698909672886027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12639546687197092461029405 4739830007698909672886027)
  ·
    refine ⟨7109745011548364509329041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4739830007698909672886027 7109745011548364509329041)
    ·
      refine ⟨5332308758661273381996781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7109745011548364509329041 5332308758661273381996781)
      ·
        refine ⟨1999615784497977518248793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5332308758661273381996781 1999615784497977518248793)
        ·
          refine ⟨1499711838373483138686595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1999615784497977518248793 1499711838373483138686595)
          ·
            refine ⟨2249567757560224708029893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1499711838373483138686595 2249567757560224708029893)
            ·
              refine ⟨421793954542542132755605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2249567757560224708029893 421793954542542132755605)
              ·
                refine ⟨19771591619181662472919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 421793954542542132755605 19771591619181662472919)
                ·
                  rfl

theorem cell22_519818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 4, 6].length) (baseStart_519818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_519818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_519818 prefixEnd_519818 := by exact prefixLift 519818
  have htrace : WordTrace (prefixWord ++ tailWord_519818) baseStart_519818 baseEnd_519818 := by
    simpa [prefixWord, tailWord_519818, baseEnd_519818] using wordTrace_append hprefix tailTrace_519818
  have hstable : (prefixWord ++ tailWord_519818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519818).length < 2 ^ (prefixWord ++ tailWord_519818).sum := by decide
  have hdescent : baseEnd_519818 < baseStart_519818 := by decide
  rcases family_descends (prefixWord ++ tailWord_519818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519863 : List Nat := [1, 1, 3, 1, 5, 2, 1, 3, 5]
def baseStart_519863 : Nat := 118140960795 + 519863 * 2 ^ 59
def prefixEnd_519863 : Nat := 4983230072969 + 3 ^ 40 * 519863 * 2
def baseEnd_519863 : Nat := 59319909664089948293711

theorem tailTrace_519863 : CollatzResearch.WordTrace tailWord_519863 prefixEnd_519863 59319909664089948293711 := by
  unfold tailWord_519863
  simp only [CollatzResearch.WordTrace]
  refine ⟨18960961315632611376932243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12640640877088407584621495 18960961315632611376932243)
  ·
    refine ⟨28441441973448917065398365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18960961315632611376932243 28441441973448917065398365)
    ·
      refine ⟨10665540740043343899524387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28441441973448917065398365 10665540740043343899524387)
      ·
        refine ⟨15998311110065015849286581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10665540740043343899524387 15998311110065015849286581)
        ·
          refine ⟨1499841666568595235870617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15998311110065015849286581 1499841666568595235870617)
          ·
            refine ⟨1124881249926446426902963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1499841666568595235870617 1124881249926446426902963)
            ·
              refine ⟨1687321874889669640354445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1124881249926446426902963 1687321874889669640354445)
              ·
                refine ⟨632745703083626115132917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1687321874889669640354445 632745703083626115132917)
                ·
                  refine ⟨59319909664089948293711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 632745703083626115132917 59319909664089948293711)
                  ·
                    rfl

theorem cell22_519863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 3, 5].length) (baseStart_519863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_519863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_519863 prefixEnd_519863 := by exact prefixLift 519863
  have htrace : WordTrace (prefixWord ++ tailWord_519863) baseStart_519863 baseEnd_519863 := by
    simpa [prefixWord, tailWord_519863, baseEnd_519863] using wordTrace_append hprefix tailTrace_519863
  have hstable : (prefixWord ++ tailWord_519863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519863).length < 2 ^ (prefixWord ++ tailWord_519863).sum := by decide
  have hdescent : baseEnd_519863 < baseStart_519863 := by decide
  rcases family_descends (prefixWord ++ tailWord_519863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519957 : List Nat := [1, 3, 2, 1, 2, 5, 1, 2, 2, 3]
def baseStart_519957 : Nat := 118140960795 + 519957 * 2 ^ 59
def prefixEnd_519957 : Nat := 4983230072969 + 3 ^ 40 * 519957 * 2
def baseEnd_519957 : Nat := 177991907113284933030845

theorem tailTrace_519957 : CollatzResearch.WordTrace tailWord_519957 prefixEnd_519957 177991907113284933030845 := by
  unfold tailWord_519957
  simp only [CollatzResearch.WordTrace]
  refine ⟨18964389777292065430854125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12642926518194710287236083 18964389777292065430854125)
  ·
    refine ⟨7111646166484524536570297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18964389777292065430854125 7111646166484524536570297)
    ·
      refine ⟨5333734624863393402427723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7111646166484524536570297 5333734624863393402427723)
      ·
        refine ⟨8000601937295090103641585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5333734624863393402427723 8000601937295090103641585)
        ·
          refine ⟨6000451452971317577731189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8000601937295090103641585 6000451452971317577731189)
          ·
            refine ⟨562542323716061022912299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6000451452971317577731189 562542323716061022912299)
            ·
              refine ⟨843813485574091534368449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 562542323716061022912299 843813485574091534368449)
              ·
                refine ⟨632860114180568650776337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 843813485574091534368449 632860114180568650776337)
                ·
                  refine ⟨474645085635426488082253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 632860114180568650776337 474645085635426488082253)
                  ·
                    refine ⟨177991907113284933030845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 474645085635426488082253 177991907113284933030845)
                    ·
                      rfl

theorem cell22_519957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 2, 2, 3].length) (baseStart_519957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_519957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_519957 prefixEnd_519957 := by exact prefixLift 519957
  have htrace : WordTrace (prefixWord ++ tailWord_519957) baseStart_519957 baseEnd_519957 := by
    simpa [prefixWord, tailWord_519957, baseEnd_519957] using wordTrace_append hprefix tailTrace_519957
  have hstable : (prefixWord ++ tailWord_519957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519957).length < 2 ^ (prefixWord ++ tailWord_519957).sum := by decide
  have hdescent : baseEnd_519957 < baseStart_519957 := by decide
  rcases family_descends (prefixWord ++ tailWord_519957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519985 : List Nat := [1, 2, 2, 3, 2, 2, 2, 2, 3, 3]
def baseStart_519985 : Nat := 118140960795 + 519985 * 2 ^ 59
def prefixEnd_519985 : Nat := 4983230072969 + 3 ^ 40 * 519985 * 2
def baseEnd_519985 : Nat := 178001492085502193330759

theorem tailTrace_519985 : CollatzResearch.WordTrace tailWord_519985 prefixEnd_519985 178001492085502193330759 := by
  unfold tailWord_519985
  simp only [CollatzResearch.WordTrace]
  refine ⟨18965411021190626212873409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12643607347460417475248939 18965411021190626212873409)
  ·
    refine ⟨14224058265892969659655057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18965411021190626212873409 14224058265892969659655057)
    ·
      refine ⟨10668043699419727244741293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14224058265892969659655057 10668043699419727244741293)
      ·
        refine ⟨4000516387282397716777985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10668043699419727244741293 4000516387282397716777985)
        ·
          refine ⟨3000387290461798287583489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4000516387282397716777985 3000387290461798287583489)
          ·
            refine ⟨2250290467846348715687617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3000387290461798287583489 2250290467846348715687617)
            ·
              refine ⟨1687717850884761536765713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2250290467846348715687617 1687717850884761536765713)
              ·
                refine ⟨1265788388163571152574285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1687717850884761536765713 1265788388163571152574285)
                ·
                  refine ⟨474670645561339182215357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1265788388163571152574285 474670645561339182215357)
                  ·
                    refine ⟨178001492085502193330759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 474670645561339182215357 178001492085502193330759)
                    ·
                      rfl

theorem cell22_519985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 2, 3, 3].length) (baseStart_519985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_519985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_519985 prefixEnd_519985 := by exact prefixLift 519985
  have htrace : WordTrace (prefixWord ++ tailWord_519985) baseStart_519985 baseEnd_519985 := by
    simpa [prefixWord, tailWord_519985, baseEnd_519985] using wordTrace_append hprefix tailTrace_519985
  have hstable : (prefixWord ++ tailWord_519985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519985).length < 2 ^ (prefixWord ++ tailWord_519985).sum := by decide
  have hdescent : baseEnd_519985 < baseStart_519985 := by decide
  rcases family_descends (prefixWord ++ tailWord_519985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519987 : List Nat := [1, 1, 1, 2, 8, 1, 2, 6]
def baseStart_519987 : Nat := 118140960795 + 519987 * 2 ^ 59
def prefixEnd_519987 : Nat := 4983230072969 + 3 ^ 40 * 519987 * 2
def baseEnd_519987 : Nat := 19778019636263872753417

theorem tailTrace_519987 : CollatzResearch.WordTrace tailWord_519987 prefixEnd_519987 19778019636263872753417 := by
  unfold tailWord_519987
  simp only [CollatzResearch.WordTrace]
  refine ⟨18965483967183380554446215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12643655978122253702964143 18965483967183380554446215)
  ·
    refine ⟨28448225950775070831669323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18965483967183380554446215 28448225950775070831669323)
    ·
      refine ⟨42672338926162606247503985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28448225950775070831669323 42672338926162606247503985)
      ·
        refine ⟨32004254194621954685627989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42672338926162606247503985 32004254194621954685627989)
        ·
          refine ⟨375049853843226031472203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 32004254194621954685627989 375049853843226031472203)
          ·
            refine ⟨562574780764839047208305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375049853843226031472203 562574780764839047208305)
            ·
              refine ⟨421931085573629285406229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 562574780764839047208305 421931085573629285406229)
              ·
                refine ⟨19778019636263872753417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 421931085573629285406229 19778019636263872753417)
                ·
                  rfl

theorem cell22_519987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 2, 6].length) (baseStart_519987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_519987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_519987 prefixEnd_519987 := by exact prefixLift 519987
  have htrace : WordTrace (prefixWord ++ tailWord_519987) baseStart_519987 baseEnd_519987 := by
    simpa [prefixWord, tailWord_519987, baseEnd_519987] using wordTrace_append hprefix tailTrace_519987
  have hstable : (prefixWord ++ tailWord_519987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519987).length < 2 ^ (prefixWord ++ tailWord_519987).sum := by decide
  have hdescent : baseEnd_519987 < baseStart_519987 := by decide
  rcases family_descends (prefixWord ++ tailWord_519987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520032 : List Nat := [2, 1, 1, 3, 3, 4, 2, 1, 5]
def baseStart_520032 : Nat := 118140960795 + 520032 * 2 ^ 59
def prefixEnd_520032 : Nat := 4983230072969 + 3 ^ 40 * 520032 * 2
def baseEnd_520032 : Nat := 59339193715336579135205

theorem tailTrace_520032 : CollatzResearch.WordTrace tailWord_520032 prefixEnd_520032 59339193715336579135205 := by
  unfold tailWord_520032
  simp only [CollatzResearch.WordTrace]
  refine ⟨9483562626010176619917175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12644750168013568826556233 9483562626010176619917175)
  ·
    refine ⟨14225343939015264929875763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9483562626010176619917175 14225343939015264929875763)
    ·
      refine ⟨21338015908522897394813645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14225343939015264929875763 21338015908522897394813645)
      ·
        refine ⟨8001755965696086523055117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21338015908522897394813645 8001755965696086523055117)
        ·
          refine ⟨3000658487136032446145669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8001755965696086523055117 3000658487136032446145669)
          ·
            refine ⟨562623466338006083652313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3000658487136032446145669 562623466338006083652313)
            ·
              refine ⟨421967599753504562739235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 562623466338006083652313 421967599753504562739235)
              ·
                refine ⟨632951399630256844108853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 421967599753504562739235 632951399630256844108853)
                ·
                  refine ⟨59339193715336579135205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 632951399630256844108853 59339193715336579135205)
                  ·
                    rfl

theorem cell22_520032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 2, 1, 5].length) (baseStart_520032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_520032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_520032 prefixEnd_520032 := by exact prefixLift 520032
  have htrace : WordTrace (prefixWord ++ tailWord_520032) baseStart_520032 baseEnd_520032 := by
    simpa [prefixWord, tailWord_520032, baseEnd_520032] using wordTrace_append hprefix tailTrace_520032
  have hstable : (prefixWord ++ tailWord_520032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520032).length < 2 ^ (prefixWord ++ tailWord_520032).sum := by decide
  have hdescent : baseEnd_520032 < baseStart_520032 := by decide
  rcases family_descends (prefixWord ++ tailWord_520032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520058 : List Nat := [3, 1, 1, 1, 1, 1, 5, 1, 3, 5]
def baseStart_520058 : Nat := 118140960795 + 520058 * 2 ^ 59
def prefixEnd_520058 : Nat := 4983230072969 + 3 ^ 40 * 520058 * 2
def baseEnd_520058 : Nat := 178026481477354336255535

theorem tailTrace_520058 : CollatzResearch.WordTrace tailWord_520058 prefixEnd_520058 178026481477354336255535 := by
  unfold tailWord_520058
  simp only [CollatzResearch.WordTrace]
  refine ⟨4742018387481539920070207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12645382366617439786853885 4742018387481539920070207)
  ·
    refine ⟨7113027581222309880105311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4742018387481539920070207 7113027581222309880105311)
    ·
      refine ⟨10669541371833464820157967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7113027581222309880105311 10669541371833464820157967)
      ·
        refine ⟨16004312057750197230236951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10669541371833464820157967 16004312057750197230236951)
        ·
          refine ⟨24006468086625295845355427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16004312057750197230236951 24006468086625295845355427)
          ·
            refine ⟨36009702129937943768033141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24006468086625295845355427 36009702129937943768033141)
            ·
              refine ⟨3375909574681682228253107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36009702129937943768033141 3375909574681682228253107)
              ·
                refine ⟨5063864362022523342379661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3375909574681682228253107 5063864362022523342379661)
                ·
                  refine ⟨1898949135758446253392373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5063864362022523342379661 1898949135758446253392373)
                  ·
                    refine ⟨178026481477354336255535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1898949135758446253392373 178026481477354336255535)
                    ·
                      rfl

theorem cell22_520058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 3, 5].length) (baseStart_520058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_520058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_520058 prefixEnd_520058 := by exact prefixLift 520058
  have htrace : WordTrace (prefixWord ++ tailWord_520058) baseStart_520058 baseEnd_520058 := by
    simpa [prefixWord, tailWord_520058, baseEnd_520058] using wordTrace_append hprefix tailTrace_520058
  have hstable : (prefixWord ++ tailWord_520058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520058).length < 2 ^ (prefixWord ++ tailWord_520058).sum := by decide
  have hdescent : baseEnd_520058 < baseStart_520058 := by decide
  rcases family_descends (prefixWord ++ tailWord_520058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520092 : List Nat := [2, 2, 3, 3, 1, 2, 2, 1, 1, 5]
def baseStart_520092 : Nat := 118140960795 + 520092 * 2 ^ 59
def prefixEnd_520092 : Nat := 4983230072969 + 3 ^ 40 * 520092 * 2
def baseEnd_520092 : Nat := 178038120372189580905431

theorem tailTrace_520092 : CollatzResearch.WordTrace tailWord_520092 prefixEnd_520092 178038120372189580905431 := by
  unfold tailWord_520092
  simp only [CollatzResearch.WordTrace]
  refine ⟨9484656815901491743509265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12646209087868655658012353 9484656815901491743509265)
  ·
    refine ⟨7113492611926118807631949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9484656815901491743509265 7113492611926118807631949)
    ·
      refine ⟨2667559729472294552861981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7113492611926118807631949 2667559729472294552861981)
      ·
        refine ⟨1000334898552110457323243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2667559729472294552861981 1000334898552110457323243)
        ·
          refine ⟨1500502347828165685984865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1000334898552110457323243 1500502347828165685984865)
          ·
            refine ⟨1125376760871124264488649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1500502347828165685984865 1125376760871124264488649)
            ·
              refine ⟨844032570653343198366487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1125376760871124264488649 844032570653343198366487)
              ·
                refine ⟨1266048855980014797549731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 844032570653343198366487 1266048855980014797549731)
                ·
                  refine ⟨1899073283970022196324597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1266048855980014797549731 1899073283970022196324597)
                  ·
                    refine ⟨178038120372189580905431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1899073283970022196324597 178038120372189580905431)
                    ·
                      rfl

theorem cell22_520092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_520092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_520092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_520092 prefixEnd_520092 := by exact prefixLift 520092
  have htrace : WordTrace (prefixWord ++ tailWord_520092) baseStart_520092 baseEnd_520092 := by
    simpa [prefixWord, tailWord_520092, baseEnd_520092] using wordTrace_append hprefix tailTrace_520092
  have hstable : (prefixWord ++ tailWord_520092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520092).length < 2 ^ (prefixWord ++ tailWord_520092).sum := by decide
  have hdescent : baseEnd_520092 < baseStart_520092 := by decide
  rcases family_descends (prefixWord ++ tailWord_520092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520094 : List Nat := [4, 3, 1, 3, 1, 1, 1, 2, 6]
def baseStart_520094 : Nat := 118140960795 + 520094 * 2 ^ 59
def prefixEnd_520094 : Nat := 4983230072969 + 3 ^ 40 * 520094 * 2
def baseEnd_520094 : Nat := 59346268337687414118475

theorem tailTrace_520094 : CollatzResearch.WordTrace tailWord_520094 prefixEnd_520094 59346268337687414118475 := by
  unfold tailWord_520094
  simp only [CollatzResearch.WordTrace]
  refine ⟨2371173322224467228573917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12646257718530491885727557 2371173322224467228573917)
  ·
    refine ⟨889189995834175210715219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2371173322224467228573917 889189995834175210715219)
    ·
      refine ⟨1333784993751262816072829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 889189995834175210715219 1333784993751262816072829)
      ·
        refine ⟨500169372656723556027311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1333784993751262816072829 500169372656723556027311)
        ·
          refine ⟨750254058985085334040967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 500169372656723556027311 750254058985085334040967)
          ·
            refine ⟨1125381088477628001061451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 750254058985085334040967 1125381088477628001061451)
            ·
              refine ⟨1688071632716442001592177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1125381088477628001061451 1688071632716442001592177)
              ·
                refine ⟨1266053724537331501194133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1688071632716442001592177 1266053724537331501194133)
                ·
                  refine ⟨59346268337687414118475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1266053724537331501194133 59346268337687414118475)
                  ·
                    rfl

theorem cell22_520094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_520094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_520094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_520094 prefixEnd_520094 := by exact prefixLift 520094
  have htrace : WordTrace (prefixWord ++ tailWord_520094) baseStart_520094 baseEnd_520094 := by
    simpa [prefixWord, tailWord_520094, baseEnd_520094] using wordTrace_append hprefix tailTrace_520094
  have hstable : (prefixWord ++ tailWord_520094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520094).length < 2 ^ (prefixWord ++ tailWord_520094).sum := by decide
  have hdescent : baseEnd_520094 < baseStart_520094 := by decide
  rcases family_descends (prefixWord ++ tailWord_520094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520120 : List Nat := [2, 1, 2, 1, 2, 3, 1, 2, 5, 3]
def baseStart_520120 : Nat := 118140960795 + 520120 * 2 ^ 59
def prefixEnd_520120 : Nat := 4983230072969 + 3 ^ 40 * 520120 * 2
def baseEnd_520120 : Nat := 178047705344406841205345

theorem tailTrace_520120 : CollatzResearch.WordTrace tailWord_520120 prefixEnd_520120 178047705344406841205345 := by
  unfold tailWord_520120
  simp only [CollatzResearch.WordTrace]
  refine ⟨9485167437850772134518907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12646889917134362846025209 9485167437850772134518907)
  ·
    refine ⟨14227751156776158201778361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9485167437850772134518907 14227751156776158201778361)
    ·
      refine ⟨10670813367582118651333771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14227751156776158201778361 10670813367582118651333771)
      ·
        refine ⟨16006220051373177977000657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10670813367582118651333771 16006220051373177977000657)
        ·
          refine ⟨12004665038529883482750493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16006220051373177977000657 12004665038529883482750493)
          ·
            refine ⟨4501749389448706306031435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12004665038529883482750493 4501749389448706306031435)
            ·
              refine ⟨6752624084173059459047153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4501749389448706306031435 6752624084173059459047153)
              ·
                refine ⟨5064468063129794594285365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6752624084173059459047153 5064468063129794594285365)
                ·
                  refine ⟨474793880918418243214253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5064468063129794594285365 474793880918418243214253)
                  ·
                    refine ⟨178047705344406841205345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 474793880918418243214253 178047705344406841205345)
                    ·
                      rfl

theorem cell22_520120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 5, 3].length) (baseStart_520120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_520120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_520120 prefixEnd_520120 := by exact prefixLift 520120
  have htrace : WordTrace (prefixWord ++ tailWord_520120) baseStart_520120 baseEnd_520120 := by
    simpa [prefixWord, tailWord_520120, baseEnd_520120] using wordTrace_append hprefix tailTrace_520120
  have hstable : (prefixWord ++ tailWord_520120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520120).length < 2 ^ (prefixWord ++ tailWord_520120).sum := by decide
  have hdescent : baseEnd_520120 < baseStart_520120 := by decide
  rcases family_descends (prefixWord ++ tailWord_520120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520242 : List Nat := [3, 2, 1, 1, 2, 3, 2, 2, 2, 4]
def baseStart_520242 : Nat := 118140960795 + 520242 * 2 ^ 59
def prefixEnd_520242 : Nat := 4983230072969 + 3 ^ 40 * 520242 * 2
def baseEnd_520242 : Nat := 178089468437639189654971

theorem tailTrace_520242 : CollatzResearch.WordTrace tailWord_520242 prefixEnd_520242 178089468437639189654971 := by
  unfold tailWord_520242
  simp only [CollatzResearch.WordTrace]
  refine ⟨4743696145314889776244745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12649856387506372736652653 4743696145314889776244745)
  ·
    refine ⟨3557772108986167332183559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4743696145314889776244745 3557772108986167332183559)
    ·
      refine ⟨5336658163479250998275339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3557772108986167332183559 5336658163479250998275339)
      ·
        refine ⟨8004987245218876497413009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5336658163479250998275339 8004987245218876497413009)
        ·
          refine ⟨6003740433914157373059757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8004987245218876497413009 6003740433914157373059757)
          ·
            refine ⟨2251402662717809014897409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6003740433914157373059757 2251402662717809014897409)
            ·
              refine ⟨1688551997038356761173057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2251402662717809014897409 1688551997038356761173057)
              ·
                refine ⟨1266413997778767570879793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1688551997038356761173057 1266413997778767570879793)
                ·
                  refine ⟨949810498334075678159845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1266413997778767570879793 949810498334075678159845)
                  ·
                    refine ⟨178089468437639189654971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 949810498334075678159845 178089468437639189654971)
                    ·
                      rfl

theorem cell22_520242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 2, 2, 4].length) (baseStart_520242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_520242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_520242 prefixEnd_520242 := by exact prefixLift 520242
  have htrace : WordTrace (prefixWord ++ tailWord_520242) baseStart_520242 baseEnd_520242 := by
    simpa [prefixWord, tailWord_520242, baseEnd_520242] using wordTrace_append hprefix tailTrace_520242
  have hstable : (prefixWord ++ tailWord_520242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520242).length < 2 ^ (prefixWord ++ tailWord_520242).sum := by decide
  have hdescent : baseEnd_520242 < baseStart_520242 := by decide
  rcases family_descends (prefixWord ++ tailWord_520242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520257 : List Nat := [1, 2, 5, 1, 2, 1, 3, 7]
def baseStart_520257 : Nat := 118140960795 + 520257 * 2 ^ 59
def prefixEnd_520257 : Nat := 4983230072969 + 3 ^ 40 * 520257 * 2
def baseEnd_520257 : Nat := 19788289249353794503325

theorem tailTrace_520257 : CollatzResearch.WordTrace tailWord_520257 prefixEnd_520257 19788289249353794503325 := by
  unfold tailWord_520257
  simp only [CollatzResearch.WordTrace]
  refine ⟨18975331676205216666775025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12650221117470144444516683 18975331676205216666775025)
  ·
    refine ⟨14231498757153912500081269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18975331676205216666775025 14231498757153912500081269)
    ·
      refine ⟨1334203008483179296882619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14231498757153912500081269 1334203008483179296882619)
      ·
        refine ⟨2001304512724768945323929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1334203008483179296882619 2001304512724768945323929)
        ·
          refine ⟨1500978384543576708992947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2001304512724768945323929 1500978384543576708992947)
          ·
            refine ⟨2251467576815365063489421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1500978384543576708992947 2251467576815365063489421)
            ·
              refine ⟨844300341305761898808533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2251467576815365063489421 844300341305761898808533)
              ·
                refine ⟨19788289249353794503325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 844300341305761898808533 19788289249353794503325)
                ·
                  rfl

theorem cell22_520257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 7].length) (baseStart_520257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_520257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_520257 prefixEnd_520257 := by exact prefixLift 520257
  have htrace : WordTrace (prefixWord ++ tailWord_520257) baseStart_520257 baseEnd_520257 := by
    simpa [prefixWord, tailWord_520257, baseEnd_520257] using wordTrace_append hprefix tailTrace_520257
  have hstable : (prefixWord ++ tailWord_520257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520257).length < 2 ^ (prefixWord ++ tailWord_520257).sum := by decide
  have hdescent : baseEnd_520257 < baseStart_520257 := by decide
  rcases family_descends (prefixWord ++ tailWord_520257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520274 : List Nat := [3, 2, 2, 1, 4, 1, 3, 6]
def baseStart_520274 : Nat := 118140960795 + 520274 * 2 ^ 59
def prefixEnd_520274 : Nat := 4983230072969 + 3 ^ 40 * 520274 * 2
def baseEnd_520274 : Nat := 19788935854622419206097

theorem tailTrace_520274 : CollatzResearch.WordTrace tailWord_520274 prefixEnd_520274 19788935854622419206097 := by
  unfold tailWord_520274
  simp only [CollatzResearch.WordTrace]
  refine ⟨4743987929285907142535969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12650634478095752380095917 4743987929285907142535969)
  ·
    refine ⟨3557990946964430356901977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4743987929285907142535969 3557990946964430356901977)
    ·
      refine ⟨2668493210223322767676483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3557990946964430356901977 2668493210223322767676483)
      ·
        refine ⟨4002739815334984151514725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2668493210223322767676483 4002739815334984151514725)
        ·
          refine ⟨750513715375309528409011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4002739815334984151514725 750513715375309528409011)
          ·
            refine ⟨1125770573062964292613517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 750513715375309528409011 1125770573062964292613517)
            ·
              refine ⟨422163964898611609730069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1125770573062964292613517 422163964898611609730069)
              ·
                refine ⟨19788935854622419206097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 422163964898611609730069 19788935854622419206097)
                ·
                  rfl

theorem cell22_520274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 3, 6].length) (baseStart_520274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_520274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_520274 prefixEnd_520274 := by exact prefixLift 520274
  have htrace : WordTrace (prefixWord ++ tailWord_520274) baseStart_520274 baseEnd_520274 := by
    simpa [prefixWord, tailWord_520274, baseEnd_520274] using wordTrace_append hprefix tailTrace_520274
  have hstable : (prefixWord ++ tailWord_520274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520274).length < 2 ^ (prefixWord ++ tailWord_520274).sum := by decide
  have hdescent : baseEnd_520274 < baseStart_520274 := by decide
  rcases family_descends (prefixWord ++ tailWord_520274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520302 : List Nat := [4, 1, 2, 2, 1, 1, 3, 1, 7]
def baseStart_520302 : Nat := 118140960795 + 520302 * 2 ^ 59
def prefixEnd_520302 : Nat := 4983230072969 + 3 ^ 40 * 520302 * 2
def baseEnd_520302 : Nat := 59370002554606344384929

theorem tailTrace_520302 : CollatzResearch.WordTrace tailWord_520302 prefixEnd_520302 59370002554606344384929 := by
  unfold tailWord_520302
  simp only [CollatzResearch.WordTrace]
  refine ⟨2372121620130273669020395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12651315307361459568108773 2372121620130273669020395)
  ·
    refine ⟨3558182430195410503530593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2372121620130273669020395 3558182430195410503530593)
    ·
      refine ⟨2668636822646557877647945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3558182430195410503530593 2668636822646557877647945)
      ·
        refine ⟨2001477616984918408235959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2668636822646557877647945 2001477616984918408235959)
        ·
          refine ⟨3002216425477377612353939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2001477616984918408235959 3002216425477377612353939)
          ·
            refine ⟨4503324638216066418530909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3002216425477377612353939 4503324638216066418530909)
            ·
              refine ⟨1688746739331024906949091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4503324638216066418530909 1688746739331024906949091)
              ·
                refine ⟨2533120108996537360423637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1688746739331024906949091 2533120108996537360423637)
                ·
                  refine ⟨59370002554606344384929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2533120108996537360423637 59370002554606344384929)
                  ·
                    rfl

theorem cell22_520302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 7].length) (baseStart_520302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_520302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_520302 prefixEnd_520302 := by exact prefixLift 520302
  have htrace : WordTrace (prefixWord ++ tailWord_520302) baseStart_520302 baseEnd_520302 := by
    simpa [prefixWord, tailWord_520302, baseEnd_520302] using wordTrace_append hprefix tailTrace_520302
  have hstable : (prefixWord ++ tailWord_520302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520302).length < 2 ^ (prefixWord ++ tailWord_520302).sum := by decide
  have hdescent : baseEnd_520302 < baseStart_520302 := by decide
  rcases family_descends (prefixWord ++ tailWord_520302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520306 : List Nat := [3, 2, 1, 2, 2, 2, 2, 4, 1, 3]
def baseStart_520306 : Nat := 118140960795 + 520306 * 2 ^ 59
def prefixEnd_520306 : Nat := 4983230072969 + 3 ^ 40 * 520306 * 2
def baseEnd_520306 : Nat := 178111376945564356054775

theorem tailTrace_520306 : CollatzResearch.WordTrace tailWord_520306 prefixEnd_520306 178111376945564356054775 := by
  unfold tailWord_520306
  simp only [CollatzResearch.WordTrace]
  refine ⟨4744279713256924508827193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12651412568685132023539181 4744279713256924508827193)
  ·
    refine ⟨3558209784942693381620395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4744279713256924508827193 3558209784942693381620395)
    ·
      refine ⟨5337314677414040072430593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3558209784942693381620395 5337314677414040072430593)
      ·
        refine ⟨4002986008060530054322945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5337314677414040072430593 4002986008060530054322945)
        ·
          refine ⟨3002239506045397540742209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4002986008060530054322945 3002239506045397540742209)
          ·
            refine ⟨2251679629534048155556657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3002239506045397540742209 2251679629534048155556657)
            ·
              refine ⟨1688759722150536116667493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2251679629534048155556657 1688759722150536116667493)
              ·
                refine ⟨316642447903225521875155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1688759722150536116667493 316642447903225521875155)
                ·
                  refine ⟨474963671854838282812733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 316642447903225521875155 474963671854838282812733)
                  ·
                    refine ⟨178111376945564356054775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 474963671854838282812733 178111376945564356054775)
                    ·
                      rfl

theorem cell22_520306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 4, 1, 3].length) (baseStart_520306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_520306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_520306 prefixEnd_520306 := by exact prefixLift 520306
  have htrace : WordTrace (prefixWord ++ tailWord_520306) baseStart_520306 baseEnd_520306 := by
    simpa [prefixWord, tailWord_520306, baseEnd_520306] using wordTrace_append hprefix tailTrace_520306
  have hstable : (prefixWord ++ tailWord_520306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520306).length < 2 ^ (prefixWord ++ tailWord_520306).sum := by decide
  have hdescent : baseEnd_520306 < baseStart_520306 := by decide
  rcases family_descends (prefixWord ++ tailWord_520306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520317 : List Nat := [1, 4, 1, 1, 3, 2, 2, 1, 2, 5]
def baseStart_520317 : Nat := 118140960795 + 520317 * 2 ^ 59
def prefixEnd_520317 : Nat := 4983230072969 + 3 ^ 40 * 520317 * 2
def baseEnd_520317 : Nat := 178115142470363994029741

theorem tailTrace_520317 : CollatzResearch.WordTrace tailWord_520317 prefixEnd_520317 178115142470363994029741 := by
  unfold tailWord_520317
  simp only [CollatzResearch.WordTrace]
  refine ⟨18977520055987846913959205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12651680037325231275972803 18977520055987846913959205)
  ·
    refine ⟨3558285010497721296367351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18977520055987846913959205 3558285010497721296367351)
    ·
      refine ⟨5337427515746581944551027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3558285010497721296367351 5337427515746581944551027)
      ·
        refine ⟨8006141273619872916826541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5337427515746581944551027 8006141273619872916826541)
        ·
          refine ⟨3002302977607452343809953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8006141273619872916826541 3002302977607452343809953)
          ·
            refine ⟨2251727233205589257857465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3002302977607452343809953 2251727233205589257857465)
            ·
              refine ⟨1688795424904191943393099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2251727233205589257857465 1688795424904191943393099)
              ·
                refine ⟨2533193137356287915089649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1688795424904191943393099 2533193137356287915089649)
                ·
                  refine ⟨1899894853017215936317237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2533193137356287915089649 1899894853017215936317237)
                  ·
                    refine ⟨178115142470363994029741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1899894853017215936317237 178115142470363994029741)
                    ·
                      rfl

theorem cell22_520317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 2, 5].length) (baseStart_520317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_520317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_520317 prefixEnd_520317 := by exact prefixLift 520317
  have htrace : WordTrace (prefixWord ++ tailWord_520317) baseStart_520317 baseEnd_520317 := by
    simpa [prefixWord, tailWord_520317, baseEnd_520317] using wordTrace_append hprefix tailTrace_520317
  have hstable : (prefixWord ++ tailWord_520317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520317).length < 2 ^ (prefixWord ++ tailWord_520317).sum := by decide
  have hdescent : baseEnd_520317 < baseStart_520317 := by decide
  rcases family_descends (prefixWord ++ tailWord_520317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520349 : List Nat := [1, 4, 2, 1, 1, 3, 2, 3, 1, 4]
def baseStart_520349 : Nat := 118140960795 + 520349 * 2 ^ 59
def prefixEnd_520349 : Nat := 4983230072969 + 3 ^ 40 * 520349 * 2
def baseEnd_520349 : Nat := 178126096724326577229643

theorem tailTrace_520349 : CollatzResearch.WordTrace tailWord_520349 prefixEnd_520349 178126096724326577229643 := by
  unfold tailWord_520349
  simp only [CollatzResearch.WordTrace]
  refine ⟨18978687191871916379124101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12652458127914610919416067 18978687191871916379124101)
  ·
    refine ⟨3558503848475984321085769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18978687191871916379124101 3558503848475984321085769)
    ·
      refine ⟨2668877886356988240814327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3558503848475984321085769 2668877886356988240814327)
      ·
        refine ⟨4003316829535482361221491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2668877886356988240814327 4003316829535482361221491)
        ·
          refine ⟨6004975244303223541832237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4003316829535482361221491 6004975244303223541832237)
          ·
            refine ⟨2251865716613708828187089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6004975244303223541832237 2251865716613708828187089)
            ·
              refine ⟨1688899287460281621140317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2251865716613708828187089 1688899287460281621140317)
              ·
                refine ⟨633337232797605607927619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1688899287460281621140317 633337232797605607927619)
                ·
                  refine ⟨950005849196408411891429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 633337232797605607927619 950005849196408411891429)
                  ·
                    refine ⟨178126096724326577229643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 950005849196408411891429 178126096724326577229643)
                    ·
                      rfl

theorem cell22_520349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_520349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_520349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_520349 prefixEnd_520349 := by exact prefixLift 520349
  have htrace : WordTrace (prefixWord ++ tailWord_520349) baseStart_520349 baseEnd_520349 := by
    simpa [prefixWord, tailWord_520349, baseEnd_520349] using wordTrace_append hprefix tailTrace_520349
  have hstable : (prefixWord ++ tailWord_520349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520349).length < 2 ^ (prefixWord ++ tailWord_520349).sum := by decide
  have hdescent : baseEnd_520349 < baseStart_520349 := by decide
  rcases family_descends (prefixWord ++ tailWord_520349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520377 : List Nat := [1, 2, 1, 4, 1, 2, 1, 2, 4, 4]
def baseStart_520377 : Nat := 118140960795 + 520377 * 2 ^ 59
def prefixEnd_520377 : Nat := 4983230072969 + 3 ^ 40 * 520377 * 2
def baseEnd_520377 : Nat := 178135681696543837529557

theorem tailTrace_520377 : CollatzResearch.WordTrace tailWord_520377 prefixEnd_520377 178135681696543837529557 := by
  unfold tailWord_520377
  simp only [CollatzResearch.WordTrace]
  refine ⟨18979708435770477161143385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12653138957180318107428923 18979708435770477161143385)
  ·
    refine ⟨14234781326827857870857539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18979708435770477161143385 14234781326827857870857539)
    ·
      refine ⟨21352171990241786806286309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14234781326827857870857539 21352171990241786806286309)
      ·
        refine ⟨4003532248170335026178683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21352171990241786806286309 4003532248170335026178683)
        ·
          refine ⟨6005298372255502539268025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4003532248170335026178683 6005298372255502539268025)
          ·
            refine ⟨4503973779191626904451019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6005298372255502539268025 4503973779191626904451019)
            ·
              refine ⟨6755960668787440356676529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4503973779191626904451019 6755960668787440356676529)
              ·
                refine ⟨5066970501590580267507397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6755960668787440356676529 5066970501590580267507397)
                ·
                  refine ⟨950056969048233800157637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5066970501590580267507397 950056969048233800157637)
                  ·
                    refine ⟨178135681696543837529557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 950056969048233800157637 178135681696543837529557)
                    ·
                      rfl

theorem cell22_520377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 4, 4].length) (baseStart_520377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_520377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_520377 prefixEnd_520377 := by exact prefixLift 520377
  have htrace : WordTrace (prefixWord ++ tailWord_520377) baseStart_520377 baseEnd_520377 := by
    simpa [prefixWord, tailWord_520377, baseEnd_520377] using wordTrace_append hprefix tailTrace_520377
  have hstable : (prefixWord ++ tailWord_520377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520377).length < 2 ^ (prefixWord ++ tailWord_520377).sum := by decide
  have hdescent : baseEnd_520377 < baseStart_520377 := by decide
  rcases family_descends (prefixWord ++ tailWord_520377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520379 : List Nat := [1, 1, 1, 1, 1, 2, 7, 3, 2, 3]
def baseStart_520379 : Nat := 118140960795 + 520379 * 2 ^ 59
def prefixEnd_520379 : Nat := 4983230072969 + 3 ^ 40 * 520379 * 2
def baseEnd_520379 : Nat := 178136366337416498979551

theorem tailTrace_520379 : CollatzResearch.WordTrace tailWord_520379 prefixEnd_520379 178136366337416498979551 := by
  unfold tailWord_520379
  simp only [CollatzResearch.WordTrace]
  refine ⟨18979781381763231502716191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12653187587842154335144127 18979781381763231502716191)
  ·
    refine ⟨28469672072644847254074287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18979781381763231502716191 28469672072644847254074287)
    ·
      refine ⟨42704508108967270881111431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28469672072644847254074287 42704508108967270881111431)
      ·
        refine ⟨64056762163450906321667147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42704508108967270881111431 64056762163450906321667147)
        ·
          refine ⟨96085143245176359482500721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64056762163450906321667147 96085143245176359482500721)
          ·
            refine ⟨72063857433882269611875541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96085143245176359482500721 72063857433882269611875541)
            ·
              refine ⟨1688996658606615694028333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 72063857433882269611875541 1688996658606615694028333)
              ·
                refine ⟨633373746977480885260625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1688996658606615694028333 633373746977480885260625)
                ·
                  refine ⟨475030310233110663945469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 633373746977480885260625 475030310233110663945469)
                  ·
                    refine ⟨178136366337416498979551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 475030310233110663945469 178136366337416498979551)
                    ·
                      rfl

theorem cell22_520379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 3, 2, 3].length) (baseStart_520379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_520379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_520379 prefixEnd_520379 := by exact prefixLift 520379
  have htrace : WordTrace (prefixWord ++ tailWord_520379) baseStart_520379 baseEnd_520379 := by
    simpa [prefixWord, tailWord_520379, baseEnd_520379] using wordTrace_append hprefix tailTrace_520379
  have hstable : (prefixWord ++ tailWord_520379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520379).length < 2 ^ (prefixWord ++ tailWord_520379).sum := by decide
  have hdescent : baseEnd_520379 < baseStart_520379 := by decide
  rcases family_descends (prefixWord ++ tailWord_520379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520394 : List Nat := [3, 1, 2, 1, 3, 1, 4, 1, 2, 4]
def baseStart_520394 : Nat := 118140960795 + 520394 * 2 ^ 59
def prefixEnd_520394 : Nat := 4983230072969 + 3 ^ 40 * 520394 * 2
def baseEnd_520394 : Nat := 178141501143961459854505

theorem tailTrace_520394 : CollatzResearch.WordTrace tailWord_520394 prefixEnd_520394 178141501143961459854505 := by
  unfold tailWord_520394
  simp only [CollatzResearch.WordTrace]
  refine ⟨4745082119177222266128059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12653552317805926043008157 4745082119177222266128059)
  ·
    refine ⟨7117623178765833399192089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4745082119177222266128059 7117623178765833399192089)
    ·
      refine ⟨5338217384074375049394067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7117623178765833399192089 5338217384074375049394067)
      ·
        refine ⟨8007326076111562574091101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5338217384074375049394067 8007326076111562574091101)
        ·
          refine ⟨3002747278541835965284163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8007326076111562574091101 3002747278541835965284163)
          ·
            refine ⟨4504120917812753947926245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3002747278541835965284163 4504120917812753947926245)
            ·
              refine ⟨844522672089891365236171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4504120917812753947926245 844522672089891365236171)
              ·
                refine ⟨1266784008134837047854257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 844522672089891365236171 1266784008134837047854257)
                ·
                  refine ⟨950088006101127785890693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1266784008134837047854257 950088006101127785890693)
                  ·
                    refine ⟨178141501143961459854505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 950088006101127785890693 178141501143961459854505)
                    ·
                      rfl

theorem cell22_520394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 1, 2, 4].length) (baseStart_520394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_520394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_520394 prefixEnd_520394 := by exact prefixLift 520394
  have htrace : WordTrace (prefixWord ++ tailWord_520394) baseStart_520394 baseEnd_520394 := by
    simpa [prefixWord, tailWord_520394, baseEnd_520394] using wordTrace_append hprefix tailTrace_520394
  have hstable : (prefixWord ++ tailWord_520394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520394).length < 2 ^ (prefixWord ++ tailWord_520394).sum := by decide
  have hdescent : baseEnd_520394 < baseStart_520394 := by decide
  rcases family_descends (prefixWord ++ tailWord_520394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520396 : List Nat := [2, 2, 1, 6, 1, 1, 1, 2, 1, 5]
def baseStart_520396 : Nat := 118140960795 + 520396 * 2 ^ 59
def prefixEnd_520396 : Nat := 4983230072969 + 3 ^ 40 * 520396 * 2
def baseEnd_520396 : Nat := 178142185784834121304499

theorem tailTrace_520396 : CollatzResearch.WordTrace tailWord_520396 prefixEnd_520396 178142185784834121304499 := by
  unfold tailWord_520396
  simp only [CollatzResearch.WordTrace]
  refine ⟨9490200711350821703042521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12653600948467762270723361 9490200711350821703042521)
  ·
    refine ⟨7117650533513116277281891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9490200711350821703042521 7117650533513116277281891)
    ·
      refine ⟨10676475800269674415922837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7117650533513116277281891 10676475800269674415922837)
      ·
        refine ⟨500459803137640988246383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 10676475800269674415922837 500459803137640988246383)
        ·
          refine ⟨750689704706461482369575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 500459803137640988246383 750689704706461482369575)
          ·
            refine ⟨1126034557059692223554363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 750689704706461482369575 1126034557059692223554363)
            ·
              refine ⟨1689051835589538335331545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1126034557059692223554363 1689051835589538335331545)
              ·
                refine ⟨1266788876692153751498659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1689051835589538335331545 1266788876692153751498659)
                ·
                  refine ⟨1900183315038230627247989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1266788876692153751498659 1900183315038230627247989)
                  ·
                    refine ⟨178142185784834121304499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1900183315038230627247989 178142185784834121304499)
                    ·
                      rfl

theorem cell22_520396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 2, 1, 5].length) (baseStart_520396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_520396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_520396 prefixEnd_520396 := by exact prefixLift 520396
  have htrace : WordTrace (prefixWord ++ tailWord_520396) baseStart_520396 baseEnd_520396 := by
    simpa [prefixWord, tailWord_520396, baseEnd_520396] using wordTrace_append hprefix tailTrace_520396
  have hstable : (prefixWord ++ tailWord_520396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520396).length < 2 ^ (prefixWord ++ tailWord_520396).sum := by decide
  have hdescent : baseEnd_520396 < baseStart_520396 := by decide
  rcases family_descends (prefixWord ++ tailWord_520396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520413 : List Nat := [1, 4, 3, 2, 1, 2, 2, 2, 2, 3]
def baseStart_520413 : Nat := 118140960795 + 520413 * 2 ^ 59
def prefixEnd_520413 : Nat := 4983230072969 + 3 ^ 40 * 520413 * 2
def baseEnd_520413 : Nat := 178148005232251743629447

theorem tailTrace_520413 : CollatzResearch.WordTrace tailWord_520413 prefixEnd_520413 178148005232251743629447 := by
  unfold tailWord_520413
  simp only [CollatzResearch.WordTrace]
  refine ⟨18981021463640055309453893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12654014309093370206302595 18981021463640055309453893)
  ·
    refine ⟨3558941524432510370522605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18981021463640055309453893 3558941524432510370522605)
    ·
      refine ⟨1334603071662191388945977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3558941524432510370522605 1334603071662191388945977)
      ·
        refine ⟨1000952303746643541709483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1334603071662191388945977 1000952303746643541709483)
        ·
          refine ⟨1501428455619965312564225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1000952303746643541709483 1501428455619965312564225)
          ·
            refine ⟨1126071341714973984423169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1501428455619965312564225 1126071341714973984423169)
            ·
              refine ⟨844553506286230488317377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1126071341714973984423169 844553506286230488317377)
              ·
                refine ⟨633415129714672866238033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 844553506286230488317377 633415129714672866238033)
                ·
                  refine ⟨475061347286004649678525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 633415129714672866238033 475061347286004649678525)
                  ·
                    refine ⟨178148005232251743629447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 475061347286004649678525 178148005232251743629447)
                    ·
                      rfl

theorem cell22_520413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_520413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_520413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_520413 prefixEnd_520413 := by exact prefixLift 520413
  have htrace : WordTrace (prefixWord ++ tailWord_520413) baseStart_520413 baseEnd_520413 := by
    simpa [prefixWord, tailWord_520413, baseEnd_520413] using wordTrace_append hprefix tailTrace_520413
  have hstable : (prefixWord ++ tailWord_520413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520413).length < 2 ^ (prefixWord ++ tailWord_520413).sum := by decide
  have hdescent : baseEnd_520413 < baseStart_520413 := by decide
  rcases family_descends (prefixWord ++ tailWord_520413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520471 : List Nat := [1, 1, 3, 4, 1, 4, 1, 2, 5]
def baseStart_520471 : Nat := 118140960795 + 520471 * 2 ^ 59
def prefixEnd_520471 : Nat := 4983230072969 + 3 ^ 40 * 520471 * 2
def baseEnd_520471 : Nat := 59389286605852975226423

theorem tailTrace_520471 : CollatzResearch.WordTrace tailWord_520471 prefixEnd_520471 59389286605852975226423 := by
  unfold tailWord_520471
  simp only [CollatzResearch.WordTrace]
  refine ⟨18983136897429931215065267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12655424598286620810043511 18983136897429931215065267)
  ·
    refine ⟨28474705346144896822597901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18983136897429931215065267 28474705346144896822597901)
    ·
      refine ⟨10678014504804336308474213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28474705346144896822597901 10678014504804336308474213)
      ·
        refine ⟨2002127719650813057838915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10678014504804336308474213 2002127719650813057838915)
        ·
          refine ⟨3003191579476219586758373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2002127719650813057838915 3003191579476219586758373)
          ·
            refine ⟨563098421151791172517195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3003191579476219586758373 563098421151791172517195)
            ·
              refine ⟨844647631727686758775793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 563098421151791172517195 844647631727686758775793)
              ·
                refine ⟨633485723795765069081845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 844647631727686758775793 633485723795765069081845)
                ·
                  refine ⟨59389286605852975226423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 633485723795765069081845 59389286605852975226423)
                  ·
                    rfl

theorem cell22_520471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 2, 5].length) (baseStart_520471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_520471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_520471 prefixEnd_520471 := by exact prefixLift 520471
  have htrace : WordTrace (prefixWord ++ tailWord_520471) baseStart_520471 baseEnd_520471 := by
    simpa [prefixWord, tailWord_520471, baseEnd_520471] using wordTrace_append hprefix tailTrace_520471
  have hstable : (prefixWord ++ tailWord_520471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520471).length < 2 ^ (prefixWord ++ tailWord_520471).sum := by decide
  have hdescent : baseEnd_520471 < baseStart_520471 := by decide
  rcases family_descends (prefixWord ++ tailWord_520471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520488 : List Nat := [2, 1, 5, 1, 3, 1, 3, 1, 5]
def baseStart_520488 : Nat := 118140960795 + 520488 * 2 ^ 59
def prefixEnd_520488 : Nat := 4983230072969 + 3 ^ 40 * 520488 * 2
def baseEnd_520488 : Nat := 59391226421658849334739

theorem tailTrace_520488 : CollatzResearch.WordTrace tailWord_520488 prefixEnd_520488 59391226421658849334739 := by
  unfold tailWord_520488
  simp only [CollatzResearch.WordTrace]
  refine ⟨9491878469184171559217059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12655837958912228745622745 9491878469184171559217059)
  ·
    refine ⟨14237817703776257338825589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9491878469184171559217059 14237817703776257338825589)
    ·
      refine ⟨1334795409729024125514899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14237817703776257338825589 1334795409729024125514899)
      ·
        refine ⟨2002193114593536188272349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1334795409729024125514899 2002193114593536188272349)
        ·
          refine ⟨750822417972576070602131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2002193114593536188272349 750822417972576070602131)
          ·
            refine ⟨1126233626958864105903197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 750822417972576070602131 1126233626958864105903197)
            ·
              refine ⟨422337610109574039713699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1126233626958864105903197 422337610109574039713699)
              ·
                refine ⟨633506415164361059570549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 422337610109574039713699 633506415164361059570549)
                ·
                  refine ⟨59391226421658849334739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 633506415164361059570549 59391226421658849334739)
                  ·
                    rfl

theorem cell22_520488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 3, 1, 5].length) (baseStart_520488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_520488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_520488 prefixEnd_520488 := by exact prefixLift 520488
  have htrace : WordTrace (prefixWord ++ tailWord_520488) baseStart_520488 baseEnd_520488 := by
    simpa [prefixWord, tailWord_520488, baseEnd_520488] using wordTrace_append hprefix tailTrace_520488
  have hstable : (prefixWord ++ tailWord_520488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520488).length < 2 ^ (prefixWord ++ tailWord_520488).sum := by decide
  have hdescent : baseEnd_520488 < baseStart_520488 := by decide
  rcases family_descends (prefixWord ++ tailWord_520488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520501 : List Nat := [1, 3, 3, 1, 2, 1, 4, 2, 1, 4]
def baseStart_520501 : Nat := 118140960795 + 520501 * 2 ^ 59
def prefixEnd_520501 : Nat := 4983230072969 + 3 ^ 40 * 520501 * 2
def baseEnd_520501 : Nat := 178178129430648847429177

theorem tailTrace_520501 : CollatzResearch.WordTrace tailWord_520501 prefixEnd_520501 178178129430648847429177 := by
  unfold tailWord_520501
  simp only [CollatzResearch.WordTrace]
  refine ⟨18984231087321246338657357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12656154058214164225771571 18984231087321246338657357)
  ·
    refine ⟨7119086657745467376996509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18984231087321246338657357 7119086657745467376996509)
    ·
      refine ⟨2669657496654550266373691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7119086657745467376996509 2669657496654550266373691)
      ·
        refine ⟨4004486244981825399560537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2669657496654550266373691 4004486244981825399560537)
        ·
          refine ⟨3003364683736369049670403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4004486244981825399560537 3003364683736369049670403)
          ·
            refine ⟨4505047025604553574505605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3003364683736369049670403 4505047025604553574505605)
            ·
              refine ⟨844696317300853795219801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4505047025604553574505605 844696317300853795219801)
              ·
                refine ⟨633522237975640346414851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 844696317300853795219801 633522237975640346414851)
                ·
                  refine ⟨950283356963460519622277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 633522237975640346414851 950283356963460519622277)
                  ·
                    refine ⟨178178129430648847429177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 950283356963460519622277 178178129430648847429177)
                    ·
                      rfl

theorem cell22_520501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_520501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_520501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_520501 prefixEnd_520501 := by exact prefixLift 520501
  have htrace : WordTrace (prefixWord ++ tailWord_520501) baseStart_520501 baseEnd_520501 := by
    simpa [prefixWord, tailWord_520501, baseEnd_520501] using wordTrace_append hprefix tailTrace_520501
  have hstable : (prefixWord ++ tailWord_520501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520501).length < 2 ^ (prefixWord ++ tailWord_520501).sum := by decide
  have hdescent : baseEnd_520501 < baseStart_520501 := by decide
  rcases family_descends (prefixWord ++ tailWord_520501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520529 : List Nat := [1, 2, 2, 1, 4, 2, 1, 1, 4, 4]
def baseStart_520529 : Nat := 118140960795 + 520529 * 2 ^ 59
def prefixEnd_520529 : Nat := 4983230072969 + 3 ^ 40 * 520529 * 2
def baseEnd_520529 : Nat := 178187714402866107729091

theorem tailTrace_520529 : CollatzResearch.WordTrace tailWord_520529 prefixEnd_520529 178187714402866107729091 := by
  unfold tailWord_520529
  simp only [CollatzResearch.WordTrace]
  refine ⟨18985252331219807120676641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12656834887479871413784427 18985252331219807120676641)
  ·
    refine ⟨14238939248414855340507481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18985252331219807120676641 14238939248414855340507481)
    ·
      refine ⟨10679204436311141505380611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14238939248414855340507481 10679204436311141505380611)
      ·
        refine ⟨16018806654466712258070917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10679204436311141505380611 16018806654466712258070917)
        ·
          refine ⟨3003526247712508548388297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16018806654466712258070917 3003526247712508548388297)
          ·
            refine ⟨2252644685784381411291223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3003526247712508548388297 2252644685784381411291223)
            ·
              refine ⟨3378967028676572116936835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2252644685784381411291223 3378967028676572116936835)
              ·
                refine ⟨5068450543014858175405253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3378967028676572116936835 5068450543014858175405253)
                ·
                  refine ⟨950334476815285907888485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5068450543014858175405253 950334476815285907888485)
                  ·
                    refine ⟨178187714402866107729091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 950334476815285907888485 178187714402866107729091)
                    ·
                      rfl

theorem cell22_520529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 4, 4].length) (baseStart_520529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_520529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_520529 prefixEnd_520529 := by exact prefixLift 520529
  have htrace : WordTrace (prefixWord ++ tailWord_520529) baseStart_520529 baseEnd_520529 := by
    simpa [prefixWord, tailWord_520529, baseEnd_520529] using wordTrace_append hprefix tailTrace_520529
  have hstable : (prefixWord ++ tailWord_520529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520529).length < 2 ^ (prefixWord ++ tailWord_520529).sum := by decide
  have hdescent : baseEnd_520529 < baseStart_520529 := by decide
  rcases family_descends (prefixWord ++ tailWord_520529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520533 : List Nat := [1, 3, 2, 2, 5, 1, 1, 1, 6]
def baseStart_520533 : Nat := 118140960795 + 520533 * 2 ^ 59
def prefixEnd_520533 : Nat := 4983230072969 + 3 ^ 40 * 520533 * 2
def baseEnd_520533 : Nat := 59396361228203810209693

theorem tailTrace_520533 : CollatzResearch.WordTrace tailWord_520533 prefixEnd_520533 59396361228203810209693 := by
  unfold tailWord_520533
  simp only [CollatzResearch.WordTrace]
  refine ⟨18985398223205315803822253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12656932148803543869214835 18985398223205315803822253)
  ·
    refine ⟨7119524333701993426433345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18985398223205315803822253 7119524333701993426433345)
    ·
      refine ⟨5339643250276495069825009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7119524333701993426433345 5339643250276495069825009)
      ·
        refine ⟨4004732437707371302368757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5339643250276495069825009 4004732437707371302368757)
        ·
          refine ⟨375443666035066059597071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4004732437707371302368757 375443666035066059597071)
          ·
            refine ⟨563165499052599089395607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375443666035066059597071 563165499052599089395607)
            ·
              refine ⟨844748248578898634093411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 563165499052599089395607 844748248578898634093411)
              ·
                refine ⟨1267122372868347951140117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 844748248578898634093411 1267122372868347951140117)
                ·
                  refine ⟨59396361228203810209693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1267122372868347951140117 59396361228203810209693)
                  ·
                    rfl

theorem cell22_520533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 1, 6].length) (baseStart_520533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_520533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_520533 prefixEnd_520533 := by exact prefixLift 520533
  have htrace : WordTrace (prefixWord ++ tailWord_520533) baseStart_520533 baseEnd_520533 := by
    simpa [prefixWord, tailWord_520533, baseEnd_520533] using wordTrace_append hprefix tailTrace_520533
  have hstable : (prefixWord ++ tailWord_520533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520533).length < 2 ^ (prefixWord ++ tailWord_520533).sum := by decide
  have hdescent : baseEnd_520533 < baseStart_520533 := by decide
  rcases family_descends (prefixWord ++ tailWord_520533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520578 : List Nat := [3, 4, 2, 1, 3, 9]
def baseStart_520578 : Nat := 118140960795 + 520578 * 2 ^ 59
def prefixEnd_520578 : Nat := 4983230072969 + 3 ^ 40 * 520578 * 2
def baseEnd_520578 : Nat := 2200055408694398929061

theorem tailTrace_520578 : CollatzResearch.WordTrace tailWord_520578 prefixEnd_520578 2200055408694398929061 := by
  unfold tailWord_520578
  simp only [CollatzResearch.WordTrace]
  refine ⟨4746759877010572122302597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12658026338694858992806925 4746759877010572122302597)
  ·
    refine ⟨890017476939482272931737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4746759877010572122302597 890017476939482272931737)
    ·
      refine ⟨667513107704611704698803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 890017476939482272931737 667513107704611704698803)
      ·
        refine ⟨1001269661556917557048205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 667513107704611704698803 1001269661556917557048205)
        ·
          refine ⟨375476123083844083893077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1001269661556917557048205 375476123083844083893077)
          ·
            refine ⟨2200055408694398929061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 375476123083844083893077 2200055408694398929061)
            ·
              rfl

theorem cell22_520578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 9].length) (baseStart_520578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_520578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_520578 prefixEnd_520578 := by exact prefixLift 520578
  have htrace : WordTrace (prefixWord ++ tailWord_520578) baseStart_520578 baseEnd_520578 := by
    simpa [prefixWord, tailWord_520578, baseEnd_520578] using wordTrace_append hprefix tailTrace_520578
  have hstable : (prefixWord ++ tailWord_520578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520578).length < 2 ^ (prefixWord ++ tailWord_520578).sum := by decide
  have hdescent : baseEnd_520578 < baseStart_520578 := by decide
  rcases family_descends (prefixWord ++ tailWord_520578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520649 : List Nat := [1, 2, 1, 1, 2, 1, 4, 2, 3, 5]
def baseStart_520649 : Nat := 118140960795 + 520649 * 2 ^ 59
def prefixEnd_520649 : Nat := 4983230072969 + 3 ^ 40 * 520649 * 2
def baseEnd_520649 : Nat := 178228792855225794728723

theorem tailTrace_520649 : CollatzResearch.WordTrace tailWord_520649 prefixEnd_520649 178228792855225794728723 := by
  unfold tailWord_520649
  simp only [CollatzResearch.WordTrace]
  refine ⟨18989629090785067615045001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12659752727190045076696667 18989629090785067615045001)
  ·
    refine ⟨14242221818088800711283751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18989629090785067615045001 14242221818088800711283751)
    ·
      refine ⟨21363332727133201066925627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14242221818088800711283751 21363332727133201066925627)
      ·
        refine ⟨32044999090699801600388441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21363332727133201066925627 32044999090699801600388441)
        ·
          refine ⟨24033749318024851200291331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32044999090699801600388441 24033749318024851200291331)
          ·
            refine ⟨36050623977037276800436997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24033749318024851200291331 36050623977037276800436997)
            ·
              refine ⟨6759491995694489400081937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36050623977037276800436997 6759491995694489400081937)
              ·
                refine ⟨5069618996770867050061453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6759491995694489400081937 5069618996770867050061453)
                ·
                  refine ⟨1901107123789075143773045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5069618996770867050061453 1901107123789075143773045)
                  ·
                    refine ⟨178228792855225794728723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1901107123789075143773045 178228792855225794728723)
                    ·
                      rfl

theorem cell22_520649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 3, 5].length) (baseStart_520649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_520649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_520649 prefixEnd_520649 := by exact prefixLift 520649
  have htrace : WordTrace (prefixWord ++ tailWord_520649) baseStart_520649 baseEnd_520649 := by
    simpa [prefixWord, tailWord_520649, baseEnd_520649] using wordTrace_append hprefix tailTrace_520649
  have hstable : (prefixWord ++ tailWord_520649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520649).length < 2 ^ (prefixWord ++ tailWord_520649).sum := by decide
  have hdescent : baseEnd_520649 < baseStart_520649 := by decide
  rcases family_descends (prefixWord ++ tailWord_520649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520685 : List Nat := [1, 5, 1, 3, 1, 1, 3, 3, 4]
def baseStart_520685 : Nat := 118140960795 + 520685 * 2 ^ 59
def prefixEnd_520685 : Nat := 4983230072969 + 3 ^ 40 * 520685 * 2
def baseEnd_520685 : Nat := 59413705463644566942871

theorem tailTrace_520685 : CollatzResearch.WordTrace tailWord_520685 prefixEnd_520685 59413705463644566942871 := by
  unfold tailWord_520685
  simp only [CollatzResearch.WordTrace]
  refine ⟨18990942118654645763355509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12660628079103097175570339 18990942118654645763355509)
  ·
    refine ⟨1780400823623873040314579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18990942118654645763355509 1780400823623873040314579)
    ·
      refine ⟨2670601235435809560471869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1780400823623873040314579 2670601235435809560471869)
      ·
        refine ⟨1001475463288428585176951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2670601235435809560471869 1001475463288428585176951)
        ·
          refine ⟨1502213194932642877765427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1001475463288428585176951 1502213194932642877765427)
          ·
            refine ⟨2253319792398964316648141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1502213194932642877765427 2253319792398964316648141)
            ·
              refine ⟨844994922149611618743053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2253319792398964316648141 844994922149611618743053)
              ·
                refine ⟨316873095806104357028645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 844994922149611618743053 316873095806104357028645)
                ·
                  refine ⟨59413705463644566942871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 316873095806104357028645 59413705463644566942871)
                  ·
                    rfl

theorem cell22_520685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 3, 4].length) (baseStart_520685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_520685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_520685 prefixEnd_520685 := by exact prefixLift 520685
  have htrace : WordTrace (prefixWord ++ tailWord_520685) baseStart_520685 baseEnd_520685 := by
    simpa [prefixWord, tailWord_520685, baseEnd_520685] using wordTrace_append hprefix tailTrace_520685
  have hstable : (prefixWord ++ tailWord_520685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520685).length < 2 ^ (prefixWord ++ tailWord_520685).sum := by decide
  have hdescent : baseEnd_520685 < baseStart_520685 := by decide
  rcases family_descends (prefixWord ++ tailWord_520685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520762 : List Nat := [3, 1, 1, 1, 3, 3, 4, 2, 1, 3]
def baseStart_520762 : Nat := 118140960795 + 520762 * 2 ^ 59
def prefixEnd_520762 : Nat := 4983230072969 + 3 ^ 40 * 520762 * 2
def baseEnd_520762 : Nat := 178267475064531166653377

theorem tailTrace_520762 : CollatzResearch.WordTrace tailWord_520762 prefixEnd_520762 178267475064531166653377 := by
  unfold tailWord_520762
  simp only [CollatzResearch.WordTrace]
  refine ⟨4748437634843921978477135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12662500359583791942605693 4748437634843921978477135)
  ·
    refine ⟨7122656452265882967715703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4748437634843921978477135 7122656452265882967715703)
    ·
      refine ⟨10683984678398824451573555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7122656452265882967715703 10683984678398824451573555)
      ·
        refine ⟨16025977017598236677360333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10683984678398824451573555 16025977017598236677360333)
        ·
          refine ⟨6009741381599338754010125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16025977017598236677360333 6009741381599338754010125)
          ·
            refine ⟨2253653018099752032753797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6009741381599338754010125 2253653018099752032753797)
            ·
              refine ⟨422559940893703506141337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2253653018099752032753797 422559940893703506141337)
              ·
                refine ⟨316919955670277629606003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 422559940893703506141337 316919955670277629606003)
                ·
                  refine ⟨475379933505416444409005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 316919955670277629606003 475379933505416444409005)
                  ·
                    refine ⟨178267475064531166653377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 475379933505416444409005 178267475064531166653377)
                    ·
                      rfl

theorem cell22_520762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 4, 2, 1, 3].length) (baseStart_520762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_520762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_520762 prefixEnd_520762 := by exact prefixLift 520762
  have htrace : WordTrace (prefixWord ++ tailWord_520762) baseStart_520762 baseEnd_520762 := by
    simpa [prefixWord, tailWord_520762, baseEnd_520762] using wordTrace_append hprefix tailTrace_520762
  have hstable : (prefixWord ++ tailWord_520762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520762).length < 2 ^ (prefixWord ++ tailWord_520762).sum := by decide
  have hdescent : baseEnd_520762 < baseStart_520762 := by decide
  rcases family_descends (prefixWord ++ tailWord_520762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520788 : List Nat := [2, 4, 1, 1, 1, 3, 2, 1, 3, 4]
def baseStart_520788 : Nat := 118140960795 + 520788 * 2 ^ 59
def prefixEnd_520788 : Nat := 4983230072969 + 3 ^ 40 * 520788 * 2
def baseEnd_520788 : Nat := 178276375395875765503297

theorem tailTrace_520788 : CollatzResearch.WordTrace tailWord_520788 prefixEnd_520788 178276375395875765503297 := by
  unfold tailWord_520788
  simp only [CollatzResearch.WordTrace]
  refine ⟨9497349418640747177177509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12663132558187662902903345 9497349418640747177177509)
  ·
    refine ⟨1780753015995140095720783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9497349418640747177177509 1780753015995140095720783)
    ·
      refine ⟨2671129523992710143581175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1780753015995140095720783 2671129523992710143581175)
      ·
        refine ⟨4006694285989065215371763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2671129523992710143581175 4006694285989065215371763)
        ·
          refine ⟨6010041428983597823057645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4006694285989065215371763 6010041428983597823057645)
          ·
            refine ⟨2253765535868849183646617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6010041428983597823057645 2253765535868849183646617)
            ·
              refine ⟨1690324151901636887734963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2253765535868849183646617 1690324151901636887734963)
              ·
                refine ⟨2535486227852455331602445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1690324151901636887734963 2535486227852455331602445)
                ·
                  refine ⟨950807335444670749350917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2535486227852455331602445 950807335444670749350917)
                  ·
                    refine ⟨178276375395875765503297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 950807335444670749350917 178276375395875765503297)
                    ·
                      rfl

theorem cell22_520788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_520788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_520788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_520788 prefixEnd_520788 := by exact prefixLift 520788
  have htrace : WordTrace (prefixWord ++ tailWord_520788) baseStart_520788 baseEnd_520788 := by
    simpa [prefixWord, tailWord_520788, baseEnd_520788] using wordTrace_append hprefix tailTrace_520788
  have hstable : (prefixWord ++ tailWord_520788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520788).length < 2 ^ (prefixWord ++ tailWord_520788).sum := by decide
  have hdescent : baseEnd_520788 < baseStart_520788 := by decide
  rcases family_descends (prefixWord ++ tailWord_520788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520805 : List Nat := [1, 3, 1, 3, 4, 1, 1, 3, 1, 4]
def baseStart_520805 : Nat := 118140960795 + 520805 * 2 ^ 59
def prefixEnd_520805 : Nat := 4983230072969 + 3 ^ 40 * 520805 * 2
def baseEnd_520805 : Nat := 178282194843293387828245

theorem tailTrace_520805 : CollatzResearch.WordTrace tailWord_520805 prefixEnd_520805 178282194843293387828245 := by
  unfold tailWord_520805
  simp only [CollatzResearch.WordTrace]
  refine ⟨18995318878219906257723869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12663545918813270838482579 18995318878219906257723869)
  ·
    refine ⟨7123244579332464846646451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18995318878219906257723869 7123244579332464846646451)
    ·
      refine ⟨10684866868998697269969677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7123244579332464846646451 10684866868998697269969677)
      ·
        refine ⟨4006825075874511476238629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10684866868998697269969677 4006825075874511476238629)
        ·
          refine ⟨751279701726470901794743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4006825075874511476238629 751279701726470901794743)
          ·
            refine ⟨1126919552589706352692115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 751279701726470901794743 1126919552589706352692115)
            ·
              refine ⟨1690379328884559529038173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1126919552589706352692115 1690379328884559529038173)
              ·
                refine ⟨633892248331709823389315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1690379328884559529038173 633892248331709823389315)
                ·
                  refine ⟨950838372497564735083973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 633892248331709823389315 950838372497564735083973)
                  ·
                    refine ⟨178282194843293387828245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 950838372497564735083973 178282194843293387828245)
                    ·
                      rfl

theorem cell22_520805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 3, 1, 4].length) (baseStart_520805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_520805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_520805 prefixEnd_520805 := by exact prefixLift 520805
  have htrace : WordTrace (prefixWord ++ tailWord_520805) baseStart_520805 baseEnd_520805 := by
    simpa [prefixWord, tailWord_520805, baseEnd_520805] using wordTrace_append hprefix tailTrace_520805
  have hstable : (prefixWord ++ tailWord_520805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520805).length < 2 ^ (prefixWord ++ tailWord_520805).sum := by decide
  have hdescent : baseEnd_520805 < baseStart_520805 := by decide
  rcases family_descends (prefixWord ++ tailWord_520805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520865 : List Nat := [1, 2, 3, 3, 4, 1, 8]
def baseStart_520865 : Nat := 118140960795 + 520865 * 2 ^ 59
def prefixEnd_520865 : Nat := 4983230072969 + 3 ^ 40 * 520865 * 2
def baseEnd_520865 : Nat := 6603804965536045604743

theorem tailTrace_520865 : CollatzResearch.WordTrace tailWord_520865 prefixEnd_520865 6603804965536045604743 := by
  unfold tailWord_520865
  simp only [CollatzResearch.WordTrace]
  refine ⟨18997507258002536504908049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12665004838668357669938699 18997507258002536504908049)
  ·
    refine ⟨14248130443501902378681037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18997507258002536504908049 14248130443501902378681037)
    ·
      refine ⟨5343048916313213392005389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14248130443501902378681037 5343048916313213392005389)
      ·
        refine ⟨2003643343617455022002021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5343048916313213392005389 2003643343617455022002021)
        ·
          refine ⟨375683126928272816625379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2003643343617455022002021 375683126928272816625379)
          ·
            refine ⟨563524690392409224938069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375683126928272816625379 563524690392409224938069)
            ·
              refine ⟨6603804965536045604743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 563524690392409224938069 6603804965536045604743)
              ·
                rfl

theorem cell22_520865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 8].length) (baseStart_520865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_520865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_520865 prefixEnd_520865 := by exact prefixLift 520865
  have htrace : WordTrace (prefixWord ++ tailWord_520865) baseStart_520865 baseEnd_520865 := by
    simpa [prefixWord, tailWord_520865, baseEnd_520865] using wordTrace_append hprefix tailTrace_520865
  have hstable : (prefixWord ++ tailWord_520865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520865).length < 2 ^ (prefixWord ++ tailWord_520865).sum := by decide
  have hdescent : baseEnd_520865 < baseStart_520865 := by decide
  rcases family_descends (prefixWord ++ tailWord_520865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520931 : List Nat := [1, 1, 1, 7, 1, 3, 2, 2, 1, 3]
def baseStart_520931 : Nat := 118140960795 + 520931 * 2 ^ 59
def prefixEnd_520931 : Nat := 4983230072969 + 3 ^ 40 * 520931 * 2
def baseEnd_520931 : Nat := 178325327218271059177859

theorem tailTrace_520931 : CollatzResearch.WordTrace tailWord_520931 prefixEnd_520931 178325327218271059177859 := by
  unfold tailWord_520931
  simp only [CollatzResearch.WordTrace]
  refine ⟨18999914475763429776810647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12666609650508953184540431 18999914475763429776810647)
  ·
    refine ⟨28499871713645144665215971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18999914475763429776810647 28499871713645144665215971)
    ·
      refine ⟨42749807570467716997823957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28499871713645144665215971 42749807570467716997823957)
      ·
        refine ⟨1001948614932837117136499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 42749807570467716997823957 1001948614932837117136499)
        ·
          refine ⟨1502922922399255675704749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1001948614932837117136499 1502922922399255675704749)
          ·
            refine ⟨563596095899720878389281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1502922922399255675704749 563596095899720878389281)
            ·
              refine ⟨422697071924790658791961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 563596095899720878389281 422697071924790658791961)
              ·
                refine ⟨317022803943592994093971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 422697071924790658791961 317022803943592994093971)
                ·
                  refine ⟨475534205915389491140957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 317022803943592994093971 475534205915389491140957)
                  ·
                    refine ⟨178325327218271059177859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 475534205915389491140957 178325327218271059177859)
                    ·
                      rfl

theorem cell22_520931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 2, 2, 1, 3].length) (baseStart_520931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_520931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_520931 prefixEnd_520931 := by exact prefixLift 520931
  have htrace : WordTrace (prefixWord ++ tailWord_520931) baseStart_520931 baseEnd_520931 := by
    simpa [prefixWord, tailWord_520931, baseEnd_520931] using wordTrace_append hprefix tailTrace_520931
  have hstable : (prefixWord ++ tailWord_520931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520931).length < 2 ^ (prefixWord ++ tailWord_520931).sum := by decide
  have hdescent : baseEnd_520931 < baseStart_520931 := by decide
  rcases family_descends (prefixWord ++ tailWord_520931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520938 : List Nat := [3, 1, 3, 1, 1, 1, 1, 5, 6]
def baseStart_520938 : Nat := 118140960795 + 520938 * 2 ^ 59
def prefixEnd_520938 : Nat := 4983230072969 + 3 ^ 40 * 520938 * 2
def baseEnd_520938 : Nat := 59442574487108458084279

theorem tailTrace_520938 : CollatzResearch.WordTrace tailWord_520938 prefixEnd_520938 59442574487108458084279 := by
  unfold tailWord_520938
  simp only [CollatzResearch.WordTrace]
  refine ⟨4750042446684517493078867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12666779857825379981543645 4750042446684517493078867)
  ·
    refine ⟨7125063670026776239618301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4750042446684517493078867 7125063670026776239618301)
    ·
      refine ⟨2671898876260041089856863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7125063670026776239618301 2671898876260041089856863)
      ·
        refine ⟨4007848314390061634785295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2671898876260041089856863 4007848314390061634785295)
        ·
          refine ⟨6011772471585092452177943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4007848314390061634785295 6011772471585092452177943)
          ·
            refine ⟨9017658707377638678266915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6011772471585092452177943 9017658707377638678266915)
            ·
              refine ⟨13526488061066458017400373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9017658707377638678266915 13526488061066458017400373)
              ·
                refine ⟨1268108255724980439131285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13526488061066458017400373 1268108255724980439131285)
                ·
                  refine ⟨59442574487108458084279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1268108255724980439131285 59442574487108458084279)
                  ·
                    rfl

theorem cell22_520938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 5, 6].length) (baseStart_520938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_520938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_520938 prefixEnd_520938 := by exact prefixLift 520938
  have htrace : WordTrace (prefixWord ++ tailWord_520938) baseStart_520938 baseEnd_520938 := by
    simpa [prefixWord, tailWord_520938, baseEnd_520938] using wordTrace_append hprefix tailTrace_520938
  have hstable : (prefixWord ++ tailWord_520938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520938).length < 2 ^ (prefixWord ++ tailWord_520938).sum := by decide
  have hdescent : baseEnd_520938 < baseStart_520938 := by decide
  rcases family_descends (prefixWord ++ tailWord_520938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520970 : List Nat := [3, 1, 2, 2, 1, 2, 2, 2, 4, 3]
def baseStart_520970 : Nat := 118140960795 + 520970 * 2 ^ 59
def prefixEnd_520970 : Nat := 4983230072969 + 3 ^ 40 * 520970 * 2
def baseEnd_520970 : Nat := 178338677715287957452739

theorem tailTrace_520970 : CollatzResearch.WordTrace tailWord_520970 prefixEnd_520970 178338677715287957452739 := by
  unfold tailWord_520970
  simp only [CollatzResearch.WordTrace]
  refine ⟨4750334230655534859370091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12667557948414759624986909 4750334230655534859370091)
  ·
    refine ⟨7125501345983302289055137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4750334230655534859370091 7125501345983302289055137)
    ·
      refine ⟨5344126009487476716791353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7125501345983302289055137 5344126009487476716791353)
      ·
        refine ⟨4008094507115607537593515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5344126009487476716791353 4008094507115607537593515)
        ·
          refine ⟨6012141760673411306390273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4008094507115607537593515 6012141760673411306390273)
          ·
            refine ⟨4509106320505058479792705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6012141760673411306390273 4509106320505058479792705)
            ·
              refine ⟨3381829740378793859844529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4509106320505058479792705 3381829740378793859844529)
              ·
                refine ⟨2536372305284095394883397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3381829740378793859844529 2536372305284095394883397)
                ·
                  refine ⟨475569807240767886540637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2536372305284095394883397 475569807240767886540637)
                  ·
                    refine ⟨178338677715287957452739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 475569807240767886540637 178338677715287957452739)
                    ·
                      rfl

theorem cell22_520970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 4, 3].length) (baseStart_520970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_520970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_520970 prefixEnd_520970 := by exact prefixLift 520970
  have htrace : WordTrace (prefixWord ++ tailWord_520970) baseStart_520970 baseEnd_520970 := by
    simpa [prefixWord, tailWord_520970, baseEnd_520970] using wordTrace_append hprefix tailTrace_520970
  have hstable : (prefixWord ++ tailWord_520970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520970).length < 2 ^ (prefixWord ++ tailWord_520970).sum := by decide
  have hdescent : baseEnd_520970 < baseStart_520970 := by decide
  rcases family_descends (prefixWord ++ tailWord_520970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521015 : List Nat := [1, 1, 3, 1, 2, 1, 3, 4, 3, 3]
def baseStart_521015 : Nat := 118140960795 + 521015 * 2 ^ 59
def prefixEnd_521015 : Nat := 4983230072969 + 3 ^ 40 * 521015 * 2
def baseEnd_521015 : Nat := 178354082134922840077601

theorem tailTrace_521015 : CollatzResearch.WordTrace tailWord_521015 prefixEnd_521015 178354082134922840077601 := by
  unfold tailWord_521015
  simp only [CollatzResearch.WordTrace]
  refine ⟨19002978207459112122868499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12668652138306074748578999 19002978207459112122868499)
  ·
    refine ⟨28504467311188668184302749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19002978207459112122868499 28504467311188668184302749)
    ·
      refine ⟨10689175241695750569113531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28504467311188668184302749 10689175241695750569113531)
      ·
        refine ⟨16033762862543625853670297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10689175241695750569113531 16033762862543625853670297)
        ·
          refine ⟨12025322146907719390252723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16033762862543625853670297 12025322146907719390252723)
          ·
            refine ⟨18037983220361579085379085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12025322146907719390252723 18037983220361579085379085)
            ·
              refine ⟨6764243707635592157017157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18037983220361579085379085 6764243707635592157017157)
              ·
                refine ⟨1268295695181673529440717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6764243707635592157017157 1268295695181673529440717)
                ·
                  refine ⟨475610885693127573540269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1268295695181673529440717 475610885693127573540269)
                  ·
                    refine ⟨178354082134922840077601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 475610885693127573540269 178354082134922840077601)
                    ·
                      rfl

theorem cell22_521015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 4, 3, 3].length) (baseStart_521015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_521015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_521015 prefixEnd_521015 := by exact prefixLift 521015
  have htrace : WordTrace (prefixWord ++ tailWord_521015) baseStart_521015 baseEnd_521015 := by
    simpa [prefixWord, tailWord_521015, baseEnd_521015] using wordTrace_append hprefix tailTrace_521015
  have hstable : (prefixWord ++ tailWord_521015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521015).length < 2 ^ (prefixWord ++ tailWord_521015).sum := by decide
  have hdescent : baseEnd_521015 < baseStart_521015 := by decide
  rcases family_descends (prefixWord ++ tailWord_521015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521043 : List Nat := [1, 1, 1, 2, 1, 1, 3, 3, 4, 5]
def baseStart_521043 : Nat := 118140960795 + 521043 * 2 ^ 59
def prefixEnd_521043 : Nat := 4983230072969 + 3 ^ 40 * 521043 * 2
def baseEnd_521043 : Nat := 178363667107140100377515

theorem tailTrace_521043 : CollatzResearch.WordTrace tailWord_521043 prefixEnd_521043 178363667107140100377515 := by
  unfold tailWord_521043
  simp only [CollatzResearch.WordTrace]
  refine ⟨19003999451357672904887783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12669332967571781936591855 19003999451357672904887783)
  ·
    refine ⟨28505999177036509357331675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19003999451357672904887783 28505999177036509357331675)
    ·
      refine ⟨42758998765554764035997513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28505999177036509357331675 42758998765554764035997513)
      ·
        refine ⟨32069249074166073026998135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42758998765554764035997513 32069249074166073026998135)
        ·
          refine ⟨48103873611249109540497203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32069249074166073026998135 48103873611249109540497203)
          ·
            refine ⟨72155810416873664310745805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48103873611249109540497203 72155810416873664310745805)
            ·
              refine ⟨27058428906327624116529677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72155810416873664310745805 27058428906327624116529677)
              ·
                refine ⟨10146910839872859043698629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27058428906327624116529677 10146910839872859043698629)
                ·
                  refine ⟨1902545782476161070693493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10146910839872859043698629 1902545782476161070693493)
                  ·
                    refine ⟨178363667107140100377515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1902545782476161070693493 178363667107140100377515)
                    ·
                      rfl

theorem cell22_521043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 4, 5].length) (baseStart_521043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_521043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_521043 prefixEnd_521043 := by exact prefixLift 521043
  have htrace : WordTrace (prefixWord ++ tailWord_521043) baseStart_521043 baseEnd_521043 := by
    simpa [prefixWord, tailWord_521043, baseEnd_521043] using wordTrace_append hprefix tailTrace_521043
  have hstable : (prefixWord ++ tailWord_521043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521043).length < 2 ^ (prefixWord ++ tailWord_521043).sum := by decide
  have hdescent : baseEnd_521043 < baseStart_521043 := by decide
  rcases family_descends (prefixWord ++ tailWord_521043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
