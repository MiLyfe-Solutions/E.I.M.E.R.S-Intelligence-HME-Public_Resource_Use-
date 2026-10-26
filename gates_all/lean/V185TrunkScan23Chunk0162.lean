import V185TrunkScan23Chunk0161

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_958356 : List Nat := [2, 4, 2, 1, 1, 3, 2, 1, 7]
def baseStart_958356 : Nat := 118140960795 + 958356 * 2 ^ 59
def prefixEnd_958356 : Nat := 4983230072969 + 3 ^ 40 * 958356 * 2
def baseEnd_958356 : Nat := 54677474013373073493623

theorem tailTrace_958356 : CollatzResearch.WordTrace tailWord_958356 prefixEnd_958356 54677474013373073493623 := by
  unfold tailWord_958356
  simp only [CollatzResearch.WordTrace]
  refine ⟨17477057458023680509571461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23302743277364907346095281 17477057458023680509571461)
  ·
    refine ⟨3276948273379440095544649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17477057458023680509571461 3276948273379440095544649)
    ·
      refine ⟨2457711205034580071658487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3276948273379440095544649 2457711205034580071658487)
      ·
        refine ⟨3686566807551870107487731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2457711205034580071658487 3686566807551870107487731)
        ·
          refine ⟨5529850211327805161231597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3686566807551870107487731 5529850211327805161231597)
          ·
            refine ⟨2073693829247926935461849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5529850211327805161231597 2073693829247926935461849)
            ·
              refine ⟨1555270371935945201596387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2073693829247926935461849 1555270371935945201596387)
              ·
                refine ⟨2332905557903917802394581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1555270371935945201596387 2332905557903917802394581)
                ·
                  refine ⟨54677474013373073493623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2332905557903917802394581 54677474013373073493623)
                  ·
                    rfl

theorem cell23_958356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 1, 7].length) (baseStart_958356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_958356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_958356 prefixEnd_958356 := by exact prefixLift 958356
  have htrace : WordTrace (prefixWord ++ tailWord_958356) baseStart_958356 baseEnd_958356 := by
    simpa [prefixWord, tailWord_958356, baseEnd_958356] using wordTrace_append hprefix tailTrace_958356
  have hstable : (prefixWord ++ tailWord_958356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958356).length < 2 ^ (prefixWord ++ tailWord_958356).sum := by decide
  have hdescent : baseEnd_958356 < baseStart_958356 := by decide
  rcases family_descends (prefixWord ++ tailWord_958356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958367 : List Nat := [1, 1, 2, 5, 3, 1, 3, 1, 2, 2, 2]
def baseStart_958367 : Nat := 118140960795 + 958367 * 2 ^ 59
def prefixEnd_958367 : Nat := 4983230072969 + 3 ^ 40 * 958367 * 2
def baseEnd_958367 : Nat := 492102914407557118405057

theorem tailTrace_958367 : CollatzResearch.WordTrace tailWord_958367 prefixEnd_958367 492102914407557118405057 := by
  unfold tailWord_958367
  simp only [CollatzResearch.WordTrace]
  refine ⟨34954516119007509897793355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23303010746005006598528903 34954516119007509897793355)
  ·
    refine ⟨52431774178511264846690033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34954516119007509897793355 52431774178511264846690033)
    ·
      refine ⟨39323830633883448635017525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52431774178511264846690033 39323830633883448635017525)
      ·
        refine ⟨3686609121926573309532893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39323830633883448635017525 3686609121926573309532893)
        ·
          refine ⟨1382478420722464991074835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3686609121926573309532893 1382478420722464991074835)
          ·
            refine ⟨2073717631083697486612253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1382478420722464991074835 2073717631083697486612253)
            ·
              refine ⟨777644111656386557479595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2073717631083697486612253 777644111656386557479595)
              ·
                refine ⟨1166466167484579836219393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 777644111656386557479595 1166466167484579836219393)
                ·
                  refine ⟨874849625613434877164545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1166466167484579836219393 874849625613434877164545)
                  ·
                    refine ⟨656137219210076157873409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 874849625613434877164545 656137219210076157873409)
                    ·
                      refine ⟨492102914407557118405057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 656137219210076157873409 492102914407557118405057)
                      ·
                        rfl

theorem cell23_958367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 3, 1, 2, 2, 2].length) (baseStart_958367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_958367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_958367 prefixEnd_958367 := by exact prefixLift 958367
  have htrace : WordTrace (prefixWord ++ tailWord_958367) baseStart_958367 baseEnd_958367 := by
    simpa [prefixWord, tailWord_958367, baseEnd_958367] using wordTrace_append hprefix tailTrace_958367
  have hstable : (prefixWord ++ tailWord_958367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958367).length < 2 ^ (prefixWord ++ tailWord_958367).sum := by decide
  have hdescent : baseEnd_958367 < baseStart_958367 := by decide
  rcases family_descends (prefixWord ++ tailWord_958367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958416 : List Nat := [2, 1, 1, 1, 1, 2, 7, 1, 3, 4]
def baseStart_958416 : Nat := 118140960795 + 958416 * 2 ^ 59
def prefixEnd_958416 : Nat := 4983230072969 + 3 ^ 40 * 958416 * 2
def baseEnd_958416 : Nat := 164042691653209142230777

theorem tailTrace_958416 : CollatzResearch.WordTrace tailWord_958416 prefixEnd_958416 164042691653209142230777 := by
  unfold tailWord_958416
  simp only [CollatzResearch.WordTrace]
  refine ⟨17478151647914995633163551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23304202197219994177551401 17478151647914995633163551)
  ·
    refine ⟨26217227471872493449745327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17478151647914995633163551 26217227471872493449745327)
    ·
      refine ⟨39325841207808740174617991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26217227471872493449745327 39325841207808740174617991)
      ·
        refine ⟨58988761811713110261926987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39325841207808740174617991 58988761811713110261926987)
        ·
          refine ⟨88483142717569665392890481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58988761811713110261926987 88483142717569665392890481)
          ·
            refine ⟨66362357038177249044667861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88483142717569665392890481 66362357038177249044667861)
            ·
              refine ⟨1555367743082279274484403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 66362357038177249044667861 1555367743082279274484403)
              ·
                refine ⟨2333051614623418911726605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1555367743082279274484403 2333051614623418911726605)
                ·
                  refine ⟨874894355483782091897477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2333051614623418911726605 874894355483782091897477)
                  ·
                    refine ⟨164042691653209142230777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 874894355483782091897477 164042691653209142230777)
                    ·
                      rfl

theorem cell23_958416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 1, 3, 4].length) (baseStart_958416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_958416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_958416 prefixEnd_958416 := by exact prefixLift 958416
  have htrace : WordTrace (prefixWord ++ tailWord_958416) baseStart_958416 baseEnd_958416 := by
    simpa [prefixWord, tailWord_958416, baseEnd_958416] using wordTrace_append hprefix tailTrace_958416
  have hstable : (prefixWord ++ tailWord_958416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958416).length < 2 ^ (prefixWord ++ tailWord_958416).sum := by decide
  have hdescent : baseEnd_958416 < baseStart_958416 := by decide
  rcases family_descends (prefixWord ++ tailWord_958416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958500 : List Nat := [2, 3, 1, 4, 2, 1, 1, 1, 1, 5, 2]
def baseStart_958500 : Nat := 118140960795 + 958500 * 2 ^ 59
def prefixEnd_958500 : Nat := 4983230072969 + 3 ^ 40 * 958500 * 2
def baseEnd_958500 : Nat := 492171207334605098041945

theorem tailTrace_958500 : CollatzResearch.WordTrace tailWord_958500 prefixEnd_958500 492171207334605098041945 := by
  unfold tailWord_958500
  simp only [CollatzResearch.WordTrace]
  refine ⟨17479683513762836806192477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23306244685017115741589969 17479683513762836806192477)
  ·
    refine ⟨6554881317661063802322179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17479683513762836806192477 6554881317661063802322179)
    ·
      refine ⟨9832321976491595703483269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6554881317661063802322179 9832321976491595703483269)
      ·
        refine ⟨1843560370592174194403113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9832321976491595703483269 1843560370592174194403113)
        ·
          refine ⟨1382670277944130645802335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1843560370592174194403113 1382670277944130645802335)
          ·
            refine ⟨2074005416916195968703503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1382670277944130645802335 2074005416916195968703503)
            ·
              refine ⟨3111008125374293953055255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2074005416916195968703503 3111008125374293953055255)
              ·
                refine ⟨4666512188061440929582883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3111008125374293953055255 4666512188061440929582883)
                ·
                  refine ⟨6999768282092161394374325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4666512188061440929582883 6999768282092161394374325)
                  ·
                    refine ⟨656228276446140130722593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6999768282092161394374325 656228276446140130722593)
                    ·
                      refine ⟨492171207334605098041945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 656228276446140130722593 492171207334605098041945)
                      ·
                        rfl

theorem cell23_958500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_958500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_958500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_958500 prefixEnd_958500 := by exact prefixLift 958500
  have htrace : WordTrace (prefixWord ++ tailWord_958500) baseStart_958500 baseEnd_958500 := by
    simpa [prefixWord, tailWord_958500, baseEnd_958500] using wordTrace_append hprefix tailTrace_958500
  have hstable : (prefixWord ++ tailWord_958500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958500).length < 2 ^ (prefixWord ++ tailWord_958500).sum := by decide
  have hdescent : baseEnd_958500 < baseStart_958500 := by decide
  rcases family_descends (prefixWord ++ tailWord_958500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958510 : List Nat := [4, 1, 3, 1, 1, 2, 4, 1, 1, 5]
def baseStart_958510 : Nat := 118140960795 + 958510 * 2 ^ 59
def prefixEnd_958510 : Nat := 4983230072969 + 3 ^ 40 * 958510 * 2
def baseEnd_958510 : Nat := 164058780713716686305633

theorem tailTrace_958510 : CollatzResearch.WordTrace tailWord_958510 prefixEnd_958510 164058780713716686305633 := by
  unfold tailWord_958510
  simp only [CollatzResearch.WordTrace]
  refine ⟨4369966469686180665031123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23306487838326296880165989 4369966469686180665031123)
  ·
    refine ⟨6554949704529270997546685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4369966469686180665031123 6554949704529270997546685)
    ·
      refine ⟨2458106139198476624080007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6554949704529270997546685 2458106139198476624080007)
      ·
        refine ⟨3687159208797714936120011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2458106139198476624080007 3687159208797714936120011)
        ·
          refine ⟨5530738813196572404180017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3687159208797714936120011 5530738813196572404180017)
          ·
            refine ⟨4148054109897429303135013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5530738813196572404180017 4148054109897429303135013)
            ·
              refine ⟨777760145605767994337815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4148054109897429303135013 777760145605767994337815)
              ·
                refine ⟨1166640218408651991506723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 777760145605767994337815 1166640218408651991506723)
                ·
                  refine ⟨1749960327612977987260085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1166640218408651991506723 1749960327612977987260085)
                  ·
                    refine ⟨164058780713716686305633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1749960327612977987260085 164058780713716686305633)
                    ·
                      rfl

theorem cell23_958510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_958510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_958510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_958510 prefixEnd_958510 := by exact prefixLift 958510
  have htrace : WordTrace (prefixWord ++ tailWord_958510) baseStart_958510 baseEnd_958510 := by
    simpa [prefixWord, tailWord_958510, baseEnd_958510] using wordTrace_append hprefix tailTrace_958510
  have hstable : (prefixWord ++ tailWord_958510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958510).length < 2 ^ (prefixWord ++ tailWord_958510).sum := by decide
  have hdescent : baseEnd_958510 < baseStart_958510 := by decide
  rcases family_descends (prefixWord ++ tailWord_958510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958513 : List Nat := [1, 2, 2, 3, 1, 4, 1, 3, 1, 1, 4]
def baseStart_958513 : Nat := 118140960795 + 958513 * 2 ^ 59
def prefixEnd_958513 : Nat := 4983230072969 + 3 ^ 40 * 958513 * 2
def baseEnd_958513 : Nat := 492177882583113547179385

theorem tailTrace_958513 : CollatzResearch.WordTrace tailWord_958513 prefixEnd_958513 492177882583113547179385 := by
  unfold tailWord_958513
  simp only [CollatzResearch.WordTrace]
  refine ⟨34959841176478576832608193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23306560784319051221738795 34959841176478576832608193)
  ·
    refine ⟨26219880882358932624456145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34959841176478576832608193 26219880882358932624456145)
    ·
      refine ⟨19664910661769199468342109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26219880882358932624456145 19664910661769199468342109)
      ·
        refine ⟨7374341498163449800628291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19664910661769199468342109 7374341498163449800628291)
        ·
          refine ⟨11061512247245174700942437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7374341498163449800628291 11061512247245174700942437)
          ·
            refine ⟨2074033546358470256426707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11061512247245174700942437 2074033546358470256426707)
            ·
              refine ⟨3111050319537705384640061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2074033546358470256426707 3111050319537705384640061)
              ·
                refine ⟨1166643869826639519240023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3111050319537705384640061 1166643869826639519240023)
                ·
                  refine ⟨1749965804739959278860035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1166643869826639519240023 1749965804739959278860035)
                  ·
                    refine ⟨2624948707109938918290053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1749965804739959278860035 2624948707109938918290053)
                    ·
                      refine ⟨492177882583113547179385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2624948707109938918290053 492177882583113547179385)
                      ·
                        rfl

theorem cell23_958513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 3, 1, 1, 4].length) (baseStart_958513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_958513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_958513 prefixEnd_958513 := by exact prefixLift 958513
  have htrace : WordTrace (prefixWord ++ tailWord_958513) baseStart_958513 baseEnd_958513 := by
    simpa [prefixWord, tailWord_958513, baseEnd_958513] using wordTrace_append hprefix tailTrace_958513
  have hstable : (prefixWord ++ tailWord_958513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958513).length < 2 ^ (prefixWord ++ tailWord_958513).sum := by decide
  have hdescent : baseEnd_958513 < baseStart_958513 := by decide
  rcases family_descends (prefixWord ++ tailWord_958513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958539 : List Nat := [1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 6]
def baseStart_958539 : Nat := 118140960795 + 958539 * 2 ^ 59
def prefixEnd_958539 : Nat := 4983230072969 + 3 ^ 40 * 958539 * 2
def baseEnd_958539 : Nat := 492191233080130445454265

theorem tailTrace_958539 : CollatzResearch.WordTrace tailWord_958539 prefixEnd_958539 492191233080130445454265 := by
  unfold tailWord_958539
  simp only [CollatzResearch.WordTrace]
  refine ⟨34960789474384383273054671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23307192982922922182036447 34960789474384383273054671)
  ·
    refine ⟨52441184211576574909582007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34960789474384383273054671 52441184211576574909582007)
    ·
      refine ⟨78661776317364862364373011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52441184211576574909582007 78661776317364862364373011)
      ·
        refine ⟨117992664476047293546559517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78661776317364862364373011 117992664476047293546559517)
        ·
          refine ⟨44247249178517735079959819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117992664476047293546559517 44247249178517735079959819)
          ·
            refine ⟨66370873767776602619939729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44247249178517735079959819 66370873767776602619939729)
            ·
              refine ⟨49778155325832451964954797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66370873767776602619939729 49778155325832451964954797)
              ·
                refine ⟨18666808247187169486858049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49778155325832451964954797 18666808247187169486858049)
                ·
                  refine ⟨14000106185390377115143537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18666808247187169486858049 14000106185390377115143537)
                  ·
                    refine ⟨10500079639042782836357653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14000106185390377115143537 10500079639042782836357653)
                    ·
                      refine ⟨492191233080130445454265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10500079639042782836357653 492191233080130445454265)
                      ·
                        rfl

theorem cell23_958539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 6].length) (baseStart_958539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_958539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_958539 prefixEnd_958539 := by exact prefixLift 958539
  have htrace : WordTrace (prefixWord ++ tailWord_958539) baseStart_958539 baseEnd_958539 := by
    simpa [prefixWord, tailWord_958539, baseEnd_958539] using wordTrace_append hprefix tailTrace_958539
  have hstable : (prefixWord ++ tailWord_958539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958539).length < 2 ^ (prefixWord ++ tailWord_958539).sum := by decide
  have hdescent : baseEnd_958539 < baseStart_958539 := by decide
  rcases family_descends (prefixWord ++ tailWord_958539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958558 : List Nat := [4, 4, 1, 1, 2, 2, 1, 3, 1, 1, 3]
def baseStart_958558 : Nat := 118140960795 + 958558 * 2 ^ 59
def prefixEnd_958558 : Nat := 4983230072969 + 3 ^ 40 * 958558 * 2
def baseEnd_958558 : Nat := 492200989212565871116679

theorem tailTrace_958558 : CollatzResearch.WordTrace tailWord_958558 prefixEnd_958558 492200989212565871116679 := by
  unfold tailWord_958558
  simp only [CollatzResearch.WordTrace]
  refine ⟨4370185307664443689749541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23307654974210366345330885 4370185307664443689749541)
  ·
    refine ⟨819409745187083191828039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4370185307664443689749541 819409745187083191828039)
    ·
      refine ⟨1229114617780624787742059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 819409745187083191828039 1229114617780624787742059)
      ·
        refine ⟨1843671926670937181613089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1229114617780624787742059 1843671926670937181613089)
        ·
          refine ⟨1382753945003202886209817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1843671926670937181613089 1382753945003202886209817)
          ·
            refine ⟨1037065458752402164657363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1382753945003202886209817 1037065458752402164657363)
            ·
              refine ⟨1555598188128603246986045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1037065458752402164657363 1555598188128603246986045)
              ·
                refine ⟨583349320548226217619767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1555598188128603246986045 583349320548226217619767)
                ·
                  refine ⟨875023980822339326429651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 583349320548226217619767 875023980822339326429651)
                  ·
                    refine ⟨1312535971233508989644477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 875023980822339326429651 1312535971233508989644477)
                    ·
                      refine ⟨492200989212565871116679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1312535971233508989644477 492200989212565871116679)
                      ·
                        rfl

theorem cell23_958558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_958558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_958558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_958558 prefixEnd_958558 := by exact prefixLift 958558
  have htrace : WordTrace (prefixWord ++ tailWord_958558) baseStart_958558 baseEnd_958558 := by
    simpa [prefixWord, tailWord_958558, baseEnd_958558] using wordTrace_append hprefix tailTrace_958558
  have hstable : (prefixWord ++ tailWord_958558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958558).length < 2 ^ (prefixWord ++ tailWord_958558).sum := by decide
  have hdescent : baseEnd_958558 < baseStart_958558 := by decide
  rcases family_descends (prefixWord ++ tailWord_958558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958563 : List Nat := [1, 1, 1, 5, 1, 1, 3, 2, 4, 1, 3]
def baseStart_958563 : Nat := 118140960795 + 958563 * 2 ^ 59
def prefixEnd_958563 : Nat := 4983230072969 + 3 ^ 40 * 958563 * 2
def baseEnd_958563 : Nat := 492203556615838351554155

theorem tailTrace_958563 : CollatzResearch.WordTrace tailWord_958563 prefixEnd_958563 492203556615838351554155 := by
  unfold tailWord_958563
  simp only [CollatzResearch.WordTrace]
  refine ⟨34961664826297435371928343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23307776550864956914618895 34961664826297435371928343)
  ·
    refine ⟨52442497239446153057892515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34961664826297435371928343 52442497239446153057892515)
    ·
      refine ⟨78663745859169229586838773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52442497239446153057892515 78663745859169229586838773)
      ·
        refine ⟨7374726174297115273766135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78663745859169229586838773 7374726174297115273766135)
        ·
          refine ⟨11062089261445672910649203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7374726174297115273766135 11062089261445672910649203)
          ·
            refine ⟨16593133892168509365973805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11062089261445672910649203 16593133892168509365973805)
            ·
              refine ⟨6222425209563191012240177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16593133892168509365973805 6222425209563191012240177)
              ·
                refine ⟨4666818907172393259180133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6222425209563191012240177 4666818907172393259180133)
                ·
                  refine ⟨875028545094823736096275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4666818907172393259180133 875028545094823736096275)
                  ·
                    refine ⟨1312542817642235604144413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 875028545094823736096275 1312542817642235604144413)
                    ·
                      refine ⟨492203556615838351554155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1312542817642235604144413 492203556615838351554155)
                      ·
                        rfl

theorem cell23_958563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 4, 1, 3].length) (baseStart_958563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_958563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_958563 prefixEnd_958563 := by exact prefixLift 958563
  have htrace : WordTrace (prefixWord ++ tailWord_958563) baseStart_958563 baseEnd_958563 := by
    simpa [prefixWord, tailWord_958563, baseEnd_958563] using wordTrace_append hprefix tailTrace_958563
  have hstable : (prefixWord ++ tailWord_958563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958563).length < 2 ^ (prefixWord ++ tailWord_958563).sum := by decide
  have hdescent : baseEnd_958563 < baseStart_958563 := by decide
  rcases family_descends (prefixWord ++ tailWord_958563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958596 : List Nat := [2, 3, 2, 1, 2, 1, 2, 1, 1, 8]
def baseStart_958596 : Nat := 118140960795 + 958596 * 2 ^ 59
def prefixEnd_958596 : Nat := 4983230072969 + 3 ^ 40 * 958596 * 2
def baseEnd_958596 : Nat := 164073500492478907480501

theorem tailTrace_958596 : CollatzResearch.WordTrace tailWord_958596 prefixEnd_958596 164073500492478907480501 := by
  unfold tailWord_958596
  simp only [CollatzResearch.WordTrace]
  refine ⟨17481434217588941003939821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23308578956785254671919761 17481434217588941003939821)
  ·
    refine ⟨6555537831595852876477433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17481434217588941003939821 6555537831595852876477433)
    ·
      refine ⟨4916653373696889657358075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6555537831595852876477433 4916653373696889657358075)
      ·
        refine ⟨7374980060545334486037113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4916653373696889657358075 7374980060545334486037113)
        ·
          refine ⟨5531235045409000864527835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7374980060545334486037113 5531235045409000864527835)
          ·
            refine ⟨8296852568113501296791753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5531235045409000864527835 8296852568113501296791753)
            ·
              refine ⟨6222639426085125972593815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8296852568113501296791753 6222639426085125972593815)
              ·
                refine ⟨9333959139127688958890723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6222639426085125972593815 9333959139127688958890723)
                ·
                  refine ⟨14000938708691533438336085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9333959139127688958890723 14000938708691533438336085)
                  ·
                    refine ⟨164073500492478907480501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 14000938708691533438336085 164073500492478907480501)
                    ·
                      rfl

theorem cell23_958596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_958596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_958596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_958596 prefixEnd_958596 := by exact prefixLift 958596
  have htrace : WordTrace (prefixWord ++ tailWord_958596) baseStart_958596 baseEnd_958596 := by
    simpa [prefixWord, tailWord_958596, baseEnd_958596] using wordTrace_append hprefix tailTrace_958596
  have hstable : (prefixWord ++ tailWord_958596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958596).length < 2 ^ (prefixWord ++ tailWord_958596).sum := by decide
  have hdescent : baseEnd_958596 < baseStart_958596 := by decide
  rcases family_descends (prefixWord ++ tailWord_958596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958597 : List Nat := [1, 3, 1, 1, 5, 1, 4, 1, 2, 1, 3]
def baseStart_958597 : Nat := 118140960795 + 958597 * 2 ^ 59
def prefixEnd_958597 : Nat := 4983230072969 + 3 ^ 40 * 958597 * 2
def baseEnd_958597 : Nat := 492221014958091218528999

theorem tailTrace_958597 : CollatzResearch.WordTrace tailWord_958597 prefixEnd_958597 492221014958091218528999 := by
  unfold tailWord_958597
  simp only [CollatzResearch.WordTrace]
  refine ⟨34962904908174259178666045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23308603272116172785777363 34962904908174259178666045)
  ·
    refine ⟨13111089340565347191999767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34962904908174259178666045 13111089340565347191999767)
    ·
      refine ⟨19666634010848020787999651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13111089340565347191999767 19666634010848020787999651)
      ·
        refine ⟨29499951016272031181999477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19666634010848020787999651 29499951016272031181999477)
        ·
          refine ⟨2765620407775502923312451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29499951016272031181999477 2765620407775502923312451)
          ·
            refine ⟨4148430611663254384968677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2765620407775502923312451 4148430611663254384968677)
            ·
              refine ⟨777830739686860197181627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4148430611663254384968677 777830739686860197181627)
              ·
                refine ⟨1166746109530290295772441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 777830739686860197181627 1166746109530290295772441)
                ·
                  refine ⟨875059582147717721829331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1166746109530290295772441 875059582147717721829331)
                  ·
                    refine ⟨1312589373221576582743997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 875059582147717721829331 1312589373221576582743997)
                    ·
                      refine ⟨492221014958091218528999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1312589373221576582743997 492221014958091218528999)
                      ·
                        rfl

theorem cell23_958597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 4, 1, 2, 1, 3].length) (baseStart_958597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_958597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_958597 prefixEnd_958597 := by exact prefixLift 958597
  have htrace : WordTrace (prefixWord ++ tailWord_958597) baseStart_958597 baseEnd_958597 := by
    simpa [prefixWord, tailWord_958597, baseEnd_958597] using wordTrace_append hprefix tailTrace_958597
  have hstable : (prefixWord ++ tailWord_958597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958597).length < 2 ^ (prefixWord ++ tailWord_958597).sum := by decide
  have hdescent : baseEnd_958597 < baseStart_958597 := by decide
  rcases family_descends (prefixWord ++ tailWord_958597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958620 : List Nat := [2, 2, 3, 2, 1, 1, 3, 2, 1, 4, 2]
def baseStart_958620 : Nat := 118140960795 + 958620 * 2 ^ 59
def prefixEnd_958620 : Nat := 4983230072969 + 3 ^ 40 * 958620 * 2
def baseEnd_958620 : Nat := 492232825013144628541393

theorem tailTrace_958620 : CollatzResearch.WordTrace tailWord_958620 prefixEnd_958620 492232825013144628541393 := by
  unfold tailWord_958620
  simp only [CollatzResearch.WordTrace]
  refine ⟨17481871893545467053376657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23309162524727289404502209 17481871893545467053376657)
  ·
    refine ⟨13111403920159100290032493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17481871893545467053376657 13111403920159100290032493)
    ·
      refine ⟨4916776470059662608762185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13111403920159100290032493 4916776470059662608762185)
      ·
        refine ⟨3687582352544746956571639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4916776470059662608762185 3687582352544746956571639)
        ·
          refine ⟨5531373528817120434857459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3687582352544746956571639 5531373528817120434857459)
          ·
            refine ⟨8297060293225680652286189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5531373528817120434857459 8297060293225680652286189)
            ·
              refine ⟨3111397609959630244607321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8297060293225680652286189 3111397609959630244607321)
              ·
                refine ⟨2333548207469722683455491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3111397609959630244607321 2333548207469722683455491)
                ·
                  refine ⟨3500322311204584025183237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2333548207469722683455491 3500322311204584025183237)
                  ·
                    refine ⟨656310433350859504721857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3500322311204584025183237 656310433350859504721857)
                    ·
                      refine ⟨492232825013144628541393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 656310433350859504721857 492232825013144628541393)
                      ·
                        rfl

theorem cell23_958620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 2, 1, 4, 2].length) (baseStart_958620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_958620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_958620 prefixEnd_958620 := by exact prefixLift 958620
  have htrace : WordTrace (prefixWord ++ tailWord_958620) baseStart_958620 baseEnd_958620 := by
    simpa [prefixWord, tailWord_958620, baseEnd_958620] using wordTrace_append hprefix tailTrace_958620
  have hstable : (prefixWord ++ tailWord_958620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958620).length < 2 ^ (prefixWord ++ tailWord_958620).sum := by decide
  have hdescent : baseEnd_958620 < baseStart_958620 := by decide
  rcases family_descends (prefixWord ++ tailWord_958620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958623 : List Nat := [1, 1, 2, 6, 1, 1, 2, 1, 2, 1, 5]
def baseStart_958623 : Nat := 118140960795 + 958623 * 2 ^ 59
def prefixEnd_958623 : Nat := 4983230072969 + 3 ^ 40 * 958623 * 2
def baseEnd_958623 : Nat := 492234365455108116803879

theorem tailTrace_958623 : CollatzResearch.WordTrace tailWord_958623 prefixEnd_958623 492234365455108116803879 := by
  unfold tailWord_958623
  simp only [CollatzResearch.WordTrace]
  refine ⟨34963853206080065619112523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23309235470720043746075015 34963853206080065619112523)
  ·
    refine ⟨52445779809120098428668785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34963853206080065619112523 52445779809120098428668785)
    ·
      refine ⟨39334334856840073821501589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52445779809120098428668785 39334334856840073821501589)
      ·
        refine ⟨1843796946414378460382887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 39334334856840073821501589 1843796946414378460382887)
        ·
          refine ⟨2765695419621567690574331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1843796946414378460382887 2765695419621567690574331)
          ·
            refine ⟨4148543129432351535861497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2765695419621567690574331 4148543129432351535861497)
            ·
              refine ⟨3111407347074263651896123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4148543129432351535861497 3111407347074263651896123)
              ·
                refine ⟨4667111020611395477844185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3111407347074263651896123 4667111020611395477844185)
                ·
                  refine ⟨3500333265458546608383139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4667111020611395477844185 3500333265458546608383139)
                  ·
                    refine ⟨5250499898187819912574709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3500333265458546608383139 5250499898187819912574709)
                    ·
                      refine ⟨492234365455108116803879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5250499898187819912574709 492234365455108116803879)
                      ·
                        rfl

theorem cell23_958623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_958623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_958623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_958623 prefixEnd_958623 := by exact prefixLift 958623
  have htrace : WordTrace (prefixWord ++ tailWord_958623) baseStart_958623 baseEnd_958623 := by
    simpa [prefixWord, tailWord_958623, baseEnd_958623] using wordTrace_append hprefix tailTrace_958623
  have hstable : (prefixWord ++ tailWord_958623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958623).length < 2 ^ (prefixWord ++ tailWord_958623).sum := by decide
  have hdescent : baseEnd_958623 < baseStart_958623 := by decide
  rcases family_descends (prefixWord ++ tailWord_958623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958673 : List Nat := [1, 2, 2, 1, 2, 2, 5, 1, 2, 5]
def baseStart_958673 : Nat := 118140960795 + 958673 * 2 ^ 59
def prefixEnd_958673 : Nat := 4983230072969 + 3 ^ 40 * 958673 * 2
def baseEnd_958673 : Nat := 164086679829277640392883

theorem tailTrace_958673 : CollatzResearch.WordTrace tailWord_958673 prefixEnd_958673 164086679829277640392883 := by
  unfold tailWord_958673
  simp only [CollatzResearch.WordTrace]
  refine ⟨34965676855898924158432673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23310451237265949438955115 34965676855898924158432673)
  ·
    refine ⟨26224257641924193118824505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34965676855898924158432673 26224257641924193118824505)
    ·
      refine ⟨19668193231443144839118379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26224257641924193118824505 19668193231443144839118379)
      ·
        refine ⟨29502289847164717258677569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19668193231443144839118379 29502289847164717258677569)
        ·
          refine ⟨22126717385373537944008177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29502289847164717258677569 22126717385373537944008177)
          ·
            refine ⟨16595038039030153458006133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22126717385373537944008177 16595038039030153458006133)
            ·
              refine ⟨1555784816159076886688075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16595038039030153458006133 1555784816159076886688075)
              ·
                refine ⟨2333677224238615330032113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1555784816159076886688075 2333677224238615330032113)
                ·
                  refine ⟨1750257918178961497524085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2333677224238615330032113 1750257918178961497524085)
                  ·
                    refine ⟨164086679829277640392883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1750257918178961497524085 164086679829277640392883)
                    ·
                      rfl

theorem cell23_958673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 1, 2, 5].length) (baseStart_958673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_958673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_958673 prefixEnd_958673 := by exact prefixLift 958673
  have htrace : WordTrace (prefixWord ++ tailWord_958673) baseStart_958673 baseEnd_958673 := by
    simpa [prefixWord, tailWord_958673, baseEnd_958673] using wordTrace_append hprefix tailTrace_958673
  have hstable : (prefixWord ++ tailWord_958673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958673).length < 2 ^ (prefixWord ++ tailWord_958673).sum := by decide
  have hdescent : baseEnd_958673 < baseStart_958673 := by decide
  rcases family_descends (prefixWord ++ tailWord_958673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958677 : List Nat := [1, 3, 2, 4, 2, 1, 2, 3, 5]
def baseStart_958677 : Nat := 118140960795 + 958677 * 2 ^ 59
def prefixEnd_958677 : Nat := 4983230072969 + 3 ^ 40 * 958677 * 2
def baseEnd_958677 : Nat := 54695788156716767280959

theorem tailTrace_958677 : CollatzResearch.WordTrace tailWord_958677 prefixEnd_958677 54695788156716767280959 := by
  unfold tailWord_958677
  simp only [CollatzResearch.WordTrace]
  refine ⟨34965822747884432841578285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23310548498589621894385523 34965822747884432841578285)
  ·
    refine ⟨13112183530456662315591857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34965822747884432841578285 13112183530456662315591857)
    ·
      refine ⟨9834137647842496736693893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13112183530456662315591857 9834137647842496736693893)
      ·
        refine ⟨1843900808970468138130105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9834137647842496736693893 1843900808970468138130105)
        ·
          refine ⟨1382925606727851103597579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1843900808970468138130105 1382925606727851103597579)
          ·
            refine ⟨2074388410091776655396369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1382925606727851103597579 2074388410091776655396369)
            ·
              refine ⟨1555791307568832491547277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2074388410091776655396369 1555791307568832491547277)
              ·
                refine ⟨583421740338312184330229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1555791307568832491547277 583421740338312184330229)
                ·
                  refine ⟨54695788156716767280959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 583421740338312184330229 54695788156716767280959)
                  ·
                    rfl

theorem cell23_958677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 3, 5].length) (baseStart_958677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_958677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_958677 prefixEnd_958677 := by exact prefixLift 958677
  have htrace : WordTrace (prefixWord ++ tailWord_958677) baseStart_958677 baseEnd_958677 := by
    simpa [prefixWord, tailWord_958677, baseEnd_958677] using wordTrace_append hprefix tailTrace_958677
  have hstable : (prefixWord ++ tailWord_958677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958677).length < 2 ^ (prefixWord ++ tailWord_958677).sum := by decide
  have hdescent : baseEnd_958677 < baseStart_958677 := by decide
  rcases family_descends (prefixWord ++ tailWord_958677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958713 : List Nat := [1, 2, 1, 3, 1, 1, 2, 1, 6, 2, 3]
def baseStart_958713 : Nat := 118140960795 + 958713 * 2 ^ 59
def prefixEnd_958713 : Nat := 4983230072969 + 3 ^ 40 * 958713 * 2
def baseEnd_958713 : Nat := 492280578714012764678465

theorem tailTrace_958713 : CollatzResearch.WordTrace tailWord_958713 prefixEnd_958713 492280578714012764678465 := by
  unfold tailWord_958713
  simp only [CollatzResearch.WordTrace]
  refine ⟨34967135775754010989888793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23311423850502673993259195 34967135775754010989888793)
  ·
    refine ⟨26225351831815508242416595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34967135775754010989888793 26225351831815508242416595)
    ·
      refine ⟨39338027747723262363624893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26225351831815508242416595 39338027747723262363624893)
      ·
        refine ⟨14751760405396223386359335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39338027747723262363624893 14751760405396223386359335)
        ·
          refine ⟨22127640608094335079539003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14751760405396223386359335 22127640608094335079539003)
          ·
            refine ⟨33191460912141502619308505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22127640608094335079539003 33191460912141502619308505)
            ·
              refine ⟨24893595684106126964481379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33191460912141502619308505 24893595684106126964481379)
              ·
                refine ⟨37340393526159190446722069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24893595684106126964481379 37340393526159190446722069)
                ·
                  refine ⟨1750330946538712052190097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 37340393526159190446722069 1750330946538712052190097)
                  ·
                    refine ⟨1312748209904034039142573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1750330946538712052190097 1312748209904034039142573)
                    ·
                      refine ⟨492280578714012764678465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1312748209904034039142573 492280578714012764678465)
                      ·
                        rfl

theorem cell23_958713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 6, 2, 3].length) (baseStart_958713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_958713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_958713 prefixEnd_958713 := by exact prefixLift 958713
  have htrace : WordTrace (prefixWord ++ tailWord_958713) baseStart_958713 baseEnd_958713 := by
    simpa [prefixWord, tailWord_958713, baseEnd_958713] using wordTrace_append hprefix tailTrace_958713
  have hstable : (prefixWord ++ tailWord_958713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958713).length < 2 ^ (prefixWord ++ tailWord_958713).sum := by decide
  have hdescent : baseEnd_958713 < baseStart_958713 := by decide
  rcases family_descends (prefixWord ++ tailWord_958713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958736 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 6]
def baseStart_958736 : Nat := 118140960795 + 958736 * 2 ^ 59
def prefixEnd_958736 : Nat := 4983230072969 + 3 ^ 40 * 958736 * 2
def baseEnd_958736 : Nat := 492292388769066174690859

theorem tailTrace_958736 : CollatzResearch.WordTrace tailWord_958736 prefixEnd_958736 492292388769066174690859 := by
  unfold tailWord_958736
  simp only [CollatzResearch.WordTrace]
  refine ⟨17483987327335342958988031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23311983103113790611984041 17483987327335342958988031)
  ·
    refine ⟨26225980991003014438482047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17483987327335342958988031 26225980991003014438482047)
    ·
      refine ⟨39338971486504521657723071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26225980991003014438482047 39338971486504521657723071)
      ·
        refine ⟨59008457229756782486584607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39338971486504521657723071 59008457229756782486584607)
        ·
          refine ⟨88512685844635173729876911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59008457229756782486584607 88512685844635173729876911)
          ·
            refine ⟨132769028766952760594815367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88512685844635173729876911 132769028766952760594815367)
            ·
              refine ⟨199153543150429140892223051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132769028766952760594815367 199153543150429140892223051)
              ·
                refine ⟨298730314725643711338334577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199153543150429140892223051 298730314725643711338334577)
                ·
                  refine ⟨224047736044232783503750933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 298730314725643711338334577 224047736044232783503750933)
                  ·
                    refine ⟨10502237627073411726738325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 224047736044232783503750933 10502237627073411726738325)
                    ·
                      refine ⟨492292388769066174690859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10502237627073411726738325 492292388769066174690859)
                      ·
                        rfl

theorem cell23_958736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 6].length) (baseStart_958736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_958736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_958736 prefixEnd_958736 := by exact prefixLift 958736
  have htrace : WordTrace (prefixWord ++ tailWord_958736) baseStart_958736 baseEnd_958736 := by
    simpa [prefixWord, tailWord_958736, baseEnd_958736] using wordTrace_append hprefix tailTrace_958736
  have hstable : (prefixWord ++ tailWord_958736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958736).length < 2 ^ (prefixWord ++ tailWord_958736).sum := by decide
  have hdescent : baseEnd_958736 < baseStart_958736 := by decide
  rcases family_descends (prefixWord ++ tailWord_958736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958737 : List Nat := [1, 2, 2, 1, 1, 5, 3, 3, 1, 4]
def baseStart_958737 : Nat := 118140960795 + 958737 * 2 ^ 59
def prefixEnd_958737 : Nat := 4983230072969 + 3 ^ 40 * 958737 * 2
def baseEnd_958737 : Nat := 164097634083240223592785

theorem tailTrace_958737 : CollatzResearch.WordTrace tailWord_958737 prefixEnd_958737 164097634083240223592785 := by
  unfold tailWord_958737
  simp only [CollatzResearch.WordTrace]
  refine ⟨34968011127667063088762465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23312007418444708725841643 34968011127667063088762465)
  ·
    refine ⟨26226008345750297316571849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34968011127667063088762465 26226008345750297316571849)
    ·
      refine ⟨19669506259312722987428887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26226008345750297316571849 19669506259312722987428887)
      ·
        refine ⟨29504259388969084481143331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19669506259312722987428887 29504259388969084481143331)
        ·
          refine ⟨44256389083453626721714997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29504259388969084481143331 44256389083453626721714997)
          ·
            refine ⟨4149036476573777505160781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44256389083453626721714997 4149036476573777505160781)
            ·
              refine ⟨1555888678715166564435293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4149036476573777505160781 1555888678715166564435293)
              ·
                refine ⟨583458254518187461663235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1555888678715166564435293 583458254518187461663235)
                ·
                  refine ⟨875187381777281192494853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 583458254518187461663235 875187381777281192494853)
                  ·
                    refine ⟨164097634083240223592785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 875187381777281192494853 164097634083240223592785)
                    ·
                      rfl

theorem cell23_958737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 3, 1, 4].length) (baseStart_958737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_958737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_958737 prefixEnd_958737 := by exact prefixLift 958737
  have htrace : WordTrace (prefixWord ++ tailWord_958737) baseStart_958737 baseEnd_958737 := by
    simpa [prefixWord, tailWord_958737, baseEnd_958737] using wordTrace_append hprefix tailTrace_958737
  have hstable : (prefixWord ++ tailWord_958737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958737).length < 2 ^ (prefixWord ++ tailWord_958737).sum := by decide
  have hdescent : baseEnd_958737 < baseStart_958737 := by decide
  rcases family_descends (prefixWord ++ tailWord_958737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958803 : List Nat := [1, 1, 1, 2, 1, 1, 4, 5, 1, 1, 5]
def baseStart_958803 : Nat := 118140960795 + 958803 * 2 ^ 59
def prefixEnd_958803 : Nat := 4983230072969 + 3 ^ 40 * 958803 * 2
def baseEnd_958803 : Nat := 492326791972917412553051

theorem tailTrace_958803 : CollatzResearch.WordTrace tailWord_958803 prefixEnd_958803 492326791972917412553051 := by
  unfold tailWord_958803
  simp only [CollatzResearch.WordTrace]
  refine ⟨34970418345427956360665063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23313612230285304240443375 34970418345427956360665063)
  ·
    refine ⟨52455627518141934540997595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34970418345427956360665063 52455627518141934540997595)
    ·
      refine ⟨78683441277212901811496393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52455627518141934540997595 78683441277212901811496393)
      ·
        refine ⟨59012580957909676358622295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78683441277212901811496393 59012580957909676358622295)
        ·
          refine ⟨88518871436864514537933443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59012580957909676358622295 88518871436864514537933443)
          ·
            refine ⟨132778307155296771806900165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88518871436864514537933443 132778307155296771806900165)
            ·
              refine ⟨24895932591618144713793781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132778307155296771806900165 24895932591618144713793781)
              ·
                refine ⟨2333993680464201066918167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24895932591618144713793781 2333993680464201066918167)
                ·
                  refine ⟨3500990520696301600377251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2333993680464201066918167 3500990520696301600377251)
                  ·
                    refine ⟨5251485781044452400565877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3500990520696301600377251 5251485781044452400565877)
                    ·
                      refine ⟨492326791972917412553051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5251485781044452400565877 492326791972917412553051)
                      ·
                        rfl

theorem cell23_958803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 5, 1, 1, 5].length) (baseStart_958803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_958803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_958803 prefixEnd_958803 := by exact prefixLift 958803
  have htrace : WordTrace (prefixWord ++ tailWord_958803) baseStart_958803 baseEnd_958803 := by
    simpa [prefixWord, tailWord_958803, baseEnd_958803] using wordTrace_append hprefix tailTrace_958803
  have hstable : (prefixWord ++ tailWord_958803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958803).length < 2 ^ (prefixWord ++ tailWord_958803).sum := by decide
  have hdescent : baseEnd_958803 < baseStart_958803 := by decide
  rcases family_descends (prefixWord ++ tailWord_958803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958820 : List Nat := [2, 3, 1, 1, 3, 1, 1, 1, 5, 2, 3]
def baseStart_958820 : Nat := 118140960795 + 958820 * 2 ^ 59
def prefixEnd_958820 : Nat := 4983230072969 + 3 ^ 40 * 958820 * 2
def baseEnd_958820 : Nat := 492335521144043846040473

theorem tailTrace_958820 : CollatzResearch.WordTrace tailWord_958820 prefixEnd_958820 492335521144043846040473 := by
  unfold tailWord_958820
  simp only [CollatzResearch.WordTrace]
  refine ⟨17485519193183184132016957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23314025590910912176022609 17485519193183184132016957)
  ·
    refine ⟨6557069697443694049506359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17485519193183184132016957 6557069697443694049506359)
    ·
      refine ⟨9835604546165541074259539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6557069697443694049506359 9835604546165541074259539)
      ·
        refine ⟨14753406819248311611389309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9835604546165541074259539 14753406819248311611389309)
        ·
          refine ⟨5532527557218116854270991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14753406819248311611389309 5532527557218116854270991)
          ·
            refine ⟨8298791335827175281406487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5532527557218116854270991 8298791335827175281406487)
            ·
              refine ⟨12448187003740762922109731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8298791335827175281406487 12448187003740762922109731)
              ·
                refine ⟨18672280505611144383164597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12448187003740762922109731 18672280505611144383164597)
                ·
                  refine ⟨1750526297401044785921681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18672280505611144383164597 1750526297401044785921681)
                  ·
                    refine ⟨1312894723050783589441261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1750526297401044785921681 1312894723050783589441261)
                    ·
                      refine ⟨492335521144043846040473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1312894723050783589441261 492335521144043846040473)
                      ·
                        rfl

theorem cell23_958820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 5, 2, 3].length) (baseStart_958820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_958820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_958820 prefixEnd_958820 := by exact prefixLift 958820
  have htrace : WordTrace (prefixWord ++ tailWord_958820) baseStart_958820 baseEnd_958820 := by
    simpa [prefixWord, tailWord_958820, baseEnd_958820] using wordTrace_append hprefix tailTrace_958820
  have hstable : (prefixWord ++ tailWord_958820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958820).length < 2 ^ (prefixWord ++ tailWord_958820).sum := by decide
  have hdescent : baseEnd_958820 < baseStart_958820 := by decide
  rcases family_descends (prefixWord ++ tailWord_958820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958834 : List Nat := [3, 2, 1, 2, 1, 4, 1, 2, 3, 2, 2]
def baseStart_958834 : Nat := 118140960795 + 958834 * 2 ^ 59
def prefixEnd_958834 : Nat := 4983230072969 + 3 ^ 40 * 958834 * 2
def baseEnd_958834 : Nat := 492342709873206791265409

theorem tailTrace_958834 : CollatzResearch.WordTrace tailWord_958834 prefixEnd_958834 492342709873206791265409 := by
  unfold tailWord_958834
  simp only [CollatzResearch.WordTrace]
  refine ⟨8742887252078912163760889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23314366005543765770029037 8742887252078912163760889)
  ·
    refine ⟨6557165439059184122820667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8742887252078912163760889 6557165439059184122820667)
    ·
      refine ⟨9835748158588776184231001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6557165439059184122820667 9835748158588776184231001)
      ·
        refine ⟨7376811118941582138173251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9835748158588776184231001 7376811118941582138173251)
        ·
          refine ⟨11065216678412373207259877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7376811118941582138173251 11065216678412373207259877)
          ·
            refine ⟨2074728127202319976361227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11065216678412373207259877 2074728127202319976361227)
            ·
              refine ⟨3112092190803479964541841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2074728127202319976361227 3112092190803479964541841)
              ·
                refine ⟨2334069143102609973406381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3112092190803479964541841 2334069143102609973406381)
                ·
                  refine ⟨875275928663478740027393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2334069143102609973406381 875275928663478740027393)
                  ·
                    refine ⟨656456946497609055020545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 875275928663478740027393 656456946497609055020545)
                    ·
                      refine ⟨492342709873206791265409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 656456946497609055020545 492342709873206791265409)
                      ·
                        rfl

theorem cell23_958834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 2, 3, 2, 2].length) (baseStart_958834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_958834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_958834 prefixEnd_958834 := by exact prefixLift 958834
  have htrace : WordTrace (prefixWord ++ tailWord_958834) baseStart_958834 baseEnd_958834 := by
    simpa [prefixWord, tailWord_958834, baseEnd_958834] using wordTrace_append hprefix tailTrace_958834
  have hstable : (prefixWord ++ tailWord_958834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958834).length < 2 ^ (prefixWord ++ tailWord_958834).sum := by decide
  have hdescent : baseEnd_958834 < baseStart_958834 := by decide
  rcases family_descends (prefixWord ++ tailWord_958834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958837 : List Nat := [1, 3, 4, 1, 2, 1, 2, 1, 3, 2, 3]
def baseStart_958837 : Nat := 118140960795 + 958837 * 2 ^ 59
def prefixEnd_958837 : Nat := 4983230072969 + 3 ^ 40 * 958837 * 2
def baseEnd_958837 : Nat := 492344250315170279527895

theorem tailTrace_958837 : CollatzResearch.WordTrace tailWord_958837 prefixEnd_958837 492344250315170279527895 := by
  unfold tailWord_958837
  simp only [CollatzResearch.WordTrace]
  refine ⟨34971658427304780167402765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23314438951536520111601843 34971658427304780167402765)
  ·
    refine ⟨13114371910239292562776037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34971658427304780167402765 13114371910239292562776037)
    ·
      refine ⟨2458944733169867355520507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13114371910239292562776037 2458944733169867355520507)
      ·
        refine ⟨3688417099754801033280761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2458944733169867355520507 3688417099754801033280761)
        ·
          refine ⟨2766312824816100774960571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3688417099754801033280761 2766312824816100774960571)
          ·
            refine ⟨4149469237224151162440857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2766312824816100774960571 4149469237224151162440857)
            ·
              refine ⟨3112101927918113371830643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4149469237224151162440857 3112101927918113371830643)
              ·
                refine ⟨4668152891877170057745965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3112101927918113371830643 4668152891877170057745965)
                ·
                  refine ⟨1750557334453938771654737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4668152891877170057745965 1750557334453938771654737)
                  ·
                    refine ⟨1312918000840454078741053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1750557334453938771654737 1312918000840454078741053)
                    ·
                      refine ⟨492344250315170279527895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1312918000840454078741053 492344250315170279527895)
                      ·
                        rfl

theorem cell23_958837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_958837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_958837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_958837 prefixEnd_958837 := by exact prefixLift 958837
  have htrace : WordTrace (prefixWord ++ tailWord_958837) baseStart_958837 baseEnd_958837 := by
    simpa [prefixWord, tailWord_958837, baseEnd_958837] using wordTrace_append hprefix tailTrace_958837
  have hstable : (prefixWord ++ tailWord_958837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958837).length < 2 ^ (prefixWord ++ tailWord_958837).sum := by decide
  have hdescent : baseEnd_958837 < baseStart_958837 := by decide
  rcases family_descends (prefixWord ++ tailWord_958837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958838 : List Nat := [5, 1, 1, 4, 1, 2, 1, 1, 2, 3, 2]
def baseStart_958838 : Nat := 118140960795 + 958838 * 2 ^ 59
def prefixEnd_958838 : Nat := 4983230072969 + 3 ^ 40 * 958838 * 2
def baseEnd_958838 : Nat := 492344763795824775615391

theorem tailTrace_958838 : CollatzResearch.WordTrace tailWord_958838 prefixEnd_958838 492344763795824775615391 := by
  unfold tailWord_958838
  simp only [CollatzResearch.WordTrace]
  refine ⟨2185730931268822333636823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23314463266867438225459445 2185730931268822333636823)
  ·
    refine ⟨3278596396903233500455235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2185730931268822333636823 3278596396903233500455235)
    ·
      refine ⟨4917894595354850250682853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3278596396903233500455235 4917894595354850250682853)
      ·
        refine ⟨922105236629034422003035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4917894595354850250682853 922105236629034422003035)
        ·
          refine ⟨1383157854943551633004553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 922105236629034422003035 1383157854943551633004553)
          ·
            refine ⟨1037368391207663724753415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1383157854943551633004553 1037368391207663724753415)
            ·
              refine ⟨1556052586811495587130123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1037368391207663724753415 1556052586811495587130123)
              ·
                refine ⟨2334078880217243380695185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1556052586811495587130123 2334078880217243380695185)
                ·
                  refine ⟨1750559160162932535521389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2334078880217243380695185 1750559160162932535521389)
                  ·
                    refine ⟨656459685061099700820521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1750559160162932535521389 656459685061099700820521)
                    ·
                      refine ⟨492344763795824775615391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 656459685061099700820521 492344763795824775615391)
                      ·
                        rfl

theorem cell23_958838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_958838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_958838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_958838 prefixEnd_958838 := by exact prefixLift 958838
  have htrace : WordTrace (prefixWord ++ tailWord_958838) baseStart_958838 baseEnd_958838 := by
    simpa [prefixWord, tailWord_958838, baseEnd_958838] using wordTrace_append hprefix tailTrace_958838
  have hstable : (prefixWord ++ tailWord_958838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958838).length < 2 ^ (prefixWord ++ tailWord_958838).sum := by decide
  have hdescent : baseEnd_958838 < baseStart_958838 := by decide
  rcases family_descends (prefixWord ++ tailWord_958838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958851 : List Nat := [1, 1, 1, 3, 7, 1, 2, 1, 1, 1, 4]
def baseStart_958851 : Nat := 118140960795 + 958851 * 2 ^ 59
def prefixEnd_958851 : Nat := 4983230072969 + 3 ^ 40 * 958851 * 2
def baseEnd_958851 : Nat := 492351439044333224752831

theorem tailTrace_958851 : CollatzResearch.WordTrace tailWord_958851 prefixEnd_958851 492351439044333224752831 := by
  unfold tailWord_958851
  simp only [CollatzResearch.WordTrace]
  refine ⟨34972169049254060558412407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23314779366169373705608271 34972169049254060558412407)
  ·
    refine ⟨52458253573881090837618611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34972169049254060558412407 52458253573881090837618611)
    ·
      refine ⟨78687380360821636256427917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52458253573881090837618611 78687380360821636256427917)
      ·
        refine ⟨29507767635308113596160469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78687380360821636256427917 29507767635308113596160469)
        ·
          refine ⟨691588303952533912410011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 29507767635308113596160469 691588303952533912410011)
          ·
            refine ⟨1037382455928800868615017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 691588303952533912410011 1037382455928800868615017)
            ·
              refine ⟨778036841946600651461263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1037382455928800868615017 778036841946600651461263)
              ·
                refine ⟨1167055262919900977191895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 778036841946600651461263 1167055262919900977191895)
                ·
                  refine ⟨1750582894379851465787843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1167055262919900977191895 1750582894379851465787843)
                  ·
                    refine ⟨2625874341569777198681765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1750582894379851465787843 2625874341569777198681765)
                    ·
                      refine ⟨492351439044333224752831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2625874341569777198681765 492351439044333224752831)
                      ·
                        rfl

theorem cell23_958851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 2, 1, 1, 1, 4].length) (baseStart_958851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_958851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_958851 prefixEnd_958851 := by exact prefixLift 958851
  have htrace : WordTrace (prefixWord ++ tailWord_958851) baseStart_958851 baseEnd_958851 := by
    simpa [prefixWord, tailWord_958851, baseEnd_958851] using wordTrace_append hprefix tailTrace_958851
  have hstable : (prefixWord ++ tailWord_958851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958851).length < 2 ^ (prefixWord ++ tailWord_958851).sum := by decide
  have hdescent : baseEnd_958851 < baseStart_958851 := by decide
  rcases family_descends (prefixWord ++ tailWord_958851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958881 : List Nat := [1, 2, 3, 5, 2, 1, 1, 1, 1, 2, 4]
def baseStart_958881 : Nat := 118140960795 + 958881 * 2 ^ 59
def prefixEnd_958881 : Nat := 4983230072969 + 3 ^ 40 * 958881 * 2
def baseEnd_958881 : Nat := 492366843463968107377693

theorem tailTrace_958881 : CollatzResearch.WordTrace tailWord_958881 prefixEnd_958881 492366843463968107377693 := by
  unfold tailWord_958881
  simp only [CollatzResearch.WordTrace]
  refine ⟨34973263239145375682004497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23315508826096917121336331 34973263239145375682004497)
  ·
    refine ⟨26229947429359031761503373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34973263239145375682004497 26229947429359031761503373)
    ·
      refine ⟨9836230286009636910563765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26229947429359031761503373 9836230286009636910563765)
      ·
        refine ⟨922146589313403460365353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9836230286009636910563765 922146589313403460365353)
        ·
          refine ⟨691609941985052595274015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 922146589313403460365353 691609941985052595274015)
          ·
            refine ⟨1037414912977578892911023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 691609941985052595274015 1037414912977578892911023)
            ·
              refine ⟨1556122369466368339366535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1037414912977578892911023 1556122369466368339366535)
              ·
                refine ⟨2334183554199552509049803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1556122369466368339366535 2334183554199552509049803)
                ·
                  refine ⟨3501275331299328763574705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2334183554199552509049803 3501275331299328763574705)
                  ·
                    refine ⟨2625956498474496572681029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3501275331299328763574705 2625956498474496572681029)
                    ·
                      refine ⟨492366843463968107377693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2625956498474496572681029 492366843463968107377693)
                      ·
                        rfl

theorem cell23_958881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_958881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_958881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_958881 prefixEnd_958881 := by exact prefixLift 958881
  have htrace : WordTrace (prefixWord ++ tailWord_958881) baseStart_958881 baseEnd_958881 := by
    simpa [prefixWord, tailWord_958881, baseEnd_958881] using wordTrace_append hprefix tailTrace_958881
  have hstable : (prefixWord ++ tailWord_958881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958881).length < 2 ^ (prefixWord ++ tailWord_958881).sum := by decide
  have hdescent : baseEnd_958881 < baseStart_958881 := by decide
  rcases family_descends (prefixWord ++ tailWord_958881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958910 : List Nat := [4, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5]
def baseStart_958910 : Nat := 118140960795 + 958910 * 2 ^ 59
def prefixEnd_958910 : Nat := 4983230072969 + 3 ^ 40 * 958910 * 2
def baseEnd_958910 : Nat := 492381734402948493915059

theorem tailTrace_958910 : CollatzResearch.WordTrace tailWord_958910 prefixEnd_958910 492381734402948493915059 := by
  unfold tailWord_958910
  simp only [CollatzResearch.WordTrace]
  refine ⟨4371790119505039204351273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23316213970693542423206789 4371790119505039204351273)
  ·
    refine ⟨3278842589628779403263455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4371790119505039204351273 3278842589628779403263455)
    ·
      refine ⟨4918263884443169104895183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3278842589628779403263455 4918263884443169104895183)
      ·
        refine ⟨7377395826664753657342775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4918263884443169104895183 7377395826664753657342775)
        ·
          refine ⟨11066093739997130486014163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7377395826664753657342775 11066093739997130486014163)
          ·
            refine ⟨16599140609995695729021245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11066093739997130486014163 16599140609995695729021245)
            ·
              refine ⟨6224677728748385898382967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16599140609995695729021245 6224677728748385898382967)
              ·
                refine ⟨9337016593122578847574451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6224677728748385898382967 9337016593122578847574451)
                ·
                  refine ⟨14005524889683868271361677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9337016593122578847574451 14005524889683868271361677)
                  ·
                    refine ⟨5252071833631450601760629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14005524889683868271361677 5252071833631450601760629)
                    ·
                      refine ⟨492381734402948493915059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5252071833631450601760629 492381734402948493915059)
                      ·
                        rfl

theorem cell23_958910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_958910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_958910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_958910 prefixEnd_958910 := by exact prefixLift 958910
  have htrace : WordTrace (prefixWord ++ tailWord_958910) baseStart_958910 baseEnd_958910 := by
    simpa [prefixWord, tailWord_958910, baseEnd_958910] using wordTrace_append hprefix tailTrace_958910
  have hstable : (prefixWord ++ tailWord_958910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958910).length < 2 ^ (prefixWord ++ tailWord_958910).sum := by decide
  have hdescent : baseEnd_958910 < baseStart_958910 := by decide
  rcases family_descends (prefixWord ++ tailWord_958910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958923 : List Nat := [1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 9]
def baseStart_958923 : Nat := 118140960795 + 958923 * 2 ^ 59
def prefixEnd_958923 : Nat := 4983230072969 + 3 ^ 40 * 958923 * 2
def baseEnd_958923 : Nat := 492388409651456943052499

theorem tailTrace_958923 : CollatzResearch.WordTrace tailWord_958923 prefixEnd_958923 492388409651456943052499 := by
  unfold tailWord_958923
  simp only [CollatzResearch.WordTrace]
  refine ⟨34974795104993216855033423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23316530069995477903355615 34974795104993216855033423)
  ·
    refine ⟨52462192657489825282550135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34974795104993216855033423 52462192657489825282550135)
    ·
      refine ⟨78693288986234737923825203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52462192657489825282550135 78693288986234737923825203)
      ·
        refine ⟨118039933479352106885737805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78693288986234737923825203 118039933479352106885737805)
        ·
          refine ⟨44264975054757040082151677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118039933479352106885737805 44264975054757040082151677)
          ·
            refine ⟨16599365645533890030806879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44264975054757040082151677 16599365645533890030806879)
            ·
              refine ⟨24899048468300835046210319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16599365645533890030806879 24899048468300835046210319)
              ·
                refine ⟨37348572702451252569315479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24899048468300835046210319 37348572702451252569315479)
                ·
                  refine ⟨56022859053676878853973219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37348572702451252569315479 56022859053676878853973219)
                  ·
                    refine ⟨84034288580515318280959829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56022859053676878853973219 84034288580515318280959829)
                    ·
                      refine ⟨492388409651456943052499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 84034288580515318280959829 492388409651456943052499)
                      ·
                        rfl

theorem cell23_958923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 9].length) (baseStart_958923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_958923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_958923 prefixEnd_958923 := by exact prefixLift 958923
  have htrace : WordTrace (prefixWord ++ tailWord_958923) baseStart_958923 baseEnd_958923 := by
    simpa [prefixWord, tailWord_958923, baseEnd_958923] using wordTrace_append hprefix tailTrace_958923
  have hstable : (prefixWord ++ tailWord_958923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958923).length < 2 ^ (prefixWord ++ tailWord_958923).sum := by decide
  have hdescent : baseEnd_958923 < baseStart_958923 := by decide
  rcases family_descends (prefixWord ++ tailWord_958923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958941 : List Nat := [1, 4, 3, 1, 1, 1, 3, 3, 2, 2, 2]
def baseStart_958941 : Nat := 118140960795 + 958941 * 2 ^ 59
def prefixEnd_958941 : Nat := 4983230072969 + 3 ^ 40 * 958941 * 2
def baseEnd_958941 : Nat := 492397652303237872627417

theorem tailTrace_958941 : CollatzResearch.WordTrace tailWord_958941 prefixEnd_958941 492397652303237872627417 := by
  unfold tailWord_958941
  simp only [CollatzResearch.WordTrace]
  refine ⟨34975451618928005929188677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23316967745952003952792451 34975451618928005929188677)
  ·
    refine ⟨6557897178549001111722877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34975451618928005929188677 6557897178549001111722877)
    ·
      refine ⟨2459211441955875416896079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6557897178549001111722877 2459211441955875416896079)
      ·
        refine ⟨3688817162933813125344119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2459211441955875416896079 3688817162933813125344119)
        ·
          refine ⟨5533225744400719688016179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3688817162933813125344119 5533225744400719688016179)
          ·
            refine ⟨8299838616601079532024269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5533225744400719688016179 8299838616601079532024269)
            ·
              refine ⟨3112439481225404824509101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8299838616601079532024269 3112439481225404824509101)
              ·
                refine ⟨1167164805459526809190913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3112439481225404824509101 1167164805459526809190913)
                ·
                  refine ⟨875373604094645106893185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1167164805459526809190913 875373604094645106893185)
                  ·
                    refine ⟨656530203070983830169889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 875373604094645106893185 656530203070983830169889)
                    ·
                      refine ⟨492397652303237872627417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 656530203070983830169889 492397652303237872627417)
                      ·
                        rfl

theorem cell23_958941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 3, 2, 2, 2].length) (baseStart_958941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_958941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_958941 prefixEnd_958941 := by exact prefixLift 958941
  have htrace : WordTrace (prefixWord ++ tailWord_958941) baseStart_958941 baseEnd_958941 := by
    simpa [prefixWord, tailWord_958941, baseEnd_958941] using wordTrace_append hprefix tailTrace_958941
  have hstable : (prefixWord ++ tailWord_958941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958941).length < 2 ^ (prefixWord ++ tailWord_958941).sum := by decide
  have hdescent : baseEnd_958941 < baseStart_958941 := by decide
  rcases family_descends (prefixWord ++ tailWord_958941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958977 : List Nat := [1, 2, 4, 1, 3, 1, 2, 2, 2, 5]
def baseStart_958977 : Nat := 118140960795 + 958977 * 2 ^ 59
def prefixEnd_958977 : Nat := 4983230072969 + 3 ^ 40 * 958977 * 2
def baseEnd_958977 : Nat := 164138712535599910592417

theorem tailTrace_958977 : CollatzResearch.WordTrace tailWord_958977 prefixEnd_958977 164138712535599910592417 := by
  unfold tailWord_958977
  simp only [CollatzResearch.WordTrace]
  refine ⟨34976764646797584077499185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23317843097865056051666123 34976764646797584077499185)
  ·
    refine ⟨26232573485098188058124389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34976764646797584077499185 26232573485098188058124389)
    ·
      refine ⟨4918607528455910260898323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26232573485098188058124389 4918607528455910260898323)
      ·
        refine ⟨7377911292683865391347485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4918607528455910260898323 7377911292683865391347485)
        ·
          refine ⟨2766716734756449521755307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7377911292683865391347485 2766716734756449521755307)
          ·
            refine ⟨4150075102134674282632961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2766716734756449521755307 4150075102134674282632961)
            ·
              refine ⟨3112556326601005711974721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4150075102134674282632961 3112556326601005711974721)
              ·
                refine ⟨2334417244950754283981041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3112556326601005711974721 2334417244950754283981041)
                ·
                  refine ⟨1750812933713065712985781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2334417244950754283981041 1750812933713065712985781)
                  ·
                    refine ⟨164138712535599910592417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1750812933713065712985781 164138712535599910592417)
                    ·
                      rfl

theorem cell23_958977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_958977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_958977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_958977 prefixEnd_958977 := by exact prefixLift 958977
  have htrace : WordTrace (prefixWord ++ tailWord_958977) baseStart_958977 baseEnd_958977 := by
    simpa [prefixWord, tailWord_958977, baseEnd_958977] using wordTrace_append hprefix tailTrace_958977
  have hstable : (prefixWord ++ tailWord_958977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958977).length < 2 ^ (prefixWord ++ tailWord_958977).sum := by decide
  have hdescent : baseEnd_958977 < baseStart_958977 := by decide
  rcases family_descends (prefixWord ++ tailWord_958977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959024 : List Nat := [2, 1, 1, 1, 2, 3, 3, 5, 1, 4]
def baseStart_959024 : Nat := 118140960795 + 959024 * 2 ^ 59
def prefixEnd_959024 : Nat := 4983230072969 + 3 ^ 40 * 959024 * 2
def baseEnd_959024 : Nat := 164146757065853682629845

theorem tailTrace_959024 : CollatzResearch.WordTrace tailWord_959024 prefixEnd_959024 164146757065853682629845 := by
  unfold tailWord_959024
  simp only [CollatzResearch.WordTrace]
  refine ⟨17489239438813655552230063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23318985918418207402973417 17489239438813655552230063)
  ·
    refine ⟨26233859158220483328345095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17489239438813655552230063 26233859158220483328345095)
    ·
      refine ⟨39350788737330724992517643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26233859158220483328345095 39350788737330724992517643)
      ·
        refine ⟨59026183105996087488776465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39350788737330724992517643 59026183105996087488776465)
        ·
          refine ⟨44269637329497065616582349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59026183105996087488776465 44269637329497065616582349)
          ·
            refine ⟨16601113998561399606218381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44269637329497065616582349 16601113998561399606218381)
            ·
              refine ⟨6225417749460524852331893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16601113998561399606218381 6225417749460524852331893)
              ·
                refine ⟨583632914011924204906115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6225417749460524852331893 583632914011924204906115)
                ·
                  refine ⟨875449371017886307359173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 583632914011924204906115 875449371017886307359173)
                  ·
                    refine ⟨164146757065853682629845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 875449371017886307359173 164146757065853682629845)
                    ·
                      rfl

theorem cell23_959024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 5, 1, 4].length) (baseStart_959024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_959024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_959024 prefixEnd_959024 := by exact prefixLift 959024
  have htrace : WordTrace (prefixWord ++ tailWord_959024) baseStart_959024 baseEnd_959024 := by
    simpa [prefixWord, tailWord_959024, baseEnd_959024] using wordTrace_append hprefix tailTrace_959024
  have hstable : (prefixWord ++ tailWord_959024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959024).length < 2 ^ (prefixWord ++ tailWord_959024).sum := by decide
  have hdescent : baseEnd_959024 < baseStart_959024 := by decide
  rcases family_descends (prefixWord ++ tailWord_959024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959037 : List Nat := [1, 4, 1, 3, 2, 2, 1, 1, 8]
def baseStart_959037 : Nat := 118140960795 + 959037 * 2 ^ 59
def prefixEnd_959037 : Nat := 4983230072969 + 3 ^ 40 * 959037 * 2
def baseEnd_959037 : Nat := 54716327382896610780775

theorem tailTrace_959037 : CollatzResearch.WordTrace tailWord_959037 prefixEnd_959037 54716327382896610780775 := by
  unfold tailWord_959037
  simp only [CollatzResearch.WordTrace]
  refine ⟨34978953026580214324683365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23319302017720142883122243 34978953026580214324683365)
  ·
    refine ⟨6558553692483790185878131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34978953026580214324683365 6558553692483790185878131)
    ·
      refine ⟨9837830538725685278817197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6558553692483790185878131 9837830538725685278817197)
      ·
        refine ⟨3689186452022131979556449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9837830538725685278817197 3689186452022131979556449)
        ·
          refine ⟨2766889839016598984667337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3689186452022131979556449 2766889839016598984667337)
          ·
            refine ⟨2075167379262449238500503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2766889839016598984667337 2075167379262449238500503)
            ·
              refine ⟨3112751068893673857750755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2075167379262449238500503 3112751068893673857750755)
              ·
                refine ⟨4669126603340510786626133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3112751068893673857750755 4669126603340510786626133)
                ·
                  refine ⟨54716327382896610780775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4669126603340510786626133 54716327382896610780775)
                  ·
                    rfl

theorem cell23_959037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 8].length) (baseStart_959037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_959037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_959037 prefixEnd_959037 := by exact prefixLift 959037
  have htrace : WordTrace (prefixWord ++ tailWord_959037) baseStart_959037 baseEnd_959037 := by
    simpa [prefixWord, tailWord_959037, baseEnd_959037] using wordTrace_append hprefix tailTrace_959037
  have hstable : (prefixWord ++ tailWord_959037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959037).length < 2 ^ (prefixWord ++ tailWord_959037).sum := by decide
  have hdescent : baseEnd_959037 < baseStart_959037 := by decide
  rcases family_descends (prefixWord ++ tailWord_959037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959040 : List Nat := [2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 6]
def baseStart_959040 : Nat := 118140960795 + 959040 * 2 ^ 59
def prefixEnd_959040 : Nat := 4983230072969 + 3 ^ 40 * 959040 * 2
def baseEnd_959040 : Nat := 492448486888032985289461

theorem tailTrace_959040 : CollatzResearch.WordTrace tailWord_959040 prefixEnd_959040 492448486888032985289461 := by
  unfold tailWord_959040
  simp only [CollatzResearch.WordTrace]
  refine ⟨17489531222784672918521287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23319374963712897224695049 17489531222784672918521287)
  ·
    refine ⟨26234296834177009377781931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17489531222784672918521287 26234296834177009377781931)
    ·
      refine ⟨39351445251265514066672897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26234296834177009377781931 39351445251265514066672897)
      ·
        refine ⟨29513583938449135550004673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39351445251265514066672897 29513583938449135550004673)
        ·
          refine ⟨22135187953836851662503505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29513583938449135550004673 22135187953836851662503505)
          ·
            refine ⟨16601390965377638746877629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22135187953836851662503505 16601390965377638746877629)
            ·
              refine ⟨6225521612016614530079111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16601390965377638746877629 6225521612016614530079111)
              ·
                refine ⟨9338282418024921795118667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6225521612016614530079111 9338282418024921795118667)
                ·
                  refine ⟨14007423627037382692678001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9338282418024921795118667 14007423627037382692678001)
                  ·
                    refine ⟨10505567720278037019508501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14007423627037382692678001 10505567720278037019508501)
                    ·
                      refine ⟨492448486888032985289461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10505567720278037019508501 492448486888032985289461)
                      ·
                        rfl

theorem cell23_959040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 6].length) (baseStart_959040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_959040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_959040 prefixEnd_959040 := by exact prefixLift 959040
  have htrace : WordTrace (prefixWord ++ tailWord_959040) baseStart_959040 baseEnd_959040 := by
    simpa [prefixWord, tailWord_959040, baseEnd_959040] using wordTrace_append hprefix tailTrace_959040
  have hstable : (prefixWord ++ tailWord_959040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959040).length < 2 ^ (prefixWord ++ tailWord_959040).sum := by decide
  have hdescent : baseEnd_959040 < baseStart_959040 := by decide
  rcases family_descends (prefixWord ++ tailWord_959040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959041 : List Nat := [1, 2, 5, 1, 1, 2, 2, 4, 1, 4]
def baseStart_959041 : Nat := 118140960795 + 959041 * 2 ^ 59
def prefixEnd_959041 : Nat := 4983230072969 + 3 ^ 40 * 959041 * 2
def baseEnd_959041 : Nat := 164149666789562493792319

theorem tailTrace_959041 : CollatzResearch.WordTrace tailWord_959041 prefixEnd_959041 164149666789562493792319 := by
  unfold tailWord_959041
  simp only [CollatzResearch.WordTrace]
  refine ⟨34979098918565723007828977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23319399279043815338552651 34979098918565723007828977)
  ·
    refine ⟨26234324188924292255871733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34979098918565723007828977 26234324188924292255871733)
    ·
      refine ⟨2459467892711652398987975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26234324188924292255871733 2459467892711652398987975)
      ·
        refine ⟨3689201839067478598481963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2459467892711652398987975 3689201839067478598481963)
        ·
          refine ⟨5533802758601217897722945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3689201839067478598481963 5533802758601217897722945)
          ·
            refine ⟨4150352068950913423292209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5533802758601217897722945 4150352068950913423292209)
            ·
              refine ⟨3112764051713185067469157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4150352068950913423292209 3112764051713185067469157)
              ·
                refine ⟨583643259696222200150467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3112764051713185067469157 583643259696222200150467)
                ·
                  refine ⟨875464889544333300225701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 583643259696222200150467 875464889544333300225701)
                  ·
                    refine ⟨164149666789562493792319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 875464889544333300225701 164149666789562493792319)
                    ·
                      rfl

theorem cell23_959041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_959041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_959041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_959041 prefixEnd_959041 := by exact prefixLift 959041
  have htrace : WordTrace (prefixWord ++ tailWord_959041) baseStart_959041 baseEnd_959041 := by
    simpa [prefixWord, tailWord_959041, baseEnd_959041] using wordTrace_append hprefix tailTrace_959041
  have hstable : (prefixWord ++ tailWord_959041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959041).length < 2 ^ (prefixWord ++ tailWord_959041).sum := by decide
  have hdescent : baseEnd_959041 < baseStart_959041 := by decide
  rcases family_descends (prefixWord ++ tailWord_959041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959064 : List Nat := [2, 1, 2, 2, 1, 2, 4, 2, 3, 1, 3]
def baseStart_959064 : Nat := 118140960795 + 959064 * 2 ^ 59
def prefixEnd_959064 : Nat := 4983230072969 + 3 ^ 40 * 959064 * 2
def baseEnd_959064 : Nat := 492460810423740891389351

theorem tailTrace_959064 : CollatzResearch.WordTrace tailWord_959064 prefixEnd_959064 492460810423740891389351 := by
  unfold tailWord_959064
  simp only [CollatzResearch.WordTrace]
  refine ⟨17489968898741198967958123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23319958531654931957277497 17489968898741198967958123)
  ·
    refine ⟨26234953348111798451937185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17489968898741198967958123 26234953348111798451937185)
    ·
      refine ⟨19676215011083848838952889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26234953348111798451937185 19676215011083848838952889)
      ·
        refine ⟨14757161258312886629214667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19676215011083848838952889 14757161258312886629214667)
        ·
          refine ⟨22135741887469329943822001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14757161258312886629214667 22135741887469329943822001)
          ·
            refine ⟨16601806415601997457866501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22135741887469329943822001 16601806415601997457866501)
            ·
              refine ⟨3112838702925374523349969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16601806415601997457866501 3112838702925374523349969)
              ·
                refine ⟨2334629027194030892512477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3112838702925374523349969 2334629027194030892512477)
                ·
                  refine ⟨875485885197761584692179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2334629027194030892512477 875485885197761584692179)
                  ·
                    refine ⟨1313228827796642377038269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 875485885197761584692179 1313228827796642377038269)
                    ·
                      refine ⟨492460810423740891389351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1313228827796642377038269 492460810423740891389351)
                      ·
                        rfl

theorem cell23_959064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 2, 3, 1, 3].length) (baseStart_959064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_959064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_959064 prefixEnd_959064 := by exact prefixLift 959064
  have htrace : WordTrace (prefixWord ++ tailWord_959064) baseStart_959064 baseEnd_959064 := by
    simpa [prefixWord, tailWord_959064, baseEnd_959064] using wordTrace_append hprefix tailTrace_959064
  have hstable : (prefixWord ++ tailWord_959064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959064).length < 2 ^ (prefixWord ++ tailWord_959064).sum := by decide
  have hdescent : baseEnd_959064 < baseStart_959064 := by decide
  rcases family_descends (prefixWord ++ tailWord_959064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959107 : List Nat := [1, 1, 1, 3, 3, 1, 4, 2, 1, 1, 5]
def baseStart_959107 : Nat := 118140960795 + 959107 * 2 ^ 59
def prefixEnd_959107 : Nat := 4983230072969 + 3 ^ 40 * 959107 * 2
def baseEnd_959107 : Nat := 492482890091884223151653

theorem tailTrace_959107 : CollatzResearch.WordTrace tailWord_959107 prefixEnd_959107 492482890091884223151653 := by
  unfold tailWord_959107
  simp only [CollatzResearch.WordTrace]
  refine ⟨34981506136326616279731575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23321004090884410853154383 34981506136326616279731575)
  ·
    refine ⟨52472259204489924419597363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34981506136326616279731575 52472259204489924419597363)
    ·
      refine ⟨78708388806734886629396045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52472259204489924419597363 78708388806734886629396045)
      ·
        refine ⟨29515645802525582486023517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78708388806734886629396045 29515645802525582486023517)
        ·
          refine ⟨11068367175947093432258819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29515645802525582486023517 11068367175947093432258819)
          ·
            refine ⟨16602550763920640148388229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11068367175947093432258819 16602550763920640148388229)
            ·
              refine ⟨3112978268235120027822793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16602550763920640148388229 3112978268235120027822793)
              ·
                refine ⟨2334733701176340020867095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3112978268235120027822793 2334733701176340020867095)
                ·
                  refine ⟨3502100551764510031300643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2334733701176340020867095 3502100551764510031300643)
                  ·
                    refine ⟨5253150827646765046950965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3502100551764510031300643 5253150827646765046950965)
                    ·
                      refine ⟨492482890091884223151653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5253150827646765046950965 492482890091884223151653)
                      ·
                        rfl

theorem cell23_959107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 2, 1, 1, 5].length) (baseStart_959107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_959107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_959107 prefixEnd_959107 := by exact prefixLift 959107
  have htrace : WordTrace (prefixWord ++ tailWord_959107) baseStart_959107 baseEnd_959107 := by
    simpa [prefixWord, tailWord_959107, baseEnd_959107] using wordTrace_append hprefix tailTrace_959107
  have hstable : (prefixWord ++ tailWord_959107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959107).length < 2 ^ (prefixWord ++ tailWord_959107).sum := by decide
  have hdescent : baseEnd_959107 < baseStart_959107 := by decide
  rcases family_descends (prefixWord ++ tailWord_959107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959155 : List Nat := [1, 1, 1, 2, 3, 4, 4, 2, 1, 2, 2]
def baseStart_959155 : Nat := 118140960795 + 959155 * 2 ^ 59
def prefixEnd_959155 : Nat := 4983230072969 + 3 ^ 40 * 959155 * 2
def baseEnd_959155 : Nat := 492507537163300035351433

theorem tailTrace_959155 : CollatzResearch.WordTrace tailWord_959155 prefixEnd_959155 492507537163300035351433 := by
  unfold tailWord_959155
  simp only [CollatzResearch.WordTrace]
  refine ⟨34983256840152720477478919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23322171226768480318319279 34983256840152720477478919)
  ·
    refine ⟨52474885260229080716218379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34983256840152720477478919 52474885260229080716218379)
    ·
      refine ⟨78712327890343621074327569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52474885260229080716218379 78712327890343621074327569)
      ·
        refine ⟨59034245917757715805745677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78712327890343621074327569 59034245917757715805745677)
        ·
          refine ⟨22137842219159143427154629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59034245917757715805745677 22137842219159143427154629)
          ·
            refine ⟨4150845416092339392591493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22137842219159143427154629 4150845416092339392591493)
            ·
              refine ⟨778283515517313636110905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4150845416092339392591493 778283515517313636110905)
              ·
                refine ⟨583712636637985227083179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 778283515517313636110905 583712636637985227083179)
                ·
                  refine ⟨875568954956977840624769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 583712636637985227083179 875568954956977840624769)
                  ·
                    refine ⟨656676716217733380468577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 875568954956977840624769 656676716217733380468577)
                    ·
                      refine ⟨492507537163300035351433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 656676716217733380468577 492507537163300035351433)
                      ·
                        rfl

theorem cell23_959155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 4, 2, 1, 2, 2].length) (baseStart_959155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_959155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_959155 prefixEnd_959155 := by exact prefixLift 959155
  have htrace : WordTrace (prefixWord ++ tailWord_959155) baseStart_959155 baseEnd_959155 := by
    simpa [prefixWord, tailWord_959155, baseEnd_959155] using wordTrace_append hprefix tailTrace_959155
  have hstable : (prefixWord ++ tailWord_959155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959155).length < 2 ^ (prefixWord ++ tailWord_959155).sum := by decide
  have hdescent : baseEnd_959155 < baseStart_959155 := by decide
  rcases family_descends (prefixWord ++ tailWord_959155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959228 : List Nat := [2, 2, 2, 1, 3, 4, 1, 1, 1, 4, 2]
def baseStart_959228 : Nat := 118140960795 + 959228 * 2 ^ 59
def prefixEnd_959228 : Nat := 4983230072969 + 3 ^ 40 * 959228 * 2
def baseEnd_959228 : Nat := 492545021251078249738597

theorem tailTrace_959228 : CollatzResearch.WordTrace tailWord_959228 prefixEnd_959228 492545021251078249738597 := by
  unfold tailWord_959228
  simp only [CollatzResearch.WordTrace]
  refine ⟨17492959684444126972443169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23323946245925502629924225 17492959684444126972443169)
  ·
    refine ⟨13119719763333095229332377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17492959684444126972443169 13119719763333095229332377)
    ·
      refine ⟨9839789822499821421999283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13119719763333095229332377 9839789822499821421999283)
      ·
        refine ⟨14759684733749732132998925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9839789822499821421999283 14759684733749732132998925)
        ·
          refine ⟨5534881775156149549874597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14759684733749732132998925 5534881775156149549874597)
          ·
            refine ⟨1037790332841778040601487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5534881775156149549874597 1037790332841778040601487)
            ·
              refine ⟨1556685499262667060902231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1037790332841778040601487 1556685499262667060902231)
              ·
                refine ⟨2335028248894000591353347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1556685499262667060902231 2335028248894000591353347)
                ·
                  refine ⟨3502542373341000887030021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2335028248894000591353347 3502542373341000887030021)
                  ·
                    refine ⟨656726695001437666318129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3502542373341000887030021 656726695001437666318129)
                    ·
                      refine ⟨492545021251078249738597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 656726695001437666318129 492545021251078249738597)
                      ·
                        rfl

theorem cell23_959228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 1, 1, 4, 2].length) (baseStart_959228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_959228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_959228 prefixEnd_959228 := by exact prefixLift 959228
  have htrace : WordTrace (prefixWord ++ tailWord_959228) baseStart_959228 baseEnd_959228 := by
    simpa [prefixWord, tailWord_959228, baseEnd_959228] using wordTrace_append hprefix tailTrace_959228
  have hstable : (prefixWord ++ tailWord_959228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959228).length < 2 ^ (prefixWord ++ tailWord_959228).sum := by decide
  have hdescent : baseEnd_959228 < baseStart_959228 := by decide
  rcases family_descends (prefixWord ++ tailWord_959228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959247 : List Nat := [1, 1, 2, 1, 1, 1, 5, 3, 1, 7]
def baseStart_959247 : Nat := 118140960795 + 959247 * 2 ^ 59
def prefixEnd_959247 : Nat := 4983230072969 + 3 ^ 40 * 959247 * 2
def baseEnd_959247 : Nat := 164184925794504558467003

theorem tailTrace_959247 : CollatzResearch.WordTrace tailWord_959247 prefixEnd_959247 164184925794504558467003 := by
  unfold tailWord_959247
  simp only [CollatzResearch.WordTrace]
  refine ⟨34986612355819420189827995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23324408237212946793218663 34986612355819420189827995)
  ·
    refine ⟨52479918533729130284741993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34986612355819420189827995 52479918533729130284741993)
    ·
      refine ⟨39359938900296847713556495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52479918533729130284741993 39359938900296847713556495)
      ·
        refine ⟨59039908350445271570334743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39359938900296847713556495 59039908350445271570334743)
        ·
          refine ⟨88559862525667907355502115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59039908350445271570334743 88559862525667907355502115)
          ·
            refine ⟨132839793788501861033253173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88559862525667907355502115 132839793788501861033253173)
            ·
              refine ⟨12453730667672049471867485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 132839793788501861033253173 12453730667672049471867485)
              ·
                refine ⟨4670149000377018551950307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12453730667672049471867485 4670149000377018551950307)
                ·
                  refine ⟨7005223500565527827925461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4670149000377018551950307 7005223500565527827925461)
                  ·
                    refine ⟨164184925794504558467003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7005223500565527827925461 164184925794504558467003)
                    ·
                      rfl

theorem cell23_959247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 7].length) (baseStart_959247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_959247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_959247 prefixEnd_959247 := by exact prefixLift 959247
  have htrace : WordTrace (prefixWord ++ tailWord_959247) baseStart_959247 baseEnd_959247 := by
    simpa [prefixWord, tailWord_959247, baseEnd_959247] using wordTrace_append hprefix tailTrace_959247
  have hstable : (prefixWord ++ tailWord_959247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959247).length < 2 ^ (prefixWord ++ tailWord_959247).sum := by decide
  have hdescent : baseEnd_959247 < baseStart_959247 := by decide
  rcases family_descends (prefixWord ++ tailWord_959247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959264 : List Nat := [2, 1, 1, 5, 1, 2, 1, 1, 4, 5]
def baseStart_959264 : Nat := 118140960795 + 959264 * 2 ^ 59
def prefixEnd_959264 : Nat := 4983230072969 + 3 ^ 40 * 959264 * 2
def baseEnd_959264 : Nat := 164187835518213369629477

theorem tailTrace_959264 : CollatzResearch.WordTrace tailWord_959264 prefixEnd_959264 164187835518213369629477 := by
  unfold tailWord_959264
  simp only [CollatzResearch.WordTrace]
  refine ⟨17493616198378916046598423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23324821597838554728797897 17493616198378916046598423)
  ·
    refine ⟨26240424297568374069897635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17493616198378916046598423 26240424297568374069897635)
    ·
      refine ⟨39360636446352561104846453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26240424297568374069897635 39360636446352561104846453)
      ·
        refine ⟨3690059666845552603579355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39360636446352561104846453 3690059666845552603579355)
        ·
          refine ⟨5535089500268328905369033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3690059666845552603579355 5535089500268328905369033)
          ·
            refine ⟨4151317125201246679026775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5535089500268328905369033 4151317125201246679026775)
            ·
              refine ⟨6226975687801870018540163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4151317125201246679026775 6226975687801870018540163)
              ·
                refine ⟨9340463531702805027810245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6226975687801870018540163 9340463531702805027810245)
                ·
                  refine ⟨1751336912194275942714421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9340463531702805027810245 1751336912194275942714421)
                  ·
                    refine ⟨164187835518213369629477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1751336912194275942714421 164187835518213369629477)
                    ·
                      rfl

theorem cell23_959264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 4, 5].length) (baseStart_959264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_959264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_959264 prefixEnd_959264 := by exact prefixLift 959264
  have htrace : WordTrace (prefixWord ++ tailWord_959264) baseStart_959264 baseEnd_959264 := by
    simpa [prefixWord, tailWord_959264, baseEnd_959264] using wordTrace_append hprefix tailTrace_959264
  have hstable : (prefixWord ++ tailWord_959264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959264).length < 2 ^ (prefixWord ++ tailWord_959264).sum := by decide
  have hdescent : baseEnd_959264 < baseStart_959264 := by decide
  rcases family_descends (prefixWord ++ tailWord_959264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959268 : List Nat := [2, 3, 1, 3, 4, 1, 1, 1, 7]
def baseStart_959268 : Nat := 118140960795 + 959268 * 2 ^ 59
def prefixEnd_959268 : Nat := 4983230072969 + 3 ^ 40 * 959268 * 2
def baseEnd_959268 : Nat := 54729506719695343693157

theorem tailTrace_959268 : CollatzResearch.WordTrace tailWord_959268 prefixEnd_959268 54729506719695343693157 := by
  unfold tailWord_959268
  simp only [CollatzResearch.WordTrace]
  refine ⟨17493689144371670388171229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23324918859162227184228305 17493689144371670388171229)
  ·
    refine ⟨6560133429139376395564211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17493689144371670388171229 6560133429139376395564211)
    ·
      refine ⟨9840200143709064593346317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6560133429139376395564211 9840200143709064593346317)
      ·
        refine ⟨3690075053890899222504869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9840200143709064593346317 3690075053890899222504869)
        ·
          refine ⟨691889072604543604219663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3690075053890899222504869 691889072604543604219663)
          ·
            refine ⟨1037833608906815406329495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 691889072604543604219663 1037833608906815406329495)
            ·
              refine ⟨1556750413360223109494243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1037833608906815406329495 1556750413360223109494243)
              ·
                refine ⟨2335125620040334664241365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1556750413360223109494243 2335125620040334664241365)
                ·
                  refine ⟨54729506719695343693157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2335125620040334664241365 54729506719695343693157)
                  ·
                    rfl

theorem cell23_959268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 1, 7].length) (baseStart_959268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_959268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_959268 prefixEnd_959268 := by exact prefixLift 959268
  have htrace : WordTrace (prefixWord ++ tailWord_959268) baseStart_959268 baseEnd_959268 := by
    simpa [prefixWord, tailWord_959268, baseEnd_959268] using wordTrace_append hprefix tailTrace_959268
  have hstable : (prefixWord ++ tailWord_959268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959268).length < 2 ^ (prefixWord ++ tailWord_959268).sum := by decide
  have hdescent : baseEnd_959268 < baseStart_959268 := by decide
  rcases family_descends (prefixWord ++ tailWord_959268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959314 : List Nat := [3, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6]
def baseStart_959314 : Nat := 118140960795 + 959314 * 2 ^ 59
def prefixEnd_959314 : Nat := 4983230072969 + 3 ^ 40 * 959314 * 2
def baseEnd_959314 : Nat := 492589180587364913263201

theorem tailTrace_959314 : CollatzResearch.WordTrace tailWord_959314 prefixEnd_959314 492589180587364913263201 := by
  unfold tailWord_959314
  simp only [CollatzResearch.WordTrace]
  refine ⟨8747264011644172658129249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23326037364384460421677997 8747264011644172658129249)
  ·
    refine ⟨6560448008733129493596937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8747264011644172658129249 6560448008733129493596937)
    ·
      refine ⟨4920336006549847120197703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6560448008733129493596937 4920336006549847120197703)
      ·
        refine ⟨7380504009824770680296555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4920336006549847120197703 7380504009824770680296555)
        ·
          refine ⟨11070756014737156020444833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7380504009824770680296555 11070756014737156020444833)
          ·
            refine ⟨8303067011052867015333625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11070756014737156020444833 8303067011052867015333625)
            ·
              refine ⟨6227300258289650261500219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8303067011052867015333625 6227300258289650261500219)
              ·
                refine ⟨9340950387434475392250329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6227300258289650261500219 9340950387434475392250329)
                ·
                  refine ⟨7005712790575856544187747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9340950387434475392250329 7005712790575856544187747)
                  ·
                    refine ⟨10508569185863784816281621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7005712790575856544187747 10508569185863784816281621)
                    ·
                      refine ⟨492589180587364913263201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10508569185863784816281621 492589180587364913263201)
                      ·
                        rfl

theorem cell23_959314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_959314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_959314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_959314 prefixEnd_959314 := by exact prefixLift 959314
  have htrace : WordTrace (prefixWord ++ tailWord_959314) baseStart_959314 baseEnd_959314 := by
    simpa [prefixWord, tailWord_959314, baseEnd_959314] using wordTrace_append hprefix tailTrace_959314
  have hstable : (prefixWord ++ tailWord_959314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959314).length < 2 ^ (prefixWord ++ tailWord_959314).sum := by decide
  have hdescent : baseEnd_959314 < baseStart_959314 := by decide
  rcases family_descends (prefixWord ++ tailWord_959314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959321 : List Nat := [1, 2, 1, 2, 2, 4, 2, 2, 2, 2, 3]
def baseStart_959321 : Nat := 118140960795 + 959321 * 2 ^ 59
def prefixEnd_959321 : Nat := 4983230072969 + 3 ^ 40 * 959321 * 2
def baseEnd_959321 : Nat := 492592774951946385875669

theorem tailTrace_959321 : CollatzResearch.WordTrace tailWord_959321 prefixEnd_959321 492592774951946385875669 := by
  unfold tailWord_959321
  simp only [CollatzResearch.WordTrace]
  refine ⟨34989311357551330828021817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23326207571700887218681211 34989311357551330828021817)
  ·
    refine ⟨26241983518163498121016363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34989311357551330828021817 26241983518163498121016363)
    ·
      refine ⟨39362975277245247181524545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26241983518163498121016363 39362975277245247181524545)
      ·
        refine ⟨29522231457933935386143409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39362975277245247181524545 29522231457933935386143409)
        ·
          refine ⟨22141673593450451539607557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29522231457933935386143409 22141673593450451539607557)
          ·
            refine ⟨4151563798771959663676417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22141673593450451539607557 4151563798771959663676417)
            ·
              refine ⟨3113672849078969747757313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4151563798771959663676417 3113672849078969747757313)
              ·
                refine ⟨2335254636809227310817985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3113672849078969747757313 2335254636809227310817985)
                ·
                  refine ⟨1751440977606920483113489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2335254636809227310817985 1751440977606920483113489)
                  ·
                    refine ⟨1313580733205190362335117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1751440977606920483113489 1313580733205190362335117)
                    ·
                      refine ⟨492592774951946385875669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1313580733205190362335117 492592774951946385875669)
                      ·
                        rfl

theorem cell23_959321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 2, 2, 2, 3].length) (baseStart_959321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_959321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_959321 prefixEnd_959321 := by exact prefixLift 959321
  have htrace : WordTrace (prefixWord ++ tailWord_959321) baseStart_959321 baseEnd_959321 := by
    simpa [prefixWord, tailWord_959321, baseEnd_959321] using wordTrace_append hprefix tailTrace_959321
  have hstable : (prefixWord ++ tailWord_959321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959321).length < 2 ^ (prefixWord ++ tailWord_959321).sum := by decide
  have hdescent : baseEnd_959321 < baseStart_959321 := by decide
  rcases family_descends (prefixWord ++ tailWord_959321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959328 : List Nat := [2, 1, 1, 3, 3, 1, 3, 4, 1, 4]
def baseStart_959328 : Nat := 118140960795 + 959328 * 2 ^ 59
def prefixEnd_959328 : Nat := 4983230072969 + 3 ^ 40 * 959328 * 2
def baseEnd_959328 : Nat := 164198789772175952829379

theorem tailTrace_959328 : CollatzResearch.WordTrace tailWord_959328 prefixEnd_959328 164198789772175952829379 := by
  unfold tailWord_959328
  simp only [CollatzResearch.WordTrace]
  refine ⟨17494783334262985511763319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23326377779017314015684425 17494783334262985511763319)
  ·
    refine ⟨26242175001394478267644979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17494783334262985511763319 26242175001394478267644979)
    ·
      refine ⟨39363262502091717401467469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26242175001394478267644979 39363262502091717401467469)
      ·
        refine ⟨14761223438284394025550301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39363262502091717401467469 14761223438284394025550301)
        ·
          refine ⟨5535458789356647759581363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14761223438284394025550301 5535458789356647759581363)
          ·
            refine ⟨8303188184034971639372045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5535458789356647759581363 8303188184034971639372045)
            ·
              refine ⟨3113695569013114364764517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8303188184034971639372045 3113695569013114364764517)
              ·
                refine ⟨583817919189958943393347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3113695569013114364764517 583817919189958943393347)
                ·
                  refine ⟨875726878784938415090021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 583817919189958943393347 875726878784938415090021)
                  ·
                    refine ⟨164198789772175952829379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 875726878784938415090021 164198789772175952829379)
                    ·
                      rfl

theorem cell23_959328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 4, 1, 4].length) (baseStart_959328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_959328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_959328 prefixEnd_959328 := by exact prefixLift 959328
  have htrace : WordTrace (prefixWord ++ tailWord_959328) baseStart_959328 baseEnd_959328 := by
    simpa [prefixWord, tailWord_959328, baseEnd_959328] using wordTrace_append hprefix tailTrace_959328
  have hstable : (prefixWord ++ tailWord_959328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959328).length < 2 ^ (prefixWord ++ tailWord_959328).sum := by decide
  have hdescent : baseEnd_959328 < baseStart_959328 := by decide
  rcases family_descends (prefixWord ++ tailWord_959328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959364 : List Nat := [2, 3, 2, 1, 1, 1, 1, 1, 2, 4, 5]
def baseStart_959364 : Nat := 118140960795 + 959364 * 2 ^ 59
def prefixEnd_959364 : Nat := 4983230072969 + 3 ^ 40 * 959364 * 2
def baseEnd_959364 : Nat := 492614854620089717637971

theorem tailTrace_959364 : CollatzResearch.WordTrace tailWord_959364 prefixEnd_959364 492614854620089717637971 := by
  unfold tailWord_959364
  simp only [CollatzResearch.WordTrace]
  refine ⟨17495439848197774585918573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23327253130930366114558097 17495439848197774585918573)
  ·
    refine ⟨6560789943074165469719465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17495439848197774585918573 6560789943074165469719465)
    ·
      refine ⟨4920592457305624102289599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6560789943074165469719465 4920592457305624102289599)
      ·
        refine ⟨7380888685958436153434399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4920592457305624102289599 7380888685958436153434399)
        ·
          refine ⟨11071333028937654230151599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7380888685958436153434399 11071333028937654230151599)
          ·
            refine ⟨16606999543406481345227399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11071333028937654230151599 16606999543406481345227399)
            ·
              refine ⟨24910499315109722017841099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16606999543406481345227399 24910499315109722017841099)
              ·
                refine ⟨37365748972664583026761649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24910499315109722017841099 37365748972664583026761649)
                ·
                  refine ⟨28024311729498437270071237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37365748972664583026761649 28024311729498437270071237)
                  ·
                    refine ⟨5254558449280956988138357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28024311729498437270071237 5254558449280956988138357)
                    ·
                      refine ⟨492614854620089717637971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5254558449280956988138357 492614854620089717637971)
                      ·
                        rfl

theorem cell23_959364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_959364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_959364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_959364 prefixEnd_959364 := by exact prefixLift 959364
  have htrace : WordTrace (prefixWord ++ tailWord_959364) baseStart_959364 baseEnd_959364 := by
    simpa [prefixWord, tailWord_959364, baseEnd_959364] using wordTrace_append hprefix tailTrace_959364
  have hstable : (prefixWord ++ tailWord_959364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959364).length < 2 ^ (prefixWord ++ tailWord_959364).sum := by decide
  have hdescent : baseEnd_959364 < baseStart_959364 := by decide
  rcases family_descends (prefixWord ++ tailWord_959364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959404 : List Nat := [2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 6]
def baseStart_959404 : Nat := 118140960795 + 959404 * 2 ^ 59
def prefixEnd_959404 : Nat := 4983230072969 + 3 ^ 40 * 959404 * 2
def baseEnd_959404 : Nat := 492635393846269561137787

theorem tailTrace_959404 : CollatzResearch.WordTrace tailWord_959404 prefixEnd_959404 492635393846269561137787 := by
  unfold tailWord_959404
  simp only [CollatzResearch.WordTrace]
  refine ⟨17496169308125318001646633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23328225744167090668862177 17496169308125318001646633)
  ·
    refine ⟨13122126981093988501234975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17496169308125318001646633 13122126981093988501234975)
    ·
      refine ⟨19683190471640982751852463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13122126981093988501234975 19683190471640982751852463)
      ·
        refine ⟨29524785707461474127778695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19683190471640982751852463 29524785707461474127778695)
        ·
          refine ⟨44287178561192211191668043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29524785707461474127778695 44287178561192211191668043)
          ·
            refine ⟨66430767841788316787502065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44287178561192211191668043 66430767841788316787502065)
            ·
              refine ⟨49823075881341237590626549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66430767841788316787502065 49823075881341237590626549)
              ·
                refine ⟨4670913363875741024121239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49823075881341237590626549 4670913363875741024121239)
                ·
                  refine ⟨7006370045813611536181859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4670913363875741024121239 7006370045813611536181859)
                  ·
                    refine ⟨10509555068720417304272789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7006370045813611536181859 10509555068720417304272789)
                    ·
                      refine ⟨492635393846269561137787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10509555068720417304272789 492635393846269561137787)
                      ·
                        rfl

theorem cell23_959404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 6].length) (baseStart_959404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_959404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_959404 prefixEnd_959404 := by exact prefixLift 959404
  have htrace : WordTrace (prefixWord ++ tailWord_959404) baseStart_959404 baseEnd_959404 := by
    simpa [prefixWord, tailWord_959404, baseEnd_959404] using wordTrace_append hprefix tailTrace_959404
  have hstable : (prefixWord ++ tailWord_959404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959404).length < 2 ^ (prefixWord ++ tailWord_959404).sum := by decide
  have hdescent : baseEnd_959404 < baseStart_959404 := by decide
  rcases family_descends (prefixWord ++ tailWord_959404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959442 : List Nat := [3, 2, 2, 3, 1, 1, 3, 1, 3, 2, 2]
def baseStart_959442 : Nat := 118140960795 + 959442 * 2 ^ 59
def prefixEnd_959442 : Nat := 4983230072969 + 3 ^ 40 * 959442 * 2
def baseEnd_959442 : Nat := 492654906111140412462613

theorem tailTrace_959442 : CollatzResearch.WordTrace tailWord_959442 prefixEnd_959442 492654906111140412462613 := by
  unfold tailWord_959442
  simp only [CollatzResearch.WordTrace]
  refine ⟨8748431147528242123294145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23329149726741978995451053 8748431147528242123294145)
  ·
    refine ⟨6561323360646181592470609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8748431147528242123294145 6561323360646181592470609)
    ·
      refine ⟨4920992520484636194352957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6561323360646181592470609 4920992520484636194352957)
      ·
        refine ⟨1845372195181738572882359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4920992520484636194352957 1845372195181738572882359)
        ·
          refine ⟨2768058292772607859323539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1845372195181738572882359 2768058292772607859323539)
          ·
            refine ⟨4152087439158911788985309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2768058292772607859323539 4152087439158911788985309)
            ·
              refine ⟨1557032789684591920869491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4152087439158911788985309 1557032789684591920869491)
              ·
                refine ⟨2335549184526887881304237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1557032789684591920869491 2335549184526887881304237)
                ·
                  refine ⟨875830944197582955489089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2335549184526887881304237 875830944197582955489089)
                  ·
                    refine ⟨656873208148187216616817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 875830944197582955489089 656873208148187216616817)
                    ·
                      refine ⟨492654906111140412462613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 656873208148187216616817 492654906111140412462613)
                      ·
                        rfl

theorem cell23_959442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_959442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_959442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_959442 prefixEnd_959442 := by exact prefixLift 959442
  have htrace : WordTrace (prefixWord ++ tailWord_959442) baseStart_959442 baseEnd_959442 := by
    simpa [prefixWord, tailWord_959442, baseEnd_959442] using wordTrace_append hprefix tailTrace_959442
  have hstable : (prefixWord ++ tailWord_959442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959442).length < 2 ^ (prefixWord ++ tailWord_959442).sum := by decide
  have hdescent : baseEnd_959442 < baseStart_959442 := by decide
  rcases family_descends (prefixWord ++ tailWord_959442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959521 : List Nat := [1, 2, 3, 2, 3, 1, 1, 1, 9]
def baseStart_959521 : Nat := 118140960795 + 959521 * 2 ^ 59
def prefixEnd_959521 : Nat := 4983230072969 + 3 ^ 40 * 959521 * 2
def baseEnd_959521 : Nat := 54743941231427289263861

theorem tailTrace_959521 : CollatzResearch.WordTrace tailWord_959521 prefixEnd_959521 54743941231427289263861 := by
  unfold tailWord_959521
  simp only [CollatzResearch.WordTrace]
  refine ⟨34996605956826764985302417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23331070637884509990201611 34996605956826764985302417)
  ·
    refine ⟨26247454467620073738976813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34996605956826764985302417 26247454467620073738976813)
    ·
      refine ⟨9842795425357527652116305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26247454467620073738976813 9842795425357527652116305)
      ·
        refine ⟨7382096569018145739087229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9842795425357527652116305 7382096569018145739087229)
        ·
          refine ⟨2768286213381804652157711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7382096569018145739087229 2768286213381804652157711)
          ·
            refine ⟨4152429320072706978236567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2768286213381804652157711 4152429320072706978236567)
            ·
              refine ⟨6228643980109060467354851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4152429320072706978236567 6228643980109060467354851)
              ·
                refine ⟨9342965970163590701032277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6228643980109060467354851 9342965970163590701032277)
                ·
                  refine ⟨54743941231427289263861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 9342965970163590701032277 54743941231427289263861)
                  ·
                    rfl

theorem cell23_959521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 9].length) (baseStart_959521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_959521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_959521 prefixEnd_959521 := by exact prefixLift 959521
  have htrace : WordTrace (prefixWord ++ tailWord_959521) baseStart_959521 baseEnd_959521 := by
    simpa [prefixWord, tailWord_959521, baseEnd_959521] using wordTrace_append hprefix tailTrace_959521
  have hstable : (prefixWord ++ tailWord_959521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959521).length < 2 ^ (prefixWord ++ tailWord_959521).sum := by decide
  have hdescent : baseEnd_959521 < baseStart_959521 := by decide
  rcases family_descends (prefixWord ++ tailWord_959521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959531 : List Nat := [1, 1, 1, 1, 2, 1, 5, 2, 1, 5, 3]
def baseStart_959531 : Nat := 118140960795 + 959531 * 2 ^ 59
def prefixEnd_959531 : Nat := 4983230072969 + 3 ^ 40 * 959531 * 2
def baseEnd_959531 : Nat := 492700605889390564249703

theorem tailTrace_959531 : CollatzResearch.WordTrace tailWord_959531 prefixEnd_959531 492700605889390564249703 := by
  unfold tailWord_959531
  simp only [CollatzResearch.WordTrace]
  refine ⟨34996970686790536693166447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23331313791193691128777631 34996970686790536693166447)
  ·
    refine ⟨52495456030185805039749671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34996970686790536693166447 52495456030185805039749671)
    ·
      refine ⟨78743184045278707559624507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52495456030185805039749671 78743184045278707559624507)
      ·
        refine ⟨118114776067918061339436761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78743184045278707559624507 118114776067918061339436761)
        ·
          refine ⟨88586082050938546004577571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118114776067918061339436761 88586082050938546004577571)
          ·
            refine ⟨132879123076407819006866357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88586082050938546004577571 132879123076407819006866357)
            ·
              refine ⟨12457417788413233031893721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 132879123076407819006866357 12457417788413233031893721)
              ·
                refine ⟨9343063341309924773920291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12457417788413233031893721 9343063341309924773920291)
                ·
                  refine ⟨14014595011964887160880437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9343063341309924773920291 14014595011964887160880437)
                  ·
                    refine ⟨1313868282371708171332541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14014595011964887160880437 1313868282371708171332541)
                    ·
                      refine ⟨492700605889390564249703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1313868282371708171332541 492700605889390564249703)
                      ·
                        rfl

theorem cell23_959531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 5, 3].length) (baseStart_959531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_959531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_959531 prefixEnd_959531 := by exact prefixLift 959531
  have htrace : WordTrace (prefixWord ++ tailWord_959531) baseStart_959531 baseEnd_959531 := by
    simpa [prefixWord, tailWord_959531, baseEnd_959531] using wordTrace_append hprefix tailTrace_959531
  have hstable : (prefixWord ++ tailWord_959531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959531).length < 2 ^ (prefixWord ++ tailWord_959531).sum := by decide
  have hdescent : baseEnd_959531 < baseStart_959531 := by decide
  rcases family_descends (prefixWord ++ tailWord_959531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959548 : List Nat := [2, 2, 2, 2, 2, 2, 1, 2, 2, 3, 3]
def baseStart_959548 : Nat := 118140960795 + 959548 * 2 ^ 59
def prefixEnd_959548 : Nat := 4983230072969 + 3 ^ 40 * 959548 * 2
def baseEnd_959548 : Nat := 492709335060516997737125

theorem tailTrace_959548 : CollatzResearch.WordTrace tailWord_959548 prefixEnd_959548 492709335060516997737125 := by
  unfold tailWord_959548
  simp only [CollatzResearch.WordTrace]
  refine ⟨17498795363864474298267649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23331727151819299064356865 17498795363864474298267649)
  ·
    refine ⟨13124096522898355723700737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17498795363864474298267649 13124096522898355723700737)
    ·
      refine ⟨9843072392173766792775553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13124096522898355723700737 9843072392173766792775553)
      ·
        refine ⟨7382304294130325094581665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9843072392173766792775553 7382304294130325094581665)
        ·
          refine ⟨5536728220597743820936249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7382304294130325094581665 5536728220597743820936249)
          ·
            refine ⟨4152546165448307865702187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5536728220597743820936249 4152546165448307865702187)
            ·
              refine ⟨6228819248172461798553281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4152546165448307865702187 6228819248172461798553281)
              ·
                refine ⟨4671614436129346348914961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6228819248172461798553281 4671614436129346348914961)
                ·
                  refine ⟨3503710827097009761686221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4671614436129346348914961 3503710827097009761686221)
                  ·
                    refine ⟨1313891560161378660632333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3503710827097009761686221 1313891560161378660632333)
                    ·
                      refine ⟨492709335060516997737125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1313891560161378660632333 492709335060516997737125)
                      ·
                        rfl

theorem cell23_959548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 2, 3, 3].length) (baseStart_959548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_959548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_959548 prefixEnd_959548 := by exact prefixLift 959548
  have htrace : WordTrace (prefixWord ++ tailWord_959548) baseStart_959548 baseEnd_959548 := by
    simpa [prefixWord, tailWord_959548, baseEnd_959548] using wordTrace_append hprefix tailTrace_959548
  have hstable : (prefixWord ++ tailWord_959548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959548).length < 2 ^ (prefixWord ++ tailWord_959548).sum := by decide
  have hdescent : baseEnd_959548 < baseStart_959548 := by decide
  rcases family_descends (prefixWord ++ tailWord_959548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959549 : List Nat := [1, 4, 1, 3, 1, 4, 1, 2, 2, 2, 2]
def baseStart_959549 : Nat := 118140960795 + 959549 * 2 ^ 59
def prefixEnd_959549 : Nat := 4983230072969 + 3 ^ 40 * 959549 * 2
def baseEnd_959549 : Nat := 492709848541171493824621

theorem tailTrace_959549 : CollatzResearch.WordTrace tailWord_959549 prefixEnd_959549 492709848541171493824621 := by
  unfold tailWord_959549
  simp only [CollatzResearch.WordTrace]
  refine ⟨34997627200725325767321701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23331751467150217178214467 34997627200725325767321701)
  ·
    refine ⟨6562055100135998581372819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34997627200725325767321701 6562055100135998581372819)
    ·
      refine ⟨9843082650203997872059229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6562055100135998581372819 9843082650203997872059229)
      ·
        refine ⟨3691155993826499202022211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9843082650203997872059229 3691155993826499202022211)
        ·
          refine ⟨5536733990739748803033317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3691155993826499202022211 5536733990739748803033317)
          ·
            refine ⟨1038137623263702900568747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5536733990739748803033317 1038137623263702900568747)
            ·
              refine ⟨1557206434895554350853121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1038137623263702900568747 1557206434895554350853121)
              ·
                refine ⟨1167904826171665763139841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1557206434895554350853121 1167904826171665763139841)
                ·
                  refine ⟨875928619628749322354881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1167904826171665763139841 875928619628749322354881)
                  ·
                    refine ⟨656946464721561991766161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 875928619628749322354881 656946464721561991766161)
                    ·
                      refine ⟨492709848541171493824621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 656946464721561991766161 492709848541171493824621)
                      ·
                        rfl

theorem cell23_959549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 2, 2, 2, 2].length) (baseStart_959549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_959549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_959549 prefixEnd_959549 := by exact prefixLift 959549
  have htrace : WordTrace (prefixWord ++ tailWord_959549) baseStart_959549 baseEnd_959549 := by
    simpa [prefixWord, tailWord_959549, baseEnd_959549] using wordTrace_append hprefix tailTrace_959549
  have hstable : (prefixWord ++ tailWord_959549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959549).length < 2 ^ (prefixWord ++ tailWord_959549).sum := by decide
  have hdescent : baseEnd_959549 < baseStart_959549 := by decide
  rcases family_descends (prefixWord ++ tailWord_959549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959551 : List Nat := [1, 1, 2, 2, 3, 1, 1, 3, 4, 5]
def baseStart_959551 : Nat := 118140960795 + 959551 * 2 ^ 59
def prefixEnd_959551 : Nat := 4983230072969 + 3 ^ 40 * 959551 * 2
def baseEnd_959551 : Nat := 164236958500826828666537

theorem tailTrace_959551 : CollatzResearch.WordTrace tailWord_959551 prefixEnd_959551 164236958500826828666537 := by
  unfold tailWord_959551
  simp only [CollatzResearch.WordTrace]
  refine ⟨34997700146718080108894507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23331800097812053405929671 34997700146718080108894507)
  ·
    refine ⟨52496550220077120163341761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34997700146718080108894507 52496550220077120163341761)
    ·
      refine ⟨39372412665057840122506321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52496550220077120163341761 39372412665057840122506321)
      ·
        refine ⟨29529309498793380091879741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39372412665057840122506321 29529309498793380091879741)
        ·
          refine ⟨11073491062047517534454903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29529309498793380091879741 11073491062047517534454903)
          ·
            refine ⟨16610236593071276301682355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11073491062047517534454903 16610236593071276301682355)
            ·
              refine ⟨24915354889606914452523533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16610236593071276301682355 24915354889606914452523533)
              ·
                refine ⟨9343258083602592919696325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24915354889606914452523533 9343258083602592919696325)
                ·
                  refine ⟨1751860890675486172443061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9343258083602592919696325 1751860890675486172443061)
                  ·
                    refine ⟨164236958500826828666537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1751860890675486172443061 164236958500826828666537)
                    ·
                      rfl

theorem cell23_959551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 4, 5].length) (baseStart_959551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_959551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_959551 prefixEnd_959551 := by exact prefixLift 959551
  have htrace : WordTrace (prefixWord ++ tailWord_959551) baseStart_959551 baseEnd_959551 := by
    simpa [prefixWord, tailWord_959551, baseEnd_959551] using wordTrace_append hprefix tailTrace_959551
  have hstable : (prefixWord ++ tailWord_959551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959551).length < 2 ^ (prefixWord ++ tailWord_959551).sum := by decide
  have hdescent : baseEnd_959551 < baseStart_959551 := by decide
  rcases family_descends (prefixWord ++ tailWord_959551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959565 : List Nat := [1, 6, 1, 1, 1, 2, 2, 1, 2, 3, 3]
def baseStart_959565 : Nat := 118140960795 + 959565 * 2 ^ 59
def prefixEnd_959565 : Nat := 4983230072969 + 3 ^ 40 * 959565 * 2
def baseEnd_959565 : Nat := 492718064231643431224547

theorem tailTrace_959565 : CollatzResearch.WordTrace tailWord_959565 prefixEnd_959565 492718064231643431224547 := by
  unfold tailWord_959565
  simp only [CollatzResearch.WordTrace]
  refine ⟨34998210768667360499904149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23332140512444906999936099 34998210768667360499904149)
  ·
    refine ⟨1640541129781282523433007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 34998210768667360499904149 1640541129781282523433007)
    ·
      refine ⟨2460811694671923785149511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1640541129781282523433007 2460811694671923785149511)
      ·
        refine ⟨3691217542007885677724267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2460811694671923785149511 3691217542007885677724267)
        ·
          refine ⟨5536826313011828516586401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3691217542007885677724267 5536826313011828516586401)
          ·
            refine ⟨4152619734758871387439801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5536826313011828516586401 4152619734758871387439801)
            ·
              refine ⟨3114464801069153540579851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4152619734758871387439801 3114464801069153540579851)
              ·
                refine ⟨4671697201603730310869777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3114464801069153540579851 4671697201603730310869777)
                ·
                  refine ⟨3503772901202797733152333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4671697201603730310869777 3503772901202797733152333)
                  ·
                    refine ⟨1313914837951049149932125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3503772901202797733152333 1313914837951049149932125)
                    ·
                      refine ⟨492718064231643431224547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1313914837951049149932125 492718064231643431224547)
                      ·
                        rfl

theorem cell23_959565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_959565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_959565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_959565 prefixEnd_959565 := by exact prefixLift 959565
  have htrace : WordTrace (prefixWord ++ tailWord_959565) baseStart_959565 baseEnd_959565 := by
    simpa [prefixWord, tailWord_959565, baseEnd_959565] using wordTrace_append hprefix tailTrace_959565
  have hstable : (prefixWord ++ tailWord_959565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959565).length < 2 ^ (prefixWord ++ tailWord_959565).sum := by decide
  have hdescent : baseEnd_959565 < baseStart_959565 := by decide
  rcases family_descends (prefixWord ++ tailWord_959565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959571 : List Nat := [1, 1, 1, 2, 1, 1, 2, 6, 1, 3, 4]
def baseStart_959571 : Nat := 118140960795 + 959571 * 2 ^ 59
def prefixEnd_959571 : Nat := 4983230072969 + 3 ^ 40 * 959571 * 2
def baseEnd_959571 : Nat := 492721145115570407749519

theorem tailTrace_959571 : CollatzResearch.WordTrace tailWord_959571 prefixEnd_959571 492721145115570407749519 := by
  unfold tailWord_959571
  simp only [CollatzResearch.WordTrace]
  refine ⟨34998429606645623524622567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23332286404430415683081711 34998429606645623524622567)
  ·
    refine ⟨52497644409968435286933851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34998429606645623524622567 52497644409968435286933851)
    ·
      refine ⟨78746466614952652930400777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52497644409968435286933851 78746466614952652930400777)
      ·
        refine ⟨59059849961214489697800583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78746466614952652930400777 59059849961214489697800583)
        ·
          refine ⟨88589774941821734546700875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59059849961214489697800583 88589774941821734546700875)
          ·
            refine ⟨132884662412732601820051313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88589774941821734546700875 132884662412732601820051313)
            ·
              refine ⟨99663496809549451365038485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132884662412732601820051313 99663496809549451365038485)
              ·
                refine ⟨4671726412947630532736179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 99663496809549451365038485 4671726412947630532736179)
                ·
                  refine ⟨7007589619421445799104269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4671726412947630532736179 7007589619421445799104269)
                  ·
                    refine ⟨2627846107283042174664101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7007589619421445799104269 2627846107283042174664101)
                    ·
                      refine ⟨492721145115570407749519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2627846107283042174664101 492721145115570407749519)
                      ·
                        rfl

theorem cell23_959571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 3, 4].length) (baseStart_959571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_959571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_959571 prefixEnd_959571 := by exact prefixLift 959571
  have htrace : WordTrace (prefixWord ++ tailWord_959571) baseStart_959571 baseEnd_959571 := by
    simpa [prefixWord, tailWord_959571, baseEnd_959571] using wordTrace_append hprefix tailTrace_959571
  have hstable : (prefixWord ++ tailWord_959571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959571).length < 2 ^ (prefixWord ++ tailWord_959571).sum := by decide
  have hdescent : baseEnd_959571 < baseStart_959571 := by decide
  rcases family_descends (prefixWord ++ tailWord_959571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959588 : List Nat := [2, 3, 1, 1, 2, 1, 1, 5, 2, 1, 4]
def baseStart_959588 : Nat := 118140960795 + 959588 * 2 ^ 59
def prefixEnd_959588 : Nat := 4983230072969 + 3 ^ 40 * 959588 * 2
def baseEnd_959588 : Nat := 492729874286696841236941

theorem tailTrace_959588 : CollatzResearch.WordTrace tailWord_959588 prefixEnd_959588 492729874286696841236941 := by
  unfold tailWord_959588
  simp only [CollatzResearch.WordTrace]
  refine ⟨17499524823792017713995709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23332699765056023618660945 17499524823792017713995709)
  ·
    refine ⟨6562321808922006642748391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17499524823792017713995709 6562321808922006642748391)
    ·
      refine ⟨9843482713383009964122587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6562321808922006642748391 9843482713383009964122587)
      ·
        refine ⟨14765224070074514946183881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9843482713383009964122587 14765224070074514946183881)
        ·
          refine ⟨11073918052555886209637911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14765224070074514946183881 11073918052555886209637911)
          ·
            refine ⟨16610877078833829314456867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11073918052555886209637911 16610877078833829314456867)
            ·
              refine ⟨24916315618250743971685301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16610877078833829314456867 24916315618250743971685301)
              ·
                refine ⟨2335904589211007247345497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24916315618250743971685301 2335904589211007247345497)
                ·
                  refine ⟨1751928441908255435509123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2335904589211007247345497 1751928441908255435509123)
                  ·
                    refine ⟨2627892662862383153263685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1751928441908255435509123 2627892662862383153263685)
                    ·
                      refine ⟨492729874286696841236941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2627892662862383153263685 492729874286696841236941)
                      ·
                        rfl

theorem cell23_959588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 5, 2, 1, 4].length) (baseStart_959588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_959588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_959588 prefixEnd_959588 := by exact prefixLift 959588
  have htrace : WordTrace (prefixWord ++ tailWord_959588) baseStart_959588 baseEnd_959588 := by
    simpa [prefixWord, tailWord_959588, baseEnd_959588] using wordTrace_append hprefix tailTrace_959588
  have hstable : (prefixWord ++ tailWord_959588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959588).length < 2 ^ (prefixWord ++ tailWord_959588).sum := by decide
  have hdescent : baseEnd_959588 < baseStart_959588 := by decide
  rcases family_descends (prefixWord ++ tailWord_959588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959601 : List Nat := [1, 2, 2, 2, 1, 1, 2, 3, 2, 1, 6]
def baseStart_959601 : Nat := 118140960795 + 959601 * 2 ^ 59
def prefixEnd_959601 : Nat := 4983230072969 + 3 ^ 40 * 959601 * 2
def baseEnd_959601 : Nat := 492736549535205290374381

theorem tailTrace_959601 : CollatzResearch.WordTrace tailWord_959601 prefixEnd_959601 492736549535205290374381 := by
  unfold tailWord_959601
  simp only [CollatzResearch.WordTrace]
  refine ⟨34999523796536938648214657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23333015864357959098809771 34999523796536938648214657)
  ·
    refine ⟨26249642847402703986160993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34999523796536938648214657 26249642847402703986160993)
    ·
      refine ⟨19687232135552027989620745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26249642847402703986160993 19687232135552027989620745)
      ·
        refine ⟨14765424101664020992215559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19687232135552027989620745 14765424101664020992215559)
        ·
          refine ⟨22148136152496031488323339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14765424101664020992215559 22148136152496031488323339)
          ·
            refine ⟨33222204228744047232485009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22148136152496031488323339 33222204228744047232485009)
            ·
              refine ⟨24916653171558035424363757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33222204228744047232485009 24916653171558035424363757)
              ·
                refine ⟨9343744939334263284136409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24916653171558035424363757 9343744939334263284136409)
                ·
                  refine ⟨7007808704500697463102307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9343744939334263284136409 7007808704500697463102307)
                  ·
                    refine ⟨10511713056751046194653461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7007808704500697463102307 10511713056751046194653461)
                    ·
                      refine ⟨492736549535205290374381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10511713056751046194653461 492736549535205290374381)
                      ·
                        rfl

theorem cell23_959601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_959601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_959601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_959601 prefixEnd_959601 := by exact prefixLift 959601
  have htrace : WordTrace (prefixWord ++ tailWord_959601) baseStart_959601 baseEnd_959601 := by
    simpa [prefixWord, tailWord_959601, baseEnd_959601] using wordTrace_append hprefix tailTrace_959601
  have hstable : (prefixWord ++ tailWord_959601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959601).length < 2 ^ (prefixWord ++ tailWord_959601).sum := by decide
  have hdescent : baseEnd_959601 < baseStart_959601 := by decide
  rcases family_descends (prefixWord ++ tailWord_959601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959608 : List Nat := [2, 1, 2, 1, 1, 1, 5, 1, 4, 2, 3]
def baseStart_959608 : Nat := 118140960795 + 959608 * 2 ^ 59
def prefixEnd_959608 : Nat := 4983230072969 + 3 ^ 40 * 959608 * 2
def baseEnd_959608 : Nat := 492740143899786762986849

theorem tailTrace_959608 : CollatzResearch.WordTrace tailWord_959608 prefixEnd_959608 492740143899786762986849 := by
  unfold tailWord_959608
  simp only [CollatzResearch.WordTrace]
  refine ⟨17499889553755789421859739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23333186071674385895812985 17499889553755789421859739)
  ·
    refine ⟨26249834330633684132789609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17499889553755789421859739 26249834330633684132789609)
    ·
      refine ⟨19687375747975263099592207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26249834330633684132789609 19687375747975263099592207)
      ·
        refine ⟨29531063621962894649388311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19687375747975263099592207 29531063621962894649388311)
        ·
          refine ⟨44296595432944341974082467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29531063621962894649388311 44296595432944341974082467)
          ·
            refine ⟨66444893149416512961123701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44296595432944341974082467 66444893149416512961123701)
            ·
              refine ⟨6229208732757798090105347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66444893149416512961123701 6229208732757798090105347)
              ·
                refine ⟨9343813099136697135158021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6229208732757798090105347 9343813099136697135158021)
                ·
                  refine ⟨1751964956088130712842129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9343813099136697135158021 1751964956088130712842129)
                  ·
                    refine ⟨1313973717066098034631597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1751964956088130712842129 1313973717066098034631597)
                    ·
                      refine ⟨492740143899786762986849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1313973717066098034631597 492740143899786762986849)
                      ·
                        rfl

theorem cell23_959608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 4, 2, 3].length) (baseStart_959608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_959608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_959608 prefixEnd_959608 := by exact prefixLift 959608
  have htrace : WordTrace (prefixWord ++ tailWord_959608) baseStart_959608 baseEnd_959608 := by
    simpa [prefixWord, tailWord_959608, baseEnd_959608] using wordTrace_append hprefix tailTrace_959608
  have hstable : (prefixWord ++ tailWord_959608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959608).length < 2 ^ (prefixWord ++ tailWord_959608).sum := by decide
  have hdescent : baseEnd_959608 < baseStart_959608 := by decide
  rcases family_descends (prefixWord ++ tailWord_959608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959642 : List Nat := [3, 1, 1, 5, 1, 2, 2, 1, 2, 2, 3]
def baseStart_959642 : Nat := 118140960795 + 959642 * 2 ^ 59
def prefixEnd_959642 : Nat := 4983230072969 + 3 ^ 40 * 959642 * 2
def baseEnd_959642 : Nat := 492757602242039629961693

theorem tailTrace_959642 : CollatzResearch.WordTrace tailWord_959642 prefixEnd_959642 492757602242039629961693 := by
  unfold tailWord_959642
  simp only [CollatzResearch.WordTrace]
  refine ⟨8750254797347100662614295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23334012792925601766971453 8750254797347100662614295)
  ·
    refine ⟨13125382196020650993921443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8750254797347100662614295 13125382196020650993921443)
    ·
      refine ⟨19688073294030976490882165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13125382196020650993921443 19688073294030976490882165)
      ·
        refine ⟨1845756871315404046020203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19688073294030976490882165 1845756871315404046020203)
        ·
          refine ⟨2768635306973106069030305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1845756871315404046020203 2768635306973106069030305)
          ·
            refine ⟨2076476480229829551772729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2768635306973106069030305 2076476480229829551772729)
            ·
              refine ⟨1557357360172372163829547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2076476480229829551772729 1557357360172372163829547)
              ·
                refine ⟨2336036040258558245744321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1557357360172372163829547 2336036040258558245744321)
                ·
                  refine ⟨1752027030193918684308241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2336036040258558245744321 1752027030193918684308241)
                  ·
                    refine ⟨1314020272645439013231181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1752027030193918684308241 1314020272645439013231181)
                    ·
                      refine ⟨492757602242039629961693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1314020272645439013231181 492757602242039629961693)
                      ·
                        rfl

theorem cell23_959642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_959642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_959642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_959642 prefixEnd_959642 := by exact prefixLift 959642
  have htrace : WordTrace (prefixWord ++ tailWord_959642) baseStart_959642 baseEnd_959642 := by
    simpa [prefixWord, tailWord_959642, baseEnd_959642] using wordTrace_append hprefix tailTrace_959642
  have hstable : (prefixWord ++ tailWord_959642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959642).length < 2 ^ (prefixWord ++ tailWord_959642).sum := by decide
  have hdescent : baseEnd_959642 < baseStart_959642 := by decide
  rcases family_descends (prefixWord ++ tailWord_959642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959651 : List Nat := [1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 7]
def baseStart_959651 : Nat := 118140960795 + 959651 * 2 ^ 59
def prefixEnd_959651 : Nat := 4983230072969 + 3 ^ 40 * 959651 * 2
def baseEnd_959651 : Nat := 492762223567930094749151

theorem tailTrace_959651 : CollatzResearch.WordTrace tailWord_959651 prefixEnd_959651 492762223567930094749151 := by
  unfold tailWord_959651
  simp only [CollatzResearch.WordTrace]
  refine ⟨35001347446355797187534807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23334231630903864791689871 35001347446355797187534807)
  ·
    refine ⟨52502021169533695781302211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35001347446355797187534807 52502021169533695781302211)
    ·
      refine ⟨78753031754300543671953317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52502021169533695781302211 78753031754300543671953317)
      ·
        refine ⟨14766193453931351938491247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78753031754300543671953317 14766193453931351938491247)
        ·
          refine ⟨22149290180897027907736871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14766193453931351938491247 22149290180897027907736871)
          ·
            refine ⟨33223935271345541861605307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22149290180897027907736871 33223935271345541861605307)
            ·
              refine ⟨49835902907018312792407961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33223935271345541861605307 49835902907018312792407961)
              ·
                refine ⟨37376927180263734594305971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49835902907018312792407961 37376927180263734594305971)
                ·
                  refine ⟨56065390770395601891458957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37376927180263734594305971 56065390770395601891458957)
                  ·
                    refine ⟨21024521538898350709297109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56065390770395601891458957 21024521538898350709297109)
                    ·
                      refine ⟨492762223567930094749151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 21024521538898350709297109 492762223567930094749151)
                      ·
                        rfl

theorem cell23_959651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_959651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_959651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_959651 prefixEnd_959651 := by exact prefixLift 959651
  have htrace : WordTrace (prefixWord ++ tailWord_959651) baseStart_959651 baseEnd_959651 := by
    simpa [prefixWord, tailWord_959651, baseEnd_959651] using wordTrace_append hprefix tailTrace_959651
  have hstable : (prefixWord ++ tailWord_959651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959651).length < 2 ^ (prefixWord ++ tailWord_959651).sum := by decide
  have hdescent : baseEnd_959651 < baseStart_959651 := by decide
  rcases family_descends (prefixWord ++ tailWord_959651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959688 : List Nat := [2, 1, 3, 1, 2, 1, 3, 3, 1, 6]
def baseStart_959688 : Nat := 118140960795 + 959688 * 2 ^ 59
def prefixEnd_959688 : Nat := 4983230072969 + 3 ^ 40 * 959688 * 2
def baseEnd_959688 : Nat := 164260407450715483328827

theorem tailTrace_959688 : CollatzResearch.WordTrace tailWord_959688 prefixEnd_959688 164260407450715483328827 := by
  unfold tailWord_959688
  simp only [CollatzResearch.WordTrace]
  refine ⟨17501348473610876253315859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23335131298147835004421145 17501348473610876253315859)
  ·
    refine ⟨26252022710416314379973789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17501348473610876253315859 26252022710416314379973789)
    ·
      refine ⟨9844508516406117892490171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26252022710416314379973789 9844508516406117892490171)
      ·
        refine ⟨14766762774609176838735257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9844508516406117892490171 14766762774609176838735257)
        ·
          refine ⟨11075072080956882629051443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14766762774609176838735257 11075072080956882629051443)
          ·
            refine ⟨16612608121435323943577165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11075072080956882629051443 16612608121435323943577165)
            ·
              refine ⟨6229728045538246478841437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16612608121435323943577165 6229728045538246478841437)
              ·
                refine ⟨2336148017076842429565539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6229728045538246478841437 2336148017076842429565539)
                ·
                  refine ⟨3504222025615263644348309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2336148017076842429565539 3504222025615263644348309)
                  ·
                    refine ⟨164260407450715483328827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3504222025615263644348309 164260407450715483328827)
                    ·
                      rfl

theorem cell23_959688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 3, 1, 6].length) (baseStart_959688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_959688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_959688 prefixEnd_959688 := by exact prefixLift 959688
  have htrace : WordTrace (prefixWord ++ tailWord_959688) baseStart_959688 baseEnd_959688 := by
    simpa [prefixWord, tailWord_959688, baseEnd_959688] using wordTrace_append hprefix tailTrace_959688
  have hstable : (prefixWord ++ tailWord_959688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959688).length < 2 ^ (prefixWord ++ tailWord_959688).sum := by decide
  have hdescent : baseEnd_959688 < baseStart_959688 := by decide
  rcases family_descends (prefixWord ++ tailWord_959688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959693 : List Nat := [1, 6, 2, 2, 2, 1, 1, 1, 2, 2, 3]
def baseStart_959693 : Nat := 118140960795 + 959693 * 2 ^ 59
def prefixEnd_959693 : Nat := 4983230072969 + 3 ^ 40 * 959693 * 2
def baseEnd_959693 : Nat := 492783789755418930423959

theorem tailTrace_959693 : CollatzResearch.WordTrace tailWord_959693 prefixEnd_959693 492783789755418930423959 := by
  unfold tailWord_959693
  simp only [CollatzResearch.WordTrace]
  refine ⟨35002879312203638360563733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23335252874802425573709155 35002879312203638360563733)
  ·
    refine ⟨1640759967759545548151425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 35002879312203638360563733 1640759967759545548151425)
    ·
      refine ⟨1230569975819659161113569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1640759967759545548151425 1230569975819659161113569)
      ·
        refine ⟨922927481864744370835177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1230569975819659161113569 922927481864744370835177)
        ·
          refine ⟨692195611398558278126383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 922927481864744370835177 692195611398558278126383)
          ·
            refine ⟨1038293417097837417189575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 692195611398558278126383 1038293417097837417189575)
            ·
              refine ⟨1557440125646756125784363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1038293417097837417189575 1557440125646756125784363)
              ·
                refine ⟨2336160188470134188676545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1557440125646756125784363 2336160188470134188676545)
                ·
                  refine ⟨1752120141352600641507409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2336160188470134188676545 1752120141352600641507409)
                  ·
                    refine ⟨1314090106014450481130557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1752120141352600641507409 1314090106014450481130557)
                    ·
                      refine ⟨492783789755418930423959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1314090106014450481130557 492783789755418930423959)
                      ·
                        rfl

theorem cell23_959693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_959693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_959693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_959693 prefixEnd_959693 := by exact prefixLift 959693
  have htrace : WordTrace (prefixWord ++ tailWord_959693) baseStart_959693 baseEnd_959693 := by
    simpa [prefixWord, tailWord_959693, baseEnd_959693] using wordTrace_append hprefix tailTrace_959693
  have hstable : (prefixWord ++ tailWord_959693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959693).length < 2 ^ (prefixWord ++ tailWord_959693).sum := by decide
  have hdescent : baseEnd_959693 < baseStart_959693 := by decide
  rcases family_descends (prefixWord ++ tailWord_959693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959712 : List Nat := [2, 1, 1, 3, 1, 4, 4, 1, 1, 1, 4]
def baseStart_959712 : Nat := 118140960795 + 959712 * 2 ^ 59
def prefixEnd_959712 : Nat := 4983230072969 + 3 ^ 40 * 959712 * 2
def baseEnd_959712 : Nat := 492793545887854356086371

theorem tailTrace_959712 : CollatzResearch.WordTrace tailWord_959712 prefixEnd_959712 492793545887854356086371 := by
  unfold tailWord_959712
  simp only [CollatzResearch.WordTrace]
  refine ⟨17501786149567402302752695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23335714866089869737003593 17501786149567402302752695)
  ·
    refine ⟨26252679224351103454129043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17501786149567402302752695 26252679224351103454129043)
    ·
      refine ⟨39379018836526655181193565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26252679224351103454129043 39379018836526655181193565)
      ·
        refine ⟨14767132063697495692947587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39379018836526655181193565 14767132063697495692947587)
        ·
          refine ⟨22150698095546243539421381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14767132063697495692947587 22150698095546243539421381)
          ·
            refine ⟨4153255892914920663641509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22150698095546243539421381 4153255892914920663641509)
            ·
              refine ⟨778735479921547624432783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4153255892914920663641509 778735479921547624432783)
              ·
                refine ⟨1168103219882321436649175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 778735479921547624432783 1168103219882321436649175)
                ·
                  refine ⟨1752154829823482154973763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1168103219882321436649175 1752154829823482154973763)
                  ·
                    refine ⟨2628232244735223232460645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1752154829823482154973763 2628232244735223232460645)
                    ·
                      refine ⟨492793545887854356086371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2628232244735223232460645 492793545887854356086371)
                      ·
                        rfl

theorem cell23_959712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 4, 1, 1, 1, 4].length) (baseStart_959712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_959712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_959712 prefixEnd_959712 := by exact prefixLift 959712
  have htrace : WordTrace (prefixWord ++ tailWord_959712) baseStart_959712 baseEnd_959712 := by
    simpa [prefixWord, tailWord_959712, baseEnd_959712] using wordTrace_append hprefix tailTrace_959712
  have hstable : (prefixWord ++ tailWord_959712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959712).length < 2 ^ (prefixWord ++ tailWord_959712).sum := by decide
  have hdescent : baseEnd_959712 < baseStart_959712 := by decide
  rcases family_descends (prefixWord ++ tailWord_959712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959722 : List Nat := [3, 1, 3, 1, 1, 3, 3, 2, 2, 4]
def baseStart_959722 : Nat := 118140960795 + 959722 * 2 ^ 59
def prefixEnd_959722 : Nat := 4983230072969 + 3 ^ 40 * 959722 * 2
def baseEnd_959722 : Nat := 164266226898133105653775

theorem tailTrace_959722 : CollatzResearch.WordTrace tailWord_959722 prefixEnd_959722 164266226898133105653775 := by
  unfold tailWord_959722
  simp only [CollatzResearch.WordTrace]
  refine ⟨8750984257274644078342355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23335958019399050875579613 8750984257274644078342355)
  ·
    refine ⟨13126476385911966117513533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8750984257274644078342355 13126476385911966117513533)
    ·
      refine ⟨4922428644716987294067575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13126476385911966117513533 4922428644716987294067575)
      ·
        refine ⟨7383642967075480941101363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4922428644716987294067575 7383642967075480941101363)
        ·
          refine ⟨11075464450613221411652045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7383642967075480941101363 11075464450613221411652045)
          ·
            refine ⟨4153299168979958029369517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11075464450613221411652045 4153299168979958029369517)
            ·
              refine ⟨1557487188367484261013569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4153299168979958029369517 1557487188367484261013569)
              ·
                refine ⟨1168115391275613195760177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1557487188367484261013569 1168115391275613195760177)
                ·
                  refine ⟨876086543456709896820133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1168115391275613195760177 876086543456709896820133)
                  ·
                    refine ⟨164266226898133105653775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 876086543456709896820133 164266226898133105653775)
                    ·
                      rfl

theorem cell23_959722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 2, 2, 4].length) (baseStart_959722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_959722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_959722 prefixEnd_959722 := by exact prefixLift 959722
  have htrace : WordTrace (prefixWord ++ tailWord_959722) baseStart_959722 baseEnd_959722 := by
    simpa [prefixWord, tailWord_959722, baseEnd_959722] using wordTrace_append hprefix tailTrace_959722
  have hstable : (prefixWord ++ tailWord_959722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959722).length < 2 ^ (prefixWord ++ tailWord_959722).sum := by decide
  have hdescent : baseEnd_959722 < baseStart_959722 := by decide
  rcases family_descends (prefixWord ++ tailWord_959722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959728 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 2, 7, 3]
def baseStart_959728 : Nat := 118140960795 + 959728 * 2 ^ 59
def prefixEnd_959728 : Nat := 4983230072969 + 3 ^ 40 * 959728 * 2
def baseEnd_959728 : Nat := 492801761578326293486297

theorem tailTrace_959728 : CollatzResearch.WordTrace tailWord_959728 prefixEnd_959728 492801761578326293486297 := by
  unfold tailWord_959728
  simp only [CollatzResearch.WordTrace]
  refine ⟨17502077933538419669043919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23336103911384559558725225 17502077933538419669043919)
  ·
    refine ⟨26253116900307629503565879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17502077933538419669043919 26253116900307629503565879)
    ·
      refine ⟨39379675350461444255348819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26253116900307629503565879 39379675350461444255348819)
      ·
        refine ⟨59069513025692166383023229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39379675350461444255348819 59069513025692166383023229)
        ·
          refine ⟨22151067384634562393633711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59069513025692166383023229 22151067384634562393633711)
          ·
            refine ⟨33226601076951843590450567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22151067384634562393633711 33226601076951843590450567)
            ·
              refine ⟨49839901615427765385675851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33226601076951843590450567 49839901615427765385675851)
              ·
                refine ⟨74759852423141648078513777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49839901615427765385675851 74759852423141648078513777)
                ·
                  refine ⟨56069889317356236058885333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74759852423141648078513777 56069889317356236058885333)
                  ·
                    refine ⟨1314138030875536782630125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56069889317356236058885333 1314138030875536782630125)
                    ·
                      refine ⟨492801761578326293486297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1314138030875536782630125 492801761578326293486297)
                      ·
                        rfl

theorem cell23_959728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 2, 7, 3].length) (baseStart_959728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_959728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_959728 prefixEnd_959728 := by exact prefixLift 959728
  have htrace : WordTrace (prefixWord ++ tailWord_959728) baseStart_959728 baseEnd_959728 := by
    simpa [prefixWord, tailWord_959728, baseEnd_959728] using wordTrace_append hprefix tailTrace_959728
  have hstable : (prefixWord ++ tailWord_959728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959728).length < 2 ^ (prefixWord ++ tailWord_959728).sum := by decide
  have hdescent : baseEnd_959728 < baseStart_959728 := by decide
  rcases family_descends (prefixWord ++ tailWord_959728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959742 : List Nat := [4, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4]
def baseStart_959742 : Nat := 118140960795 + 959742 * 2 ^ 59
def prefixEnd_959742 : Nat := 4983230072969 + 3 ^ 40 * 959742 * 2
def baseEnd_959742 : Nat := 492808950307489238711233

theorem tailTrace_959742 : CollatzResearch.WordTrace tailWord_959742 prefixEnd_959742 492808950307489238711233 := by
  unfold tailWord_959742
  simp only [CollatzResearch.WordTrace]
  refine ⟨4375583311128264966137185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23336444326017413152731653 4375583311128264966137185)
  ·
    refine ⟨3281687483346198724602889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4375583311128264966137185 3281687483346198724602889)
    ·
      refine ⟨2461265612509649043452167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3281687483346198724602889 2461265612509649043452167)
      ·
        refine ⟨3691898418764473565178251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2461265612509649043452167 3691898418764473565178251)
        ·
          refine ⟨5537847628146710347767377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3691898418764473565178251 5537847628146710347767377)
          ·
            refine ⟨4153385721110032760825533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5537847628146710347767377 4153385721110032760825533)
            ·
              refine ⟨1557519645416262285309575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4153385721110032760825533 1557519645416262285309575)
              ·
                refine ⟨2336279468124393427964363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1557519645416262285309575 2336279468124393427964363)
                ·
                  refine ⟨3504419202186590141946545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2336279468124393427964363 3504419202186590141946545)
                  ·
                    refine ⟨2628314401639942606459909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3504419202186590141946545 2628314401639942606459909)
                    ·
                      refine ⟨492808950307489238711233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2628314401639942606459909 492808950307489238711233)
                      ·
                        rfl

theorem cell23_959742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_959742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_959742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_959742 prefixEnd_959742 := by exact prefixLift 959742
  have htrace : WordTrace (prefixWord ++ tailWord_959742) baseStart_959742 baseEnd_959742 := by
    simpa [prefixWord, tailWord_959742, baseEnd_959742] using wordTrace_append hprefix tailTrace_959742
  have hstable : (prefixWord ++ tailWord_959742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959742).length < 2 ^ (prefixWord ++ tailWord_959742).sum := by decide
  have hdescent : baseEnd_959742 < baseStart_959742 := by decide
  rcases family_descends (prefixWord ++ tailWord_959742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959752 : List Nat := [2, 1, 3, 2, 4, 2, 2, 7]
def baseStart_959752 : Nat := 118140960795 + 959752 * 2 ^ 59
def prefixEnd_959752 : Nat := 4983230072969 + 3 ^ 40 * 959752 * 2
def baseEnd_959752 : Nat := 18252373522742007392081

theorem tailTrace_959752 : CollatzResearch.WordTrace tailWord_959752 prefixEnd_959752 18252373522742007392081 := by
  unfold tailWord_959752
  simp only [CollatzResearch.WordTrace]
  refine ⟨17502515609494945718480755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23336687479326594291307673 17502515609494945718480755)
  ·
    refine ⟨26253773414242418577721133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17502515609494945718480755 26253773414242418577721133)
    ·
      refine ⟨9845165030340906966645425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26253773414242418577721133 9845165030340906966645425)
      ·
        refine ⟨7383873772755680224984069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9845165030340906966645425 7383873772755680224984069)
        ·
          refine ⟨1384476332391690042184513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7383873772755680224984069 1384476332391690042184513)
          ·
            refine ⟨1038357249293767531638385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1384476332391690042184513 1038357249293767531638385)
            ·
              refine ⟨778767936970325648728789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1038357249293767531638385 778767936970325648728789)
              ·
                refine ⟨18252373522742007392081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 778767936970325648728789 18252373522742007392081)
                ·
                  rfl

theorem cell23_959752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 2, 7].length) (baseStart_959752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_959752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_959752 prefixEnd_959752 := by exact prefixLift 959752
  have htrace : WordTrace (prefixWord ++ tailWord_959752) baseStart_959752 baseEnd_959752 := by
    simpa [prefixWord, tailWord_959752, baseEnd_959752] using wordTrace_append hprefix tailTrace_959752
  have hstable : (prefixWord ++ tailWord_959752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959752).length < 2 ^ (prefixWord ++ tailWord_959752).sum := by decide
  have hdescent : baseEnd_959752 < baseStart_959752 := by decide
  rcases family_descends (prefixWord ++ tailWord_959752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959788 : List Nat := [2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 5]
def baseStart_959788 : Nat := 118140960795 + 959788 * 2 ^ 59
def prefixEnd_959788 : Nat := 4983230072969 + 3 ^ 40 * 959788 * 2
def baseEnd_959788 : Nat := 492832570417596058736021

theorem tailTrace_959788 : CollatzResearch.WordTrace tailWord_959788 prefixEnd_959788 492832570417596058736021 := by
  unfold tailWord_959788
  simp only [CollatzResearch.WordTrace]
  refine ⟨17503172123429734792636009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23337562831239646390181345 17503172123429734792636009)
  ·
    refine ⟨13127379092572301094477007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17503172123429734792636009 13127379092572301094477007)
    ·
      refine ⟨19691068638858451641715511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13127379092572301094477007 19691068638858451641715511)
      ·
        refine ⟨29536602958287677462573267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19691068638858451641715511 29536602958287677462573267)
        ·
          refine ⟨44304904437431516193859901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29536602958287677462573267 44304904437431516193859901)
          ·
            refine ⟨16614339164036818572697463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44304904437431516193859901 16614339164036818572697463)
            ·
              refine ⟨24921508746055227859046195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16614339164036818572697463 24921508746055227859046195)
              ·
                refine ⟨37382263119082841788569293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24921508746055227859046195 37382263119082841788569293)
                ·
                  refine ⟨14018348669656065670713485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37382263119082841788569293 14018348669656065670713485)
                  ·
                    refine ⟨5256880751121024626517557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14018348669656065670713485 5256880751121024626517557)
                    ·
                      refine ⟨492832570417596058736021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5256880751121024626517557 492832570417596058736021)
                      ·
                        rfl

theorem cell23_959788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 5].length) (baseStart_959788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_959788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_959788 prefixEnd_959788 := by exact prefixLift 959788
  have htrace : WordTrace (prefixWord ++ tailWord_959788) baseStart_959788 baseEnd_959788 := by
    simpa [prefixWord, tailWord_959788, baseEnd_959788] using wordTrace_append hprefix tailTrace_959788
  have hstable : (prefixWord ++ tailWord_959788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959788).length < 2 ^ (prefixWord ++ tailWord_959788).sum := by decide
  have hdescent : baseEnd_959788 < baseStart_959788 := by decide
  rcases family_descends (prefixWord ++ tailWord_959788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959802 : List Nat := [3, 1, 1, 1, 4, 1, 2, 3, 1, 4, 2]
def baseStart_959802 : Nat := 118140960795 + 959802 * 2 ^ 59
def prefixEnd_959802 : Nat := 4983230072969 + 3 ^ 40 * 959802 * 2
def baseEnd_959802 : Nat := 492839759146759003960957

theorem tailTrace_959802 : CollatzResearch.WordTrace tailWord_959802 prefixEnd_959802 492839759146759003960957 := by
  unfold tailWord_959802
  simp only [CollatzResearch.WordTrace]
  refine ⟨8751713717202187494070415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23337903245872499984187773 8751713717202187494070415)
  ·
    refine ⟨13127570575803281241105623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8751713717202187494070415 13127570575803281241105623)
    ·
      refine ⟨19691355863704921861658435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13127570575803281241105623 19691355863704921861658435)
      ·
        refine ⟨29537033795557382792487653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19691355863704921861658435 29537033795557382792487653)
        ·
          refine ⟨5538193836667009273591435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29537033795557382792487653 5538193836667009273591435)
          ·
            refine ⟨8307290755000513910387153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5538193836667009273591435 8307290755000513910387153)
            ·
              refine ⟨6230468066250385432790365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8307290755000513910387153 6230468066250385432790365)
              ·
                refine ⟨2336425524843894537296387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6230468066250385432790365 2336425524843894537296387)
                ·
                  refine ⟨3504638287265841805944581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2336425524843894537296387 3504638287265841805944581)
                  ·
                    refine ⟨657119678862345338614609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3504638287265841805944581 657119678862345338614609)
                    ·
                      refine ⟨492839759146759003960957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 657119678862345338614609 492839759146759003960957)
                      ·
                        rfl

theorem cell23_959802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 3, 1, 4, 2].length) (baseStart_959802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_959802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_959802 prefixEnd_959802 := by exact prefixLift 959802
  have htrace : WordTrace (prefixWord ++ tailWord_959802) baseStart_959802 baseEnd_959802 := by
    simpa [prefixWord, tailWord_959802, baseEnd_959802] using wordTrace_append hprefix tailTrace_959802
  have hstable : (prefixWord ++ tailWord_959802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959802).length < 2 ^ (prefixWord ++ tailWord_959802).sum := by decide
  have hdescent : baseEnd_959802 < baseStart_959802 := by decide
  rcases family_descends (prefixWord ++ tailWord_959802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959808 : List Nat := [2, 1, 1, 2, 2, 1, 4, 1, 9]
def baseStart_959808 : Nat := 118140960795 + 959808 * 2 ^ 59
def prefixEnd_959808 : Nat := 4983230072969 + 3 ^ 40 * 959808 * 2
def baseEnd_959808 : Nat := 54760315558965108942881

theorem tailTrace_959808 : CollatzResearch.WordTrace tailWord_959808 prefixEnd_959808 54760315558965108942881 := by
  unfold tailWord_959808
  simp only [CollatzResearch.WordTrace]
  refine ⟨17503536853393506500500039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23338049137858008667333385 17503536853393506500500039)
  ·
    refine ⟨26255305280090259750750059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17503536853393506500500039 26255305280090259750750059)
    ·
      refine ⟨39382957920135389626125089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26255305280090259750750059 39382957920135389626125089)
      ·
        refine ⟨29537218440101542219593817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39382957920135389626125089 29537218440101542219593817)
        ·
          refine ⟨22152913830076156664695363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29537218440101542219593817 22152913830076156664695363)
          ·
            refine ⟨33229370745114234997043045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22152913830076156664695363 33229370745114234997043045)
            ·
              refine ⟨6230507014708919061945571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33229370745114234997043045 6230507014708919061945571)
              ·
                refine ⟨9345760522063378592918357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6230507014708919061945571 9345760522063378592918357)
                ·
                  refine ⟨54760315558965108942881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 9345760522063378592918357 54760315558965108942881)
                  ·
                    rfl

theorem cell23_959808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 9].length) (baseStart_959808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_959808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_959808 prefixEnd_959808 := by exact prefixLift 959808
  have htrace : WordTrace (prefixWord ++ tailWord_959808) baseStart_959808 baseEnd_959808 := by
    simpa [prefixWord, tailWord_959808, baseEnd_959808] using wordTrace_append hprefix tailTrace_959808
  have hstable : (prefixWord ++ tailWord_959808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959808).length < 2 ^ (prefixWord ++ tailWord_959808).sum := by decide
  have hdescent : baseEnd_959808 < baseStart_959808 := by decide
  rcases family_descends (prefixWord ++ tailWord_959808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959852 : List Nat := [2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 3]
def baseStart_959852 : Nat := 118140960795 + 959852 * 2 ^ 59
def prefixEnd_959852 : Nat := 4983230072969 + 3 ^ 40 * 959852 * 2
def baseEnd_959852 : Nat := 492865433179483808335727

theorem tailTrace_959852 : CollatzResearch.WordTrace tailWord_959852 prefixEnd_959852 492865433179483808335727 := by
  unfold tailWord_959852
  simp only [CollatzResearch.WordTrace]
  refine ⟨17504339259313804257800905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23339119012418405677067873 17504339259313804257800905)
  ·
    refine ⟨13128254444485353193350679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17504339259313804257800905 13128254444485353193350679)
    ·
      refine ⟨19692381666728029790026019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13128254444485353193350679 19692381666728029790026019)
      ·
        refine ⟨29538572500092044685039029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19692381666728029790026019 29538572500092044685039029)
        ·
          refine ⟨2769241171883629189222409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29538572500092044685039029 2769241171883629189222409)
          ·
            refine ⟨2076930878912721891916807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2769241171883629189222409 2076930878912721891916807)
            ·
              refine ⟨3115396318369082837875211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2076930878912721891916807 3115396318369082837875211)
              ·
                refine ⟨4673094477553624256812817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3115396318369082837875211 4673094477553624256812817)
                ·
                  refine ⟨3504820858165218192609613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4673094477553624256812817 3504820858165218192609613)
                  ·
                    refine ⟨1314307821811956822228605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3504820858165218192609613 1314307821811956822228605)
                    ·
                      refine ⟨492865433179483808335727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1314307821811956822228605 492865433179483808335727)
                      ·
                        rfl

theorem cell23_959852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 3].length) (baseStart_959852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_959852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_959852 prefixEnd_959852 := by exact prefixLift 959852
  have htrace : WordTrace (prefixWord ++ tailWord_959852) baseStart_959852 baseEnd_959852 := by
    simpa [prefixWord, tailWord_959852, baseEnd_959852] using wordTrace_append hprefix tailTrace_959852
  have hstable : (prefixWord ++ tailWord_959852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959852).length < 2 ^ (prefixWord ++ tailWord_959852).sum := by decide
  have hdescent : baseEnd_959852 < baseStart_959852 := by decide
  rcases family_descends (prefixWord ++ tailWord_959852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959945 : List Nat := [1, 2, 1, 1, 2, 1, 3, 2, 5, 5]
def baseStart_959945 : Nat := 118140960795 + 959945 * 2 ^ 59
def prefixEnd_959945 : Nat := 4983230072969 + 3 ^ 40 * 959945 * 2
def baseEnd_959945 : Nat := 164304395626783981490933

theorem tailTrace_959945 : CollatzResearch.WordTrace tailWord_959945 prefixEnd_959945 164304395626783981490933 := by
  unfold tailWord_959945
  simp only [CollatzResearch.WordTrace]
  refine ⟨35012070507290685398737289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23341380338193790265824859 35012070507290685398737289)
  ·
    refine ⟨26259052880468014049052967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35012070507290685398737289 26259052880468014049052967)
    ·
      refine ⟨39388579320702021073579451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26259052880468014049052967 39388579320702021073579451)
      ·
        refine ⟨59082868981053031610369177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39388579320702021073579451 59082868981053031610369177)
        ·
          refine ⟨44312151735789773707776883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59082868981053031610369177 44312151735789773707776883)
          ·
            refine ⟨66468227603684660561665325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44312151735789773707776883 66468227603684660561665325)
            ·
              refine ⟨24925585351381747710624497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66468227603684660561665325 24925585351381747710624497)
              ·
                refine ⟨18694189013536310782968373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24925585351381747710624497 18694189013536310782968373)
                ·
                  refine ⟨1752580220019029135903285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18694189013536310782968373 1752580220019029135903285)
                  ·
                    refine ⟨164304395626783981490933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1752580220019029135903285 164304395626783981490933)
                    ·
                      rfl

theorem cell23_959945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 5, 5].length) (baseStart_959945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_959945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_959945 prefixEnd_959945 := by exact prefixLift 959945
  have htrace : WordTrace (prefixWord ++ tailWord_959945) baseStart_959945 baseEnd_959945 := by
    simpa [prefixWord, tailWord_959945, baseEnd_959945] using wordTrace_append hprefix tailTrace_959945
  have hstable : (prefixWord ++ tailWord_959945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959945).length < 2 ^ (prefixWord ++ tailWord_959945).sum := by decide
  have hdescent : baseEnd_959945 < baseStart_959945 := by decide
  rcases family_descends (prefixWord ++ tailWord_959945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959986 : List Nat := [3, 2, 1, 4, 1, 1, 1, 3, 2, 3, 2]
def baseStart_959986 : Nat := 118140960795 + 959986 * 2 ^ 59
def prefixEnd_959986 : Nat := 4983230072969 + 3 ^ 40 * 959986 * 2
def baseEnd_959986 : Nat := 492934239587186284060111

theorem tailTrace_959986 : CollatzResearch.WordTrace tailWord_959986 prefixEnd_959986 492934239587186284060111 := by
  unfold tailWord_959986
  simp only [CollatzResearch.WordTrace]
  refine ⟨8753391475035537350244953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23342377266761432933986541 8753391475035537350244953)
  ·
    refine ⟨6565043606276653012683715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8753391475035537350244953 6565043606276653012683715)
    ·
      refine ⟨9847565409414979519025573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6565043606276653012683715 9847565409414979519025573)
      ·
        refine ⟨1846418514265308659817295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9847565409414979519025573 1846418514265308659817295)
        ·
          refine ⟨2769627771397962989725943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1846418514265308659817295 2769627771397962989725943)
          ·
            refine ⟨4154441657096944484588915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2769627771397962989725943 4154441657096944484588915)
            ·
              refine ⟨6231662485645416726883373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4154441657096944484588915 6231662485645416726883373)
              ·
                refine ⟨2336873432117031272581265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6231662485645416726883373 2336873432117031272581265)
                ·
                  refine ⟨1752655074087773454435949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2336873432117031272581265 1752655074087773454435949)
                  ·
                    refine ⟨657245652782915045413481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1752655074087773454435949 657245652782915045413481)
                    ·
                      refine ⟨492934239587186284060111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 657245652782915045413481 492934239587186284060111)
                      ·
                        rfl

theorem cell23_959986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_959986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_959986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_959986 prefixEnd_959986 := by exact prefixLift 959986
  have htrace : WordTrace (prefixWord ++ tailWord_959986) baseStart_959986 baseEnd_959986 := by
    simpa [prefixWord, tailWord_959986, baseEnd_959986] using wordTrace_append hprefix tailTrace_959986
  have hstable : (prefixWord ++ tailWord_959986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959986).length < 2 ^ (prefixWord ++ tailWord_959986).sum := by decide
  have hdescent : baseEnd_959986 < baseStart_959986 := by decide
  rcases family_descends (prefixWord ++ tailWord_959986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959992 : List Nat := [2, 1, 2, 1, 1, 6, 1, 2, 1, 6]
def baseStart_959992 : Nat := 118140960795 + 959992 * 2 ^ 59
def prefixEnd_959992 : Nat := 4983230072969 + 3 ^ 40 * 959992 * 2
def baseEnd_959992 : Nat := 164312440157037753528361

theorem tailTrace_959992 : CollatzResearch.WordTrace tailWord_959992 prefixEnd_959992 164312440157037753528361 := by
  unfold tailWord_959992
  simp only [CollatzResearch.WordTrace]
  refine ⟨17506892369060206212849115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23342523158746941617132153 17506892369060206212849115)
  ·
    refine ⟨26260338553590309319273673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17506892369060206212849115 26260338553590309319273673)
    ·
      refine ⟨19695253915192731989455255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26260338553590309319273673 19695253915192731989455255)
      ·
        refine ⟨29542880872789097984182883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19695253915192731989455255 29542880872789097984182883)
        ·
          refine ⟨44314321309183646976274325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29542880872789097984182883 44314321309183646976274325)
          ·
            refine ⟨2077233811367983452012859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 44314321309183646976274325 2077233811367983452012859)
            ·
              refine ⟨3115850717051975178019289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2077233811367983452012859 3115850717051975178019289)
              ·
                refine ⟨2336888037788981383514467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3115850717051975178019289 2336888037788981383514467)
                ·
                  refine ⟨3505332056683472075271701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2336888037788981383514467 3505332056683472075271701)
                  ·
                    refine ⟨164312440157037753528361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3505332056683472075271701 164312440157037753528361)
                    ·
                      rfl

theorem cell23_959992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 2, 1, 6].length) (baseStart_959992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_959992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_959992 prefixEnd_959992 := by exact prefixLift 959992
  have htrace : WordTrace (prefixWord ++ tailWord_959992) baseStart_959992 baseEnd_959992 := by
    simpa [prefixWord, tailWord_959992, baseEnd_959992] using wordTrace_append hprefix tailTrace_959992
  have hstable : (prefixWord ++ tailWord_959992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959992).length < 2 ^ (prefixWord ++ tailWord_959992).sum := by decide
  have hdescent : baseEnd_959992 < baseStart_959992 := by decide
  rcases family_descends (prefixWord ++ tailWord_959992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959999 : List Nat := [1, 1, 2, 2, 1, 2, 2, 1, 7, 2, 2]
def baseStart_959999 : Nat := 118140960795 + 959999 * 2 ^ 59
def prefixEnd_959999 : Nat := 4983230072969 + 3 ^ 40 * 959999 * 2
def baseEnd_959999 : Nat := 492940914835694733197551

theorem tailTrace_959999 : CollatzResearch.WordTrace tailWord_959999 prefixEnd_959999 492940914835694733197551 := by
  unfold tailWord_959999
  simp only [CollatzResearch.WordTrace]
  refine ⟨35014040049095052621203051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23342693366063368414135367 35014040049095052621203051)
  ·
    refine ⟨52521060073642578931804577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35014040049095052621203051 52521060073642578931804577)
    ·
      refine ⟨39390795055231934198853433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52521060073642578931804577 39390795055231934198853433)
      ·
        refine ⟨29543096291423950649140075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39390795055231934198853433 29543096291423950649140075)
        ·
          refine ⟨44314644437135925973710113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29543096291423950649140075 44314644437135925973710113)
          ·
            refine ⟨33235983327851944480282585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44314644437135925973710113 33235983327851944480282585)
            ·
              refine ⟨24926987495888958360211939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33235983327851944480282585 24926987495888958360211939)
              ·
                refine ⟨37390481243833437540317909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24926987495888958360211939 37390481243833437540317909)
                ·
                  refine ⟨876339404152346192351201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 37390481243833437540317909 876339404152346192351201)
                  ·
                    refine ⟨657254553114259644263401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 876339404152346192351201 657254553114259644263401)
                    ·
                      refine ⟨492940914835694733197551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 657254553114259644263401 492940914835694733197551)
                      ·
                        rfl

theorem cell23_959999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 7, 2, 2].length) (baseStart_959999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_959999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_959999 prefixEnd_959999 := by exact prefixLift 959999
  have htrace : WordTrace (prefixWord ++ tailWord_959999) baseStart_959999 baseEnd_959999 := by
    simpa [prefixWord, tailWord_959999, baseEnd_959999] using wordTrace_append hprefix tailTrace_959999
  have hstable : (prefixWord ++ tailWord_959999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959999).length < 2 ^ (prefixWord ++ tailWord_959999).sum := by decide
  have hdescent : baseEnd_959999 < baseStart_959999 := by decide
  rcases family_descends (prefixWord ++ tailWord_959999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960009 : List Nat := [1, 2, 1, 1, 3, 1, 6, 2, 2, 4]
def baseStart_960009 : Nat := 118140960795 + 960009 * 2 ^ 59
def prefixEnd_960009 : Nat := 4983230072969 + 3 ^ 40 * 960009 * 2
def baseEnd_960009 : Nat := 164315349880746564690835

theorem tailTrace_960009 : CollatzResearch.WordTrace tailWord_960009 prefixEnd_960009 164315349880746564690835 := by
  unfold tailWord_960009
  simp only [CollatzResearch.WordTrace]
  refine ⟨35014404779058824329067081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23342936519372549552711387 35014404779058824329067081)
  ·
    refine ⟨26260803584294118246800311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35014404779058824329067081 26260803584294118246800311)
    ·
      refine ⟨39391205376441177370200467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26260803584294118246800311 39391205376441177370200467)
      ·
        refine ⟨59086808064661766055300701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39391205376441177370200467 59086808064661766055300701)
        ·
          refine ⟨22157553024248162270737763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59086808064661766055300701 22157553024248162270737763)
          ·
            refine ⟨33236329536372243406106645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22157553024248162270737763 33236329536372243406106645)
            ·
              refine ⟨1557952947017448909661249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 33236329536372243406106645 1557952947017448909661249)
              ·
                refine ⟨1168464710263086682245937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1557952947017448909661249 1168464710263086682245937)
                ·
                  refine ⟨876348532697315011684453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1168464710263086682245937 876348532697315011684453)
                  ·
                    refine ⟨164315349880746564690835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 876348532697315011684453 164315349880746564690835)
                    ·
                      rfl

theorem cell23_960009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 2, 2, 4].length) (baseStart_960009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_960009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_960009 prefixEnd_960009 := by exact prefixLift 960009
  have htrace : WordTrace (prefixWord ++ tailWord_960009) baseStart_960009 baseEnd_960009 := by
    simpa [prefixWord, tailWord_960009, baseEnd_960009] using wordTrace_append hprefix tailTrace_960009
  have hstable : (prefixWord ++ tailWord_960009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960009).length < 2 ^ (prefixWord ++ tailWord_960009).sum := by decide
  have hdescent : baseEnd_960009 < baseStart_960009 := by decide
  rcases family_descends (prefixWord ++ tailWord_960009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960010 : List Nat := [3, 1, 2, 2, 2, 4, 2, 2, 1, 1, 3]
def baseStart_960010 : Nat := 118140960795 + 960010 * 2 ^ 59
def prefixEnd_960010 : Nat := 4983230072969 + 3 ^ 40 * 960010 * 2
def baseEnd_960010 : Nat := 492946563122894190160001

theorem tailTrace_960010 : CollatzResearch.WordTrace tailWord_960010 prefixEnd_960010 492946563122894190160001 := by
  unfold tailWord_960010
  simp only [CollatzResearch.WordTrace]
  refine ⟨8753610313013800374963371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23342960834703467666568989 8753610313013800374963371)
  ·
    refine ⟨13130415469520700562445057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8753610313013800374963371 13130415469520700562445057)
    ·
      refine ⟨9847811602140525421833793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13130415469520700562445057 9847811602140525421833793)
      ·
        refine ⟨7385858701605394066375345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9847811602140525421833793 7385858701605394066375345)
        ·
          refine ⟨5539394026204045549781509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7385858701605394066375345 5539394026204045549781509)
          ·
            refine ⟨1038636379913258540584033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5539394026204045549781509 1038636379913258540584033)
            ·
              refine ⟨778977284934943905438025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1038636379913258540584033 778977284934943905438025)
              ·
                refine ⟨584232963701207929078519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 778977284934943905438025 584232963701207929078519)
                ·
                  refine ⟨876349445551811893617779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 584232963701207929078519 876349445551811893617779)
                  ·
                    refine ⟨1314524168327717840426669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 876349445551811893617779 1314524168327717840426669)
                    ·
                      refine ⟨492946563122894190160001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1314524168327717840426669 492946563122894190160001)
                      ·
                        rfl

theorem cell23_960010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 2, 2, 1, 1, 3].length) (baseStart_960010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_960010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_960010 prefixEnd_960010 := by exact prefixLift 960010
  have htrace : WordTrace (prefixWord ++ tailWord_960010) baseStart_960010 baseEnd_960010 := by
    simpa [prefixWord, tailWord_960010, baseEnd_960010] using wordTrace_append hprefix tailTrace_960010
  have hstable : (prefixWord ++ tailWord_960010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960010).length < 2 ^ (prefixWord ++ tailWord_960010).sum := by decide
  have hdescent : baseEnd_960010 < baseStart_960010 := by decide
  rcases family_descends (prefixWord ++ tailWord_960010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960029 : List Nat := [1, 4, 2, 2, 1, 1, 4, 1, 1, 2, 4]
def baseStart_960029 : Nat := 118140960795 + 960029 * 2 ^ 59
def prefixEnd_960029 : Nat := 4983230072969 + 3 ^ 40 * 960029 * 2
def baseEnd_960029 : Nat := 492956319255329615822413

theorem tailTrace_960029 : CollatzResearch.WordTrace tailWord_960029 prefixEnd_960029 492956319255329615822413 := by
  unfold tailWord_960029
  simp only [CollatzResearch.WordTrace]
  refine ⟨35015134238986367744795141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23343422825990911829863427 35015134238986367744795141)
  ·
    refine ⟨6565337669809943952149089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35015134238986367744795141 6565337669809943952149089)
    ·
      refine ⟨4924003252357457964111817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6565337669809943952149089 4924003252357457964111817)
      ·
        refine ⟨3693002439268093473083863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4924003252357457964111817 3693002439268093473083863)
        ·
          refine ⟨5539503658902140209625795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3693002439268093473083863 5539503658902140209625795)
          ·
            refine ⟨8309255488353210314438693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5539503658902140209625795 8309255488353210314438693)
            ·
              refine ⟨1557985404066226933957255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8309255488353210314438693 1557985404066226933957255)
              ·
                refine ⟨2336978106099340400935883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1557985404066226933957255 2336978106099340400935883)
                ·
                  refine ⟨3505467159149010601403825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2336978106099340400935883 3505467159149010601403825)
                  ·
                    refine ⟨2629100369361757951052869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3505467159149010601403825 2629100369361757951052869)
                    ·
                      refine ⟨492956319255329615822413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2629100369361757951052869 492956319255329615822413)
                      ·
                        rfl

theorem cell23_960029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_960029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_960029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_960029 prefixEnd_960029 := by exact prefixLift 960029
  have htrace : WordTrace (prefixWord ++ tailWord_960029) baseStart_960029 baseEnd_960029 := by
    simpa [prefixWord, tailWord_960029, baseEnd_960029] using wordTrace_append hprefix tailTrace_960029
  have hstable : (prefixWord ++ tailWord_960029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960029).length < 2 ^ (prefixWord ++ tailWord_960029).sum := by decide
  have hdescent : baseEnd_960029 < baseStart_960029 := by decide
  rcases family_descends (prefixWord ++ tailWord_960029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960049 : List Nat := [1, 2, 2, 3, 1, 1, 1, 4, 4, 1, 3]
def baseStart_960049 : Nat := 118140960795 + 960049 * 2 ^ 59
def prefixEnd_960049 : Nat := 4983230072969 + 3 ^ 40 * 960049 * 2
def baseEnd_960049 : Nat := 492966588868419537572321

theorem tailTrace_960049 : CollatzResearch.WordTrace tailWord_960049 prefixEnd_960049 492966588868419537572321 := by
  unfold tailWord_960049
  simp only [CollatzResearch.WordTrace]
  refine ⟨35015863698913911160523201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23343909132609274107015467 35015863698913911160523201)
  ·
    refine ⟨26261897774185433370392401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35015863698913911160523201 26261897774185433370392401)
    ·
      refine ⟨19696423330639075027794301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26261897774185433370392401 19696423330639075027794301)
      ·
        refine ⟨7386158748989653135422863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19696423330639075027794301 7386158748989653135422863)
        ·
          refine ⟨11079238123484479703134295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7386158748989653135422863 11079238123484479703134295)
          ·
            refine ⟨16618857185226719554701443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11079238123484479703134295 16618857185226719554701443)
            ·
              refine ⟨24928285777840079332052165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16618857185226719554701443 24928285777840079332052165)
              ·
                refine ⟨4674053583345014874759781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24928285777840079332052165 4674053583345014874759781)
                ·
                  refine ⟨876385046877190289017459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4674053583345014874759781 876385046877190289017459)
                  ·
                    refine ⟨1314577570315785433526189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 876385046877190289017459 1314577570315785433526189)
                    ·
                      refine ⟨492966588868419537572321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1314577570315785433526189 492966588868419537572321)
                      ·
                        rfl

theorem cell23_960049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 4, 1, 3].length) (baseStart_960049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_960049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_960049 prefixEnd_960049 := by exact prefixLift 960049
  have htrace : WordTrace (prefixWord ++ tailWord_960049) baseStart_960049 baseEnd_960049 := by
    simpa [prefixWord, tailWord_960049, baseEnd_960049] using wordTrace_append hprefix tailTrace_960049
  have hstable : (prefixWord ++ tailWord_960049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960049).length < 2 ^ (prefixWord ++ tailWord_960049).sum := by decide
  have hdescent : baseEnd_960049 < baseStart_960049 := by decide
  rcases family_descends (prefixWord ++ tailWord_960049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960053 : List Nat := [1, 3, 3, 1, 1, 5, 2, 1, 1, 2, 3]
def baseStart_960053 : Nat := 118140960795 + 960053 * 2 ^ 59
def prefixEnd_960053 : Nat := 4983230072969 + 3 ^ 40 * 960053 * 2
def baseEnd_960053 : Nat := 492968642791037521922303

theorem tailTrace_960053 : CollatzResearch.WordTrace tailWord_960053 prefixEnd_960053 492968642791037521922303 := by
  unfold tailWord_960053
  simp only [CollatzResearch.WordTrace]
  refine ⟨35016009590899419843668813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23344006393932946562445875 35016009590899419843668813)
  ·
    refine ⟨13131003596587282441375805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35016009590899419843668813 13131003596587282441375805)
    ·
      refine ⟨4924126348720230915515927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13131003596587282441375805 4924126348720230915515927)
      ·
        refine ⟨7386189523080346373273891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4924126348720230915515927 7386189523080346373273891)
        ·
          refine ⟨11079284284620519559910837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7386189523080346373273891 11079284284620519559910837)
          ·
            refine ⟨1038682901683173708741641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11079284284620519559910837 1038682901683173708741641)
            ·
              refine ⟨779012176262380281556231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1038682901683173708741641 779012176262380281556231)
              ·
                refine ⟨1168518264393570422334347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 779012176262380281556231 1168518264393570422334347)
                ·
                  refine ⟨1752777396590355633501521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1168518264393570422334347 1752777396590355633501521)
                  ·
                    refine ⟨1314583047442766725126141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1752777396590355633501521 1314583047442766725126141)
                    ·
                      refine ⟨492968642791037521922303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1314583047442766725126141 492968642791037521922303)
                      ·
                        rfl

theorem cell23_960053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 2, 1, 1, 2, 3].length) (baseStart_960053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_960053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_960053 prefixEnd_960053 := by exact prefixLift 960053
  have htrace : WordTrace (prefixWord ++ tailWord_960053) baseStart_960053 baseEnd_960053 := by
    simpa [prefixWord, tailWord_960053, baseEnd_960053] using wordTrace_append hprefix tailTrace_960053
  have hstable : (prefixWord ++ tailWord_960053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960053).length < 2 ^ (prefixWord ++ tailWord_960053).sum := by decide
  have hdescent : baseEnd_960053 < baseStart_960053 := by decide
  rcases family_descends (prefixWord ++ tailWord_960053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960129 : List Nat := [1, 2, 4, 2, 1, 2, 3, 1, 7]
def baseStart_960129 : Nat := 118140960795 + 960129 * 2 ^ 59
def prefixEnd_960129 : Nat := 4983230072969 + 3 ^ 40 * 960129 * 2
def baseEnd_960129 : Nat := 54778629702308802730217

theorem tailTrace_960129 : CollatzResearch.WordTrace tailWord_960129 prefixEnd_960129 54778629702308802730217 := by
  unfold tailWord_960129
  simp only [CollatzResearch.WordTrace]
  refine ⟨35018781538624084823435441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23345854359082723215623627 35018781538624084823435441)
  ·
    refine ⟨26264086153968063617576581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35018781538624084823435441 26264086153968063617576581)
    ·
      refine ⟨4924516153869011928295609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26264086153968063617576581 4924516153869011928295609)
      ·
        refine ⟨3693387115401758946221707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4924516153869011928295609 3693387115401758946221707)
        ·
          refine ⟨5540080673102638419332561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3693387115401758946221707 5540080673102638419332561)
          ·
            refine ⟨4155060504826978814499421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5540080673102638419332561 4155060504826978814499421)
            ·
              refine ⟨1558147689310117055437283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4155060504826978814499421 1558147689310117055437283)
              ·
                refine ⟨2337221533965175583155925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1558147689310117055437283 2337221533965175583155925)
                ·
                  refine ⟨54778629702308802730217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2337221533965175583155925 54778629702308802730217)
                  ·
                    rfl

theorem cell23_960129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 1, 7].length) (baseStart_960129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_960129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_960129 prefixEnd_960129 := by exact prefixLift 960129
  have htrace : WordTrace (prefixWord ++ tailWord_960129) baseStart_960129 baseEnd_960129 := by
    simpa [prefixWord, tailWord_960129, baseEnd_960129] using wordTrace_append hprefix tailTrace_960129
  have hstable : (prefixWord ++ tailWord_960129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960129).length < 2 ^ (prefixWord ++ tailWord_960129).sum := by decide
  have hdescent : baseEnd_960129 < baseStart_960129 := by decide
  rcases family_descends (prefixWord ++ tailWord_960129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960179 : List Nat := [1, 1, 1, 2, 3, 3, 1, 4, 2, 1, 4]
def baseStart_960179 : Nat := 118140960795 + 960179 * 2 ^ 59
def prefixEnd_960179 : Nat := 4983230072969 + 3 ^ 40 * 960179 * 2
def baseEnd_960179 : Nat := 493033341353504028946723

theorem tailTrace_960179 : CollatzResearch.WordTrace tailWord_960179 prefixEnd_960179 493033341353504028946723 := by
  unfold tailWord_960179
  simp only [CollatzResearch.WordTrace]
  refine ⟨35020605188442943362755591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23347070125628628908503727 35020605188442943362755591)
  ·
    refine ⟨52530907782664415044133387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35020605188442943362755591 52530907782664415044133387)
    ·
      refine ⟨78796361673996622566200081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52530907782664415044133387 78796361673996622566200081)
      ·
        refine ⟨59097271255497466924650061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78796361673996622566200081 59097271255497466924650061)
        ·
          refine ⟨22161476720811550096743773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59097271255497466924650061 22161476720811550096743773)
          ·
            refine ⟨8310553770304331286278915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22161476720811550096743773 8310553770304331286278915)
            ·
              refine ⟨12465830655456496929418373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8310553770304331286278915 12465830655456496929418373)
              ·
                refine ⟨2337343247898093174265945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12465830655456496929418373 2337343247898093174265945)
                ·
                  refine ⟨1753007435923569880699459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2337343247898093174265945 1753007435923569880699459)
                  ·
                    refine ⟨2629511153885354821049189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1753007435923569880699459 2629511153885354821049189)
                    ·
                      refine ⟨493033341353504028946723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2629511153885354821049189 493033341353504028946723)
                      ·
                        rfl

theorem cell23_960179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 4, 2, 1, 4].length) (baseStart_960179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_960179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_960179 prefixEnd_960179 := by exact prefixLift 960179
  have htrace : WordTrace (prefixWord ++ tailWord_960179) baseStart_960179 baseEnd_960179 := by
    simpa [prefixWord, tailWord_960179, baseEnd_960179] using wordTrace_append hprefix tailTrace_960179
  have hstable : (prefixWord ++ tailWord_960179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960179).length < 2 ^ (prefixWord ++ tailWord_960179).sum := by decide
  have hdescent : baseEnd_960179 < baseStart_960179 := by decide
  rcases family_descends (prefixWord ++ tailWord_960179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960199 : List Nat := [1, 1, 4, 1, 1, 1, 4, 2, 1, 4, 3]
def baseStart_960199 : Nat := 118140960795 + 960199 * 2 ^ 59
def prefixEnd_960199 : Nat := 4983230072969 + 3 ^ 40 * 960199 * 2
def baseEnd_960199 : Nat := 493043610966593950696631

theorem tailTrace_960199 : CollatzResearch.WordTrace tailWord_960199 prefixEnd_960199 493043610966593950696631 := by
  unfold tailWord_960199
  simp only [CollatzResearch.WordTrace]
  refine ⟨35021334648370486778483651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23347556432246991185655767 35021334648370486778483651)
  ·
    refine ⟨52532001972555730167725477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35021334648370486778483651 52532001972555730167725477)
    ·
      refine ⟨9849750369854199406448527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52532001972555730167725477 9849750369854199406448527)
      ·
        refine ⟨14774625554781299109672791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9849750369854199406448527 14774625554781299109672791)
        ·
          refine ⟨22161938332171948664509187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14774625554781299109672791 22161938332171948664509187)
          ·
            refine ⟨33242907498257922996763781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22161938332171948664509187 33242907498257922996763781)
            ·
              refine ⟨6233045155923360561893209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33242907498257922996763781 6233045155923360561893209)
              ·
                refine ⟨4674783866942520421419907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6233045155923360561893209 4674783866942520421419907)
                ·
                  refine ⟨7012175800413780632129861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4674783866942520421419907 7012175800413780632129861)
                  ·
                    refine ⟨1314782962577583868524349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7012175800413780632129861 1314782962577583868524349)
                    ·
                      refine ⟨493043610966593950696631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1314782962577583868524349 493043610966593950696631)
                      ·
                        rfl

theorem cell23_960199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 4, 3].length) (baseStart_960199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_960199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_960199 prefixEnd_960199 := by exact prefixLift 960199
  have htrace : WordTrace (prefixWord ++ tailWord_960199) baseStart_960199 baseEnd_960199 := by
    simpa [prefixWord, tailWord_960199, baseEnd_960199] using wordTrace_append hprefix tailTrace_960199
  have hstable : (prefixWord ++ tailWord_960199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960199).length < 2 ^ (prefixWord ++ tailWord_960199).sum := by decide
  have hdescent : baseEnd_960199 < baseStart_960199 := by decide
  rcases family_descends (prefixWord ++ tailWord_960199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960206 : List Nat := [4, 1, 1, 1, 3, 1, 3, 2, 3, 4]
def baseStart_960206 : Nat := 118140960795 + 960206 * 2 ^ 59
def prefixEnd_960206 : Nat := 4983230072969 + 3 ^ 40 * 960206 * 2
def baseEnd_960206 : Nat := 164349068443725141103033

theorem tailTrace_960206 : CollatzResearch.WordTrace tailWord_960206 prefixEnd_960206 164349068443725141103033 := by
  unfold tailWord_960206
  simp only [CollatzResearch.WordTrace]
  refine ⟨4377698744918140871748559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23347726639563417982658981 4377698744918140871748559)
  ·
    refine ⟨6566548117377211307622839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4377698744918140871748559 6566548117377211307622839)
    ·
      refine ⟨9849822176065816961434259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6566548117377211307622839 9849822176065816961434259)
      ·
        refine ⟨14774733264098725442151389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9849822176065816961434259 14774733264098725442151389)
        ·
          refine ⟨5540524974037022040806771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14774733264098725442151389 5540524974037022040806771)
          ·
            refine ⟨8310787461055533061210157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5540524974037022040806771 8310787461055533061210157)
            ·
              refine ⟨3116545297895824897953809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8310787461055533061210157 3116545297895824897953809)
              ·
                refine ⟨2337408973421868673465357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3116545297895824897953809 2337408973421868673465357)
                ·
                  refine ⟨876528365033200752549509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2337408973421868673465357 876528365033200752549509)
                  ·
                    refine ⟨164349068443725141103033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 876528365033200752549509 164349068443725141103033)
                    ·
                      rfl

theorem cell23_960206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 2, 3, 4].length) (baseStart_960206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_960206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_960206 prefixEnd_960206 := by exact prefixLift 960206
  have htrace : WordTrace (prefixWord ++ tailWord_960206) baseStart_960206 baseEnd_960206 := by
    simpa [prefixWord, tailWord_960206, baseEnd_960206] using wordTrace_append hprefix tailTrace_960206
  have hstable : (prefixWord ++ tailWord_960206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960206).length < 2 ^ (prefixWord ++ tailWord_960206).sum := by decide
  have hdescent : baseEnd_960206 < baseStart_960206 := by decide
  rcases family_descends (prefixWord ++ tailWord_960206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960223 : List Nat := [1, 1, 2, 3, 2, 2, 4, 3, 1, 4]
def baseStart_960223 : Nat := 118140960795 + 960223 * 2 ^ 59
def prefixEnd_960223 : Nat := 4983230072969 + 3 ^ 40 * 960223 * 2
def baseEnd_960223 : Nat := 164351978167433952265507

theorem tailTrace_960223 : CollatzResearch.WordTrace tailWord_960223 prefixEnd_960223 164351978167433952265507 := by
  unfold tailWord_960223
  simp only [CollatzResearch.WordTrace]
  refine ⟨35022210000283538877357323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23348140000189025918238215 35022210000283538877357323)
  ·
    refine ⟨52533315000425308316035985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35022210000283538877357323 52533315000425308316035985)
    ·
      refine ⟨39399986250318981237026989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52533315000425308316035985 39399986250318981237026989)
      ·
        refine ⟨14774994843869617963885121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39399986250318981237026989 14774994843869617963885121)
        ·
          refine ⟨11081246132902213472913841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14774994843869617963885121 11081246132902213472913841)
          ·
            refine ⟨8310934599676660104685381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11081246132902213472913841 8310934599676660104685381)
            ·
              refine ⟨1558300237439373769628509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8310934599676660104685381 1558300237439373769628509)
              ·
                refine ⟨584362589039765163610691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1558300237439373769628509 584362589039765163610691)
                ·
                  refine ⟨876543883559647745416037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 584362589039765163610691 876543883559647745416037)
                  ·
                    refine ⟨164351978167433952265507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 876543883559647745416037 164351978167433952265507)
                    ·
                      rfl

theorem cell23_960223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 3, 1, 4].length) (baseStart_960223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_960223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_960223 prefixEnd_960223 := by exact prefixLift 960223
  have htrace : WordTrace (prefixWord ++ tailWord_960223) baseStart_960223 baseEnd_960223 := by
    simpa [prefixWord, tailWord_960223, baseEnd_960223] using wordTrace_append hprefix tailTrace_960223
  have hstable : (prefixWord ++ tailWord_960223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960223).length < 2 ^ (prefixWord ++ tailWord_960223).sum := by decide
  have hdescent : baseEnd_960223 < baseStart_960223 := by decide
  rcases family_descends (prefixWord ++ tailWord_960223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960256 : List Nat := [2, 1, 1, 2, 1, 1, 2, 4, 4, 3, 2]
def baseStart_960256 : Nat := 118140960795 + 960256 * 2 ^ 59
def prefixEnd_960256 : Nat := 4983230072969 + 3 ^ 40 * 960256 * 2
def baseEnd_960256 : Nat := 493072879363900227683869

theorem tailTrace_960256 : CollatzResearch.WordTrace tailWord_960256 prefixEnd_960256 493072879363900227683869 := by
  unfold tailWord_960256
  simp only [CollatzResearch.WordTrace]
  refine ⟨17511706804581992756654311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23348942406109323675539081 17511706804581992756654311)
  ·
    refine ⟨26267560206872989134981467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17511706804581992756654311 26267560206872989134981467)
    ·
      refine ⟨39401340310309483702472201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26267560206872989134981467 39401340310309483702472201)
      ·
        refine ⟨29551005232732112776854151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39401340310309483702472201 29551005232732112776854151)
        ·
          refine ⟨44326507849098169165281227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29551005232732112776854151 44326507849098169165281227)
          ·
            refine ⟨66489761773647253747921841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44326507849098169165281227 66489761773647253747921841)
            ·
              refine ⟨49867321330235440310941381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66489761773647253747921841 49867321330235440310941381)
              ·
                refine ⟨9350122749419145058301509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49867321330235440310941381 9350122749419145058301509)
                ·
                  refine ⟨1753148015516089698431533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9350122749419145058301509 1753148015516089698431533)
                  ·
                    refine ⟨657430505818533636911825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1753148015516089698431533 657430505818533636911825)
                    ·
                      refine ⟨493072879363900227683869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 657430505818533636911825 493072879363900227683869)
                      ·
                        rfl

theorem cell23_960256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 4, 3, 2].length) (baseStart_960256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_960256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_960256 prefixEnd_960256 := by exact prefixLift 960256
  have htrace : WordTrace (prefixWord ++ tailWord_960256) baseStart_960256 baseEnd_960256 := by
    simpa [prefixWord, tailWord_960256, baseEnd_960256] using wordTrace_append hprefix tailTrace_960256
  have hstable : (prefixWord ++ tailWord_960256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960256).length < 2 ^ (prefixWord ++ tailWord_960256).sum := by decide
  have hdescent : baseEnd_960256 < baseStart_960256 := by decide
  rcases family_descends (prefixWord ++ tailWord_960256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960266 : List Nat := [3, 1, 2, 2, 1, 3, 1, 4, 1, 5]
def baseStart_960266 : Nat := 118140960795 + 960266 * 2 ^ 59
def prefixEnd_960266 : Nat := 4983230072969 + 3 ^ 40 * 960266 * 2
def baseEnd_960266 : Nat := 164359338056815062852941

theorem tailTrace_960266 : CollatzResearch.WordTrace tailWord_960266 prefixEnd_960266 164359338056815062852941 := by
  unfold tailWord_960266
  simp only [CollatzResearch.WordTrace]
  refine ⟨8755944584781939305293163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23349185559418504814115101 8755944584781939305293163)
  ·
    refine ⟨13133916877172908957939745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8755944584781939305293163 13133916877172908957939745)
    ·
      refine ⟨9850437657879681718454809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13133916877172908957939745 9850437657879681718454809)
      ·
        refine ⟨7387828243409761288841107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9850437657879681718454809 7387828243409761288841107)
        ·
          refine ⟨11081742365114641933261661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7387828243409761288841107 11081742365114641933261661)
          ·
            refine ⟨4155653386917990724973123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11081742365114641933261661 4155653386917990724973123)
            ·
              refine ⟨6233480080376986087459685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4155653386917990724973123 6233480080376986087459685)
              ·
                refine ⟨1168777515070684891398691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6233480080376986087459685 1168777515070684891398691)
                ·
                  refine ⟨1753166272606027337098037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1168777515070684891398691 1753166272606027337098037)
                  ·
                    refine ⟨164359338056815062852941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1753166272606027337098037 164359338056815062852941)
                    ·
                      rfl

theorem cell23_960266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 4, 1, 5].length) (baseStart_960266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_960266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_960266 prefixEnd_960266 := by exact prefixLift 960266
  have htrace : WordTrace (prefixWord ++ tailWord_960266) baseStart_960266 baseEnd_960266 := by
    simpa [prefixWord, tailWord_960266, baseEnd_960266] using wordTrace_append hprefix tailTrace_960266
  have hstable : (prefixWord ++ tailWord_960266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960266).length < 2 ^ (prefixWord ++ tailWord_960266).sum := by decide
  have hdescent : baseEnd_960266 < baseStart_960266 := by decide
  rcases family_descends (prefixWord ++ tailWord_960266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960280 : List Nat := [2, 1, 2, 3, 1, 1, 5, 3, 1, 1, 3]
def baseStart_960280 : Nat := 118140960795 + 960280 * 2 ^ 59
def prefixEnd_960280 : Nat := 4983230072969 + 3 ^ 40 * 960280 * 2
def baseEnd_960280 : Nat := 493085202899608133783759

theorem tailTrace_960280 : CollatzResearch.WordTrace tailWord_960280 prefixEnd_960280 493085202899608133783759 := by
  unfold tailWord_960280
  simp only [CollatzResearch.WordTrace]
  refine ⟨17512144480538518806091147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23349525974051358408121529 17512144480538518806091147)
  ·
    refine ⟨26268216720807778209136721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17512144480538518806091147 26268216720807778209136721)
    ·
      refine ⟨19701162540605833656852541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26268216720807778209136721 19701162540605833656852541)
      ·
        refine ⟨7387935952727187621319703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19701162540605833656852541 7387935952727187621319703)
        ·
          refine ⟨11081903929090781431979555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7387935952727187621319703 11081903929090781431979555)
          ·
            refine ⟨16622855893636172147969333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11081903929090781431979555 16622855893636172147969333)
            ·
              refine ⟨1558392740028391138872125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16622855893636172147969333 1558392740028391138872125)
              ·
                refine ⟨584397277510646677077047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1558392740028391138872125 584397277510646677077047)
                ·
                  refine ⟨876595916265970015615571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 584397277510646677077047 876595916265970015615571)
                  ·
                    refine ⟨1314893874398955023423357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 876595916265970015615571 1314893874398955023423357)
                    ·
                      refine ⟨493085202899608133783759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1314893874398955023423357 493085202899608133783759)
                      ·
                        rfl

theorem cell23_960280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 3, 1, 1, 3].length) (baseStart_960280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_960280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_960280 prefixEnd_960280 := by exact prefixLift 960280
  have htrace : WordTrace (prefixWord ++ tailWord_960280) baseStart_960280 baseEnd_960280 := by
    simpa [prefixWord, tailWord_960280, baseEnd_960280] using wordTrace_append hprefix tailTrace_960280
  have hstable : (prefixWord ++ tailWord_960280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960280).length < 2 ^ (prefixWord ++ tailWord_960280).sum := by decide
  have hdescent : baseEnd_960280 < baseStart_960280 := by decide
  rcases family_descends (prefixWord ++ tailWord_960280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960306 : List Nat := [3, 2, 1, 1, 3, 2, 2, 2, 1, 1, 5]
def baseStart_960306 : Nat := 118140960795 + 960306 * 2 ^ 59
def prefixEnd_960306 : Nat := 4983230072969 + 3 ^ 40 * 960306 * 2
def baseEnd_960306 : Nat := 493098553396625032058639

theorem tailTrace_960306 : CollatzResearch.WordTrace tailWord_960306 prefixEnd_960306 493098553396625032058639 := by
  unfold tailWord_960306
  simp only [CollatzResearch.WordTrace]
  refine ⟨8756309314745711013157193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23350158172655229368419181 8756309314745711013157193)
  ·
    refine ⟨6567231986059283259867895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8756309314745711013157193 6567231986059283259867895)
    ·
      refine ⟨9850847979088924889801843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6567231986059283259867895 9850847979088924889801843)
      ·
        refine ⟨14776271968633387334702765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9850847979088924889801843 14776271968633387334702765)
        ·
          refine ⟨5541101988237520250513537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14776271968633387334702765 5541101988237520250513537)
          ·
            refine ⟨4155826491178140187885153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5541101988237520250513537 4155826491178140187885153)
            ·
              refine ⟨3116869868383605140913865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4155826491178140187885153 3116869868383605140913865)
              ·
                refine ⟨2337652401287703855685399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3116869868383605140913865 2337652401287703855685399)
                ·
                  refine ⟨3506478601931555783528099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2337652401287703855685399 3506478601931555783528099)
                  ·
                    refine ⟨5259717902897333675292149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3506478601931555783528099 5259717902897333675292149)
                    ·
                      refine ⟨493098553396625032058639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5259717902897333675292149 493098553396625032058639)
                      ·
                        rfl

theorem cell23_960306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 2, 1, 1, 5].length) (baseStart_960306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_960306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_960306 prefixEnd_960306 := by exact prefixLift 960306
  have htrace : WordTrace (prefixWord ++ tailWord_960306) baseStart_960306 baseEnd_960306 := by
    simpa [prefixWord, tailWord_960306, baseEnd_960306] using wordTrace_append hprefix tailTrace_960306
  have hstable : (prefixWord ++ tailWord_960306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960306).length < 2 ^ (prefixWord ++ tailWord_960306).sum := by decide
  have hdescent : baseEnd_960306 < baseStart_960306 := by decide
  rcases family_descends (prefixWord ++ tailWord_960306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960323 : List Nat := [1, 1, 1, 3, 1, 5, 3, 2, 1, 2, 3]
def baseStart_960323 : Nat := 118140960795 + 960323 * 2 ^ 59
def prefixEnd_960323 : Nat := 4983230072969 + 3 ^ 40 * 960323 * 2
def baseEnd_960323 : Nat := 493107282567751465546061

theorem tailTrace_960323 : CollatzResearch.WordTrace tailWord_960323 prefixEnd_960323 493107282567751465546061 := by
  unfold tailWord_960323
  simp only [CollatzResearch.WordTrace]
  refine ⟨35025857299921255955997623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23350571533280837303998415 35025857299921255955997623)
  ·
    refine ⟨52538785949881883933996435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35025857299921255955997623 52538785949881883933996435)
    ·
      refine ⟨78808178924822825900994653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52538785949881883933996435 78808178924822825900994653)
      ·
        refine ⟨29553067096808559712872995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78808178924822825900994653 29553067096808559712872995)
        ·
          refine ⟨44329600645212839569309493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29553067096808559712872995 44329600645212839569309493)
          ·
            refine ⟨4155900060488703709622765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44329600645212839569309493 4155900060488703709622765)
            ·
              refine ⟨1558462522683263891108537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4155900060488703709622765 1558462522683263891108537)
              ·
                refine ⟨1168846892012447918331403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1558462522683263891108537 1168846892012447918331403)
                ·
                  refine ⟨1753270338018671877497105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1168846892012447918331403 1753270338018671877497105)
                  ·
                    refine ⟨1314952753514003908122829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1753270338018671877497105 1314952753514003908122829)
                    ·
                      refine ⟨493107282567751465546061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1314952753514003908122829 493107282567751465546061)
                      ·
                        rfl

theorem cell23_960323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 2, 1, 2, 3].length) (baseStart_960323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_960323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_960323 prefixEnd_960323 := by exact prefixLift 960323
  have htrace : WordTrace (prefixWord ++ tailWord_960323) baseStart_960323 baseEnd_960323 := by
    simpa [prefixWord, tailWord_960323, baseEnd_960323] using wordTrace_append hprefix tailTrace_960323
  have hstable : (prefixWord ++ tailWord_960323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960323).length < 2 ^ (prefixWord ++ tailWord_960323).sum := by decide
  have hdescent : baseEnd_960323 < baseStart_960323 := by decide
  rcases family_descends (prefixWord ++ tailWord_960323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960333 : List Nat := [1, 6, 1, 2, 1, 1, 1, 1, 3, 2, 4]
def baseStart_960333 : Nat := 118140960795 + 960333 * 2 ^ 59
def prefixEnd_960333 : Nat := 4983230072969 + 3 ^ 40 * 960333 * 2
def baseEnd_960333 : Nat := 493112417374296426421015

theorem tailTrace_960333 : CollatzResearch.WordTrace tailWord_960333 prefixEnd_960333 493112417374296426421015 := by
  unfold tailWord_960333
  simp only [CollatzResearch.WordTrace]
  refine ⟨35026222029885027663861653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23350814686590018442574435 35026222029885027663861653)
  ·
    refine ⟨1641854157650860671743515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 35026222029885027663861653 1641854157650860671743515)
    ·
      refine ⟨2462781236476291007615273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1641854157650860671743515 2462781236476291007615273)
      ·
        refine ⟨1847085927357218255711455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2462781236476291007615273 1847085927357218255711455)
        ·
          refine ⟨2770628891035827383567183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1847085927357218255711455 2770628891035827383567183)
          ·
            refine ⟨4155943336553741075350775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2770628891035827383567183 4155943336553741075350775)
            ·
              refine ⟨6233915004830611613026163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4155943336553741075350775 6233915004830611613026163)
              ·
                refine ⟨9350872507245917419539245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6233915004830611613026163 9350872507245917419539245)
                ·
                  refine ⟨3506577190217219032327217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9350872507245917419539245 3506577190217219032327217)
                  ·
                    refine ⟨2629932892662914274245413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3506577190217219032327217 2629932892662914274245413)
                    ·
                      refine ⟨493112417374296426421015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2629932892662914274245413 493112417374296426421015)
                      ·
                        rfl

theorem cell23_960333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_960333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_960333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_960333 prefixEnd_960333 := by exact prefixLift 960333
  have htrace : WordTrace (prefixWord ++ tailWord_960333) baseStart_960333 baseEnd_960333 := by
    simpa [prefixWord, tailWord_960333, baseEnd_960333] using wordTrace_append hprefix tailTrace_960333
  have hstable : (prefixWord ++ tailWord_960333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960333).length < 2 ^ (prefixWord ++ tailWord_960333).sum := by decide
  have hdescent : baseEnd_960333 < baseStart_960333 := by decide
  rcases family_descends (prefixWord ++ tailWord_960333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960354 : List Nat := [3, 3, 2, 1, 2, 2, 1, 4, 1, 2, 2]
def baseStart_960354 : Nat := 118140960795 + 960354 * 2 ^ 59
def prefixEnd_960354 : Nat := 4983230072969 + 3 ^ 40 * 960354 * 2
def baseEnd_960354 : Nat := 493123200468040844258419

theorem tailTrace_960354 : CollatzResearch.WordTrace tailWord_960354 prefixEnd_960354 493123200468040844258419 := by
  unfold tailWord_960354
  simp only [CollatzResearch.WordTrace]
  refine ⟨8756746990702237062594029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23351325308539298833584077 8756746990702237062594029)
  ·
    refine ⟨3283780121513338898472761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8756746990702237062594029 3283780121513338898472761)
    ·
      refine ⟨2462835091135004173854571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3283780121513338898472761 2462835091135004173854571)
      ·
        refine ⟨3694252636702506260781857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2462835091135004173854571 3694252636702506260781857)
        ·
          refine ⟨2770689477526879695586393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3694252636702506260781857 2770689477526879695586393)
          ·
            refine ⟨2078017108145159771689795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2770689477526879695586393 2078017108145159771689795)
            ·
              refine ⟨3117025662217739657534693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2078017108145159771689795 3117025662217739657534693)
              ·
                refine ⟨584442311665826185787755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3117025662217739657534693 584442311665826185787755)
                ·
                  refine ⟨876663467498739278681633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 584442311665826185787755 876663467498739278681633)
                  ·
                    refine ⟨657497600624054459011225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 876663467498739278681633 657497600624054459011225)
                    ·
                      refine ⟨493123200468040844258419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 657497600624054459011225 493123200468040844258419)
                      ·
                        rfl

theorem cell23_960354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 4, 1, 2, 2].length) (baseStart_960354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_960354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_960354 prefixEnd_960354 := by exact prefixLift 960354
  have htrace : WordTrace (prefixWord ++ tailWord_960354) baseStart_960354 baseEnd_960354 := by
    simpa [prefixWord, tailWord_960354, baseEnd_960354] using wordTrace_append hprefix tailTrace_960354
  have hstable : (prefixWord ++ tailWord_960354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960354).length < 2 ^ (prefixWord ++ tailWord_960354).sum := by decide
  have hdescent : baseEnd_960354 < baseStart_960354 := by decide
  rcases family_descends (prefixWord ++ tailWord_960354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960393 : List Nat := [1, 2, 1, 1, 5, 1, 1, 4, 1, 4, 2]
def baseStart_960393 : Nat := 118140960795 + 960393 * 2 ^ 59
def prefixEnd_960393 : Nat := 4983230072969 + 3 ^ 40 * 960393 * 2
def baseEnd_960393 : Nat := 493143226213566191670739

theorem tailTrace_960393 : CollatzResearch.WordTrace tailWord_960393 prefixEnd_960393 493143226213566191670739 := by
  unfold tailWord_960393
  simp only [CollatzResearch.WordTrace]
  refine ⟨35028410409667657911045833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23352273606445105274030555 35028410409667657911045833)
  ·
    refine ⟨26271307807250743433284375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35028410409667657911045833 26271307807250743433284375)
    ·
      refine ⟨39406961710876115149926563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26271307807250743433284375 39406961710876115149926563)
      ·
        refine ⟨59110442566314172724889845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39406961710876115149926563 59110442566314172724889845)
        ·
          refine ⟨5541603990591953692958423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59110442566314172724889845 5541603990591953692958423)
          ·
            refine ⟨8312405985887930539437635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5541603990591953692958423 8312405985887930539437635)
            ·
              refine ⟨12468608978831895809156453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8312405985887930539437635 12468608978831895809156453)
              ·
                refine ⟨2337864183530980464216835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12468608978831895809156453 2337864183530980464216835)
                ·
                  refine ⟨3506796275296470696325253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2337864183530980464216835 3506796275296470696325253)
                  ·
                    refine ⟨657524301618088255560985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3506796275296470696325253 657524301618088255560985)
                    ·
                      refine ⟨493143226213566191670739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 657524301618088255560985 493143226213566191670739)
                      ·
                        rfl

theorem cell23_960393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 4, 1, 4, 2].length) (baseStart_960393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_960393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_960393 prefixEnd_960393 := by exact prefixLift 960393
  have htrace : WordTrace (prefixWord ++ tailWord_960393) baseStart_960393 baseEnd_960393 := by
    simpa [prefixWord, tailWord_960393, baseEnd_960393] using wordTrace_append hprefix tailTrace_960393
  have hstable : (prefixWord ++ tailWord_960393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960393).length < 2 ^ (prefixWord ++ tailWord_960393).sum := by decide
  have hdescent : baseEnd_960393 < baseStart_960393 := by decide
  rcases family_descends (prefixWord ++ tailWord_960393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960423 : List Nat := [1, 1, 6, 1, 2, 1, 2, 1, 2, 2, 4]
def baseStart_960423 : Nat := 118140960795 + 960423 * 2 ^ 59
def prefixEnd_960423 : Nat := 4983230072969 + 3 ^ 40 * 960423 * 2
def baseEnd_960423 : Nat := 493158630633201074295601

theorem tailTrace_960423 : CollatzResearch.WordTrace tailWord_960423 prefixEnd_960423 493158630633201074295601 := by
  unfold tailWord_960423
  simp only [CollatzResearch.WordTrace]
  refine ⟨35029504599558973034637923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23353003066372648689758615 35029504599558973034637923)
  ·
    refine ⟨52544256899338459551956885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35029504599558973034637923 52544256899338459551956885)
    ·
      refine ⟨2463012042156490291497979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 52544256899338459551956885 2463012042156490291497979)
      ·
        refine ⟨3694518063234735437246969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2463012042156490291497979 3694518063234735437246969)
        ·
          refine ⟨2770888547426051577935227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3694518063234735437246969 2770888547426051577935227)
          ·
            refine ⟨4156332821139077366902841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2770888547426051577935227 4156332821139077366902841)
            ·
              refine ⟨3117249615854308025177131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4156332821139077366902841 3117249615854308025177131)
              ·
                refine ⟨4675874423781462037765697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3117249615854308025177131 4675874423781462037765697)
                ·
                  refine ⟨3506905817836096528324273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4675874423781462037765697 3506905817836096528324273)
                  ·
                    refine ⟨2630179363377072396243205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3506905817836096528324273 2630179363377072396243205)
                    ·
                      refine ⟨493158630633201074295601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2630179363377072396243205 493158630633201074295601)
                      ·
                        rfl

theorem cell23_960423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_960423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_960423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_960423 prefixEnd_960423 := by exact prefixLift 960423
  have htrace : WordTrace (prefixWord ++ tailWord_960423) baseStart_960423 baseEnd_960423 := by
    simpa [prefixWord, tailWord_960423, baseEnd_960423] using wordTrace_append hprefix tailTrace_960423
  have hstable : (prefixWord ++ tailWord_960423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960423).length < 2 ^ (prefixWord ++ tailWord_960423).sum := by decide
  have hdescent : baseEnd_960423 < baseStart_960423 := by decide
  rcases family_descends (prefixWord ++ tailWord_960423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960473 : List Nat := [1, 2, 1, 2, 6, 1, 1, 1, 1, 2, 5]
def baseStart_960473 : Nat := 118140960795 + 960473 * 2 ^ 59
def prefixEnd_960473 : Nat := 4983230072969 + 3 ^ 40 * 960473 * 2
def baseEnd_960473 : Nat := 493184304665925878670371

theorem tailTrace_960473 : CollatzResearch.WordTrace tailWord_960473 prefixEnd_960473 493184304665925878670371 := by
  unfold tailWord_960473
  simp only [CollatzResearch.WordTrace]
  refine ⟨35031328249377831573958073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23354218832918554382638715 35031328249377831573958073)
  ·
    refine ⟨26273496187033373680468555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35031328249377831573958073 26273496187033373680468555)
    ·
      refine ⟨39410244280550060520702833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26273496187033373680468555 39410244280550060520702833)
      ·
        refine ⟨29557683210412545390527125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39410244280550060520702833 29557683210412545390527125)
        ·
          refine ⟨1385516400488088065180959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 29557683210412545390527125 1385516400488088065180959)
          ·
            refine ⟨2078274600732132097771439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1385516400488088065180959 2078274600732132097771439)
            ·
              refine ⟨3117411901098198146657159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2078274600732132097771439 3117411901098198146657159)
              ·
                refine ⟨4676117851647297219985739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3117411901098198146657159 4676117851647297219985739)
                ·
                  refine ⟨7014176777470945829978609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4676117851647297219985739 7014176777470945829978609)
                  ·
                    refine ⟨5260632583103209372483957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7014176777470945829978609 5260632583103209372483957)
                    ·
                      refine ⟨493184304665925878670371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5260632583103209372483957 493184304665925878670371)
                      ·
                        rfl

theorem cell23_960473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 2, 5].length) (baseStart_960473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_960473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_960473 prefixEnd_960473 := by exact prefixLift 960473
  have htrace : WordTrace (prefixWord ++ tailWord_960473) baseStart_960473 baseEnd_960473 := by
    simpa [prefixWord, tailWord_960473, baseEnd_960473] using wordTrace_append hprefix tailTrace_960473
  have hstable : (prefixWord ++ tailWord_960473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960473).length < 2 ^ (prefixWord ++ tailWord_960473).sum := by decide
  have hdescent : baseEnd_960473 < baseStart_960473 := by decide
  rcases family_descends (prefixWord ++ tailWord_960473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960496 : List Nat := [2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 4]
def baseStart_960496 : Nat := 118140960795 + 960496 * 2 ^ 59
def prefixEnd_960496 : Nat := 4983230072969 + 3 ^ 40 * 960496 * 2
def baseEnd_960496 : Nat := 493196114720979288682765

theorem tailTrace_960496 : CollatzResearch.WordTrace tailWord_960496 prefixEnd_960496 493196114720979288682765 := by
  unfold tailWord_960496
  simp only [CollatzResearch.WordTrace]
  refine ⟨17516083564147253251022671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23354778085529671001363561 17516083564147253251022671)
  ·
    refine ⟨26274125346220879876534007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17516083564147253251022671 26274125346220879876534007)
    ·
      refine ⟨39411188019331319814801011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26274125346220879876534007 39411188019331319814801011)
      ·
        refine ⟨59116782028996979722201517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39411188019331319814801011 59116782028996979722201517)
        ·
          refine ⟨22168793260873867395825569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59116782028996979722201517 22168793260873867395825569)
          ·
            refine ⟨16626594945655400546869177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22168793260873867395825569 16626594945655400546869177)
            ·
              refine ⟨12469946209241550410151883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16626594945655400546869177 12469946209241550410151883)
              ·
                refine ⟨18704919313862325615227825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12469946209241550410151883 18704919313862325615227825)
                ·
                  refine ⟨14028689485396744211420869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18704919313862325615227825 14028689485396744211420869)
                  ·
                    refine ⟨2630379278511889539641413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14028689485396744211420869 2630379278511889539641413)
                    ·
                      refine ⟨493196114720979288682765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2630379278511889539641413 493196114720979288682765)
                      ·
                        rfl

theorem cell23_960496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 4].length) (baseStart_960496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_960496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_960496 prefixEnd_960496 := by exact prefixLift 960496
  have htrace : WordTrace (prefixWord ++ tailWord_960496) baseStart_960496 baseEnd_960496 := by
    simpa [prefixWord, tailWord_960496, baseEnd_960496] using wordTrace_append hprefix tailTrace_960496
  have hstable : (prefixWord ++ tailWord_960496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960496).length < 2 ^ (prefixWord ++ tailWord_960496).sum := by decide
  have hdescent : baseEnd_960496 < baseStart_960496 := by decide
  rcases family_descends (prefixWord ++ tailWord_960496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960523 : List Nat := [1, 1, 1, 1, 6, 1, 4, 2, 6]
def baseStart_960523 : Nat := 118140960795 + 960523 * 2 ^ 59
def prefixEnd_960523 : Nat := 4983230072969 + 3 ^ 40 * 960523 * 2
def baseEnd_960523 : Nat := 54801108744294520338349

theorem tailTrace_960523 : CollatzResearch.WordTrace tailWord_960523 prefixEnd_960523 54801108744294520338349 := by
  unfold tailWord_960523
  simp only [CollatzResearch.WordTrace]
  refine ⟨35033151899196690113278223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23355434599464460075518815 35033151899196690113278223)
  ·
    refine ⟨52549727848795035169917335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35033151899196690113278223 52549727848795035169917335)
    ·
      refine ⟨78824591773192552754876003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52549727848795035169917335 78824591773192552754876003)
      ·
        refine ⟨118236887659788829132314005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78824591773192552754876003 118236887659788829132314005)
        ·
          refine ⟨5542354109052601365577219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 118236887659788829132314005 5542354109052601365577219)
          ·
            refine ⟨8313531163578902048365829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5542354109052601365577219 8313531163578902048365829)
            ·
              refine ⟨1558787093171044134068593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8313531163578902048365829 1558787093171044134068593)
              ·
                refine ⟨1169090319878283100551445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1558787093171044134068593 1169090319878283100551445)
                ·
                  refine ⟨54801108744294520338349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1169090319878283100551445 54801108744294520338349)
                  ·
                    rfl

theorem cell23_960523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 2, 6].length) (baseStart_960523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_960523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_960523 prefixEnd_960523 := by exact prefixLift 960523
  have htrace : WordTrace (prefixWord ++ tailWord_960523) baseStart_960523 baseEnd_960523 := by
    simpa [prefixWord, tailWord_960523, baseEnd_960523] using wordTrace_append hprefix tailTrace_960523
  have hstable : (prefixWord ++ tailWord_960523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960523).length < 2 ^ (prefixWord ++ tailWord_960523).sum := by decide
  have hdescent : baseEnd_960523 < baseStart_960523 := by decide
  rcases family_descends (prefixWord ++ tailWord_960523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960560 : List Nat := [2, 1, 1, 1, 2, 6, 1, 1, 1, 5, 2]
def baseStart_960560 : Nat := 118140960795 + 960560 * 2 ^ 59
def prefixEnd_960560 : Nat := 4983230072969 + 3 ^ 40 * 960560 * 2
def baseEnd_960560 : Nat := 493228977482867038282471

theorem tailTrace_960560 : CollatzResearch.WordTrace tailWord_960560 prefixEnd_960560 493228977482867038282471 := by
  unfold tailWord_960560
  simp only [CollatzResearch.WordTrace]
  refine ⟨17517250700031322716187567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23356334266708430288250089 17517250700031322716187567)
  ·
    refine ⟨26275876050046984074281351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17517250700031322716187567 26275876050046984074281351)
    ·
      refine ⟨39413814075070476111422027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26275876050046984074281351 39413814075070476111422027)
      ·
        refine ⟨59120721112605714167133041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39413814075070476111422027 59120721112605714167133041)
        ·
          refine ⟨44340540834454285625349781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59120721112605714167133041 44340540834454285625349781)
          ·
            refine ⟨2078462851615044638688271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 44340540834454285625349781 2078462851615044638688271)
            ·
              refine ⟨3117694277422566958032407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2078462851615044638688271 3117694277422566958032407)
              ·
                refine ⟨4676541416133850437048611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3117694277422566958032407 4676541416133850437048611)
                ·
                  refine ⟨7014812124200775655572917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4676541416133850437048611 7014812124200775655572917)
                  ·
                    refine ⟨657638636643822717709961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7014812124200775655572917 657638636643822717709961)
                    ·
                      refine ⟨493228977482867038282471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 657638636643822717709961 493228977482867038282471)
                      ·
                        rfl

theorem cell23_960560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 1, 5, 2].length) (baseStart_960560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_960560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_960560 prefixEnd_960560 := by exact prefixLift 960560
  have htrace : WordTrace (prefixWord ++ tailWord_960560) baseStart_960560 baseEnd_960560 := by
    simpa [prefixWord, tailWord_960560, baseEnd_960560] using wordTrace_append hprefix tailTrace_960560
  have hstable : (prefixWord ++ tailWord_960560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960560).length < 2 ^ (prefixWord ++ tailWord_960560).sum := by decide
  have hdescent : baseEnd_960560 < baseStart_960560 := by decide
  rcases family_descends (prefixWord ++ tailWord_960560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960567 : List Nat := [1, 1, 3, 1, 2, 2, 3, 5, 1, 1, 3]
def baseStart_960567 : Nat := 118140960795 + 960567 * 2 ^ 59
def prefixEnd_960567 : Nat := 4983230072969 + 3 ^ 40 * 960567 * 2
def baseEnd_960567 : Nat := 493232571847448510894939

theorem tailTrace_960567 : CollatzResearch.WordTrace tailWord_960567 prefixEnd_960567 493232571847448510894939 := by
  unfold tailWord_960567
  simp only [CollatzResearch.WordTrace]
  refine ⟨35034756711037285627879955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23356504474024857085253303 35034756711037285627879955)
  ·
    refine ⟨52552135066555928441819933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35034756711037285627879955 52552135066555928441819933)
    ·
      refine ⟨19707050649958473165682475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52552135066555928441819933 19707050649958473165682475)
      ·
        refine ⟨29560575974937709748523713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19707050649958473165682475 29560575974937709748523713)
        ·
          refine ⟨22170431981203282311392785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29560575974937709748523713 22170431981203282311392785)
          ·
            refine ⟨16627823985902461733544589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22170431981203282311392785 16627823985902461733544589)
            ·
              refine ⟨6235433994713423150079221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16627823985902461733544589 6235433994713423150079221)
              ·
                refine ⟨584571937004383420319927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6235433994713423150079221 584571937004383420319927)
                ·
                  refine ⟨876857905506575130479891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 584571937004383420319927 876857905506575130479891)
                  ·
                    refine ⟨1315286858259862695719837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 876857905506575130479891 1315286858259862695719837)
                    ·
                      refine ⟨493232571847448510894939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1315286858259862695719837 493232571847448510894939)
                      ·
                        rfl

theorem cell23_960567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 5, 1, 1, 3].length) (baseStart_960567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_960567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_960567 prefixEnd_960567 := by exact prefixLift 960567
  have htrace : WordTrace (prefixWord ++ tailWord_960567) baseStart_960567 baseEnd_960567 := by
    simpa [prefixWord, tailWord_960567, baseEnd_960567] using wordTrace_append hprefix tailTrace_960567
  have hstable : (prefixWord ++ tailWord_960567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960567).length < 2 ^ (prefixWord ++ tailWord_960567).sum := by decide
  have hdescent : baseEnd_960567 < baseStart_960567 := by decide
  rcases family_descends (prefixWord ++ tailWord_960567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960574 : List Nat := [4, 2, 1, 3, 3, 1, 1, 2, 6]
def baseStart_960574 : Nat := 118140960795 + 960574 * 2 ^ 59
def prefixEnd_960574 : Nat := 4983230072969 + 3 ^ 40 * 960574 * 2
def baseEnd_960574 : Nat := 54804018468003331500823

theorem tailTrace_960574 : CollatzResearch.WordTrace tailWord_960574 prefixEnd_960574 54804018468003331500823 := by
  unfold tailWord_960574
  simp only [CollatzResearch.WordTrace]
  refine ⟨4379376502751490727923097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23356674681341283882256517 4379376502751490727923097)
  ·
    refine ⟨3284532377063618045942323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4379376502751490727923097 3284532377063618045942323)
    ·
      refine ⟨4926798565595427068913485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3284532377063618045942323 4926798565595427068913485)
      ·
        refine ⟨1847549462098285150842557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4926798565595427068913485 1847549462098285150842557)
        ·
          refine ⟨692831048286856931565959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1847549462098285150842557 692831048286856931565959)
          ·
            refine ⟨1039246572430285397348939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 692831048286856931565959 1039246572430285397348939)
            ·
              refine ⟨1558869858645428096023409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1039246572430285397348939 1558869858645428096023409)
              ·
                refine ⟨1169152393984071072017557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1558869858645428096023409 1169152393984071072017557)
                ·
                  refine ⟨54804018468003331500823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1169152393984071072017557 54804018468003331500823)
                  ·
                    rfl

theorem cell23_960574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 2, 6].length) (baseStart_960574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_960574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_960574 prefixEnd_960574 := by exact prefixLift 960574
  have htrace : WordTrace (prefixWord ++ tailWord_960574) baseStart_960574 baseEnd_960574 := by
    simpa [prefixWord, tailWord_960574, baseEnd_960574] using wordTrace_append hprefix tailTrace_960574
  have hstable : (prefixWord ++ tailWord_960574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960574).length < 2 ^ (prefixWord ++ tailWord_960574).sum := by decide
  have hdescent : baseEnd_960574 < baseStart_960574 := by decide
  rcases family_descends (prefixWord ++ tailWord_960574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960600 : List Nat := [2, 1, 2, 2, 1, 6, 1, 1, 1, 6]
def baseStart_960600 : Nat := 118140960795 + 960600 * 2 ^ 59
def prefixEnd_960600 : Nat := 4983230072969 + 3 ^ 40 * 960600 * 2
def baseEnd_960600 : Nat := 164416505569682293927429

theorem tailTrace_960600 : CollatzResearch.WordTrace tailWord_960600 prefixEnd_960600 164416505569682293927429 := by
  unfold tailWord_960600
  simp only [CollatzResearch.WordTrace]
  refine ⟨17517980159958866131915627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23357306879945154842554169 17517980159958866131915627)
  ·
    refine ⟨26276970239938299197873441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17517980159958866131915627 26276970239938299197873441)
    ·
      refine ⟨19707727679953724398405081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26276970239938299197873441 19707727679953724398405081)
      ·
        refine ⟨14780795759965293298803811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19707727679953724398405081 14780795759965293298803811)
        ·
          refine ⟨22171193639947939948205717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14780795759965293298803811 22171193639947939948205717)
          ·
            refine ⟨1039274701872559685072143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 22171193639947939948205717 1039274701872559685072143)
            ·
              refine ⟨1558912052808839527608215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1039274701872559685072143 1558912052808839527608215)
              ·
                refine ⟨2338368079213259291412323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1558912052808839527608215 2338368079213259291412323)
                ·
                  refine ⟨3507552118819888937118485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2338368079213259291412323 3507552118819888937118485)
                  ·
                    refine ⟨164416505569682293927429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3507552118819888937118485 164416505569682293927429)
                    ·
                      rfl

theorem cell23_960600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 1, 1, 6].length) (baseStart_960600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_960600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_960600 prefixEnd_960600 := by exact prefixLift 960600
  have htrace : WordTrace (prefixWord ++ tailWord_960600) baseStart_960600 baseEnd_960600 := by
    simpa [prefixWord, tailWord_960600, baseEnd_960600] using wordTrace_append hprefix tailTrace_960600
  have hstable : (prefixWord ++ tailWord_960600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960600).length < 2 ^ (prefixWord ++ tailWord_960600).sum := by decide
  have hdescent : baseEnd_960600 < baseStart_960600 := by decide
  rcases family_descends (prefixWord ++ tailWord_960600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960613 : List Nat := [1, 3, 1, 3, 2, 3, 1, 9]
def baseStart_960613 : Nat := 118140960795 + 960613 * 2 ^ 59
def prefixEnd_960613 : Nat := 4983230072969 + 3 ^ 40 * 960613 * 2
def baseEnd_960613 : Nat := 18268747850279827071101

theorem tailTrace_960613 : CollatzResearch.WordTrace tailWord_960613 prefixEnd_960613 18268747850279827071101 := by
  unfold tailWord_960613
  simp only [CollatzResearch.WordTrace]
  refine ⟨35036434468870635484054493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23357622979247090322702995 35036434468870635484054493)
  ·
    refine ⟨13138662925826488306520435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35036434468870635484054493 13138662925826488306520435)
    ·
      refine ⟨19707994388739732459780653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13138662925826488306520435 19707994388739732459780653)
      ·
        refine ⟨7390497895777399672417745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19707994388739732459780653 7390497895777399672417745)
        ·
          refine ⟨5542873421833049754313309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7390497895777399672417745 5542873421833049754313309)
          ·
            refine ⟨2078577533187393657867491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5542873421833049754313309 2078577533187393657867491)
            ·
              refine ⟨3117866299781090486801237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2078577533187393657867491 3117866299781090486801237)
              ·
                refine ⟨18268747850279827071101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3117866299781090486801237 18268747850279827071101)
                ·
                  rfl

theorem cell23_960613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 9].length) (baseStart_960613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_960613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_960613 prefixEnd_960613 := by exact prefixLift 960613
  have htrace : WordTrace (prefixWord ++ tailWord_960613) baseStart_960613 baseEnd_960613 := by
    simpa [prefixWord, tailWord_960613, baseEnd_960613] using wordTrace_append hprefix tailTrace_960613
  have hstable : (prefixWord ++ tailWord_960613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960613).length < 2 ^ (prefixWord ++ tailWord_960613).sum := by decide
  have hdescent : baseEnd_960613 < baseStart_960613 := by decide
  rcases family_descends (prefixWord ++ tailWord_960613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960618 : List Nat := [3, 1, 3, 2, 4, 1, 1, 3, 1, 1, 3]
def baseStart_960618 : Nat := 118140960795 + 960618 * 2 ^ 59
def prefixEnd_960618 : Nat := 4983230072969 + 3 ^ 40 * 960618 * 2
def baseEnd_960618 : Nat := 493258759360827811357205

theorem tailTrace_960618 : CollatzResearch.WordTrace tailWord_960618 prefixEnd_960618 493258759360827811357205 := by
  unfold tailWord_960618
  simp only [CollatzResearch.WordTrace]
  refine ⟨8759154208463130334496627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23357744555901680891991005 8759154208463130334496627)
  ·
    refine ⟨13138731312694695501744941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8759154208463130334496627 13138731312694695501744941)
    ·
      refine ⟨4927024242260510813154353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13138731312694695501744941 4927024242260510813154353)
      ·
        refine ⟨3695268181695383109865765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4927024242260510813154353 3695268181695383109865765)
        ·
          refine ⟨692862784067884333099831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3695268181695383109865765 692862784067884333099831)
          ·
            refine ⟨1039294176101826499649747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 692862784067884333099831 1039294176101826499649747)
            ·
              refine ⟨1558941264152739749474621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1039294176101826499649747 1558941264152739749474621)
              ·
                refine ⟨584602974057277406052983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1558941264152739749474621 584602974057277406052983)
                ·
                  refine ⟨876904461085916109079475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 584602974057277406052983 876904461085916109079475)
                  ·
                    refine ⟨1315356691628874163619213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 876904461085916109079475 1315356691628874163619213)
                    ·
                      refine ⟨493258759360827811357205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1315356691628874163619213 493258759360827811357205)
                      ·
                        rfl

theorem cell23_960618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 3, 1, 1, 3].length) (baseStart_960618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_960618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_960618 prefixEnd_960618 := by exact prefixLift 960618
  have htrace : WordTrace (prefixWord ++ tailWord_960618) baseStart_960618 baseEnd_960618 := by
    simpa [prefixWord, tailWord_960618, baseEnd_960618] using wordTrace_append hprefix tailTrace_960618
  have hstable : (prefixWord ++ tailWord_960618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960618).length < 2 ^ (prefixWord ++ tailWord_960618).sum := by decide
  have hdescent : baseEnd_960618 < baseStart_960618 := by decide
  rcases family_descends (prefixWord ++ tailWord_960618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960630 : List Nat := [5, 1, 1, 2, 1, 4, 9]
def baseStart_960630 : Nat := 118140960795 + 960630 * 2 ^ 59
def prefixEnd_960630 : Nat := 4983230072969 + 3 ^ 40 * 960630 * 2
def baseEnd_960630 : Nat := 6089690384304713140829

theorem tailTrace_960630 : CollatzResearch.WordTrace tailWord_960630 prefixEnd_960630 6089690384304713140829 := by
  unfold tailWord_960630
  simp only [CollatzResearch.WordTrace]
  refine ⟨2189815906863065461713959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23358036339872698258282229 2189815906863065461713959)
  ·
    refine ⟨3284723860294598192570939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2189815906863065461713959 3284723860294598192570939)
    ·
      refine ⟨4927085790441897288856409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3284723860294598192570939 4927085790441897288856409)
      ·
        refine ⟨3695314342831422966642307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4927085790441897288856409 3695314342831422966642307)
        ·
          refine ⟨5542971514247134449963461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3695314342831422966642307 5542971514247134449963461)
          ·
            refine ⟨1039307158921337709368149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5542971514247134449963461 1039307158921337709368149)
            ·
              refine ⟨6089690384304713140829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1039307158921337709368149 6089690384304713140829)
              ·
                rfl

theorem cell23_960630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 9].length) (baseStart_960630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_960630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_960630 prefixEnd_960630 := by exact prefixLift 960630
  have htrace : WordTrace (prefixWord ++ tailWord_960630) baseStart_960630 baseEnd_960630 := by
    simpa [prefixWord, tailWord_960630, baseEnd_960630] using wordTrace_append hprefix tailTrace_960630
  have hstable : (prefixWord ++ tailWord_960630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960630).length < 2 ^ (prefixWord ++ tailWord_960630).sum := by decide
  have hdescent : baseEnd_960630 < baseStart_960630 := by decide
  rcases family_descends (prefixWord ++ tailWord_960630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960641 : List Nat := [1, 2, 4, 2, 3, 2, 1, 1, 3, 2, 2]
def baseStart_960641 : Nat := 118140960795 + 960641 * 2 ^ 59
def prefixEnd_960641 : Nat := 4983230072969 + 3 ^ 40 * 960641 * 2
def baseEnd_960641 : Nat := 493270569415881221369599

theorem tailTrace_960641 : CollatzResearch.WordTrace tailWord_960641 prefixEnd_960641 493270569415881221369599 := by
  unfold tailWord_960641
  simp only [CollatzResearch.WordTrace]
  refine ⟨35037455712769196266073777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23358303808512797510715851 35037455712769196266073777)
  ·
    refine ⟨26278091784576897199555333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35037455712769196266073777 26278091784576897199555333)
    ·
      refine ⟨4927142209608168224916625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26278091784576897199555333 4927142209608168224916625)
      ·
        refine ⟨3695356657206126168687469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4927142209608168224916625 3695356657206126168687469)
        ·
          refine ⟨1385758746452297313257801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3695356657206126168687469 1385758746452297313257801)
          ·
            refine ⟨1039319059839222984943351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1385758746452297313257801 1039319059839222984943351)
            ·
              refine ⟨1558978589758834477415027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1039319059839222984943351 1558978589758834477415027)
              ·
                refine ⟨2338467884638251716122541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1558978589758834477415027 2338467884638251716122541)
                ·
                  refine ⟨876925456739344393545953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2338467884638251716122541 876925456739344393545953)
                  ·
                    refine ⟨657694092554508295159465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 876925456739344393545953 657694092554508295159465)
                    ·
                      refine ⟨493270569415881221369599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 657694092554508295159465 493270569415881221369599)
                      ·
                        rfl

theorem cell23_960641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 1, 3, 2, 2].length) (baseStart_960641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_960641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_960641 prefixEnd_960641 := by exact prefixLift 960641
  have htrace : WordTrace (prefixWord ++ tailWord_960641) baseStart_960641 baseEnd_960641 := by
    simpa [prefixWord, tailWord_960641, baseEnd_960641] using wordTrace_append hprefix tailTrace_960641
  have hstable : (prefixWord ++ tailWord_960641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960641).length < 2 ^ (prefixWord ++ tailWord_960641).sum := by decide
  have hdescent : baseEnd_960641 < baseStart_960641 := by decide
  rcases family_descends (prefixWord ++ tailWord_960641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960692 : List Nat := [2, 5, 3, 1, 1, 1, 1, 4, 1, 2, 2]
def baseStart_960692 : Nat := 118140960795 + 960692 * 2 ^ 59
def prefixEnd_960692 : Nat := 4983230072969 + 3 ^ 40 * 960692 * 2
def baseEnd_960692 : Nat := 493296756929260521831865

theorem tailTrace_960692 : CollatzResearch.WordTrace tailWord_960692 prefixEnd_960692 493296756929260521831865 := by
  unfold tailWord_960692
  simp only [CollatzResearch.WordTrace]
  refine ⟨17519657917792215988090165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23359543890389621317453553 17519657917792215988090165)
  ·
    refine ⟨1642467929793020248883453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17519657917792215988090165 1642467929793020248883453)
    ·
      refine ⟨615925473672382593331295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1642467929793020248883453 615925473672382593331295)
      ·
        refine ⟨923888210508573889996943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 615925473672382593331295 923888210508573889996943)
        ·
          refine ⟨1385832315762860834995415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 923888210508573889996943 1385832315762860834995415)
          ·
            refine ⟨2078748473644291252493123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1385832315762860834995415 2078748473644291252493123)
            ·
              refine ⟨3118122710466436878739685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2078748473644291252493123 3118122710466436878739685)
              ·
                refine ⟨584648008212456914763691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3118122710466436878739685 584648008212456914763691)
                ·
                  refine ⟨876972012318685372145537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 584648008212456914763691 876972012318685372145537)
                  ·
                    refine ⟨657729009239014029109153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 876972012318685372145537 657729009239014029109153)
                    ·
                      refine ⟨493296756929260521831865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 657729009239014029109153 493296756929260521831865)
                      ·
                        rfl

theorem cell23_960692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_960692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_960692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_960692 prefixEnd_960692 := by exact prefixLift 960692
  have htrace : WordTrace (prefixWord ++ tailWord_960692) baseStart_960692 baseEnd_960692 := by
    simpa [prefixWord, tailWord_960692, baseEnd_960692] using wordTrace_append hprefix tailTrace_960692
  have hstable : (prefixWord ++ tailWord_960692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960692).length < 2 ^ (prefixWord ++ tailWord_960692).sum := by decide
  have hdescent : baseEnd_960692 < baseStart_960692 := by decide
  rcases family_descends (prefixWord ++ tailWord_960692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960703 : List Nat := [1, 1, 2, 2, 2, 2, 1, 5, 7]
def baseStart_960703 : Nat := 118140960795 + 960703 * 2 ^ 59
def prefixEnd_960703 : Nat := 4983230072969 + 3 ^ 40 * 960703 * 2
def baseEnd_960703 : Nat := 54811378357384442088257

theorem tailTrace_960703 : CollatzResearch.WordTrace tailWord_960703 prefixEnd_960703 54811378357384442088257 := by
  unfold tailWord_960703
  simp only [CollatzResearch.WordTrace]
  refine ⟨35039717038544580854830763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23359811359029720569887175 35039717038544580854830763)
  ·
    refine ⟨52559575557816871282246145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35039717038544580854830763 52559575557816871282246145)
    ·
      refine ⟨39419681668362653461684609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52559575557816871282246145 39419681668362653461684609)
      ·
        refine ⟨29564761251271990096263457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39419681668362653461684609 29564761251271990096263457)
        ·
          refine ⟨22173570938453992572197593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29564761251271990096263457 22173570938453992572197593)
          ·
            refine ⟨16630178203840494429148195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22173570938453992572197593 16630178203840494429148195)
            ·
              refine ⟨24945267305760741643722293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16630178203840494429148195 24945267305760741643722293)
              ·
                refine ⟨2338618809915069529098965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24945267305760741643722293 2338618809915069529098965)
                ·
                  refine ⟨54811378357384442088257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2338618809915069529098965 54811378357384442088257)
                  ·
                    rfl

theorem cell23_960703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 5, 7].length) (baseStart_960703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_960703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_960703 prefixEnd_960703 := by exact prefixLift 960703
  have htrace : WordTrace (prefixWord ++ tailWord_960703) baseStart_960703 baseEnd_960703 := by
    simpa [prefixWord, tailWord_960703, baseEnd_960703] using wordTrace_append hprefix tailTrace_960703
  have hstable : (prefixWord ++ tailWord_960703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960703).length < 2 ^ (prefixWord ++ tailWord_960703).sum := by decide
  have hdescent : baseEnd_960703 < baseStart_960703 := by decide
  rcases family_descends (prefixWord ++ tailWord_960703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960714 : List Nat := [3, 1, 2, 1, 3, 1, 1, 5, 2, 2, 2]
def baseStart_960714 : Nat := 118140960795 + 960714 * 2 ^ 59
def prefixEnd_960714 : Nat := 4983230072969 + 3 ^ 40 * 960714 * 2
def baseEnd_960714 : Nat := 493308053503659435756763

theorem tailTrace_960714 : CollatzResearch.WordTrace tailWord_960714 prefixEnd_960714 493308053503659435756763 := by
  unfold tailWord_960714
  simp only [CollatzResearch.WordTrace]
  refine ⟨8760029560376182433370299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23360078827669819822320797 8760029560376182433370299)
  ·
    refine ⟨13140044340564273650055449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8760029560376182433370299 13140044340564273650055449)
    ·
      refine ⟨9855033255423205237541587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13140044340564273650055449 9855033255423205237541587)
      ·
        refine ⟨14782549883134807856312381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9855033255423205237541587 14782549883134807856312381)
        ·
          refine ⟨5543456206175552946117143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14782549883134807856312381 5543456206175552946117143)
          ·
            refine ⟨8315184309263329419175715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5543456206175552946117143 8315184309263329419175715)
            ·
              refine ⟨12472776463894994128763573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8315184309263329419175715 12472776463894994128763573)
              ·
                refine ⟨1169322793490155699571585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12472776463894994128763573 1169322793490155699571585)
                ·
                  refine ⟨876992095117616774678689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1169322793490155699571585 876992095117616774678689)
                  ·
                    refine ⟨657744071338212581009017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 876992095117616774678689 657744071338212581009017)
                    ·
                      refine ⟨493308053503659435756763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 657744071338212581009017 493308053503659435756763)
                      ·
                        rfl

theorem cell23_960714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 5, 2, 2, 2].length) (baseStart_960714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_960714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_960714 prefixEnd_960714 := by exact prefixLift 960714
  have htrace : WordTrace (prefixWord ++ tailWord_960714) baseStart_960714 baseEnd_960714 := by
    simpa [prefixWord, tailWord_960714, baseEnd_960714] using wordTrace_append hprefix tailTrace_960714
  have hstable : (prefixWord ++ tailWord_960714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960714).length < 2 ^ (prefixWord ++ tailWord_960714).sum := by decide
  have hdescent : baseEnd_960714 < baseStart_960714 := by decide
  rcases family_descends (prefixWord ++ tailWord_960714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960737 : List Nat := [1, 2, 3, 1, 3, 1, 4, 3, 5]
def baseStart_960737 : Nat := 118140960795 + 960737 * 2 ^ 59
def prefixEnd_960737 : Nat := 4983230072969 + 3 ^ 40 * 960737 * 2
def baseEnd_960737 : Nat := 54813318173190316196573

theorem tailTrace_960737 : CollatzResearch.WordTrace tailWord_960737 prefixEnd_960737 54813318173190316196573 := by
  unfold tailWord_960737
  simp only [CollatzResearch.WordTrace]
  refine ⟨35040957120421404661568465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23360638080280936441045643 35040957120421404661568465)
  ·
    refine ⟨26280717840316053496176349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35040957120421404661568465 26280717840316053496176349)
    ·
      refine ⟨9855269190118520061066131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26280717840316053496176349 9855269190118520061066131)
      ·
        refine ⟨14782903785177780091599197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9855269190118520061066131 14782903785177780091599197)
        ·
          refine ⟨5543588919441667534349699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14782903785177780091599197 5543588919441667534349699)
          ·
            refine ⟨8315383379162501301524549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5543588919441667534349699 8315383379162501301524549)
            ·
              refine ⟨1559134383592968994035853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8315383379162501301524549 1559134383592968994035853)
              ·
                refine ⟨584675393847363372763445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1559134383592968994035853 584675393847363372763445)
                ·
                  refine ⟨54813318173190316196573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 584675393847363372763445 54813318173190316196573)
                  ·
                    rfl

theorem cell23_960737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 3, 5].length) (baseStart_960737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_960737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_960737 prefixEnd_960737 := by exact prefixLift 960737
  have htrace : WordTrace (prefixWord ++ tailWord_960737) baseStart_960737 baseEnd_960737 := by
    simpa [prefixWord, tailWord_960737, baseEnd_960737] using wordTrace_append hprefix tailTrace_960737
  have hstable : (prefixWord ++ tailWord_960737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960737).length < 2 ^ (prefixWord ++ tailWord_960737).sum := by decide
  have hdescent : baseEnd_960737 < baseStart_960737 := by decide
  rcases family_descends (prefixWord ++ tailWord_960737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960750 : List Nat := [4, 1, 2, 1, 1, 1, 1, 3, 4, 5]
def baseStart_960750 : Nat := 118140960795 + 960750 * 2 ^ 59
def prefixEnd_960750 : Nat := 4983230072969 + 3 ^ 40 * 960750 * 2
def baseEnd_960750 : Nat := 164442179602407098302199

theorem tailTrace_960750 : CollatzResearch.WordTrace tailWord_960750 prefixEnd_960750 164442179602407098302199 := by
  unfold tailWord_960750
  simp only [CollatzResearch.WordTrace]
  refine ⟨4380178908671788485223963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23360954179582871921194469 4380178908671788485223963)
  ·
    refine ⟨6570268363007682727835945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4380178908671788485223963 6570268363007682727835945)
    ·
      refine ⟨4927701272255762045876959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6570268363007682727835945 4927701272255762045876959)
      ·
        refine ⟨7391551908383643068815439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4927701272255762045876959 7391551908383643068815439)
        ·
          refine ⟨11087327862575464603223159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7391551908383643068815439 11087327862575464603223159)
          ·
            refine ⟨16630991793863196904834739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11087327862575464603223159 16630991793863196904834739)
            ·
              refine ⟨24946487690794795357252109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16630991793863196904834739 24946487690794795357252109)
              ·
                refine ⟨9354932884048048258969541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24946487690794795357252109 9354932884048048258969541)
                ·
                  refine ⟨1754049915759009048556789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9354932884048048258969541 1754049915759009048556789)
                  ·
                    refine ⟨164442179602407098302199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1754049915759009048556789 164442179602407098302199)
                    ·
                      rfl

theorem cell23_960750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_960750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_960750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_960750 prefixEnd_960750 := by exact prefixLift 960750
  have htrace : WordTrace (prefixWord ++ tailWord_960750) baseStart_960750 baseEnd_960750 := by
    simpa [prefixWord, tailWord_960750, baseEnd_960750] using wordTrace_append hprefix tailTrace_960750
  have hstable : (prefixWord ++ tailWord_960750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960750).length < 2 ^ (prefixWord ++ tailWord_960750).sum := by decide
  have hdescent : baseEnd_960750 < baseStart_960750 := by decide
  rcases family_descends (prefixWord ++ tailWord_960750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960877 : List Nat := [1, 5, 1, 1, 1, 2, 1, 1, 5, 1, 4]
def baseStart_960877 : Nat := 118140960795 + 960877 * 2 ^ 59
def prefixEnd_960877 : Nat := 4983230072969 + 3 ^ 40 * 960877 * 2
def baseEnd_960877 : Nat := 493391750850342298018513

theorem tailTrace_960877 : CollatzResearch.WordTrace tailWord_960877 prefixEnd_960877 493391750850342298018513 := by
  unfold tailWord_960877
  simp only [CollatzResearch.WordTrace]
  refine ⟨35046063339914208571664885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23364042226609472381109923 35046063339914208571664885)
  ·
    refine ⟨3285568438116957053593583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35046063339914208571664885 3285568438116957053593583)
    ·
      refine ⟨4928352657175435580390375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3285568438116957053593583 4928352657175435580390375)
      ·
        refine ⟨7392528985763153370585563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4928352657175435580390375 7392528985763153370585563)
        ·
          refine ⟨11088793478644730055878345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7392528985763153370585563 11088793478644730055878345)
          ·
            refine ⟨8316595108983547541908759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11088793478644730055878345 8316595108983547541908759)
            ·
              refine ⟨12474892663475321312863139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8316595108983547541908759 12474892663475321312863139)
              ·
                refine ⟨18712338995212981969294709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12474892663475321312863139 18712338995212981969294709)
                ·
                  refine ⟨1754281780801217059621379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18712338995212981969294709 1754281780801217059621379)
                  ·
                    refine ⟨2631422671201825589432069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1754281780801217059621379 2631422671201825589432069)
                    ·
                      refine ⟨493391750850342298018513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2631422671201825589432069 493391750850342298018513)
                      ·
                        rfl

theorem cell23_960877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_960877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_960877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_960877 prefixEnd_960877 := by exact prefixLift 960877
  have htrace : WordTrace (prefixWord ++ tailWord_960877) baseStart_960877 baseEnd_960877 := by
    simpa [prefixWord, tailWord_960877, baseEnd_960877] using wordTrace_append hprefix tailTrace_960877
  have hstable : (prefixWord ++ tailWord_960877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960877).length < 2 ^ (prefixWord ++ tailWord_960877).sum := by decide
  have hdescent : baseEnd_960877 < baseStart_960877 := by decide
  rcases family_descends (prefixWord ++ tailWord_960877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960898 : List Nat := [3, 4, 2, 1, 2, 1, 1, 1, 1, 5, 2]
def baseStart_960898 : Nat := 118140960795 + 960898 * 2 ^ 59
def prefixEnd_960898 : Nat := 4983230072969 + 3 ^ 40 * 960898 * 2
def baseEnd_960898 : Nat := 493402533944086715855917

theorem tailTrace_960898 : CollatzResearch.WordTrace tailWord_960898 prefixEnd_960898 493402533944086715855917 := by
  unfold tailWord_960898
  simp only [CollatzResearch.WordTrace]
  refine ⟨8761707318209532289544837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23364552848558752772119565 8761707318209532289544837)
  ·
    refine ⟨1642820122164287304289657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8761707318209532289544837 1642820122164287304289657)
    ·
      refine ⟨1232115091623215478217243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1642820122164287304289657 1232115091623215478217243)
      ·
        refine ⟨1848172637434823217325865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1232115091623215478217243 1848172637434823217325865)
        ·
          refine ⟨1386129478076117412994399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1848172637434823217325865 1386129478076117412994399)
          ·
            refine ⟨2079194217114176119491599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1386129478076117412994399 2079194217114176119491599)
            ·
              refine ⟨3118791325671264179237399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2079194217114176119491599 3118791325671264179237399)
              ·
                refine ⟨4678186988506896268856099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3118791325671264179237399 4678186988506896268856099)
                ·
                  refine ⟨7017280482760344403284149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4678186988506896268856099 7017280482760344403284149)
                  ·
                    refine ⟨657870045258782287807889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7017280482760344403284149 657870045258782287807889)
                    ·
                      refine ⟨493402533944086715855917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 657870045258782287807889 493402533944086715855917)
                      ·
                        rfl

theorem cell23_960898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_960898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_960898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_960898 prefixEnd_960898 := by exact prefixLift 960898
  have htrace : WordTrace (prefixWord ++ tailWord_960898) baseStart_960898 baseEnd_960898 := by
    simpa [prefixWord, tailWord_960898, baseEnd_960898] using wordTrace_append hprefix tailTrace_960898
  have hstable : (prefixWord ++ tailWord_960898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960898).length < 2 ^ (prefixWord ++ tailWord_960898).sum := by decide
  have hdescent : baseEnd_960898 < baseStart_960898 := by decide
  rcases family_descends (prefixWord ++ tailWord_960898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960907 : List Nat := [1, 1, 1, 1, 4, 4, 2, 2, 1, 2, 4]
def baseStart_960907 : Nat := 118140960795 + 960907 * 2 ^ 59
def prefixEnd_960907 : Nat := 4983230072969 + 3 ^ 40 * 960907 * 2
def baseEnd_960907 : Nat := 493407155269977180643375

theorem tailTrace_960907 : CollatzResearch.WordTrace tailWord_960907 prefixEnd_960907 493407155269977180643375 := by
  unfold tailWord_960907
  simp only [CollatzResearch.WordTrace]
  refine ⟨35047157529805523695256975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23364771686537015796837983 35047157529805523695256975)
  ·
    refine ⟨52570736294708285542885463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35047157529805523695256975 52570736294708285542885463)
    ·
      refine ⟨78856104442062428314328195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52570736294708285542885463 78856104442062428314328195)
      ·
        refine ⟨118284156663093642471492293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78856104442062428314328195 118284156663093642471492293)
        ·
          refine ⟨22178279374330057963404805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118284156663093642471492293 22178279374330057963404805)
          ·
            refine ⟨4158427382686885868138401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22178279374330057963404805 4158427382686885868138401)
            ·
              refine ⟨3118820537015164401103801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4158427382686885868138401 3118820537015164401103801)
              ·
                refine ⟨2339115402761373300827851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3118820537015164401103801 2339115402761373300827851)
                ·
                  refine ⟨3508673104142059951241777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2339115402761373300827851 3508673104142059951241777)
                  ·
                    refine ⟨2631504828106544963431333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3508673104142059951241777 2631504828106544963431333)
                    ·
                      refine ⟨493407155269977180643375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2631504828106544963431333 493407155269977180643375)
                      ·
                        rfl

theorem cell23_960907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 2, 1, 2, 4].length) (baseStart_960907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_960907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_960907 prefixEnd_960907 := by exact prefixLift 960907
  have htrace : WordTrace (prefixWord ++ tailWord_960907) baseStart_960907 baseEnd_960907 := by
    simpa [prefixWord, tailWord_960907, baseEnd_960907] using wordTrace_append hprefix tailTrace_960907
  have hstable : (prefixWord ++ tailWord_960907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960907).length < 2 ^ (prefixWord ++ tailWord_960907).sum := by decide
  have hdescent : baseEnd_960907 < baseStart_960907 := by decide
  rcases family_descends (prefixWord ++ tailWord_960907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960928 : List Nat := [2, 1, 1, 4, 1, 3, 2, 4, 1, 2, 2]
def baseStart_960928 : Nat := 118140960795 + 960928 * 2 ^ 59
def prefixEnd_960928 : Nat := 4983230072969 + 3 ^ 40 * 960928 * 2
def baseEnd_960928 : Nat := 493417938363721598480779

theorem tailTrace_960928 : CollatzResearch.WordTrace tailWord_960928 prefixEnd_960928 493417938363721598480779 := by
  unfold tailWord_960928
  simp only [CollatzResearch.WordTrace]
  refine ⟨17523961731364722140885719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23365282308486296187847625 17523961731364722140885719)
  ·
    refine ⟨26285942597047083211328579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17523961731364722140885719 26285942597047083211328579)
    ·
      refine ⟨39428913895570624816992869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26285942597047083211328579 39428913895570624816992869)
      ·
        refine ⟨7392921355419492153186163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39428913895570624816992869 7392921355419492153186163)
        ·
          refine ⟨11089382033129238229779245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7392921355419492153186163 11089382033129238229779245)
          ·
            refine ⟨4158518262423464336167217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11089382033129238229779245 4158518262423464336167217)
            ·
              refine ⟨3118888696817598252125413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4158518262423464336167217 3118888696817598252125413)
              ·
                refine ⟨584791630653299672273515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3118888696817598252125413 584791630653299672273515)
                ·
                  refine ⟨877187445979949508410273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 584791630653299672273515 877187445979949508410273)
                  ·
                    refine ⟨657890584484962131307705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 877187445979949508410273 657890584484962131307705)
                    ·
                      refine ⟨493417938363721598480779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 657890584484962131307705 493417938363721598480779)
                      ·
                        rfl

theorem cell23_960928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 4, 1, 2, 2].length) (baseStart_960928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_960928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_960928 prefixEnd_960928 := by exact prefixLift 960928
  have htrace : WordTrace (prefixWord ++ tailWord_960928) baseStart_960928 baseEnd_960928 := by
    simpa [prefixWord, tailWord_960928, baseEnd_960928] using wordTrace_append hprefix tailTrace_960928
  have hstable : (prefixWord ++ tailWord_960928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960928).length < 2 ^ (prefixWord ++ tailWord_960928).sum := by decide
  have hdescent : baseEnd_960928 < baseStart_960928 := by decide
  rcases family_descends (prefixWord ++ tailWord_960928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960954 : List Nat := [3, 1, 1, 1, 2, 1, 1, 5, 3, 3, 2]
def baseStart_960954 : Nat := 118140960795 + 960954 * 2 ^ 59
def prefixEnd_960954 : Nat := 4983230072969 + 3 ^ 40 * 960954 * 2
def baseEnd_960954 : Nat := 493431288860738496755659

theorem tailTrace_960954 : CollatzResearch.WordTrace tailWord_960954 prefixEnd_960954 493431288860738496755659 := by
  unfold tailWord_960954
  simp only [CollatzResearch.WordTrace]
  refine ⟨8762217940158812680554479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23365914507090167148145277 8762217940158812680554479)
  ·
    refine ⟨13143326910238219020831719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8762217940158812680554479 13143326910238219020831719)
    ·
      refine ⟨19714990365357328531247579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13143326910238219020831719 19714990365357328531247579)
      ·
        refine ⟨29572485548035992796871369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19714990365357328531247579 29572485548035992796871369)
        ·
          refine ⟨22179364161026994597653527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29572485548035992796871369 22179364161026994597653527)
          ·
            refine ⟨33269046241540491896480291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22179364161026994597653527 33269046241540491896480291)
            ·
              refine ⟨49903569362310737844720437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33269046241540491896480291 49903569362310737844720437)
              ·
                refine ⟨4678459627716631672942541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49903569362310737844720437 4678459627716631672942541)
                ·
                  refine ⟨1754422360393736877353453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4678459627716631672942541 1754422360393736877353453)
                  ·
                    refine ⟨657908385147651329007545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1754422360393736877353453 657908385147651329007545)
                    ·
                      refine ⟨493431288860738496755659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 657908385147651329007545 493431288860738496755659)
                      ·
                        rfl

theorem cell23_960954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 3, 3, 2].length) (baseStart_960954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_960954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_960954 prefixEnd_960954 := by exact prefixLift 960954
  have htrace : WordTrace (prefixWord ++ tailWord_960954) baseStart_960954 baseEnd_960954 := by
    simpa [prefixWord, tailWord_960954, baseEnd_960954] using wordTrace_append hprefix tailTrace_960954
  have hstable : (prefixWord ++ tailWord_960954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960954).length < 2 ^ (prefixWord ++ tailWord_960954).sum := by decide
  have hdescent : baseEnd_960954 < baseStart_960954 := by decide
  rcases family_descends (prefixWord ++ tailWord_960954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960957 : List Nat := [1, 4, 1, 2, 2, 2, 1, 1, 2, 2, 5]
def baseStart_960957 : Nat := 118140960795 + 960957 * 2 ^ 59
def prefixEnd_960957 : Nat := 4983230072969 + 3 ^ 40 * 960957 * 2
def baseEnd_960957 : Nat := 493432829302701985018145

theorem tailTrace_960957 : CollatzResearch.WordTrace tailWord_960957 prefixEnd_960957 493432829302701985018145 := by
  unfold tailWord_960957
  simp only [CollatzResearch.WordTrace]
  refine ⟨35048981179624382234577125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23365987453082921489718083 35048981179624382234577125)
  ·
    refine ⟨6571683971179571668983211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35048981179624382234577125 6571683971179571668983211)
    ·
      refine ⟨9857525956769357503474817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6571683971179571668983211 9857525956769357503474817)
      ·
        refine ⟨7393144467577018127606113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9857525956769357503474817 7393144467577018127606113)
        ·
          refine ⟨5544858350682763595704585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7393144467577018127606113 5544858350682763595704585)
          ·
            refine ⟨4158643763012072696778439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5544858350682763595704585 4158643763012072696778439)
            ·
              refine ⟨6237965644518109045167659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4158643763012072696778439 6237965644518109045167659)
              ·
                refine ⟨9356948466777163567751489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6237965644518109045167659 9356948466777163567751489)
                ·
                  refine ⟨7017711350082872675813617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9356948466777163567751489 7017711350082872675813617)
                  ·
                    refine ⟨5263283512562154506860213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7017711350082872675813617 5263283512562154506860213)
                    ·
                      refine ⟨493432829302701985018145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5263283512562154506860213 493432829302701985018145)
                      ·
                        rfl

theorem cell23_960957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_960957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_960957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_960957 prefixEnd_960957 := by exact prefixLift 960957
  have htrace : WordTrace (prefixWord ++ tailWord_960957) baseStart_960957 baseEnd_960957 := by
    simpa [prefixWord, tailWord_960957, baseEnd_960957] using wordTrace_append hprefix tailTrace_960957
  have hstable : (prefixWord ++ tailWord_960957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960957).length < 2 ^ (prefixWord ++ tailWord_960957).sum := by decide
  have hdescent : baseEnd_960957 < baseStart_960957 := by decide
  rcases family_descends (prefixWord ++ tailWord_960957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960995 : List Nat := [1, 1, 1, 6, 3, 2, 2, 1, 2, 1, 3]
def baseStart_960995 : Nat := 118140960795 + 960995 * 2 ^ 59
def prefixEnd_960995 : Nat := 4983230072969 + 3 ^ 40 * 960995 * 2
def baseEnd_960995 : Nat := 493452341567572836342971

theorem tailTrace_960995 : CollatzResearch.WordTrace tailWord_960995 prefixEnd_960995 493452341567572836342971 := by
  unfold tailWord_960995
  simp only [CollatzResearch.WordTrace]
  refine ⟨35050367153486714724460439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23366911435657809816306959 35050367153486714724460439)
  ·
    refine ⟨52575550730230072086690659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35050367153486714724460439 52575550730230072086690659)
    ·
      refine ⟨78863326095345108130035989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52575550730230072086690659 78863326095345108130035989)
      ·
        refine ⟨3696718410719301943595437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 78863326095345108130035989 3696718410719301943595437)
        ·
          refine ⟨1386269404019738228848289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3696718410719301943595437 1386269404019738228848289)
          ·
            refine ⟨1039702053014803671636217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1386269404019738228848289 1039702053014803671636217)
            ·
              refine ⟨779776539761102753727163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1039702053014803671636217 779776539761102753727163)
              ·
                refine ⟨1169664809641654130590745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 779776539761102753727163 1169664809641654130590745)
                ·
                  refine ⟨877248607231240597943059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1169664809641654130590745 877248607231240597943059)
                  ·
                    refine ⟨1315872910846860896914589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 877248607231240597943059 1315872910846860896914589)
                    ·
                      refine ⟨493452341567572836342971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1315872910846860896914589 493452341567572836342971)
                      ·
                        rfl

theorem cell23_960995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 2, 1, 2, 1, 3].length) (baseStart_960995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_960995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_960995 prefixEnd_960995 := by exact prefixLift 960995
  have htrace : WordTrace (prefixWord ++ tailWord_960995) baseStart_960995 baseEnd_960995 := by
    simpa [prefixWord, tailWord_960995, baseEnd_960995] using wordTrace_append hprefix tailTrace_960995
  have hstable : (prefixWord ++ tailWord_960995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960995).length < 2 ^ (prefixWord ++ tailWord_960995).sum := by decide
  have hdescent : baseEnd_960995 < baseStart_960995 := by decide
  rcases family_descends (prefixWord ++ tailWord_960995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961005 : List Nat := [1, 5, 1, 3, 1, 3, 1, 2, 1, 3, 2]
def baseStart_961005 : Nat := 118140960795 + 961005 * 2 ^ 59
def prefixEnd_961005 : Nat := 4983230072969 + 3 ^ 40 * 961005 * 2
def baseEnd_961005 : Nat := 493457476374117797217925

theorem tailTrace_961005 : CollatzResearch.WordTrace tailWord_961005 prefixEnd_961005 493457476374117797217925 := by
  unfold tailWord_961005
  simp only [CollatzResearch.WordTrace]
  refine ⟨35050731883450486432324469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23367154588966990954882979 35050731883450486432324469)
  ·
    refine ⟨3286006114073483103030419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35050731883450486432324469 3286006114073483103030419)
    ·
      refine ⟨4929009171110224654545629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3286006114073483103030419 4929009171110224654545629)
      ·
        refine ⟨1848378439166334245454611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4929009171110224654545629 1848378439166334245454611)
        ·
          refine ⟨2772567658749501368181917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1848378439166334245454611 2772567658749501368181917)
          ·
            refine ⟨1039712872031063013068219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2772567658749501368181917 1039712872031063013068219)
            ·
              refine ⟨1559569308046594519602329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1039712872031063013068219 1559569308046594519602329)
              ·
                refine ⟨1169676981034945889701747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1559569308046594519602329 1169676981034945889701747)
                ·
                  refine ⟨1754515471552418834552621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1169676981034945889701747 1754515471552418834552621)
                  ·
                    refine ⟨657943301832157062957233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1754515471552418834552621 657943301832157062957233)
                    ·
                      refine ⟨493457476374117797217925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 657943301832157062957233 493457476374117797217925)
                      ·
                        rfl

theorem cell23_961005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_961005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_961005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_961005 prefixEnd_961005 := by exact prefixLift 961005
  have htrace : WordTrace (prefixWord ++ tailWord_961005) baseStart_961005 baseEnd_961005 := by
    simpa [prefixWord, tailWord_961005, baseEnd_961005] using wordTrace_append hprefix tailTrace_961005
  have hstable : (prefixWord ++ tailWord_961005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961005).length < 2 ^ (prefixWord ++ tailWord_961005).sum := by decide
  have hdescent : baseEnd_961005 < baseStart_961005 := by decide
  rcases family_descends (prefixWord ++ tailWord_961005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961034 : List Nat := [3, 1, 2, 2, 2, 1, 2, 2, 2, 3, 3]
def baseStart_961034 : Nat := 118140960795 + 961034 * 2 ^ 59
def prefixEnd_961034 : Nat := 4983230072969 + 3 ^ 40 * 961034 * 2
def baseEnd_961034 : Nat := 493472367313098183755291

theorem tailTrace_961034 : CollatzResearch.WordTrace tailWord_961034 prefixEnd_961034 493472367313098183755291 := by
  unfold tailWord_961034
  simp only [CollatzResearch.WordTrace]
  refine ⟨8762947400086356096282539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23367859733563616256753437 8762947400086356096282539)
  ·
    refine ⟨13144421100129534144423809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8762947400086356096282539 13144421100129534144423809)
    ·
      refine ⟨9858315825097150608317857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13144421100129534144423809 9858315825097150608317857)
      ·
        refine ⟨7393736868822862956238393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9858315825097150608317857 7393736868822862956238393)
        ·
          refine ⟨5545302651617147217178795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7393736868822862956238393 5545302651617147217178795)
          ·
            refine ⟨8317953977425720825768193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5545302651617147217178795 8317953977425720825768193)
            ·
              refine ⟨6238465483069290619326145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8317953977425720825768193 6238465483069290619326145)
              ·
                refine ⟨4678849112301967964494609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6238465483069290619326145 4678849112301967964494609)
                ·
                  refine ⟨3509136834226475973370957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4678849112301967964494609 3509136834226475973370957)
                  ·
                    refine ⟨1315926312834928490014109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3509136834226475973370957 1315926312834928490014109)
                    ·
                      refine ⟨493472367313098183755291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1315926312834928490014109 493472367313098183755291)
                      ·
                        rfl

theorem cell23_961034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 2, 3, 3].length) (baseStart_961034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_961034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_961034 prefixEnd_961034 := by exact prefixLift 961034
  have htrace : WordTrace (prefixWord ++ tailWord_961034) baseStart_961034 baseEnd_961034 := by
    simpa [prefixWord, tailWord_961034, baseEnd_961034] using wordTrace_append hprefix tailTrace_961034
  have hstable : (prefixWord ++ tailWord_961034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961034).length < 2 ^ (prefixWord ++ tailWord_961034).sum := by decide
  have hdescent : baseEnd_961034 < baseStart_961034 := by decide
  rcases family_descends (prefixWord ++ tailWord_961034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961087 : List Nat := [1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 6]
def baseStart_961087 : Nat := 118140960795 + 961087 * 2 ^ 59
def prefixEnd_961087 : Nat := 4983230072969 + 3 ^ 40 * 961087 * 2
def baseEnd_961087 : Nat := 493499581787786476392547

theorem tailTrace_961087 : CollatzResearch.WordTrace tailWord_961087 prefixEnd_961087 493499581787786476392547 := by
  unfold tailWord_961087
  simp only [CollatzResearch.WordTrace]
  refine ⟨35053722669153414436809515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23369148446102276291206343 35053722669153414436809515)
  ·
    refine ⟨52580584003730121655214273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35053722669153414436809515 52580584003730121655214273)
    ·
      refine ⟨39435438002797591241410705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52580584003730121655214273 39435438002797591241410705)
      ·
        refine ⟨29576578502098193431058029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39435438002797591241410705 29576578502098193431058029)
        ·
          refine ⟨11091216938286822536646761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29576578502098193431058029 11091216938286822536646761)
          ·
            refine ⟨8318412703715116902485071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11091216938286822536646761 8318412703715116902485071)
            ·
              refine ⟨12477619055572675353727607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8318412703715116902485071 12477619055572675353727607)
              ·
                refine ⟨18716428583359013030591411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12477619055572675353727607 18716428583359013030591411)
                ·
                  refine ⟨28074642875038519545887117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18716428583359013030591411 28074642875038519545887117)
                  ·
                    refine ⟨10527991078139444829707669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28074642875038519545887117 10527991078139444829707669)
                    ·
                      refine ⟨493499581787786476392547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10527991078139444829707669 493499581787786476392547)
                      ·
                        rfl

theorem cell23_961087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 6].length) (baseStart_961087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_961087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_961087 prefixEnd_961087 := by exact prefixLift 961087
  have htrace : WordTrace (prefixWord ++ tailWord_961087) baseStart_961087 baseEnd_961087 := by
    simpa [prefixWord, tailWord_961087, baseEnd_961087] using wordTrace_append hprefix tailTrace_961087
  have hstable : (prefixWord ++ tailWord_961087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961087).length < 2 ^ (prefixWord ++ tailWord_961087).sum := by decide
  have hdescent : baseEnd_961087 < baseStart_961087 := by decide
  rcases family_descends (prefixWord ++ tailWord_961087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961124 : List Nat := [2, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3]
def baseStart_961124 : Nat := 118140960795 + 961124 * 2 ^ 59
def prefixEnd_961124 : Nat := 4983230072969 + 3 ^ 40 * 961124 * 2
def baseEnd_961124 : Nat := 493518580572002831629877

theorem tailTrace_961124 : CollatzResearch.WordTrace tailWord_961124 prefixEnd_961124 493518580572002831629877 := by
  unfold tailWord_961124
  simp only [CollatzResearch.WordTrace]
  refine ⟨17527536085009684877953213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23370048113346246503937617 17527536085009684877953213)
  ·
    refine ⟨6572826031878631829232455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17527536085009684877953213 6572826031878631829232455)
    ·
      refine ⟨9859239047817947743848683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6572826031878631829232455 9859239047817947743848683)
      ·
        refine ⟨14788858571726921615773025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9859239047817947743848683 14788858571726921615773025)
        ·
          refine ⟨11091643928795191211829769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14788858571726921615773025 11091643928795191211829769)
          ·
            refine ⟨8318732946596393408872327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11091643928795191211829769 8318732946596393408872327)
            ·
              refine ⟨12478099419894590113308491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8318732946596393408872327 12478099419894590113308491)
              ·
                refine ⟨18717149129841885169962737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12478099419894590113308491 18717149129841885169962737)
                ·
                  refine ⟨14037861847381413877472053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18717149129841885169962737 14037861847381413877472053)
                  ·
                    refine ⟨1316049548192007551013005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14037861847381413877472053 1316049548192007551013005)
                    ·
                      refine ⟨493518580572002831629877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1316049548192007551013005 493518580572002831629877)
                      ·
                        rfl

theorem cell23_961124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3].length) (baseStart_961124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_961124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_961124 prefixEnd_961124 := by exact prefixLift 961124
  have htrace : WordTrace (prefixWord ++ tailWord_961124) baseStart_961124 baseEnd_961124 := by
    simpa [prefixWord, tailWord_961124, baseEnd_961124] using wordTrace_append hprefix tailTrace_961124
  have hstable : (prefixWord ++ tailWord_961124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961124).length < 2 ^ (prefixWord ++ tailWord_961124).sum := by decide
  have hdescent : baseEnd_961124 < baseStart_961124 := by decide
  rcases family_descends (prefixWord ++ tailWord_961124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961178 : List Nat := [3, 1, 1, 6, 1, 1, 1, 1, 3, 5]
def baseStart_961178 : Nat := 118140960795 + 961178 * 2 ^ 59
def prefixEnd_961178 : Nat := 4983230072969 + 3 ^ 40 * 961178 * 2
def baseEnd_961178 : Nat := 164515436175781873451543

theorem tailTrace_961178 : CollatzResearch.WordTrace tailWord_961178 prefixEnd_961178 164515436175781873451543 := by
  unfold tailWord_961178
  simp only [CollatzResearch.WordTrace]
  refine ⟨8764260427955934244593047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23371361141215824652248125 8764260427955934244593047)
  ·
    refine ⟨13146390641933901366889571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8764260427955934244593047 13146390641933901366889571)
    ·
      refine ⟨19719585962900852050334357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13146390641933901366889571 19719585962900852050334357)
      ·
        refine ⟨924355592010977439859423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 19719585962900852050334357 924355592010977439859423)
        ·
          refine ⟨1386533388016466159789135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 924355592010977439859423 1386533388016466159789135)
          ·
            refine ⟨2079800082024699239683703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1386533388016466159789135 2079800082024699239683703)
            ·
              refine ⟨3119700123037048859525555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2079800082024699239683703 3119700123037048859525555)
              ·
                refine ⟨4679550184555573289288333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3119700123037048859525555 4679550184555573289288333)
                ·
                  refine ⟨1754831319208339983483125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4679550184555573289288333 1754831319208339983483125)
                  ·
                    refine ⟨164515436175781873451543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1754831319208339983483125 164515436175781873451543)
                    ·
                      rfl

theorem cell23_961178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 3, 5].length) (baseStart_961178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_961178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_961178 prefixEnd_961178 := by exact prefixLift 961178
  have htrace : WordTrace (prefixWord ++ tailWord_961178) baseStart_961178 baseEnd_961178 := by
    simpa [prefixWord, tailWord_961178, baseEnd_961178] using wordTrace_append hprefix tailTrace_961178
  have hstable : (prefixWord ++ tailWord_961178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961178).length < 2 ^ (prefixWord ++ tailWord_961178).sum := by decide
  have hdescent : baseEnd_961178 < baseStart_961178 := by decide
  rcases family_descends (prefixWord ++ tailWord_961178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961181 : List Nat := [1, 4, 2, 1, 1, 1, 2, 1, 2, 6, 2]
def baseStart_961181 : Nat := 118140960795 + 961181 * 2 ^ 59
def prefixEnd_961181 : Nat := 4983230072969 + 3 ^ 40 * 961181 * 2
def baseEnd_961181 : Nat := 493547848969309108617115

theorem tailTrace_961181 : CollatzResearch.WordTrace tailWord_961181 prefixEnd_961181 493547848969309108617115 := by
  unfold tailWord_961181
  simp only [CollatzResearch.WordTrace]
  refine ⟨35057151130812868490731397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23371434087208578993820931 35057151130812868490731397)
  ·
    refine ⟨6573215837027412842012137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35057151130812868490731397 6573215837027412842012137)
    ·
      refine ⟨4929911877770559631509103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6573215837027412842012137 4929911877770559631509103)
      ·
        refine ⟨7394867816655839447263655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4929911877770559631509103 7394867816655839447263655)
        ·
          refine ⟨11092301724983759170895483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7394867816655839447263655 11092301724983759170895483)
          ·
            refine ⟨16638452587475638756343225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11092301724983759170895483 16638452587475638756343225)
            ·
              refine ⟨12478839440606729067257419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16638452587475638756343225 12478839440606729067257419)
              ·
                refine ⟨18718259160910093600886129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12478839440606729067257419 18718259160910093600886129)
                ·
                  refine ⟨14038694370682570200664597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18718259160910093600886129 14038694370682570200664597)
                  ·
                    refine ⟨658063798625745478156153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14038694370682570200664597 658063798625745478156153)
                    ·
                      refine ⟨493547848969309108617115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 658063798625745478156153 493547848969309108617115)
                      ·
                        rfl

theorem cell23_961181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 6, 2].length) (baseStart_961181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_961181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_961181 prefixEnd_961181 := by exact prefixLift 961181
  have htrace : WordTrace (prefixWord ++ tailWord_961181) baseStart_961181 baseEnd_961181 := by
    simpa [prefixWord, tailWord_961181, baseEnd_961181] using wordTrace_append hprefix tailTrace_961181
  have hstable : (prefixWord ++ tailWord_961181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961181).length < 2 ^ (prefixWord ++ tailWord_961181).sum := by decide
  have hdescent : baseEnd_961181 < baseStart_961181 := by decide
  rcases family_descends (prefixWord ++ tailWord_961181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961185 : List Nat := [1, 2, 3, 3, 3, 1, 2, 1, 2, 3, 2]
def baseStart_961185 : Nat := 118140960795 + 961185 * 2 ^ 59
def prefixEnd_961185 : Nat := 4983230072969 + 3 ^ 40 * 961185 * 2
def baseEnd_961185 : Nat := 493549902891927092967097

theorem tailTrace_961185 : CollatzResearch.WordTrace tailWord_961185 prefixEnd_961185 493549902891927092967097 := by
  unfold tailWord_961185
  simp only [CollatzResearch.WordTrace]
  refine ⟨35057297022798377173877009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23371531348532251449251339 35057297022798377173877009)
  ·
    refine ⟨26292972767098782880407757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35057297022798377173877009 26292972767098782880407757)
    ·
      refine ⟨9859864787662043580152909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26292972767098782880407757 9859864787662043580152909)
      ·
        refine ⟨3697449295373266342557341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9859864787662043580152909 3697449295373266342557341)
        ·
          refine ⟨1386543485764974878459003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3697449295373266342557341 1386543485764974878459003)
          ·
            refine ⟨2079815228647462317688505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1386543485764974878459003 2079815228647462317688505)
            ·
              refine ⟨1559861421485596738266379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2079815228647462317688505 1559861421485596738266379)
              ·
                refine ⟨2339792132228395107399569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1559861421485596738266379 2339792132228395107399569)
                ·
                  refine ⟨1754844099171296330549677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2339792132228395107399569 1754844099171296330549677)
                  ·
                    refine ⟨658066537189236123956129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1754844099171296330549677 658066537189236123956129)
                    ·
                      refine ⟨493549902891927092967097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 658066537189236123956129 493549902891927092967097)
                      ·
                        rfl

theorem cell23_961185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 1, 2, 3, 2].length) (baseStart_961185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_961185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_961185 prefixEnd_961185 := by exact prefixLift 961185
  have htrace : WordTrace (prefixWord ++ tailWord_961185) baseStart_961185 baseEnd_961185 := by
    simpa [prefixWord, tailWord_961185, baseEnd_961185] using wordTrace_append hprefix tailTrace_961185
  have hstable : (prefixWord ++ tailWord_961185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961185).length < 2 ^ (prefixWord ++ tailWord_961185).sum := by decide
  have hdescent : baseEnd_961185 < baseStart_961185 := by decide
  rcases family_descends (prefixWord ++ tailWord_961185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961228 : List Nat := [2, 2, 1, 5, 1, 2, 2, 1, 1, 2, 4]
def baseStart_961228 : Nat := 118140960795 + 961228 * 2 ^ 59
def prefixEnd_961228 : Nat := 4983230072969 + 3 ^ 40 * 961228 * 2
def baseEnd_961228 : Nat := 493571982560070424729399

theorem tailTrace_961228 : CollatzResearch.WordTrace tailWord_961228 prefixEnd_961228 493571982560070424729399 := by
  unfold tailWord_961228
  simp only [CollatzResearch.WordTrace]
  refine ⟨17529432680821297758846169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23372576907761730345128225 17529432680821297758846169)
  ·
    refine ⟨13147074510615973319134627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17529432680821297758846169 13147074510615973319134627)
    ·
      refine ⟨19720611765923959978701941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13147074510615973319134627 19720611765923959978701941)
      ·
        refine ⟨1848807353055371248003307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19720611765923959978701941 1848807353055371248003307)
        ·
          refine ⟨2773211029583056872004961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1848807353055371248003307 2773211029583056872004961)
          ·
            refine ⟨2079908272187292654003721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2773211029583056872004961 2079908272187292654003721)
            ·
              refine ⟨1559931204140469490502791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2079908272187292654003721 1559931204140469490502791)
              ·
                refine ⟨2339896806210704235754187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1559931204140469490502791 2339896806210704235754187)
                ·
                  refine ⟨3509845209316056353631281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2339896806210704235754187 3509845209316056353631281)
                  ·
                    refine ⟨2632383906987042265223461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3509845209316056353631281 2632383906987042265223461)
                    ·
                      refine ⟨493571982560070424729399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2632383906987042265223461 493571982560070424729399)
                      ·
                        rfl

theorem cell23_961228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_961228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_961228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_961228 prefixEnd_961228 := by exact prefixLift 961228
  have htrace : WordTrace (prefixWord ++ tailWord_961228) baseStart_961228 baseEnd_961228 := by
    simpa [prefixWord, tailWord_961228, baseEnd_961228] using wordTrace_append hprefix tailTrace_961228
  have hstable : (prefixWord ++ tailWord_961228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961228).length < 2 ^ (prefixWord ++ tailWord_961228).sum := by decide
  have hdescent : baseEnd_961228 < baseStart_961228 := by decide
  rcases family_descends (prefixWord ++ tailWord_961228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961231 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 8, 1, 3]
def baseStart_961231 : Nat := 118140960795 + 961231 * 2 ^ 59
def prefixEnd_961231 : Nat := 4983230072969 + 3 ^ 40 * 961231 * 2
def baseEnd_961231 : Nat := 493573523002033912991885

theorem tailTrace_961231 : CollatzResearch.WordTrace tailWord_961231 prefixEnd_961231 493573523002033912991885 := by
  unfold tailWord_961231
  simp only [CollatzResearch.WordTrace]
  refine ⟨35058974780631727030051547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23372649853754484686701031 35058974780631727030051547)
  ·
    refine ⟨52588462170947590545077321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35058974780631727030051547 52588462170947590545077321)
    ·
      refine ⟨39441346628210692908807991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52588462170947590545077321 39441346628210692908807991)
      ·
        refine ⟨59162019942316039363211987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39441346628210692908807991 59162019942316039363211987)
        ·
          refine ⟨88743029913474059044817981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59162019942316039363211987 88743029913474059044817981)
          ·
            refine ⟨33278636217552772141806743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88743029913474059044817981 33278636217552772141806743)
            ·
              refine ⟨49917954326329158212710115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33278636217552772141806743 49917954326329158212710115)
              ·
                refine ⟨74876931489493737319065173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49917954326329158212710115 74876931489493737319065173)
                ·
                  refine ⟨877464040892504734207795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 74876931489493737319065173 877464040892504734207795)
                  ·
                    refine ⟨1316196061338757101311693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 877464040892504734207795 1316196061338757101311693)
                    ·
                      refine ⟨493573523002033912991885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1316196061338757101311693 493573523002033912991885)
                      ·
                        rfl

theorem cell23_961231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 8, 1, 3].length) (baseStart_961231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_961231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_961231 prefixEnd_961231 := by exact prefixLift 961231
  have htrace : WordTrace (prefixWord ++ tailWord_961231) baseStart_961231 baseEnd_961231 := by
    simpa [prefixWord, tailWord_961231, baseEnd_961231] using wordTrace_append hprefix tailTrace_961231
  have hstable : (prefixWord ++ tailWord_961231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961231).length < 2 ^ (prefixWord ++ tailWord_961231).sum := by decide
  have hdescent : baseEnd_961231 < baseStart_961231 := by decide
  rcases family_descends (prefixWord ++ tailWord_961231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961264 : List Nat := [2, 1, 1, 1, 3, 1, 3, 1, 4, 6]
def baseStart_961264 : Nat := 118140960795 + 961264 * 2 ^ 59
def prefixEnd_961264 : Nat := 4983230072969 + 3 ^ 40 * 961264 * 2
def baseEnd_961264 : Nat := 164530155954544094626411

theorem tailTrace_961264 : CollatzResearch.WordTrace tailWord_961264 prefixEnd_961264 164530155954544094626411 := by
  unfold tailWord_961264
  simp only [CollatzResearch.WordTrace]
  refine ⟨17530089194756086833001423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23373452259674782444001897 17530089194756086833001423)
  ·
    refine ⟨26295133792134130249502135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17530089194756086833001423 26295133792134130249502135)
    ·
      refine ⟨39442700688201195374253203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26295133792134130249502135 39442700688201195374253203)
      ·
        refine ⟨59164051032301793061379805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39442700688201195374253203 59164051032301793061379805)
        ·
          refine ⟨22186519137113172398017427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59164051032301793061379805 22186519137113172398017427)
          ·
            refine ⟨33279778705669758597026141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22186519137113172398017427 33279778705669758597026141)
            ·
              refine ⟨12479917014626159473884803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33279778705669758597026141 12479917014626159473884803)
              ·
                refine ⟨18719875521939239210827205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12479917014626159473884803 18719875521939239210827205)
                ·
                  refine ⟨3509976660363607352030101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18719875521939239210827205 3509976660363607352030101)
                  ·
                    refine ⟨164530155954544094626411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3509976660363607352030101 164530155954544094626411)
                    ·
                      rfl

theorem cell23_961264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 4, 6].length) (baseStart_961264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_961264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_961264 prefixEnd_961264 := by exact prefixLift 961264
  have htrace : WordTrace (prefixWord ++ tailWord_961264) baseStart_961264 baseEnd_961264 := by
    simpa [prefixWord, tailWord_961264, baseEnd_961264] using wordTrace_append hprefix tailTrace_961264
  have hstable : (prefixWord ++ tailWord_961264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961264).length < 2 ^ (prefixWord ++ tailWord_961264).sum := by decide
  have hdescent : baseEnd_961264 < baseStart_961264 := by decide
  rcases family_descends (prefixWord ++ tailWord_961264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961388 : List Nat := [2, 2, 1, 1, 4, 1, 2, 3, 3, 4]
def baseStart_961388 : Nat := 118140960795 + 961388 * 2 ^ 59
def prefixEnd_961388 : Nat := 4983230072969 + 3 ^ 40 * 961388 * 2
def baseEnd_961388 : Nat := 164551379821596599576221

theorem tailTrace_961388 : CollatzResearch.WordTrace tailWord_961388 prefixEnd_961388 164551379821596599576221 := by
  unfold tailWord_961388
  simp only [CollatzResearch.WordTrace]
  refine ⟨17532350520531471421758409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23376467360708628562344545 17532350520531471421758409)
  ·
    refine ⟨13149262890398603566318807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17532350520531471421758409 13149262890398603566318807)
    ·
      refine ⟨19723894335597905349478211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13149262890398603566318807 19723894335597905349478211)
      ·
        refine ⟨29585841503396858024217317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19723894335597905349478211 29585841503396858024217317)
        ·
          refine ⟨5547345281886910879540747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29585841503396858024217317 5547345281886910879540747)
          ·
            refine ⟨8321017922830366319311121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5547345281886910879540747 8321017922830366319311121)
            ·
              refine ⟨6240763442122774739483341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8321017922830366319311121 6240763442122774739483341)
              ·
                refine ⟨2340286290796040527306253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6240763442122774739483341 2340286290796040527306253)
                ·
                  refine ⟨877607359048515197739845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2340286290796040527306253 877607359048515197739845)
                  ·
                    refine ⟨164551379821596599576221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 877607359048515197739845 164551379821596599576221)
                    ·
                      rfl

theorem cell23_961388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 4].length) (baseStart_961388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_961388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_961388 prefixEnd_961388 := by exact prefixLift 961388
  have htrace : WordTrace (prefixWord ++ tailWord_961388) baseStart_961388 baseEnd_961388 := by
    simpa [prefixWord, tailWord_961388, baseEnd_961388] using wordTrace_append hprefix tailTrace_961388
  have hstable : (prefixWord ++ tailWord_961388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961388).length < 2 ^ (prefixWord ++ tailWord_961388).sum := by decide
  have hdescent : baseEnd_961388 < baseStart_961388 := by decide
  rcases family_descends (prefixWord ++ tailWord_961388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961415 : List Nat := [1, 1, 4, 2, 3, 1, 3, 1, 2, 2, 3]
def baseStart_961415 : Nat := 118140960795 + 961415 * 2 ^ 59
def prefixEnd_961415 : Nat := 4983230072969 + 3 ^ 40 * 961415 * 2
def baseEnd_961415 : Nat := 493668003442461193091039

theorem tailTrace_961415 : CollatzResearch.WordTrace tailWord_961415 prefixEnd_961415 493668003442461193091039 := by
  unfold tailWord_961415
  simp only [CollatzResearch.WordTrace]
  refine ⟨35065685811965126454749699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23377123874643417636499799 35065685811965126454749699)
  ·
    refine ⟨52598528717947689682124549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35065685811965126454749699 52598528717947689682124549)
    ·
      refine ⟨9862224134615191815398353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52598528717947689682124549 9862224134615191815398353)
      ·
        refine ⟨7396668100961393861548765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9862224134615191815398353 7396668100961393861548765)
        ·
          refine ⟨2773750537860522698080787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7396668100961393861548765 2773750537860522698080787)
          ·
            refine ⟨4160625806790784047121181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2773750537860522698080787 4160625806790784047121181)
            ·
              refine ⟨1560234677546544017670443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4160625806790784047121181 1560234677546544017670443)
              ·
                refine ⟨2340352016319816026505665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1560234677546544017670443 2340352016319816026505665)
                ·
                  refine ⟨1755264012239862019879249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2340352016319816026505665 1755264012239862019879249)
                  ·
                    refine ⟨1316448009179896514909437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1755264012239862019879249 1316448009179896514909437)
                    ·
                      refine ⟨493668003442461193091039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1316448009179896514909437 493668003442461193091039)
                      ·
                        rfl

theorem cell23_961415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 1, 2, 2, 3].length) (baseStart_961415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_961415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_961415 prefixEnd_961415 := by exact prefixLift 961415
  have htrace : WordTrace (prefixWord ++ tailWord_961415) baseStart_961415 baseEnd_961415 := by
    simpa [prefixWord, tailWord_961415, baseEnd_961415] using wordTrace_append hprefix tailTrace_961415
  have hstable : (prefixWord ++ tailWord_961415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961415).length < 2 ^ (prefixWord ++ tailWord_961415).sum := by decide
  have hdescent : baseEnd_961415 < baseStart_961415 := by decide
  rcases family_descends (prefixWord ++ tailWord_961415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961465 : List Nat := [1, 2, 1, 4, 2, 3, 2, 2, 1, 5]
def baseStart_961465 : Nat := 118140960795 + 961465 * 2 ^ 59
def prefixEnd_961465 : Nat := 4983230072969 + 3 ^ 40 * 961465 * 2
def baseEnd_961465 : Nat := 164564559158395332488603

theorem tailTrace_961465 : CollatzResearch.WordTrace tailWord_961465 prefixEnd_961465 164564559158395332488603 := by
  unfold tailWord_961465
  simp only [CollatzResearch.WordTrace]
  refine ⟨35067509461783984994069849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23378339641189323329379899 35067509461783984994069849)
  ·
    refine ⟨26300632096337988745552387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35067509461783984994069849 26300632096337988745552387)
    ·
      refine ⟨39450948144506983118328581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26300632096337988745552387 39450948144506983118328581)
      ·
        refine ⟨7397052777095059334686609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39450948144506983118328581 7397052777095059334686609)
        ·
          refine ⟨5547789582821294501014957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7397052777095059334686609 5547789582821294501014957)
          ·
            refine ⟨2080421093557985437880609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5547789582821294501014957 2080421093557985437880609)
            ·
              refine ⟨1560315820168489078410457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2080421093557985437880609 1560315820168489078410457)
              ·
                refine ⟨1170236865126366808807843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1560315820168489078410457 1170236865126366808807843)
                ·
                  refine ⟨1755355297689550213211765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1170236865126366808807843 1755355297689550213211765)
                  ·
                    refine ⟨164564559158395332488603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1755355297689550213211765 164564559158395332488603)
                    ·
                      rfl

theorem cell23_961465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 2, 1, 5].length) (baseStart_961465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_961465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_961465 prefixEnd_961465 := by exact prefixLift 961465
  have htrace : WordTrace (prefixWord ++ tailWord_961465) baseStart_961465 baseEnd_961465 := by
    simpa [prefixWord, tailWord_961465, baseEnd_961465] using wordTrace_append hprefix tailTrace_961465
  have hstable : (prefixWord ++ tailWord_961465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961465).length < 2 ^ (prefixWord ++ tailWord_961465).sum := by decide
  have hdescent : baseEnd_961465 < baseStart_961465 := by decide
  rcases family_descends (prefixWord ++ tailWord_961465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961481 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 5, 1, 6]
def baseStart_961481 : Nat := 118140960795 + 961481 * 2 ^ 59
def prefixEnd_961481 : Nat := 4983230072969 + 3 ^ 40 * 961481 * 2
def baseEnd_961481 : Nat := 493701893165657934865735

theorem tailTrace_961481 : CollatzResearch.WordTrace tailWord_961481 prefixEnd_961481 493701893165657934865735 := by
  unfold tailWord_961481
  simp only [CollatzResearch.WordTrace]
  refine ⟨35068093029726019726652297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23378728686484013151101531 35068093029726019726652297)
  ·
    refine ⟨26301069772294514794989223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35068093029726019726652297 26301069772294514794989223)
    ·
      refine ⟨39451604658441772192483835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26301069772294514794989223 39451604658441772192483835)
      ·
        refine ⟨59177406987662658288725753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39451604658441772192483835 59177406987662658288725753)
        ·
          refine ⟨44383055240746993716544315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59177406987662658288725753 44383055240746993716544315)
          ·
            refine ⟨66574582861120490574816473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44383055240746993716544315 66574582861120490574816473)
            ·
              refine ⟨49930937145840367931112355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66574582861120490574816473 49930937145840367931112355)
              ·
                refine ⟨74896405718760551896668533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49930937145840367931112355 74896405718760551896668533)
                ·
                  refine ⟨7021538036133801740312675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74896405718760551896668533 7021538036133801740312675)
                  ·
                    refine ⟨10532307054200702610469013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7021538036133801740312675 10532307054200702610469013)
                    ·
                      refine ⟨493701893165657934865735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10532307054200702610469013 493701893165657934865735)
                      ·
                        rfl

theorem cell23_961481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 1, 6].length) (baseStart_961481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_961481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_961481 prefixEnd_961481 := by exact prefixLift 961481
  have htrace : WordTrace (prefixWord ++ tailWord_961481) baseStart_961481 baseEnd_961481 := by
    simpa [prefixWord, tailWord_961481, baseEnd_961481] using wordTrace_append hprefix tailTrace_961481
  have hstable : (prefixWord ++ tailWord_961481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961481).length < 2 ^ (prefixWord ++ tailWord_961481).sum := by decide
  have hdescent : baseEnd_961481 < baseStart_961481 := by decide
  rcases family_descends (prefixWord ++ tailWord_961481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961488 : List Nat := [2, 1, 1, 1, 1, 2, 3, 2, 5, 2, 3]
def baseStart_961488 : Nat := 118140960795 + 961488 * 2 ^ 59
def prefixEnd_961488 : Nat := 4983230072969 + 3 ^ 40 * 961488 * 2
def baseEnd_961488 : Nat := 493705487530239407478203

theorem tailTrace_961488 : CollatzResearch.WordTrace tailWord_961488 prefixEnd_961488 493705487530239407478203 := by
  unfold tailWord_961488
  simp only [CollatzResearch.WordTrace]
  refine ⟨17534174170350329961078559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23378898893800439948104745 17534174170350329961078559)
  ·
    refine ⟨26301261255525494941617839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17534174170350329961078559 26301261255525494941617839)
    ·
      refine ⟨39451891883288242412426759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26301261255525494941617839 39451891883288242412426759)
      ·
        refine ⟨59177837824932363618640139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39451891883288242412426759 59177837824932363618640139)
        ·
          refine ⟨88766756737398545427960209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59177837824932363618640139 88766756737398545427960209)
          ·
            refine ⟨66575067553048909070970157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88766756737398545427960209 66575067553048909070970157)
            ·
              refine ⟨24965650332393340901613809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66575067553048909070970157 24965650332393340901613809)
              ·
                refine ⟨18724237749295005676210357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24965650332393340901613809 18724237749295005676210357)
                ·
                  refine ⟨1755397288996406782144721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18724237749295005676210357 1755397288996406782144721)
                  ·
                    refine ⟨1316547966747305086608541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1755397288996406782144721 1316547966747305086608541)
                    ·
                      refine ⟨493705487530239407478203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1316547966747305086608541 493705487530239407478203)
                      ·
                        rfl

theorem cell23_961488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 5, 2, 3].length) (baseStart_961488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_961488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_961488 prefixEnd_961488 := by exact prefixLift 961488
  have htrace : WordTrace (prefixWord ++ tailWord_961488) baseStart_961488 baseEnd_961488 := by
    simpa [prefixWord, tailWord_961488, baseEnd_961488] using wordTrace_append hprefix tailTrace_961488
  have hstable : (prefixWord ++ tailWord_961488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961488).length < 2 ^ (prefixWord ++ tailWord_961488).sum := by decide
  have hdescent : baseEnd_961488 < baseStart_961488 := by decide
  rcases family_descends (prefixWord ++ tailWord_961488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961498 : List Nat := [3, 1, 1, 2, 4, 1, 1, 2, 1, 1, 6]
def baseStart_961498 : Nat := 118140960795 + 961498 * 2 ^ 59
def prefixEnd_961498 : Nat := 4983230072969 + 3 ^ 40 * 961498 * 2
def baseEnd_961498 : Nat := 493710622336784368353157

theorem tailTrace_961498 : CollatzResearch.WordTrace tailWord_961498 prefixEnd_961498 493710622336784368353157 := by
  unfold tailWord_961498
  simp only [CollatzResearch.WordTrace]
  refine ⟨8767178267666107907505287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23379142047109621086680765 8767178267666107907505287)
  ·
    refine ⟨13150767401499161861257931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8767178267666107907505287 13150767401499161861257931)
    ·
      refine ⟨19726151102248742791886897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13150767401499161861257931 19726151102248742791886897)
      ·
        refine ⟨14794613326686557093915173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19726151102248742791886897 14794613326686557093915173)
        ·
          refine ⟨2773989998753729455109095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14794613326686557093915173 2773989998753729455109095)
          ·
            refine ⟨4160984998130594182663643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2773989998753729455109095 4160984998130594182663643)
            ·
              refine ⟨6241477497195891273995465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4160984998130594182663643 6241477497195891273995465)
              ·
                refine ⟨4681108122896918455496599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6241477497195891273995465 4681108122896918455496599)
                ·
                  refine ⟨7021662184345377683244899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4681108122896918455496599 7021662184345377683244899)
                  ·
                    refine ⟨10532493276518066524867349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7021662184345377683244899 10532493276518066524867349)
                    ·
                      refine ⟨493710622336784368353157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10532493276518066524867349 493710622336784368353157)
                      ·
                        rfl

theorem cell23_961498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 1, 1, 6].length) (baseStart_961498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_961498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_961498 prefixEnd_961498 := by exact prefixLift 961498
  have htrace : WordTrace (prefixWord ++ tailWord_961498) baseStart_961498 baseEnd_961498 := by
    simpa [prefixWord, tailWord_961498, baseEnd_961498] using wordTrace_append hprefix tailTrace_961498
  have hstable : (prefixWord ++ tailWord_961498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961498).length < 2 ^ (prefixWord ++ tailWord_961498).sum := by decide
  have hdescent : baseEnd_961498 < baseStart_961498 := by decide
  rcases family_descends (prefixWord ++ tailWord_961498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961512 : List Nat := [2, 1, 4, 1, 1, 1, 6, 1, 2, 4]
def baseStart_961512 : Nat := 118140960795 + 961512 * 2 ^ 59
def prefixEnd_961512 : Nat := 4983230072969 + 3 ^ 40 * 961512 * 2
def baseEnd_961512 : Nat := 164572603688649104526031

theorem tailTrace_961512 : CollatzResearch.WordTrace tailWord_961512 prefixEnd_961512 164572603688649104526031 := by
  unfold tailWord_961512
  simp only [CollatzResearch.WordTrace]
  refine ⟨17534611846306856010515395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23379482461742474680687193 17534611846306856010515395)
  ·
    refine ⟨26301917769460284015773093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17534611846306856010515395 26301917769460284015773093)
    ·
      refine ⟨4931609581773803252957455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26301917769460284015773093 4931609581773803252957455)
      ·
        refine ⟨7397414372660704879436183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4931609581773803252957455 7397414372660704879436183)
        ·
          refine ⟨11096121558991057319154275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7397414372660704879436183 11096121558991057319154275)
          ·
            refine ⟨16644182338486585978731413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11096121558991057319154275 16644182338486585978731413)
            ·
              refine ⟨780196047116558717753035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16644182338486585978731413 780196047116558717753035)
              ·
                refine ⟨1170294070674838076629553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 780196047116558717753035 1170294070674838076629553)
                ·
                  refine ⟨877720553006128557472165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1170294070674838076629553 877720553006128557472165)
                  ·
                    refine ⟨164572603688649104526031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 877720553006128557472165 164572603688649104526031)
                    ·
                      rfl

theorem cell23_961512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 6, 1, 2, 4].length) (baseStart_961512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_961512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_961512 prefixEnd_961512 := by exact prefixLift 961512
  have htrace : WordTrace (prefixWord ++ tailWord_961512) baseStart_961512 baseEnd_961512 := by
    simpa [prefixWord, tailWord_961512, baseEnd_961512] using wordTrace_append hprefix tailTrace_961512
  have hstable : (prefixWord ++ tailWord_961512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961512).length < 2 ^ (prefixWord ++ tailWord_961512).sum := by decide
  have hdescent : baseEnd_961512 < baseStart_961512 := by decide
  rcases family_descends (prefixWord ++ tailWord_961512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961592 : List Nat := [2, 1, 2, 1, 5, 1, 2, 2, 1, 4, 2]
def baseStart_961592 : Nat := 118140960795 + 961592 * 2 ^ 59
def prefixEnd_961592 : Nat := 4983230072969 + 3 ^ 40 * 961592 * 2
def baseEnd_961592 : Nat := 493758889518307000577725

theorem tailTrace_961592 : CollatzResearch.WordTrace tailWord_961592 prefixEnd_961592 493758889518307000577725 := by
  unfold tailWord_961592
  simp only [CollatzResearch.WordTrace]
  refine ⟨17536070766161942841971515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23381427688215923789295353 17536070766161942841971515)
  ·
    refine ⟨26304106149242914262957273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17536070766161942841971515 26304106149242914262957273)
    ·
      refine ⟨19728079611932185697217955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26304106149242914262957273 19728079611932185697217955)
      ·
        refine ⟨29592119417898278545826933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19728079611932185697217955 29592119417898278545826933)
        ·
          refine ⟨2774261195427963613671275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29592119417898278545826933 2774261195427963613671275)
          ·
            refine ⟨4161391793141945420506913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2774261195427963613671275 4161391793141945420506913)
            ·
              refine ⟨3121043844856459065380185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4161391793141945420506913 3121043844856459065380185)
              ·
                refine ⟨2340782883642344299035139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3121043844856459065380185 2340782883642344299035139)
                ·
                  refine ⟨3511174325463516448552709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2340782883642344299035139 3511174325463516448552709)
                  ·
                    refine ⟨658345186024409334103633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3511174325463516448552709 658345186024409334103633)
                    ·
                      refine ⟨493758889518307000577725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 658345186024409334103633 493758889518307000577725)
                      ·
                        rfl

theorem cell23_961592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 2, 1, 4, 2].length) (baseStart_961592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_961592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_961592 prefixEnd_961592 := by exact prefixLift 961592
  have htrace : WordTrace (prefixWord ++ tailWord_961592) baseStart_961592 baseEnd_961592 := by
    simpa [prefixWord, tailWord_961592, baseEnd_961592] using wordTrace_append hprefix tailTrace_961592
  have hstable : (prefixWord ++ tailWord_961592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961592).length < 2 ^ (prefixWord ++ tailWord_961592).sum := by decide
  have hdescent : baseEnd_961592 < baseStart_961592 := by decide
  rcases family_descends (prefixWord ++ tailWord_961592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961596 : List Nat := [2, 2, 2, 2, 2, 4, 2, 1, 1, 3, 2]
def baseStart_961596 : Nat := 118140960795 + 961596 * 2 ^ 59
def prefixEnd_961596 : Nat := 4983230072969 + 3 ^ 40 * 961596 * 2
def baseEnd_961596 : Nat := 493760943440924984927707

theorem tailTrace_961596 : CollatzResearch.WordTrace tailWord_961596 prefixEnd_961596 493760943440924984927707 := by
  unfold tailWord_961596
  simp only [CollatzResearch.WordTrace]
  refine ⟨17536143712154697183544321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23381524949539596244725761 17536143712154697183544321)
  ·
    refine ⟨13152107784116022887658241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17536143712154697183544321 13152107784116022887658241)
    ·
      refine ⟨9864080838087017165743681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13152107784116022887658241 9864080838087017165743681)
      ·
        refine ⟨7398060628565262874307761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9864080838087017165743681 7398060628565262874307761)
        ·
          refine ⟨5548545471423947155730821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7398060628565262874307761 5548545471423947155730821)
          ·
            refine ⟨1040352275891990091699529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5548545471423947155730821 1040352275891990091699529)
            ·
              refine ⟨780264206918992568774647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1040352275891990091699529 780264206918992568774647)
              ·
                refine ⟨1170396310378488853161971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 780264206918992568774647 1170396310378488853161971)
                ·
                  refine ⟨1755594465567733279742957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1170396310378488853161971 1755594465567733279742957)
                  ·
                    refine ⟨658347924587899979903609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1755594465567733279742957 658347924587899979903609)
                    ·
                      refine ⟨493760943440924984927707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 658347924587899979903609 493760943440924984927707)
                      ·
                        rfl

theorem cell23_961596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 2, 1, 1, 3, 2].length) (baseStart_961596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_961596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_961596 prefixEnd_961596 := by exact prefixLift 961596
  have htrace : WordTrace (prefixWord ++ tailWord_961596) baseStart_961596 baseEnd_961596 := by
    simpa [prefixWord, tailWord_961596, baseEnd_961596] using wordTrace_append hprefix tailTrace_961596
  have hstable : (prefixWord ++ tailWord_961596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961596).length < 2 ^ (prefixWord ++ tailWord_961596).sum := by decide
  have hdescent : baseEnd_961596 < baseStart_961596 := by decide
  rcases family_descends (prefixWord ++ tailWord_961596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961645 : List Nat := [1, 5, 1, 1, 2, 2, 2, 1, 1, 7]
def baseStart_961645 : Nat := 118140960795 + 961645 * 2 ^ 59
def prefixEnd_961645 : Nat := 4983230072969 + 3 ^ 40 * 961645 * 2
def baseEnd_961645 : Nat := 164595367997665097738327

theorem tailTrace_961645 : CollatzResearch.WordTrace tailWord_961645 prefixEnd_961645 164595367997665097738327 := by
  unfold tailWord_961645
  simp only [CollatzResearch.WordTrace]
  refine ⟨35074074601131875735622389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23382716400754583823748259 35074074601131875735622389)
  ·
    refine ⟨3288194493856113350214599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35074074601131875735622389 3288194493856113350214599)
    ·
      refine ⟨4932291740784170025321899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3288194493856113350214599 4932291740784170025321899)
      ·
        refine ⟨7398437611176255037982849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4932291740784170025321899 7398437611176255037982849)
        ·
          refine ⟨5548828208382191278487137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7398437611176255037982849 5548828208382191278487137)
          ·
            refine ⟨4161621156286643458865353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5548828208382191278487137 4161621156286643458865353)
            ·
              refine ⟨3121215867214982594149015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4161621156286643458865353 3121215867214982594149015)
              ·
                refine ⟨4681823800822473891223523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3121215867214982594149015 4681823800822473891223523)
                ·
                  refine ⟨7022735701233710836835285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4681823800822473891223523 7022735701233710836835285)
                  ·
                    refine ⟨164595367997665097738327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7022735701233710836835285 164595367997665097738327)
                    ·
                      rfl

theorem cell23_961645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_961645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_961645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_961645 prefixEnd_961645 := by exact prefixLift 961645
  have htrace : WordTrace (prefixWord ++ tailWord_961645) baseStart_961645 baseEnd_961645 := by
    simpa [prefixWord, tailWord_961645, baseEnd_961645] using wordTrace_append hprefix tailTrace_961645
  have hstable : (prefixWord ++ tailWord_961645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961645).length < 2 ^ (prefixWord ++ tailWord_961645).sum := by decide
  have hdescent : baseEnd_961645 < baseStart_961645 := by decide
  rcases family_descends (prefixWord ++ tailWord_961645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961672 : List Nat := [2, 1, 3, 4, 2, 1, 1, 1, 1, 2, 5]
def baseStart_961672 : Nat := 118140960795 + 961672 * 2 ^ 59
def prefixEnd_961672 : Nat := 4983230072969 + 3 ^ 40 * 961672 * 2
def baseEnd_961672 : Nat := 493799967970666687577357

theorem tailTrace_961672 : CollatzResearch.WordTrace tailWord_961672 prefixEnd_961672 493799967970666687577357 := by
  unfold tailWord_961672
  simp only [CollatzResearch.WordTrace]
  refine ⟨17537529686017029673427635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23383372914689372897903513 17537529686017029673427635)
  ·
    refine ⟨26306294529025544510141453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17537529686017029673427635 26306294529025544510141453)
    ·
      refine ⟨9864860448384579191303045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26306294529025544510141453 9864860448384579191303045)
      ·
        refine ⟨1849661334072108598369321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9864860448384579191303045 1849661334072108598369321)
        ·
          refine ⟨1387246000554081448776991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1849661334072108598369321 1387246000554081448776991)
          ·
            refine ⟨2080869000831122173165487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1387246000554081448776991 2080869000831122173165487)
            ·
              refine ⟨3121303501246683259748231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2080869000831122173165487 3121303501246683259748231)
              ·
                refine ⟨4681955251870024889622347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3121303501246683259748231 4681955251870024889622347)
                ·
                  refine ⟨7022932877805037334433521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4681955251870024889622347 7022932877805037334433521)
                  ·
                    refine ⟨5267199658353778000825141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7022932877805037334433521 5267199658353778000825141)
                    ·
                      refine ⟨493799967970666687577357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5267199658353778000825141 493799967970666687577357)
                      ·
                        rfl

theorem cell23_961672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_961672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_961672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_961672 prefixEnd_961672 := by exact prefixLift 961672
  have htrace : WordTrace (prefixWord ++ tailWord_961672) baseStart_961672 baseEnd_961672 := by
    simpa [prefixWord, tailWord_961672, baseEnd_961672] using wordTrace_append hprefix tailTrace_961672
  have hstable : (prefixWord ++ tailWord_961672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961672).length < 2 ^ (prefixWord ++ tailWord_961672).sum := by decide
  have hdescent : baseEnd_961672 < baseStart_961672 := by decide
  rcases family_descends (prefixWord ++ tailWord_961672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961685 : List Nat := [1, 3, 2, 1, 1, 1, 2, 4, 1, 4, 3]
def baseStart_961685 : Nat := 118140960795 + 961685 * 2 ^ 59
def prefixEnd_961685 : Nat := 4983230072969 + 3 ^ 40 * 961685 * 2
def baseEnd_961685 : Nat := 493806643219175136714797

theorem tailTrace_961685 : CollatzResearch.WordTrace tailWord_961685 prefixEnd_961685 493806643219175136714797 := by
  unfold tailWord_961685
  simp only [CollatzResearch.WordTrace]
  refine ⟨35075533520986962567078509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23383689013991308378052339 35075533520986962567078509)
  ·
    refine ⟨13153325070370110962654441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35075533520986962567078509 13153325070370110962654441)
    ·
      refine ⟨9864993802777583221990831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13153325070370110962654441 9864993802777583221990831)
      ·
        refine ⟨14797490704166374832986247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9864993802777583221990831 14797490704166374832986247)
        ·
          refine ⟨22196236056249562249479371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14797490704166374832986247 22196236056249562249479371)
          ·
            refine ⟨33294354084374343374219057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22196236056249562249479371 33294354084374343374219057)
            ·
              refine ⟨24970765563280757530664293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33294354084374343374219057 24970765563280757530664293)
              ·
                refine ⟨4682018543115142036999555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24970765563280757530664293 4682018543115142036999555)
                ·
                  refine ⟨7023027814672713055499333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4682018543115142036999555 7023027814672713055499333)
                  ·
                    refine ⟨1316817715251133697906125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7023027814672713055499333 1316817715251133697906125)
                    ·
                      refine ⟨493806643219175136714797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1316817715251133697906125 493806643219175136714797)
                      ·
                        rfl

theorem cell23_961685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 4, 3].length) (baseStart_961685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_961685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_961685 prefixEnd_961685 := by exact prefixLift 961685
  have htrace : WordTrace (prefixWord ++ tailWord_961685) baseStart_961685 baseEnd_961685 := by
    simpa [prefixWord, tailWord_961685, baseEnd_961685] using wordTrace_append hprefix tailTrace_961685
  have hstable : (prefixWord ++ tailWord_961685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961685).length < 2 ^ (prefixWord ++ tailWord_961685).sum := by decide
  have hdescent : baseEnd_961685 < baseStart_961685 := by decide
  rcases family_descends (prefixWord ++ tailWord_961685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961726 : List Nat := [4, 2, 1, 1, 3, 2, 1, 4, 1, 4]
def baseStart_961726 : Nat := 118140960795 + 961726 * 2 ^ 59
def prefixEnd_961726 : Nat := 4983230072969 + 3 ^ 40 * 961726 * 2
def baseEnd_961726 : Nat := 164609231975336492100703

theorem tailTrace_961726 : CollatzResearch.WordTrace tailWord_961726 prefixEnd_961726 164609231975336492100703 := by
  unfold tailWord_961726
  simp only [CollatzResearch.WordTrace]
  refine ⟨4384628614229803321165129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23384685942558951046214021 4384628614229803321165129)
  ·
    refine ⟨3288471460672352490873847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4384628614229803321165129 3288471460672352490873847)
    ·
      refine ⟨4932707191008528736310771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3288471460672352490873847 4932707191008528736310771)
      ·
        refine ⟨7399060786512793104466157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4932707191008528736310771 7399060786512793104466157)
        ·
          refine ⟨2774647794942297414174809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7399060786512793104466157 2774647794942297414174809)
          ·
            refine ⟨2080985846206723060631107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2774647794942297414174809 2080985846206723060631107)
            ·
              refine ⟨3121478769310084590946661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2080985846206723060631107 3121478769310084590946661)
              ·
                refine ⟨585277269245640860802499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3121478769310084590946661 585277269245640860802499)
                ·
                  refine ⟨877915903868461291203749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 585277269245640860802499 877915903868461291203749)
                  ·
                    refine ⟨164609231975336492100703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 877915903868461291203749 164609231975336492100703)
                    ·
                      rfl

theorem cell23_961726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 4, 1, 4].length) (baseStart_961726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_961726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_961726 prefixEnd_961726 := by exact prefixLift 961726
  have htrace : WordTrace (prefixWord ++ tailWord_961726) baseStart_961726 baseEnd_961726 := by
    simpa [prefixWord, tailWord_961726, baseEnd_961726] using wordTrace_append hprefix tailTrace_961726
  have hstable : (prefixWord ++ tailWord_961726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961726).length < 2 ^ (prefixWord ++ tailWord_961726).sum := by decide
  have hdescent : baseEnd_961726 < baseStart_961726 := by decide
  rcases family_descends (prefixWord ++ tailWord_961726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961749 : List Nat := [1, 3, 2, 4, 1, 1, 1, 1, 5, 1, 3]
def baseStart_961749 : Nat := 118140960795 + 961749 * 2 ^ 59
def prefixEnd_961749 : Nat := 4983230072969 + 3 ^ 40 * 961749 * 2
def baseEnd_961749 : Nat := 493839505981062886314503

theorem tailTrace_961749 : CollatzResearch.WordTrace tailWord_961749 prefixEnd_961749 493839505981062886314503 := by
  unfold tailWord_961749
  simp only [CollatzResearch.WordTrace]
  refine ⟨35077867792755101497408301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23385245195170067664938867 35077867792755101497408301)
  ·
    refine ⟨13154200422283163061528113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35077867792755101497408301 13154200422283163061528113)
    ·
      refine ⟨9865650316712372296146085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13154200422283163061528113 9865650316712372296146085)
      ·
        refine ⟨1849809434383569805527391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9865650316712372296146085 1849809434383569805527391)
        ·
          refine ⟨2774714151575354708291087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1849809434383569805527391 2774714151575354708291087)
          ·
            refine ⟨4162071227363032062436631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2774714151575354708291087 4162071227363032062436631)
            ·
              refine ⟨6243106841044548093654947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4162071227363032062436631 6243106841044548093654947)
              ·
                refine ⟨9364660261566822140482421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6243106841044548093654947 9364660261566822140482421)
                ·
                  refine ⟨877936899521889575670227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9364660261566822140482421 877936899521889575670227)
                  ·
                    refine ⟨1316905349282834363505341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 877936899521889575670227 1316905349282834363505341)
                    ·
                      refine ⟨493839505981062886314503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1316905349282834363505341 493839505981062886314503)
                      ·
                        rfl

theorem cell23_961749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_961749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_961749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_961749 prefixEnd_961749 := by exact prefixLift 961749
  have htrace : WordTrace (prefixWord ++ tailWord_961749) baseStart_961749 baseEnd_961749 := by
    simpa [prefixWord, tailWord_961749, baseEnd_961749] using wordTrace_append hprefix tailTrace_961749
  have hstable : (prefixWord ++ tailWord_961749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961749).length < 2 ^ (prefixWord ++ tailWord_961749).sum := by decide
  have hdescent : baseEnd_961749 < baseStart_961749 := by decide
  rcases family_descends (prefixWord ++ tailWord_961749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961755 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 7, 1, 4]
def baseStart_961755 : Nat := 118140960795 + 961755 * 2 ^ 59
def prefixEnd_961755 : Nat := 4983230072969 + 3 ^ 40 * 961755 * 2
def baseEnd_961755 : Nat := 493842586864989862839475

theorem tailTrace_961755 : CollatzResearch.WordTrace tailWord_961755 prefixEnd_961755 493842586864989862839475 := by
  unfold tailWord_961755
  simp only [CollatzResearch.WordTrace]
  refine ⟨35078086630733364522126719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23385391087155576348084479 35078086630733364522126719)
  ·
    refine ⟨52617129946100046783190079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35078086630733364522126719 52617129946100046783190079)
    ·
      refine ⟨78925694919150070174785119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52617129946100046783190079 78925694919150070174785119)
      ·
        refine ⟨118388542378725105262177679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78925694919150070174785119 118388542378725105262177679)
        ·
          refine ⟨177582813568087657893266519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118388542378725105262177679 177582813568087657893266519)
          ·
            refine ⟨266374220352131486839899779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177582813568087657893266519 266374220352131486839899779)
            ·
              refine ⟨399561330528197230259849669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266374220352131486839899779 399561330528197230259849669)
              ·
                refine ⟨74917749474036980673721813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 399561330528197230259849669 74917749474036980673721813)
                ·
                  refine ⟨1755884753297741734540355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 74917749474036980673721813 1755884753297741734540355)
                  ·
                    refine ⟨2633827129946612601810533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1755884753297741734540355 2633827129946612601810533)
                    ·
                      refine ⟨493842586864989862839475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2633827129946612601810533 493842586864989862839475)
                      ·
                        rfl

theorem cell23_961755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 7, 1, 4].length) (baseStart_961755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_961755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_961755 prefixEnd_961755 := by exact prefixLift 961755
  have htrace : WordTrace (prefixWord ++ tailWord_961755) baseStart_961755 baseEnd_961755 := by
    simpa [prefixWord, tailWord_961755, baseEnd_961755] using wordTrace_append hprefix tailTrace_961755
  have hstable : (prefixWord ++ tailWord_961755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961755).length < 2 ^ (prefixWord ++ tailWord_961755).sum := by decide
  have hdescent : baseEnd_961755 < baseStart_961755 := by decide
  rcases family_descends (prefixWord ++ tailWord_961755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961759 : List Nat := [1, 1, 2, 3, 2, 1, 5, 1, 2, 3, 2]
def baseStart_961759 : Nat := 118140960795 + 961759 * 2 ^ 59
def prefixEnd_961759 : Nat := 4983230072969 + 3 ^ 40 * 961759 * 2
def baseEnd_961759 : Nat := 493844640787607847189457

theorem tailTrace_961759 : CollatzResearch.WordTrace tailWord_961759 prefixEnd_961759 493844640787607847189457 := by
  unfold tailWord_961759
  simp only [CollatzResearch.WordTrace]
  refine ⟨35078232522718873205272331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23385488348479248803514887 35078232522718873205272331)
  ·
    refine ⟨52617348784078309807908497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35078232522718873205272331 52617348784078309807908497)
    ·
      refine ⟨39463011588058732355931373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52617348784078309807908497 39463011588058732355931373)
      ·
        refine ⟨14798629345522024633474265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39463011588058732355931373 14798629345522024633474265)
        ·
          refine ⟨11098972009141518475105699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14798629345522024633474265 11098972009141518475105699)
          ·
            refine ⟨16648458013712277712658549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11098972009141518475105699 16648458013712277712658549)
            ·
              refine ⟨1560792938785526035561739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16648458013712277712658549 1560792938785526035561739)
              ·
                refine ⟨2341189408178289053342609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1560792938785526035561739 2341189408178289053342609)
                ·
                  refine ⟨1755892056133716790006957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2341189408178289053342609 1755892056133716790006957)
                  ·
                    refine ⟨658459521050143796252609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1755892056133716790006957 658459521050143796252609)
                    ·
                      refine ⟨493844640787607847189457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 658459521050143796252609 493844640787607847189457)
                      ·
                        rfl

theorem cell23_961759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 1, 2, 3, 2].length) (baseStart_961759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_961759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_961759 prefixEnd_961759 := by exact prefixLift 961759
  have htrace : WordTrace (prefixWord ++ tailWord_961759) baseStart_961759 baseEnd_961759 := by
    simpa [prefixWord, tailWord_961759, baseEnd_961759] using wordTrace_append hprefix tailTrace_961759
  have hstable : (prefixWord ++ tailWord_961759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961759).length < 2 ^ (prefixWord ++ tailWord_961759).sum := by decide
  have hdescent : baseEnd_961759 < baseStart_961759 := by decide
  rcases family_descends (prefixWord ++ tailWord_961759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961785 : List Nat := [1, 2, 1, 3, 1, 1, 4, 2, 1, 1, 6]
def baseStart_961785 : Nat := 118140960795 + 961785 * 2 ^ 59
def prefixEnd_961785 : Nat := 4983230072969 + 3 ^ 40 * 961785 * 2
def baseEnd_961785 : Nat := 493857991284624745464337

theorem tailTrace_961785 : CollatzResearch.WordTrace tailWord_961785 prefixEnd_961785 493857991284624745464337 := by
  unfold tailWord_961785
  simp only [CollatzResearch.WordTrace]
  refine ⟨35079180820624679645718809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23386120547083119763812539 35079180820624679645718809)
  ·
    refine ⟨26309385615468509734289107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35079180820624679645718809 26309385615468509734289107)
    ·
      refine ⟨39464078423202764601433661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26309385615468509734289107 39464078423202764601433661)
      ·
        refine ⟨14799029408701036725537623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39464078423202764601433661 14799029408701036725537623)
        ·
          refine ⟨22198544113051555088306435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14799029408701036725537623 22198544113051555088306435)
          ·
            refine ⟨33297816169577332632459653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22198544113051555088306435 33297816169577332632459653)
            ·
              refine ⟨6243340531795749868586185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33297816169577332632459653 6243340531795749868586185)
              ·
                refine ⟨4682505398846812401439639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6243340531795749868586185 4682505398846812401439639)
                ·
                  refine ⟨7023758098270218602159459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4682505398846812401439639 7023758098270218602159459)
                  ·
                    refine ⟨10535637147405327903239189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7023758098270218602159459 10535637147405327903239189)
                    ·
                      refine ⟨493857991284624745464337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10535637147405327903239189 493857991284624745464337)
                      ·
                        rfl

theorem cell23_961785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 1, 6].length) (baseStart_961785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_961785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_961785 prefixEnd_961785 := by exact prefixLift 961785
  have htrace : WordTrace (prefixWord ++ tailWord_961785) baseStart_961785 baseEnd_961785 := by
    simpa [prefixWord, tailWord_961785, baseEnd_961785] using wordTrace_append hprefix tailTrace_961785
  have hstable : (prefixWord ++ tailWord_961785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961785).length < 2 ^ (prefixWord ++ tailWord_961785).sum := by decide
  have hdescent : baseEnd_961785 < baseStart_961785 := by decide
  rcases family_descends (prefixWord ++ tailWord_961785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961806 : List Nat := [4, 1, 1, 2, 1, 3, 2, 2, 3, 2, 2]
def baseStart_961806 : Nat := 118140960795 + 961806 * 2 ^ 59
def prefixEnd_961806 : Nat := 4983230072969 + 3 ^ 40 * 961806 * 2
def baseEnd_961806 : Nat := 493868774378369163301741

theorem tailTrace_961806 : CollatzResearch.WordTrace tailWord_961806 prefixEnd_961806 493868774378369163301741 := by
  unfold tailWord_961806
  simp only [CollatzResearch.WordTrace]
  refine ⟨4384993344193575029029159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23386631169032400154822181 4384993344193575029029159)
  ·
    refine ⟨6577490016290362543543739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4384993344193575029029159 6577490016290362543543739)
    ·
      refine ⟨9866235024435543815315609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6577490016290362543543739 9866235024435543815315609)
      ·
        refine ⟨7399676268326657861486707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9866235024435543815315609 7399676268326657861486707)
        ·
          refine ⟨11099514402489986792230061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7399676268326657861486707 11099514402489986792230061)
          ·
            refine ⟨4162317900933745047086273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11099514402489986792230061 4162317900933745047086273)
            ·
              refine ⟨3121738425700308785314705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4162317900933745047086273 3121738425700308785314705)
              ·
                refine ⟨2341303819275231588986029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3121738425700308785314705 2341303819275231588986029)
                ·
                  refine ⟨877988932228211845869761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2341303819275231588986029 877988932228211845869761)
                  ·
                    refine ⟨658491699171158884402321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 877988932228211845869761 658491699171158884402321)
                    ·
                      refine ⟨493868774378369163301741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 658491699171158884402321 493868774378369163301741)
                      ·
                        rfl

theorem cell23_961806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 2, 3, 2, 2].length) (baseStart_961806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_961806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_961806 prefixEnd_961806 := by exact prefixLift 961806
  have htrace : WordTrace (prefixWord ++ tailWord_961806) baseStart_961806 baseEnd_961806 := by
    simpa [prefixWord, tailWord_961806, baseEnd_961806] using wordTrace_append hprefix tailTrace_961806
  have hstable : (prefixWord ++ tailWord_961806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961806).length < 2 ^ (prefixWord ++ tailWord_961806).sum := by decide
  have hdescent : baseEnd_961806 < baseStart_961806 := by decide
  rcases family_descends (prefixWord ++ tailWord_961806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961809 : List Nat := [1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 3]
def baseStart_961809 : Nat := 118140960795 + 961809 * 2 ^ 59
def prefixEnd_961809 : Nat := 4983230072969 + 3 ^ 40 * 961809 * 2
def baseEnd_961809 : Nat := 493870314820332651564227

theorem tailTrace_961809 : CollatzResearch.WordTrace tailWord_961809 prefixEnd_961809 493870314820332651564227 := by
  unfold tailWord_961809
  simp only [CollatzResearch.WordTrace]
  refine ⟨35080056172537731744592481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23386704115025154496394987 35080056172537731744592481)
  ·
    refine ⟨26310042129403298808444361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35080056172537731744592481 26310042129403298808444361)
    ·
      refine ⟨19732531597052474106333271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26310042129403298808444361 19732531597052474106333271)
      ·
        refine ⟨29598797395578711159499907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19732531597052474106333271 29598797395578711159499907)
        ·
          refine ⟨44398196093368066739249861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29598797395578711159499907 44398196093368066739249861)
          ·
            refine ⟨8324661767506512513609349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44398196093368066739249861 8324661767506512513609349)
            ·
              refine ⟨1560874081407471096301753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8324661767506512513609349 1560874081407471096301753)
              ·
                refine ⟨1170655561055603322226315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1560874081407471096301753 1170655561055603322226315)
                ·
                  refine ⟨1755983341583404983339473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1170655561055603322226315 1755983341583404983339473)
                  ·
                    refine ⟨1316987506187553737504605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1755983341583404983339473 1316987506187553737504605)
                    ·
                      refine ⟨493870314820332651564227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1316987506187553737504605 493870314820332651564227)
                      ·
                        rfl

theorem cell23_961809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 3].length) (baseStart_961809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_961809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_961809 prefixEnd_961809 := by exact prefixLift 961809
  have htrace : WordTrace (prefixWord ++ tailWord_961809) baseStart_961809 baseEnd_961809 := by
    simpa [prefixWord, tailWord_961809, baseEnd_961809] using wordTrace_append hprefix tailTrace_961809
  have hstable : (prefixWord ++ tailWord_961809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961809).length < 2 ^ (prefixWord ++ tailWord_961809).sum := by decide
  have hdescent : baseEnd_961809 < baseStart_961809 := by decide
  rcases family_descends (prefixWord ++ tailWord_961809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961825 : List Nat := [1, 2, 3, 2, 1, 1, 1, 2, 1, 9]
def baseStart_961825 : Nat := 118140960795 + 961825 * 2 ^ 59
def prefixEnd_961825 : Nat := 4983230072969 + 3 ^ 40 * 961825 * 2
def baseEnd_961825 : Nat := 164626176836934862988051

theorem tailTrace_961825 : CollatzResearch.WordTrace tailWord_961825 prefixEnd_961825 164626176836934862988051 := by
  unfold tailWord_961825
  simp only [CollatzResearch.WordTrace]
  refine ⟨35080639740479766477174929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23387093160319844318116619 35080639740479766477174929)
  ·
    refine ⟨26310479805359824857881197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35080639740479766477174929 26310479805359824857881197)
    ·
      refine ⟨9866429927009934321705449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26310479805359824857881197 9866429927009934321705449)
      ·
        refine ⟨7399822445257450741279087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9866429927009934321705449 7399822445257450741279087)
        ·
          refine ⟨11099733667886176111918631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7399822445257450741279087 11099733667886176111918631)
          ·
            refine ⟨16649600501829264167877947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11099733667886176111918631 16649600501829264167877947)
            ·
              refine ⟨24974400752743896251816921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16649600501829264167877947 24974400752743896251816921)
              ·
                refine ⟨18730800564557922188862691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24974400752743896251816921 18730800564557922188862691)
                ·
                  refine ⟨28096200846836883283294037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18730800564557922188862691 28096200846836883283294037)
                  ·
                    refine ⟨164626176836934862988051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 28096200846836883283294037 164626176836934862988051)
                    ·
                      rfl

theorem cell23_961825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 9].length) (baseStart_961825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_961825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_961825 prefixEnd_961825 := by exact prefixLift 961825
  have htrace : WordTrace (prefixWord ++ tailWord_961825) baseStart_961825 baseEnd_961825 := by
    simpa [prefixWord, tailWord_961825, baseEnd_961825] using wordTrace_append hprefix tailTrace_961825
  have hstable : (prefixWord ++ tailWord_961825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961825).length < 2 ^ (prefixWord ++ tailWord_961825).sum := by decide
  have hdescent : baseEnd_961825 < baseStart_961825 := by decide
  rcases family_descends (prefixWord ++ tailWord_961825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961839 : List Nat := [1, 1, 2, 1, 2, 1, 3, 6, 2, 1, 3]
def baseStart_961839 : Nat := 118140960795 + 961839 * 2 ^ 59
def prefixEnd_961839 : Nat := 4983230072969 + 3 ^ 40 * 961839 * 2
def baseEnd_961839 : Nat := 493885719239967534189089

theorem tailTrace_961839 : CollatzResearch.WordTrace tailWord_961839 prefixEnd_961839 493885719239967534189089 := by
  unfold tailWord_961839
  simp only [CollatzResearch.WordTrace]
  refine ⟨35081150362429046868184571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23387433574952697912123047 35081150362429046868184571)
  ·
    refine ⟨52621725543643570302276857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35081150362429046868184571 52621725543643570302276857)
    ·
      refine ⟨39466294157732677726707643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52621725543643570302276857 39466294157732677726707643)
      ·
        refine ⟨59199441236599016590061465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39466294157732677726707643 59199441236599016590061465)
        ·
          refine ⟨44399580927449262442546099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59199441236599016590061465 44399580927449262442546099)
          ·
            refine ⟨66599371391173893663819149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44399580927449262442546099 66599371391173893663819149)
            ·
              refine ⟨24974764271690210123932181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66599371391173893663819149 24974764271690210123932181)
              ·
                refine ⟨1170692075235478599559321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24974764271690210123932181 1170692075235478599559321)
                ·
                  refine ⟨878019056426608949669491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1170692075235478599559321 878019056426608949669491)
                  ·
                    refine ⟨1317028584639913424504237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 878019056426608949669491 1317028584639913424504237)
                    ·
                      refine ⟨493885719239967534189089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1317028584639913424504237 493885719239967534189089)
                      ·
                        rfl

theorem cell23_961839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 6, 2, 1, 3].length) (baseStart_961839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_961839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_961839 prefixEnd_961839 := by exact prefixLift 961839
  have htrace : WordTrace (prefixWord ++ tailWord_961839) baseStart_961839 baseEnd_961839 := by
    simpa [prefixWord, tailWord_961839, baseEnd_961839] using wordTrace_append hprefix tailTrace_961839
  have hstable : (prefixWord ++ tailWord_961839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961839).length < 2 ^ (prefixWord ++ tailWord_961839).sum := by decide
  have hdescent : baseEnd_961839 < baseStart_961839 := by decide
  rcases family_descends (prefixWord ++ tailWord_961839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961846 : List Nat := [5, 1, 2, 3, 1, 1, 2, 8]
def baseStart_961846 : Nat := 118140960795 + 961846 * 2 ^ 59
def prefixEnd_961846 : Nat := 4983230072969 + 3 ^ 40 * 961846 * 2
def baseEnd_961846 : Nat := 18292196800168481733391

theorem tailTrace_961846 : CollatzResearch.WordTrace tailWord_961846 prefixEnd_961846 18292196800168481733391 := by
  unfold tailWord_961846
  simp only [CollatzResearch.WordTrace]
  refine ⟨2192587854587730441480587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23387603782269124709126261 2192587854587730441480587)
  ·
    refine ⟨3288881781881595662220881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2192587854587730441480587 3288881781881595662220881)
    ·
      refine ⟨2466661336411196746665661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3288881781881595662220881 2466661336411196746665661)
      ·
        refine ⟨924998001154198779999623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2466661336411196746665661 924998001154198779999623)
        ·
          refine ⟨1387497001731298169999435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 924998001154198779999623 1387497001731298169999435)
          ·
            refine ⟨2081245502596947254999153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1387497001731298169999435 2081245502596947254999153)
            ·
              refine ⟨1560934126947710441249365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2081245502596947254999153 1560934126947710441249365)
              ·
                refine ⟨18292196800168481733391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1560934126947710441249365 18292196800168481733391)
                ·
                  rfl

theorem cell23_961846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 8].length) (baseStart_961846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_961846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_961846 prefixEnd_961846 := by exact prefixLift 961846
  have htrace : WordTrace (prefixWord ++ tailWord_961846) baseStart_961846 baseEnd_961846 := by
    simpa [prefixWord, tailWord_961846, baseEnd_961846] using wordTrace_append hprefix tailTrace_961846
  have hstable : (prefixWord ++ tailWord_961846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961846).length < 2 ^ (prefixWord ++ tailWord_961846).sum := by decide
  have hdescent : baseEnd_961846 < baseStart_961846 := by decide
  rcases family_descends (prefixWord ++ tailWord_961846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961879 : List Nat := [1, 1, 3, 2, 3, 2, 1, 1, 3, 4, 2]
def baseStart_961879 : Nat := 118140960795 + 961879 * 2 ^ 59
def prefixEnd_961879 : Nat := 4983230072969 + 3 ^ 40 * 961879 * 2
def baseEnd_961879 : Nat := 493906258466147377688905

theorem tailTrace_961879 : CollatzResearch.WordTrace tailWord_961879 prefixEnd_961879 493906258466147377688905 := by
  unfold tailWord_961879
  simp only [CollatzResearch.WordTrace]
  refine ⟨35082609282284133699640691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23388406188189422466427127 35082609282284133699640691)
  ·
    refine ⟨52623913923426200549461037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35082609282284133699640691 52623913923426200549461037)
    ·
      refine ⟨19733967721284825206047889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52623913923426200549461037 19733967721284825206047889)
      ·
        refine ⟨14800475790963618904535917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19733967721284825206047889 14800475790963618904535917)
        ·
          refine ⟨5550178421611357089200969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14800475790963618904535917 5550178421611357089200969)
          ·
            refine ⟨4162633816208517816900727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5550178421611357089200969 4162633816208517816900727)
            ·
              refine ⟨6243950724312776725351091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4162633816208517816900727 6243950724312776725351091)
              ·
                refine ⟨9365926086469165088026637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6243950724312776725351091 9365926086469165088026637)
                ·
                  refine ⟨3512222282425936908009989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9365926086469165088026637 3512222282425936908009989)
                  ·
                    refine ⟨658541677954863170251873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3512222282425936908009989 658541677954863170251873)
                    ·
                      refine ⟨493906258466147377688905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 658541677954863170251873 493906258466147377688905)
                      ·
                        rfl

theorem cell23_961879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 3, 4, 2].length) (baseStart_961879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_961879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_961879 prefixEnd_961879 := by exact prefixLift 961879
  have htrace : WordTrace (prefixWord ++ tailWord_961879) baseStart_961879 baseEnd_961879 := by
    simpa [prefixWord, tailWord_961879, baseEnd_961879] using wordTrace_append hprefix tailTrace_961879
  have hstable : (prefixWord ++ tailWord_961879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961879).length < 2 ^ (prefixWord ++ tailWord_961879).sum := by decide
  have hdescent : baseEnd_961879 < baseStart_961879 := by decide
  rcases family_descends (prefixWord ++ tailWord_961879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961882 : List Nat := [3, 1, 1, 2, 1, 2, 4, 1, 2, 1, 5]
def baseStart_961882 : Nat := 118140960795 + 961882 * 2 ^ 59
def prefixEnd_961882 : Nat := 4983230072969 + 3 ^ 40 * 961882 * 2
def baseEnd_961882 : Nat := 493907798908110865951391

theorem tailTrace_961882 : CollatzResearch.WordTrace tailWord_961882 prefixEnd_961882 493907798908110865951391 := by
  unfold tailWord_961882
  simp only [CollatzResearch.WordTrace]
  refine ⟨8770679675318316302999975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23388479134182176807999933 8770679675318316302999975)
  ·
    refine ⟨13156019512977474454499963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8770679675318316302999975 13156019512977474454499963)
    ·
      refine ⟨19734029269466211681749945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13156019512977474454499963 19734029269466211681749945)
      ·
        refine ⟨14800521952099658761312459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19734029269466211681749945 14800521952099658761312459)
        ·
          refine ⟨22200782928149488141968689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14800521952099658761312459 22200782928149488141968689)
          ·
            refine ⟨16650587196112116106476517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22200782928149488141968689 16650587196112116106476517)
            ·
              refine ⟨3121985099271021769964347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16650587196112116106476517 3121985099271021769964347)
              ·
                refine ⟨4682977648906532654946521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3121985099271021769964347 4682977648906532654946521)
                ·
                  refine ⟨3512233236679899491209891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4682977648906532654946521 3512233236679899491209891)
                  ·
                    refine ⟨5268349855019849236814837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3512233236679899491209891 5268349855019849236814837)
                    ·
                      refine ⟨493907798908110865951391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5268349855019849236814837 493907798908110865951391)
                      ·
                        rfl

theorem cell23_961882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 2, 1, 5].length) (baseStart_961882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_961882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_961882 prefixEnd_961882 := by exact prefixLift 961882
  have htrace : WordTrace (prefixWord ++ tailWord_961882) baseStart_961882 baseEnd_961882 := by
    simpa [prefixWord, tailWord_961882, baseEnd_961882] using wordTrace_append hprefix tailTrace_961882
  have hstable : (prefixWord ++ tailWord_961882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961882).length < 2 ^ (prefixWord ++ tailWord_961882).sum := by decide
  have hdescent : baseEnd_961882 < baseStart_961882 := by decide
  rcases family_descends (prefixWord ++ tailWord_961882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961932 : List Nat := [2, 2, 1, 2, 1, 3, 3, 1, 1, 7]
def baseStart_961932 : Nat := 118140960795 + 961932 * 2 ^ 59
def prefixEnd_961932 : Nat := 4983230072969 + 3 ^ 40 * 961932 * 2
def baseEnd_961932 : Nat := 164644490980278556775387

theorem tailTrace_961932 : CollatzResearch.WordTrace tailWord_961932 prefixEnd_961932 164644490980278556775387 := by
  unfold tailWord_961932
  simp only [CollatzResearch.WordTrace]
  refine ⟨17542271175546061875660025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23389694900728082500880033 17542271175546061875660025)
  ·
    refine ⟨13156703381659546406745019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17542271175546061875660025 13156703381659546406745019)
    ·
      refine ⟨19735055072489319610117529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13156703381659546406745019 19735055072489319610117529)
      ·
        refine ⟨14801291304366989707588147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19735055072489319610117529 14801291304366989707588147)
        ·
          refine ⟨22201936956550484561382221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14801291304366989707588147 22201936956550484561382221)
          ·
            refine ⟨8325726358706431710518333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22201936956550484561382221 8325726358706431710518333)
            ·
              refine ⟨3122147384514911891444375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8325726358706431710518333 3122147384514911891444375)
              ·
                refine ⟨4683221076772367837166563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3122147384514911891444375 4683221076772367837166563)
                ·
                  refine ⟨7024831615158551755749845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4683221076772367837166563 7024831615158551755749845)
                  ·
                    refine ⟨164644490980278556775387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7024831615158551755749845 164644490980278556775387)
                    ·
                      rfl

theorem cell23_961932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 1, 7].length) (baseStart_961932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_961932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_961932 prefixEnd_961932 := by exact prefixLift 961932
  have htrace : WordTrace (prefixWord ++ tailWord_961932) baseStart_961932 baseEnd_961932 := by
    simpa [prefixWord, tailWord_961932, baseEnd_961932] using wordTrace_append hprefix tailTrace_961932
  have hstable : (prefixWord ++ tailWord_961932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961932).length < 2 ^ (prefixWord ++ tailWord_961932).sum := by decide
  have hdescent : baseEnd_961932 < baseStart_961932 := by decide
  rcases family_descends (prefixWord ++ tailWord_961932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961992 : List Nat := [2, 1, 3, 1, 3, 1, 1, 1, 10]
def baseStart_961992 : Nat := 118140960795 + 961992 * 2 ^ 59
def prefixEnd_961992 : Nat := 4983230072969 + 3 ^ 40 * 961992 * 2
def baseEnd_961992 : Nat := 54884920197789492841765

theorem tailTrace_961992 : CollatzResearch.WordTrace tailWord_961992 prefixEnd_961992 54884920197789492841765 := by
  unfold tailWord_961992
  simp only [CollatzResearch.WordTrace]
  refine ⟨17543365365437376999252115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23391153820583169332336153 17543365365437376999252115)
  ·
    refine ⟨26315048048156065498878173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17543365365437376999252115 26315048048156065498878173)
    ·
      refine ⟨9868143018058524562079315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26315048048156065498878173 9868143018058524562079315)
      ·
        refine ⟨14802214527087786843118973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9868143018058524562079315 14802214527087786843118973)
        ·
          refine ⟨5550830447657920066169615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14802214527087786843118973 5550830447657920066169615)
          ·
            refine ⟨8326245671486880099254423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5550830447657920066169615 8326245671486880099254423)
            ·
              refine ⟨12489368507230320148881635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8326245671486880099254423 12489368507230320148881635)
              ·
                refine ⟨18734052760845480223322453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12489368507230320148881635 18734052760845480223322453)
                ·
                  refine ⟨54884920197789492841765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 18734052760845480223322453 54884920197789492841765)
                  ·
                    rfl

theorem cell23_961992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 10].length) (baseStart_961992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_961992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_961992 prefixEnd_961992 := by exact prefixLift 961992
  have htrace : WordTrace (prefixWord ++ tailWord_961992) baseStart_961992 baseEnd_961992 := by
    simpa [prefixWord, tailWord_961992, baseEnd_961992] using wordTrace_append hprefix tailTrace_961992
  have hstable : (prefixWord ++ tailWord_961992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961992).length < 2 ^ (prefixWord ++ tailWord_961992).sum := by decide
  have hdescent : baseEnd_961992 < baseStart_961992 := by decide
  rcases family_descends (prefixWord ++ tailWord_961992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962013 : List Nat := [1, 4, 3, 1, 1, 4, 1, 1, 3, 4]
def baseStart_962013 : Nat := 118140960795 + 962013 * 2 ^ 59
def prefixEnd_962013 : Nat := 4983230072969 + 3 ^ 40 * 962013 * 2
def baseEnd_962013 : Nat := 164658354957949951137763

theorem tailTrace_962013 : CollatzResearch.WordTrace tailWord_962013 prefixEnd_962013 164658354957949951137763 := by
  unfold tailWord_962013
  simp only [CollatzResearch.WordTrace]
  refine ⟨35087496663798674585018693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23391664442532449723345795 35087496663798674585018693)
  ·
    refine ⟨6578905624462251484691005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35087496663798674585018693 6578905624462251484691005)
    ·
      refine ⟨2467089609173344306759127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6578905624462251484691005 2467089609173344306759127)
      ·
        refine ⟨3700634413760016460138691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2467089609173344306759127 3700634413760016460138691)
        ·
          refine ⟨5550951620640024690208037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3700634413760016460138691 5550951620640024690208037)
          ·
            refine ⟨1040803428870004629414007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5550951620640024690208037 1040803428870004629414007)
            ·
              refine ⟨1561205143305006944121011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1040803428870004629414007 1561205143305006944121011)
              ·
                refine ⟨2341807714957510416181517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1561205143305006944121011 2341807714957510416181517)
                ·
                  refine ⟨878177893109066406068069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2341807714957510416181517 878177893109066406068069)
                  ·
                    refine ⟨164658354957949951137763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 878177893109066406068069 164658354957949951137763)
                    ·
                      rfl

theorem cell23_962013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_962013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_962013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_962013 prefixEnd_962013 := by exact prefixLift 962013
  have htrace : WordTrace (prefixWord ++ tailWord_962013) baseStart_962013 baseEnd_962013 := by
    simpa [prefixWord, tailWord_962013, baseEnd_962013] using wordTrace_append hprefix tailTrace_962013
  have hstable : (prefixWord ++ tailWord_962013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962013).length < 2 ^ (prefixWord ++ tailWord_962013).sum := by decide
  have hdescent : baseEnd_962013 < baseStart_962013 := by decide
  rcases family_descends (prefixWord ++ tailWord_962013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962026 : List Nat := [3, 1, 3, 1, 4, 1, 1, 3, 6]
def baseStart_962026 : Nat := 118140960795 + 962026 * 2 ^ 59
def prefixEnd_962026 : Nat := 4983230072969 + 3 ^ 40 * 962026 * 2
def baseEnd_962026 : Nat := 54886860013595366950081

theorem tailTrace_962026 : CollatzResearch.WordTrace tailWord_962026 prefixEnd_962026 54886860013595366950081 := by
  unfold tailWord_962026
  simp only [CollatzResearch.WordTrace]
  refine ⟨8771992703187894451310483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23391980541834385203494621 8771992703187894451310483)
  ·
    refine ⟨13157989054781841676965725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8771992703187894451310483 13157989054781841676965725)
    ·
      refine ⟨4934245895543190628862147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13157989054781841676965725 4934245895543190628862147)
      ·
        refine ⟨7401368843314785943293221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4934245895543190628862147 7401368843314785943293221)
        ·
          refine ⟨1387756658121522364367479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7401368843314785943293221 1387756658121522364367479)
          ·
            refine ⟨2081634987182283546551219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1387756658121522364367479 2081634987182283546551219)
            ·
              refine ⟨3122452480773425319826829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2081634987182283546551219 3122452480773425319826829)
              ·
                refine ⟨1170919680290034494935061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3122452480773425319826829 1170919680290034494935061)
                ·
                  refine ⟨54886860013595366950081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1170919680290034494935061 54886860013595366950081)
                  ·
                    rfl

theorem cell23_962026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 3, 6].length) (baseStart_962026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_962026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_962026 prefixEnd_962026 := by exact prefixLift 962026
  have htrace : WordTrace (prefixWord ++ tailWord_962026) baseStart_962026 baseEnd_962026 := by
    simpa [prefixWord, tailWord_962026, baseEnd_962026] using wordTrace_append hprefix tailTrace_962026
  have hstable : (prefixWord ++ tailWord_962026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962026).length < 2 ^ (prefixWord ++ tailWord_962026).sum := by decide
  have hdescent : baseEnd_962026 < baseStart_962026 := by decide
  rcases family_descends (prefixWord ++ tailWord_962026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962039 : List Nat := [1, 1, 3, 1, 1, 1, 1, 8, 1, 5]
def baseStart_962039 : Nat := 118140960795 + 962039 * 2 ^ 59
def prefixEnd_962039 : Nat := 4983230072969 + 3 ^ 40 * 962039 * 2
def baseEnd_962039 : Nat := 164662805123622250562723

theorem tailTrace_962039 : CollatzResearch.WordTrace tailWord_962039 prefixEnd_962039 164662805123622250562723 := by
  unfold tailWord_962039
  simp only [CollatzResearch.WordTrace]
  refine ⟨35088444961704481025465171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23392296641136320683643447 35088444961704481025465171)
  ·
    refine ⟨52632667442556721538197757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35088444961704481025465171 52632667442556721538197757)
    ·
      refine ⟨19737250290958770576824159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52632667442556721538197757 19737250290958770576824159)
      ·
        refine ⟨29605875436438155865236239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19737250290958770576824159 29605875436438155865236239)
        ·
          refine ⟨44408813154657233797854359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29605875436438155865236239 44408813154657233797854359)
          ·
            refine ⟨66613219731985850696781539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44408813154657233797854359 66613219731985850696781539)
            ·
              refine ⟨99919829597978776045172309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66613219731985850696781539 99919829597978776045172309)
              ·
                refine ⟨1170935503101313781779363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 99919829597978776045172309 1170935503101313781779363)
                ·
                  refine ⟨1756403254651970672669045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1170935503101313781779363 1756403254651970672669045)
                  ·
                    refine ⟨164662805123622250562723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1756403254651970672669045 164662805123622250562723)
                    ·
                      rfl

theorem cell23_962039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 8, 1, 5].length) (baseStart_962039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_962039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_962039 prefixEnd_962039 := by exact prefixLift 962039
  have htrace : WordTrace (prefixWord ++ tailWord_962039) baseStart_962039 baseEnd_962039 := by
    simpa [prefixWord, tailWord_962039, baseEnd_962039] using wordTrace_append hprefix tailTrace_962039
  have hstable : (prefixWord ++ tailWord_962039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962039).length < 2 ^ (prefixWord ++ tailWord_962039).sum := by decide
  have hdescent : baseEnd_962039 < baseStart_962039 := by decide
  rcases family_descends (prefixWord ++ tailWord_962039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962053 : List Nat := [1, 3, 1, 1, 2, 2, 1, 7, 1, 1, 3]
def baseStart_962053 : Nat := 118140960795 + 962053 * 2 ^ 59
def prefixEnd_962053 : Nat := 4983230072969 + 3 ^ 40 * 962053 * 2
def baseEnd_962053 : Nat := 493995604100029696913105

theorem tailTrace_962053 : CollatzResearch.WordTrace tailWord_962053 prefixEnd_962053 493995604100029696913105 := by
  unfold tailWord_962053
  simp only [CollatzResearch.WordTrace]
  refine ⟨35088955583653761416474813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23392637055769174277649875 35088955583653761416474813)
  ·
    refine ⟨13158358343870160531178055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35088955583653761416474813 13158358343870160531178055)
    ·
      refine ⟨19737537515805240796767083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13158358343870160531178055 19737537515805240796767083)
      ·
        refine ⟨29606306273707861195150625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19737537515805240796767083 29606306273707861195150625)
        ·
          refine ⟨22204729705280895896362969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29606306273707861195150625 22204729705280895896362969)
          ·
            refine ⟨16653547278960671922272227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22204729705280895896362969 16653547278960671922272227)
            ·
              refine ⟨24980320918441007883408341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16653547278960671922272227 24980320918441007883408341)
              ·
                refine ⟨585476271525961122267383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 24980320918441007883408341 585476271525961122267383)
                ·
                  refine ⟨878214407288941683401075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 585476271525961122267383 878214407288941683401075)
                  ·
                    refine ⟨1317321610933412525101613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 878214407288941683401075 1317321610933412525101613)
                    ·
                      refine ⟨493995604100029696913105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1317321610933412525101613 493995604100029696913105)
                      ·
                        rfl

theorem cell23_962053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 7, 1, 1, 3].length) (baseStart_962053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_962053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_962053 prefixEnd_962053 := by exact prefixLift 962053
  have htrace : WordTrace (prefixWord ++ tailWord_962053) baseStart_962053 baseEnd_962053 := by
    simpa [prefixWord, tailWord_962053, baseEnd_962053] using wordTrace_append hprefix tailTrace_962053
  have hstable : (prefixWord ++ tailWord_962053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962053).length < 2 ^ (prefixWord ++ tailWord_962053).sum := by decide
  have hdescent : baseEnd_962053 < baseStart_962053 := by decide
  rcases family_descends (prefixWord ++ tailWord_962053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962079 : List Nat := [1, 1, 2, 4, 1, 1, 2, 4, 1, 1, 5]
def baseStart_962079 : Nat := 118140960795 + 962079 * 2 ^ 59
def prefixEnd_962079 : Nat := 4983230072969 + 3 ^ 40 * 962079 * 2
def baseEnd_962079 : Nat := 494008954597046595187985

theorem tailTrace_962079 : CollatzResearch.WordTrace tailWord_962079 prefixEnd_962079 494008954597046595187985 := by
  unfold tailWord_962079
  simp only [CollatzResearch.WordTrace]
  refine ⟨35089903881559567856921291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23393269254373045237947527 35089903881559567856921291)
  ·
    refine ⟨52634855822339351785381937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35089903881559567856921291 52634855822339351785381937)
    ·
      refine ⟨39476141866754513839036453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52634855822339351785381937 39476141866754513839036453)
      ·
        refine ⟨7401776600016471344819335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39476141866754513839036453 7401776600016471344819335)
        ·
          refine ⟨11102664900024707017229003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7401776600016471344819335 11102664900024707017229003)
          ·
            refine ⟨16653997350037060525843505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11102664900024707017229003 16653997350037060525843505)
            ·
              refine ⟨12490498012527795394382629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16653997350037060525843505 12490498012527795394382629)
              ·
                refine ⟨2341968377348961636446743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12490498012527795394382629 2341968377348961636446743)
                ·
                  refine ⟨3512952566023442454670115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2341968377348961636446743 3512952566023442454670115)
                  ·
                    refine ⟨5269428849035163682005173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3512952566023442454670115 5269428849035163682005173)
                    ·
                      refine ⟨494008954597046595187985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5269428849035163682005173 494008954597046595187985)
                      ·
                        rfl

theorem cell23_962079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_962079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_962079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_962079 prefixEnd_962079 := by exact prefixLift 962079
  have htrace : WordTrace (prefixWord ++ tailWord_962079) baseStart_962079 baseEnd_962079 := by
    simpa [prefixWord, tailWord_962079, baseEnd_962079] using wordTrace_append hprefix tailTrace_962079
  have hstable : (prefixWord ++ tailWord_962079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962079).length < 2 ^ (prefixWord ++ tailWord_962079).sum := by decide
  have hdescent : baseEnd_962079 < baseStart_962079 := by decide
  rcases family_descends (prefixWord ++ tailWord_962079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962096 : List Nat := [2, 1, 1, 1, 2, 3, 1, 6, 1, 2, 3]
def baseStart_962096 : Nat := 118140960795 + 962096 * 2 ^ 59
def prefixEnd_962096 : Nat := 4983230072969 + 3 ^ 40 * 962096 * 2
def baseEnd_962096 : Nat := 494017683768173028675407

theorem tailTrace_962096 : CollatzResearch.WordTrace tailWord_962096 prefixEnd_962096 494017683768173028675407 := by
  unfold tailWord_962096
  simp only [CollatzResearch.WordTrace]
  refine ⟨17545261961248989880145071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23393682614998653173526761 17545261961248989880145071)
  ·
    refine ⟨26317892941873484820217607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17545261961248989880145071 26317892941873484820217607)
    ·
      refine ⟨39476839412810227230326411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26317892941873484820217607 39476839412810227230326411)
      ·
        refine ⟨59215259119215340845489617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39476839412810227230326411 59215259119215340845489617)
        ·
          refine ⟨44411444339411505634117213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59215259119215340845489617 44411444339411505634117213)
          ·
            refine ⟨16654291627279314612793955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44411444339411505634117213 16654291627279314612793955)
            ·
              refine ⟨24981437440918971919190933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16654291627279314612793955 24981437440918971919190933)
              ·
                refine ⟨1171004880043076808712075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24981437440918971919190933 1171004880043076808712075)
                ·
                  refine ⟨1756507320064615213068113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1171004880043076808712075 1756507320064615213068113)
                  ·
                    refine ⟨1317380490048461409801085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1756507320064615213068113 1317380490048461409801085)
                    ·
                      refine ⟨494017683768173028675407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1317380490048461409801085 494017683768173028675407)
                      ·
                        rfl

theorem cell23_962096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 6, 1, 2, 3].length) (baseStart_962096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_962096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_962096 prefixEnd_962096 := by exact prefixLift 962096
  have htrace : WordTrace (prefixWord ++ tailWord_962096) baseStart_962096 baseEnd_962096 := by
    simpa [prefixWord, tailWord_962096, baseEnd_962096] using wordTrace_append hprefix tailTrace_962096
  have hstable : (prefixWord ++ tailWord_962096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962096).length < 2 ^ (prefixWord ++ tailWord_962096).sum := by decide
  have hdescent : baseEnd_962096 < baseStart_962096 := by decide
  rcases family_descends (prefixWord ++ tailWord_962096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962113 : List Nat := [1, 2, 5, 1, 1, 1, 3, 3, 1, 2, 3]
def baseStart_962113 : Nat := 118140960795 + 962113 * 2 ^ 59
def prefixEnd_962113 : Nat := 4983230072969 + 3 ^ 40 * 962113 * 2
def baseEnd_962113 : Nat := 494026412939299462162829

theorem tailTrace_962113 : CollatzResearch.WordTrace tailWord_962113 prefixEnd_962113 494026412939299462162829 := by
  unfold tailWord_962113
  simp only [CollatzResearch.WordTrace]
  refine ⟨35091143963436391663658993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23394095975624261109105995 35091143963436391663658993)
  ·
    refine ⟨26318357972577293747744245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35091143963436391663658993 26318357972577293747744245)
    ·
      refine ⟨2467346059929121288851023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26318357972577293747744245 2467346059929121288851023)
      ·
        refine ⟨3701019089893681933276535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2467346059929121288851023 3701019089893681933276535)
        ·
          refine ⟨5551528634840522899914803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3701019089893681933276535 5551528634840522899914803)
          ·
            refine ⟨8327292952260784349872205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5551528634840522899914803 8327292952260784349872205)
            ·
              refine ⟨3122734857097794131202077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8327292952260784349872205 3122734857097794131202077)
              ·
                refine ⟨1171025571411672799200779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3122734857097794131202077 1171025571411672799200779)
                ·
                  refine ⟨1756538357117509198801169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1171025571411672799200779 1756538357117509198801169)
                  ·
                    refine ⟨1317403767838131899100877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1756538357117509198801169 1317403767838131899100877)
                    ·
                      refine ⟨494026412939299462162829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1317403767838131899100877 494026412939299462162829)
                      ·
                        rfl

theorem cell23_962113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_962113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_962113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_962113 prefixEnd_962113 := by exact prefixLift 962113
  have htrace : WordTrace (prefixWord ++ tailWord_962113) baseStart_962113 baseEnd_962113 := by
    simpa [prefixWord, tailWord_962113, baseEnd_962113] using wordTrace_append hprefix tailTrace_962113
  have hstable : (prefixWord ++ tailWord_962113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962113).length < 2 ^ (prefixWord ++ tailWord_962113).sum := by decide
  have hdescent : baseEnd_962113 < baseStart_962113 := by decide
  rcases family_descends (prefixWord ++ tailWord_962113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962153 : List Nat := [1, 2, 1, 1, 1, 4, 3, 4, 1, 3, 2]
def baseStart_962153 : Nat := 118140960795 + 962153 * 2 ^ 59
def prefixEnd_962153 : Nat := 4983230072969 + 3 ^ 40 * 962153 * 2
def baseEnd_962153 : Nat := 494046952165479305662645

theorem tailTrace_962153 : CollatzResearch.WordTrace tailWord_962153 prefixEnd_962153 494046952165479305662645 := by
  unfold tailWord_962153
  simp only [CollatzResearch.WordTrace]
  refine ⟨35092602883291478495115113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23395068588860985663410075 35092602883291478495115113)
  ·
    refine ⟨26319452162468608871336335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35092602883291478495115113 26319452162468608871336335)
    ·
      refine ⟨39479178243702913307004503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26319452162468608871336335 39479178243702913307004503)
      ·
        refine ⟨59218767365554369960506755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39479178243702913307004503 59218767365554369960506755)
        ·
          refine ⟨88828151048331554940760133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59218767365554369960506755 88828151048331554940760133)
          ·
            refine ⟨16655278321562166551392525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88828151048331554940760133 16655278321562166551392525)
            ·
              refine ⟨6245729370585812456772197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16655278321562166551392525 6245729370585812456772197)
              ·
                refine ⟨1171074256984839835644787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6245729370585812456772197 1171074256984839835644787)
                ·
                  refine ⟨1756611385477259753467181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1171074256984839835644787 1756611385477259753467181)
                  ·
                    refine ⟨658729269553972407550193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1756611385477259753467181 658729269553972407550193)
                    ·
                      refine ⟨494046952165479305662645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 658729269553972407550193 494046952165479305662645)
                      ·
                        rfl

theorem cell23_962153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 4, 1, 3, 2].length) (baseStart_962153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_962153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_962153 prefixEnd_962153 := by exact prefixLift 962153
  have htrace : WordTrace (prefixWord ++ tailWord_962153) baseStart_962153 baseEnd_962153 := by
    simpa [prefixWord, tailWord_962153, baseEnd_962153] using wordTrace_append hprefix tailTrace_962153
  have hstable : (prefixWord ++ tailWord_962153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962153).length < 2 ^ (prefixWord ++ tailWord_962153).sum := by decide
  have hdescent : baseEnd_962153 < baseStart_962153 := by decide
  rcases family_descends (prefixWord ++ tailWord_962153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962194 : List Nat := [3, 2, 3, 1, 3, 2, 2, 1, 2, 1, 3]
def baseStart_962194 : Nat := 118140960795 + 962194 * 2 ^ 59
def prefixEnd_962194 : Nat := 4983230072969 + 3 ^ 40 * 962194 * 2
def baseEnd_962194 : Nat := 494068004872313645249957

theorem tailTrace_962194 : CollatzResearch.WordTrace tailWord_962194 prefixEnd_962194 494068004872313645249957 := by
  unfold tailWord_962194
  simp only [CollatzResearch.WordTrace]
  refine ⟨8773524569035735624339409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23396065517428628331571757 8773524569035735624339409)
  ·
    refine ⟨6580143426776801718254557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8773524569035735624339409 6580143426776801718254557)
    ·
      refine ⟨2467553785041300644345459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6580143426776801718254557 2467553785041300644345459)
      ·
        refine ⟨3701330677561950966518189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2467553785041300644345459 3701330677561950966518189)
        ·
          refine ⟨1387999004085731612444321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3701330677561950966518189 1387999004085731612444321)
          ·
            refine ⟨1040999253064298709333241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1387999004085731612444321 1040999253064298709333241)
            ·
              refine ⟨780749439798224031999931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1040999253064298709333241 780749439798224031999931)
              ·
                refine ⟨1171124159697336047999897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 780749439798224031999931 1171124159697336047999897)
                ·
                  refine ⟨878343119773002035999923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1171124159697336047999897 878343119773002035999923)
                  ·
                    refine ⟨1317514679659503053999885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 878343119773002035999923 1317514679659503053999885)
                    ·
                      refine ⟨494068004872313645249957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1317514679659503053999885 494068004872313645249957)
                      ·
                        rfl

theorem cell23_962194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 2, 1, 2, 1, 3].length) (baseStart_962194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_962194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_962194 prefixEnd_962194 := by exact prefixLift 962194
  have htrace : WordTrace (prefixWord ++ tailWord_962194) baseStart_962194 baseEnd_962194 := by
    simpa [prefixWord, tailWord_962194, baseEnd_962194] using wordTrace_append hprefix tailTrace_962194
  have hstable : (prefixWord ++ tailWord_962194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962194).length < 2 ^ (prefixWord ++ tailWord_962194).sum := by decide
  have hdescent : baseEnd_962194 < baseStart_962194 := by decide
  rcases family_descends (prefixWord ++ tailWord_962194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962204 : List Nat := [2, 2, 3, 2, 4, 1, 1, 2, 1, 3, 2]
def baseStart_962204 : Nat := 118140960795 + 962204 * 2 ^ 59
def prefixEnd_962204 : Nat := 4983230072969 + 3 ^ 40 * 962204 * 2
def baseEnd_962204 : Nat := 494073139678858606124911

theorem tailTrace_962204 : CollatzResearch.WordTrace tailWord_962204 prefixEnd_962204 494073139678858606124911 := by
  unfold tailWord_962204
  simp only [CollatzResearch.WordTrace]
  refine ⟨17547231503053357102610833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23396308670737809470147777 17547231503053357102610833)
  ·
    refine ⟨13160423627290017826958125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17547231503053357102610833 13160423627290017826958125)
    ·
      refine ⟨4935158860233756685109297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13160423627290017826958125 4935158860233756685109297)
      ·
        refine ⟨3701369145175317513831973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4935158860233756685109297 3701369145175317513831973)
        ·
          refine ⟨694006714720372033843495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3701369145175317513831973 694006714720372033843495)
          ·
            refine ⟨1041010072080558050765243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 694006714720372033843495 1041010072080558050765243)
            ·
              refine ⟨1561515108120837076147865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1041010072080558050765243 1561515108120837076147865)
              ·
                refine ⟨1171136331090627807110899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1561515108120837076147865 1171136331090627807110899)
                ·
                  refine ⟨1756704496635941710666349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1171136331090627807110899 1756704496635941710666349)
                  ·
                    refine ⟨658764186238478141499881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1756704496635941710666349 658764186238478141499881)
                    ·
                      refine ⟨494073139678858606124911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 658764186238478141499881 494073139678858606124911)
                      ·
                        rfl

theorem cell23_962204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 2, 1, 3, 2].length) (baseStart_962204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_962204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_962204 prefixEnd_962204 := by exact prefixLift 962204
  have htrace : WordTrace (prefixWord ++ tailWord_962204) baseStart_962204 baseEnd_962204 := by
    simpa [prefixWord, tailWord_962204, baseEnd_962204] using wordTrace_append hprefix tailTrace_962204
  have hstable : (prefixWord ++ tailWord_962204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962204).length < 2 ^ (prefixWord ++ tailWord_962204).sum := by decide
  have hdescent : baseEnd_962204 < baseStart_962204 := by decide
  rcases family_descends (prefixWord ++ tailWord_962204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962273 : List Nat := [1, 2, 3, 1, 5, 1, 1, 1, 1, 3, 4]
def baseStart_962273 : Nat := 118140960795 + 962273 * 2 ^ 59
def prefixEnd_962273 : Nat := 4983230072969 + 3 ^ 40 * 962273 * 2
def baseEnd_962273 : Nat := 494108569844018836162093

theorem tailTrace_962273 : CollatzResearch.WordTrace tailWord_962273 prefixEnd_962273 494108569844018836162093 := by
  unfold tailWord_962273
  simp only [CollatzResearch.WordTrace]
  refine ⟨35096979642856738989483473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23397986428571159326322315 35096979642856738989483473)
  ·
    refine ⟨26322734732142554242112605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35096979642856738989483473 26322734732142554242112605)
    ·
      refine ⟨9871025524553457840792227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26322734732142554242112605 9871025524553457840792227)
      ·
        refine ⟨14806538286830186761188341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9871025524553457840792227 14806538286830186761188341)
        ·
          refine ⟨1388112964390330008861407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14806538286830186761188341 1388112964390330008861407)
          ·
            refine ⟨2082169446585495013292111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1388112964390330008861407 2082169446585495013292111)
            ·
              refine ⟨3123254169878242519938167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2082169446585495013292111 3123254169878242519938167)
              ·
                refine ⟨4684881254817363779907251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3123254169878242519938167 4684881254817363779907251)
                ·
                  refine ⟨7027321882226045669860877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4684881254817363779907251 7027321882226045669860877)
                  ·
                    refine ⟨2635245705834767126197829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7027321882226045669860877 2635245705834767126197829)
                    ·
                      refine ⟨494108569844018836162093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2635245705834767126197829 494108569844018836162093)
                      ·
                        rfl

theorem cell23_962273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 3, 4].length) (baseStart_962273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_962273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_962273 prefixEnd_962273 := by exact prefixLift 962273
  have htrace : WordTrace (prefixWord ++ tailWord_962273) baseStart_962273 baseEnd_962273 := by
    simpa [prefixWord, tailWord_962273, baseEnd_962273] using wordTrace_append hprefix tailTrace_962273
  have hstable : (prefixWord ++ tailWord_962273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962273).length < 2 ^ (prefixWord ++ tailWord_962273).sum := by decide
  have hdescent : baseEnd_962273 < baseStart_962273 := by decide
  rcases family_descends (prefixWord ++ tailWord_962273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962286 : List Nat := [4, 1, 2, 1, 1, 2, 1, 1, 1, 3, 6]
def baseStart_962286 : Nat := 118140960795 + 962286 * 2 ^ 59
def prefixEnd_962286 : Nat := 4983230072969 + 3 ^ 40 * 962286 * 2
def baseEnd_962286 : Nat := 494115245092527285299533

theorem tailTrace_962286 : CollatzResearch.WordTrace tailWord_962286 prefixEnd_962286 494115245092527285299533 := by
  unfold tailWord_962286
  simp only [CollatzResearch.WordTrace]
  refine ⟨4387181723976205276213339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23398302527873094806471141 4387181723976205276213339)
  ·
    refine ⟨6580772585964307914320009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4387181723976205276213339 6580772585964307914320009)
    ·
      refine ⟨4935579439473230935740007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6580772585964307914320009 4935579439473230935740007)
      ·
        refine ⟨7403369159209846403610011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4935579439473230935740007 7403369159209846403610011)
        ·
          refine ⟨11105053738814769605415017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7403369159209846403610011 11105053738814769605415017)
          ·
            refine ⟨8328790304111077204061263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11105053738814769605415017 8328790304111077204061263)
            ·
              refine ⟨12493185456166615806091895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8328790304111077204061263 12493185456166615806091895)
              ·
                refine ⟨18739778184249923709137843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12493185456166615806091895 18739778184249923709137843)
                ·
                  refine ⟨28109667276374885563706765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18739778184249923709137843 28109667276374885563706765)
                  ·
                    refine ⟨10541125228640582086390037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28109667276374885563706765 10541125228640582086390037)
                    ·
                      refine ⟨494115245092527285299533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10541125228640582086390037 494115245092527285299533)
                      ·
                        rfl

theorem cell23_962286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_962286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_962286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_962286 prefixEnd_962286 := by exact prefixLift 962286
  have htrace : WordTrace (prefixWord ++ tailWord_962286) baseStart_962286 baseEnd_962286 := by
    simpa [prefixWord, tailWord_962286, baseEnd_962286] using wordTrace_append hprefix tailTrace_962286
  have hstable : (prefixWord ++ tailWord_962286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962286).length < 2 ^ (prefixWord ++ tailWord_962286).sum := by decide
  have hdescent : baseEnd_962286 < baseStart_962286 := by decide
  rcases family_descends (prefixWord ++ tailWord_962286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962296 : List Nat := [2, 1, 2, 1, 1, 2, 2, 6, 6]
def baseStart_962296 : Nat := 118140960795 + 962296 * 2 ^ 59
def prefixEnd_962296 : Nat := 4983230072969 + 3 ^ 40 * 962296 * 2
def baseEnd_962296 : Nat := 54902264433230249574943

theorem tailTrace_962296 : CollatzResearch.WordTrace tailWord_962296 prefixEnd_962296 54902264433230249574943 := by
  unfold tailWord_962296
  simp only [CollatzResearch.WordTrace]
  refine ⟨17548909260886706958785371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23398545681182275945047161 17548909260886706958785371)
  ·
    refine ⟨26323363891330060438178057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17548909260886706958785371 26323363891330060438178057)
    ·
      refine ⟨19742522918497545328633543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26323363891330060438178057 19742522918497545328633543)
      ·
        refine ⟨29613784377746317992950315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19742522918497545328633543 29613784377746317992950315)
        ·
          refine ⟨44420676566619476989425473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29613784377746317992950315 44420676566619476989425473)
          ·
            refine ⟨33315507424964607742069105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44420676566619476989425473 33315507424964607742069105)
            ·
              refine ⟨24986630568723455806551829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33315507424964607742069105 24986630568723455806551829)
              ·
                refine ⟨1171248307908911990932117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24986630568723455806551829 1171248307908911990932117)
                ·
                  refine ⟨54902264433230249574943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1171248307908911990932117 54902264433230249574943)
                  ·
                    rfl

theorem cell23_962296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 6, 6].length) (baseStart_962296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_962296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_962296 prefixEnd_962296 := by exact prefixLift 962296
  have htrace : WordTrace (prefixWord ++ tailWord_962296) baseStart_962296 baseEnd_962296 := by
    simpa [prefixWord, tailWord_962296, baseEnd_962296] using wordTrace_append hprefix tailTrace_962296
  have hstable : (prefixWord ++ tailWord_962296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962296).length < 2 ^ (prefixWord ++ tailWord_962296).sum := by decide
  have hdescent : baseEnd_962296 < baseStart_962296 := by decide
  rcases family_descends (prefixWord ++ tailWord_962296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962300 : List Nat := [2, 2, 2, 1, 3, 1, 1, 6, 1, 4]
def baseStart_962300 : Nat := 118140960795 + 962300 * 2 ^ 59
def prefixEnd_962300 : Nat := 4983230072969 + 3 ^ 40 * 962300 * 2
def baseEnd_962300 : Nat := 164707477940563410174823

theorem tailTrace_962300 : CollatzResearch.WordTrace tailWord_962300 prefixEnd_962300 164707477940563410174823 := by
  unfold tailWord_962300
  simp only [CollatzResearch.WordTrace]
  refine ⟨17548982206879461300358177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23398642942505948400477569 17548982206879461300358177)
  ·
    refine ⟨13161736655159595975268633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17548982206879461300358177 13161736655159595975268633)
    ·
      refine ⟨9871302491369696981451475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13161736655159595975268633 9871302491369696981451475)
      ·
        refine ⟨14806953737054545472177213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9871302491369696981451475 14806953737054545472177213)
        ·
          refine ⟨5552607651395454552066455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14806953737054545472177213 5552607651395454552066455)
          ·
            refine ⟨8328911477093181828099683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5552607651395454552066455 8328911477093181828099683)
            ·
              refine ⟨12493367215639772742149525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8328911477093181828099683 12493367215639772742149525)
              ·
                refine ⟨585626588233114347288259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12493367215639772742149525 585626588233114347288259)
                ·
                  refine ⟨878439882349671520932389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 585626588233114347288259 878439882349671520932389)
                  ·
                    refine ⟨164707477940563410174823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 878439882349671520932389 164707477940563410174823)
                    ·
                      rfl

theorem cell23_962300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 6, 1, 4].length) (baseStart_962300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_962300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_962300 prefixEnd_962300 := by exact prefixLift 962300
  have htrace : WordTrace (prefixWord ++ tailWord_962300) baseStart_962300 baseEnd_962300 := by
    simpa [prefixWord, tailWord_962300, baseEnd_962300] using wordTrace_append hprefix tailTrace_962300
  have hstable : (prefixWord ++ tailWord_962300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962300).length < 2 ^ (prefixWord ++ tailWord_962300).sum := by decide
  have hdescent : baseEnd_962300 < baseStart_962300 := by decide
  rcases family_descends (prefixWord ++ tailWord_962300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962323 : List Nat := [1, 1, 1, 2, 1, 3, 2, 3, 5, 1, 3]
def baseStart_962323 : Nat := 118140960795 + 962323 * 2 ^ 59
def prefixEnd_962323 : Nat := 4983230072969 + 3 ^ 40 * 962323 * 2
def baseEnd_962323 : Nat := 494134243876743640536863

theorem tailTrace_962323 : CollatzResearch.WordTrace tailWord_962323 prefixEnd_962323 494134243876743640536863 := by
  unfold tailWord_962323
  simp only [CollatzResearch.WordTrace]
  refine ⟨35098803292675597528803623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23399202195117065019202415 35098803292675597528803623)
  ·
    refine ⟨52648204939013396293205435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35098803292675597528803623 52648204939013396293205435)
    ·
      refine ⟨78972307408520094439808153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52648204939013396293205435 78972307408520094439808153)
      ·
        refine ⟨59229230556390070829856115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78972307408520094439808153 59229230556390070829856115)
        ·
          refine ⟨88843845834585106244784173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59229230556390070829856115 88843845834585106244784173)
          ·
            refine ⟨33316442187969414841794065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88843845834585106244784173 33316442187969414841794065)
            ·
              refine ⟨24987331640977061131345549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33316442187969414841794065 24987331640977061131345549)
              ·
                refine ⟨9370249365366397924254581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24987331640977061131345549 9370249365366397924254581)
                ·
                  refine ⟨878460878003099805398867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9370249365366397924254581 878460878003099805398867)
                  ·
                    refine ⟨1317691317004649708098301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 878460878003099805398867 1317691317004649708098301)
                    ·
                      refine ⟨494134243876743640536863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1317691317004649708098301 494134243876743640536863)
                      ·
                        rfl

theorem cell23_962323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 5, 1, 3].length) (baseStart_962323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_962323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_962323 prefixEnd_962323 := by exact prefixLift 962323
  have htrace : WordTrace (prefixWord ++ tailWord_962323) baseStart_962323 baseEnd_962323 := by
    simpa [prefixWord, tailWord_962323, baseEnd_962323] using wordTrace_append hprefix tailTrace_962323
  have hstable : (prefixWord ++ tailWord_962323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962323).length < 2 ^ (prefixWord ++ tailWord_962323).sum := by decide
  have hdescent : baseEnd_962323 < baseStart_962323 := by decide
  rcases family_descends (prefixWord ++ tailWord_962323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962380 : List Nat := [2, 2, 1, 3, 4, 1, 1, 1, 3, 1, 4]
def baseStart_962380 : Nat := 118140960795 + 962380 * 2 ^ 59
def prefixEnd_962380 : Nat := 4983230072969 + 3 ^ 40 * 962380 * 2
def baseEnd_962380 : Nat := 494163512274049917524101

theorem tailTrace_962380 : CollatzResearch.WordTrace tailWord_962380 prefixEnd_962380 494163512274049917524101 := by
  unfold tailWord_962380
  simp only [CollatzResearch.WordTrace]
  refine ⟨17550441126734548131814297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23400588168979397509085729 17550441126734548131814297)
  ·
    refine ⟨13162830845050911098860723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17550441126734548131814297 13162830845050911098860723)
    ·
      refine ⟨19744246267576366648291085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13162830845050911098860723 19744246267576366648291085)
      ·
        refine ⟨7404092350341137493109157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19744246267576366648291085 7404092350341137493109157)
        ·
          refine ⟨1388267315688963279957967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7404092350341137493109157 1388267315688963279957967)
          ·
            refine ⟨2082400973533444919936951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1388267315688963279957967 2082400973533444919936951)
            ·
              refine ⟨3123601460300167379905427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2082400973533444919936951 3123601460300167379905427)
              ·
                refine ⟨4685402190450251069858141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3123601460300167379905427 4685402190450251069858141)
                ·
                  refine ⟨1757025821418844151196803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4685402190450251069858141 1757025821418844151196803)
                  ·
                    refine ⟨2635538732128266226795205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1757025821418844151196803 2635538732128266226795205)
                    ·
                      refine ⟨494163512274049917524101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2635538732128266226795205 494163512274049917524101)
                      ·
                        rfl

theorem cell23_962380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 3, 1, 4].length) (baseStart_962380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_962380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_962380 prefixEnd_962380 := by exact prefixLift 962380
  have htrace : WordTrace (prefixWord ++ tailWord_962380) baseStart_962380 baseEnd_962380 := by
    simpa [prefixWord, tailWord_962380, baseEnd_962380] using wordTrace_append hprefix tailTrace_962380
  have hstable : (prefixWord ++ tailWord_962380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962380).length < 2 ^ (prefixWord ++ tailWord_962380).sum := by decide
  have hdescent : baseEnd_962380 < baseStart_962380 := by decide
  rcases family_descends (prefixWord ++ tailWord_962380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962393 : List Nat := [1, 2, 1, 2, 2, 3, 3, 2, 1, 2, 4]
def baseStart_962393 : Nat := 118140960795 + 962393 * 2 ^ 59
def prefixEnd_962393 : Nat := 4983230072969 + 3 ^ 40 * 962393 * 2
def baseEnd_962393 : Nat := 494170187522558366661541

theorem tailTrace_962393 : CollatzResearch.WordTrace tailWord_962393 prefixEnd_962393 494170187522558366661541 := by
  unfold tailWord_962393
  simp only [CollatzResearch.WordTrace]
  refine ⟨35101356402421999483851833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23400904268281332989234555 35101356402421999483851833)
  ·
    refine ⟨26326017301816499612888875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35101356402421999483851833 26326017301816499612888875)
    ·
      refine ⟨39489025952724749419333313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26326017301816499612888875 39489025952724749419333313)
      ·
        refine ⟨29616769464543562064499985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39489025952724749419333313 29616769464543562064499985)
        ·
          refine ⟨22212577098407671548374989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29616769464543562064499985 22212577098407671548374989)
          ·
            refine ⟨8329716411902876830640621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22212577098407671548374989 8329716411902876830640621)
            ·
              refine ⟨3123643654463578811490233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8329716411902876830640621 3123643654463578811490233)
              ·
                refine ⟨2342732740847684108617675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3123643654463578811490233 2342732740847684108617675)
                ·
                  refine ⟨3514099111271526162926513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2342732740847684108617675 3514099111271526162926513)
                  ·
                    refine ⟨2635574333453644622194885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3514099111271526162926513 2635574333453644622194885)
                    ·
                      refine ⟨494170187522558366661541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2635574333453644622194885 494170187522558366661541)
                      ·
                        rfl

theorem cell23_962393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 2, 1, 2, 4].length) (baseStart_962393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_962393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_962393 prefixEnd_962393 := by exact prefixLift 962393
  have htrace : WordTrace (prefixWord ++ tailWord_962393) baseStart_962393 baseEnd_962393 := by
    simpa [prefixWord, tailWord_962393, baseEnd_962393] using wordTrace_append hprefix tailTrace_962393
  have hstable : (prefixWord ++ tailWord_962393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962393).length < 2 ^ (prefixWord ++ tailWord_962393).sum := by decide
  have hdescent : baseEnd_962393 < baseStart_962393 := by decide
  rcases family_descends (prefixWord ++ tailWord_962393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962400 : List Nat := [2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 5]
def baseStart_962400 : Nat := 118140960795 + 962400 * 2 ^ 59
def prefixEnd_962400 : Nat := 4983230072969 + 3 ^ 40 * 962400 * 2
def baseEnd_962400 : Nat := 494173781887139839274009

theorem tailTrace_962400 : CollatzResearch.WordTrace tailWord_962400 prefixEnd_962400 494173781887139839274009 := by
  unfold tailWord_962400
  simp only [CollatzResearch.WordTrace]
  refine ⟨17550805856698319839678327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23401074475597759786237769 17550805856698319839678327)
  ·
    refine ⟨26326208785047479759517491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17550805856698319839678327 26326208785047479759517491)
    ·
      refine ⟨39489313177571219639276237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26326208785047479759517491 39489313177571219639276237)
      ·
        refine ⟨14808492441589207364728589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39489313177571219639276237 14808492441589207364728589)
        ·
          refine ⟨5553184665595952761773221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14808492441589207364728589 5553184665595952761773221)
          ·
            refine ⟨1041222124799241142832479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5553184665595952761773221 1041222124799241142832479)
            ·
              refine ⟨1561833187198861714248719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1041222124799241142832479 1561833187198861714248719)
              ·
                refine ⟨2342749780798292571373079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1561833187198861714248719 2342749780798292571373079)
                ·
                  refine ⟨3514124671197438857059619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2342749780798292571373079 3514124671197438857059619)
                  ·
                    refine ⟨5271187006796158285589429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3514124671197438857059619 5271187006796158285589429)
                    ·
                      refine ⟨494173781887139839274009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5271187006796158285589429 494173781887139839274009)
                      ·
                        rfl

theorem cell23_962400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 5].length) (baseStart_962400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_962400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_962400 prefixEnd_962400 := by exact prefixLift 962400
  have htrace : WordTrace (prefixWord ++ tailWord_962400) baseStart_962400 baseEnd_962400 := by
    simpa [prefixWord, tailWord_962400, baseEnd_962400] using wordTrace_append hprefix tailTrace_962400
  have hstable : (prefixWord ++ tailWord_962400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962400).length < 2 ^ (prefixWord ++ tailWord_962400).sum := by decide
  have hdescent : baseEnd_962400 < baseStart_962400 := by decide
  rcases family_descends (prefixWord ++ tailWord_962400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962403 : List Nat := [1, 1, 1, 5, 5, 10]
def baseStart_962403 : Nat := 118140960795 + 962403 * 2 ^ 59
def prefixEnd_962403 : Nat := 4983230072969 + 3 ^ 40 * 962403 * 2
def baseEnd_962403 : Nat := 2033643301765857314965

theorem tailTrace_962403 : CollatzResearch.WordTrace tailWord_962403 prefixEnd_962403 2033643301765857314965 := by
  unfold tailWord_962403
  simp only [CollatzResearch.WordTrace]
  refine ⟨35101721132385771191715863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23401147421590514127810575 35101721132385771191715863)
  ·
    refine ⟨52652581698578656787573795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35101721132385771191715863 52652581698578656787573795)
    ·
      refine ⟨78978872547867985181360693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52652581698578656787573795 78978872547867985181360693)
      ·
        refine ⟨7404269301362623610752565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78978872547867985181360693 7404269301362623610752565)
        ·
          refine ⟨694150247002745963508053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7404269301362623610752565 694150247002745963508053)
          ·
            refine ⟨2033643301765857314965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 694150247002745963508053 2033643301765857314965)
            ·
              rfl

theorem cell23_962403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 10].length) (baseStart_962403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_962403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_962403 prefixEnd_962403 := by exact prefixLift 962403
  have htrace : WordTrace (prefixWord ++ tailWord_962403) baseStart_962403 baseEnd_962403 := by
    simpa [prefixWord, tailWord_962403, baseEnd_962403] using wordTrace_append hprefix tailTrace_962403
  have hstable : (prefixWord ++ tailWord_962403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962403).length < 2 ^ (prefixWord ++ tailWord_962403).sum := by decide
  have hdescent : baseEnd_962403 < baseStart_962403 := by decide
  rcases family_descends (prefixWord ++ tailWord_962403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962473 : List Nat := [1, 2, 1, 1, 1, 1, 4, 3, 2, 4, 3]
def baseStart_962473 : Nat := 118140960795 + 962473 * 2 ^ 59
def prefixEnd_962473 : Nat := 4983230072969 + 3 ^ 40 * 962473 * 2
def baseEnd_962473 : Nat := 494211265974918053661173

theorem tailTrace_962473 : CollatzResearch.WordTrace tailWord_962473 prefixEnd_962473 494211265974918053661173 := by
  unfold tailWord_962473
  simp only [CollatzResearch.WordTrace]
  refine ⟨35104274242132173146764073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23402849494754782097842715 35104274242132173146764073)
  ·
    refine ⟨26328205681599129860073055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35104274242132173146764073 26328205681599129860073055)
    ·
      refine ⟨39492308522398694790109583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26328205681599129860073055 39492308522398694790109583)
      ·
        refine ⟨59238462783598042185164375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39492308522398694790109583 59238462783598042185164375)
        ·
          refine ⟨88857694175397063277746563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59238462783598042185164375 88857694175397063277746563)
          ·
            refine ⟨133286541263095594916619845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88857694175397063277746563 133286541263095594916619845)
            ·
              refine ⟨24991226486830424046866221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133286541263095594916619845 24991226486830424046866221)
              ·
                refine ⟨9371709932561409017574833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24991226486830424046866221 9371709932561409017574833)
                ·
                  refine ⟨7028782449421056763181125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9371709932561409017574833 7028782449421056763181125)
                  ·
                    refine ⟨1317896709266448143096461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7028782449421056763181125 1317896709266448143096461)
                    ·
                      refine ⟨494211265974918053661173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1317896709266448143096461 494211265974918053661173)
                      ·
                        rfl

theorem cell23_962473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 4, 3].length) (baseStart_962473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_962473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_962473 prefixEnd_962473 := by exact prefixLift 962473
  have htrace : WordTrace (prefixWord ++ tailWord_962473) baseStart_962473 baseEnd_962473 := by
    simpa [prefixWord, tailWord_962473, baseEnd_962473] using wordTrace_append hprefix tailTrace_962473
  have hstable : (prefixWord ++ tailWord_962473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962473).length < 2 ^ (prefixWord ++ tailWord_962473).sum := by decide
  have hdescent : baseEnd_962473 < baseStart_962473 := by decide
  rcases family_descends (prefixWord ++ tailWord_962473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962478 : List Nat := [4, 1, 5, 1, 2, 1, 1, 1, 1, 2, 4]
def baseStart_962478 : Nat := 118140960795 + 962478 * 2 ^ 59
def prefixEnd_962478 : Nat := 4983230072969 + 3 ^ 40 * 962478 * 2
def baseEnd_962478 : Nat := 494213833378190534098651

theorem tailTrace_962478 : CollatzResearch.WordTrace tailWord_962478 prefixEnd_962478 494213833378190534098651 := by
  unfold tailWord_962478
  simp only [CollatzResearch.WordTrace]
  refine ⟨4388057075889257375087011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23402971071409372667130725 4388057075889257375087011)
  ·
    refine ⟨6582085613833886062630517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4388057075889257375087011 6582085613833886062630517)
    ·
      refine ⟨617070526296926818371611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6582085613833886062630517 617070526296926818371611)
      ·
        refine ⟨925605789445390227557417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 617070526296926818371611 925605789445390227557417)
        ·
          refine ⟨694204342084042670668063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 925605789445390227557417 694204342084042670668063)
          ·
            refine ⟨1041306513126064006002095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 694204342084042670668063 1041306513126064006002095)
            ·
              refine ⟨1561959769689096009003143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1041306513126064006002095 1561959769689096009003143)
              ·
                refine ⟨2342939654533644013504715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1561959769689096009003143 2342939654533644013504715)
                ·
                  refine ⟨3514409481800466020257073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2342939654533644013504715 3514409481800466020257073)
                  ·
                    refine ⟨2635807111350349515192805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3514409481800466020257073 2635807111350349515192805)
                    ·
                      refine ⟨494213833378190534098651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2635807111350349515192805 494213833378190534098651)
                      ·
                        rfl

theorem cell23_962478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_962478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_962478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_962478 prefixEnd_962478 := by exact prefixLift 962478
  have htrace : WordTrace (prefixWord ++ tailWord_962478) baseStart_962478 baseEnd_962478 := by
    simpa [prefixWord, tailWord_962478, baseEnd_962478] using wordTrace_append hprefix tailTrace_962478
  have hstable : (prefixWord ++ tailWord_962478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962478).length < 2 ^ (prefixWord ++ tailWord_962478).sum := by decide
  have hdescent : baseEnd_962478 < baseStart_962478 := by decide
  rcases family_descends (prefixWord ++ tailWord_962478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962483 : List Nat := [1, 1, 1, 2, 3, 1, 3, 3, 2, 2, 4]
def baseStart_962483 : Nat := 118140960795 + 962483 * 2 ^ 59
def prefixEnd_962483 : Nat := 4983230072969 + 3 ^ 40 * 962483 * 2
def baseEnd_962483 : Nat := 494216400781463014536127

theorem tailTrace_962483 : CollatzResearch.WordTrace tailWord_962483 prefixEnd_962483 494216400781463014536127 := by
  unfold tailWord_962483
  simp only [CollatzResearch.WordTrace]
  refine ⟨35104638972095944854628103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23403092648063963236418735 35104638972095944854628103)
  ·
    refine ⟨52656958458143917281942155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35104638972095944854628103 52656958458143917281942155)
    ·
      refine ⟨78985437687215875922913233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52656958458143917281942155 78985437687215875922913233)
      ·
        refine ⟨59239078265411906942184925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78985437687215875922913233 59239078265411906942184925)
        ·
          refine ⟨22214654349529465103319347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59239078265411906942184925 22214654349529465103319347)
          ·
            refine ⟨33321981524294197654979021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22214654349529465103319347 33321981524294197654979021)
            ·
              refine ⟨12495743071610324120617133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33321981524294197654979021 12495743071610324120617133)
              ·
                refine ⟨4685903651853871545231425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12495743071610324120617133 4685903651853871545231425)
                ·
                  refine ⟨3514427738890403658923569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4685903651853871545231425 3514427738890403658923569)
                  ·
                    refine ⟨2635820804167802744192677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3514427738890403658923569 2635820804167802744192677)
                    ·
                      refine ⟨494216400781463014536127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2635820804167802744192677 494216400781463014536127)
                      ·
                        rfl

theorem cell23_962483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 2, 2, 4].length) (baseStart_962483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_962483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_962483 prefixEnd_962483 := by exact prefixLift 962483
  have htrace : WordTrace (prefixWord ++ tailWord_962483) baseStart_962483 baseEnd_962483 := by
    simpa [prefixWord, tailWord_962483, baseEnd_962483] using wordTrace_append hprefix tailTrace_962483
  have hstable : (prefixWord ++ tailWord_962483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962483).length < 2 ^ (prefixWord ++ tailWord_962483).sum := by decide
  have hdescent : baseEnd_962483 < baseStart_962483 := by decide
  rcases family_descends (prefixWord ++ tailWord_962483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962560 : List Nat := [2, 1, 1, 2, 1, 1, 1, 3, 3, 6, 2]
def baseStart_962560 : Nat := 118140960795 + 962560 * 2 ^ 59
def prefixEnd_962560 : Nat := 4983230072969 + 3 ^ 40 * 962560 * 2
def baseEnd_962560 : Nat := 494255938791859213273273

theorem tailTrace_962560 : CollatzResearch.WordTrace tailWord_962560 prefixEnd_962560 494255938791859213273273 := by
  unfold tailWord_962560
  simp only [CollatzResearch.WordTrace]
  refine ⟨17553723696408493502590567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23404964928544658003454089 17553723696408493502590567)
  ·
    refine ⟨26330585544612740253885851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17553723696408493502590567 26330585544612740253885851)
    ·
      refine ⟨39495878316919110380828777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26330585544612740253885851 39495878316919110380828777)
      ·
        refine ⟨29621908737689332785621583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39495878316919110380828777 29621908737689332785621583)
        ·
          refine ⟨44432863106533999178432375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29621908737689332785621583 44432863106533999178432375)
          ·
            refine ⟨66649294659800998767648563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44432863106533999178432375 66649294659800998767648563)
            ·
              refine ⟨99973941989701498151472845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66649294659800998767648563 99973941989701498151472845)
              ·
                refine ⟨37490228246138061806802317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99973941989701498151472845 37490228246138061806802317)
                ·
                  refine ⟨14058835592301773177550869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37490228246138061806802317 14058835592301773177550869)
                  ·
                    refine ⟨659007918389145617697697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14058835592301773177550869 659007918389145617697697)
                    ·
                      refine ⟨494255938791859213273273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 659007918389145617697697 494255938791859213273273)
                      ·
                        rfl

theorem cell23_962560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 6, 2].length) (baseStart_962560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_962560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_962560 prefixEnd_962560 := by exact prefixLift 962560
  have htrace : WordTrace (prefixWord ++ tailWord_962560) baseStart_962560 baseEnd_962560 := by
    simpa [prefixWord, tailWord_962560, baseEnd_962560] using wordTrace_append hprefix tailTrace_962560
  have hstable : (prefixWord ++ tailWord_962560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962560).length < 2 ^ (prefixWord ++ tailWord_962560).sum := by decide
  have hdescent : baseEnd_962560 < baseStart_962560 := by decide
  rcases family_descends (prefixWord ++ tailWord_962560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962603 : List Nat := [1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 6]
def baseStart_962603 : Nat := 118140960795 + 962603 * 2 ^ 59
def prefixEnd_962603 : Nat := 4983230072969 + 3 ^ 40 * 962603 * 2
def baseEnd_962603 : Nat := 494278018460002545035575

theorem tailTrace_962603 : CollatzResearch.WordTrace tailWord_962603 prefixEnd_962603 494278018460002545035575 := by
  unfold tailWord_962603
  simp only [CollatzResearch.WordTrace]
  refine ⟨35109015731661205348996463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23406010487774136899330975 35109015731661205348996463)
  ·
    refine ⟨52663523597491808023494695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35109015731661205348996463 52663523597491808023494695)
    ·
      refine ⟨78995285396237712035242043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52663523597491808023494695 78995285396237712035242043)
      ·
        refine ⟨118492928094356568052863065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78995285396237712035242043 118492928094356568052863065)
        ·
          refine ⟨88869696070767426039647299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118492928094356568052863065 88869696070767426039647299)
          ·
            refine ⟨133304544106151139059470949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88869696070767426039647299 133304544106151139059470949)
            ·
              refine ⟨24994602019903338573650803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133304544106151139059470949 24994602019903338573650803)
              ·
                refine ⟨37491903029855007860476205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24994602019903338573650803 37491903029855007860476205)
                ·
                  refine ⟨14059463636195627947678577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37491903029855007860476205 14059463636195627947678577)
                  ·
                    refine ⟨10544597727146720960758933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14059463636195627947678577 10544597727146720960758933)
                    ·
                      refine ⟨494278018460002545035575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10544597727146720960758933 494278018460002545035575)
                      ·
                        rfl

theorem cell23_962603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 6].length) (baseStart_962603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_962603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_962603 prefixEnd_962603 := by exact prefixLift 962603
  have htrace : WordTrace (prefixWord ++ tailWord_962603) baseStart_962603 baseEnd_962603 := by
    simpa [prefixWord, tailWord_962603, baseEnd_962603] using wordTrace_append hprefix tailTrace_962603
  have hstable : (prefixWord ++ tailWord_962603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962603).length < 2 ^ (prefixWord ++ tailWord_962603).sum := by decide
  have hdescent : baseEnd_962603 < baseStart_962603 := by decide
  rcases family_descends (prefixWord ++ tailWord_962603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962678 : List Nat := [5, 1, 1, 2, 1, 2, 3, 3, 1, 1, 3]
def baseStart_962678 : Nat := 118140960795 + 962678 * 2 ^ 59
def prefixEnd_962678 : Nat := 4983230072969 + 3 ^ 40 * 962678 * 2
def baseEnd_962678 : Nat := 494316529509089751597731

theorem tailTrace_962678 : CollatzResearch.WordTrace tailWord_962678 prefixEnd_962678 494316529509089751597731 := by
  unfold tailWord_962678
  simp only [CollatzResearch.WordTrace]
  refine ⟨2194484450399343322373543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23407834137592995438651125 2194484450399343322373543)
  ·
    refine ⟨3291726675599014983560315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2194484450399343322373543 3291726675599014983560315)
    ·
      refine ⟨4937590013398522475340473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3291726675599014983560315 4937590013398522475340473)
      ·
        refine ⟨3703192510048891856505355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4937590013398522475340473 3703192510048891856505355)
        ·
          refine ⟨5554788765073337784758033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3703192510048891856505355 5554788765073337784758033)
          ·
            refine ⟨4166091573805003338568525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5554788765073337784758033 4166091573805003338568525)
            ·
              refine ⟨1562284340176876251963197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4166091573805003338568525 1562284340176876251963197)
              ·
                refine ⟨585856627566328594486199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1562284340176876251963197 585856627566328594486199)
                ·
                  refine ⟨878784941349492891729299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 585856627566328594486199 878784941349492891729299)
                  ·
                    refine ⟨1318177412024239337593949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 878784941349492891729299 1318177412024239337593949)
                    ·
                      refine ⟨494316529509089751597731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1318177412024239337593949 494316529509089751597731)
                      ·
                        rfl

theorem cell23_962678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 3, 1, 1, 3].length) (baseStart_962678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_962678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_962678 prefixEnd_962678 := by exact prefixLift 962678
  have htrace : WordTrace (prefixWord ++ tailWord_962678) baseStart_962678 baseEnd_962678 := by
    simpa [prefixWord, tailWord_962678, baseEnd_962678] using wordTrace_append hprefix tailTrace_962678
  have hstable : (prefixWord ++ tailWord_962678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962678).length < 2 ^ (prefixWord ++ tailWord_962678).sum := by decide
  have hdescent : baseEnd_962678 < baseStart_962678 := by decide
  rcases family_descends (prefixWord ++ tailWord_962678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962680 : List Nat := [2, 1, 2, 1, 1, 1, 3, 3, 3, 2, 4]
def baseStart_962680 : Nat := 118140960795 + 962680 * 2 ^ 59
def prefixEnd_962680 : Nat := 4983230072969 + 3 ^ 40 * 962680 * 2
def baseEnd_962680 : Nat := 494317556470398743772721

theorem tailTrace_962680 : CollatzResearch.WordTrace tailWord_962680 prefixEnd_962680 494317556470398743772721 := by
  unfold tailWord_962680
  simp only [CollatzResearch.WordTrace]
  refine ⟨17555912076191123749774747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23407882768254831666366329 17555912076191123749774747)
  ·
    refine ⟨26333868114286685624662121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17555912076191123749774747 26333868114286685624662121)
    ·
      refine ⟨19750401085715014218496591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26333868114286685624662121 19750401085715014218496591)
      ·
        refine ⟨29625601628572521327744887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19750401085715014218496591 29625601628572521327744887)
        ·
          refine ⟨44438402442858781991617331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29625601628572521327744887 44438402442858781991617331)
          ·
            refine ⟨66657603664288172987425997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44438402442858781991617331 66657603664288172987425997)
            ·
              refine ⟨24996601374108064870284749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66657603664288172987425997 24996601374108064870284749)
              ·
                refine ⟨9373725515290524326356781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24996601374108064870284749 9373725515290524326356781)
                ·
                  refine ⟨3515147068233946622383793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9373725515290524326356781 3515147068233946622383793)
                  ·
                    refine ⟨2636360301175459966787845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3515147068233946622383793 2636360301175459966787845)
                    ·
                      refine ⟨494317556470398743772721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2636360301175459966787845 494317556470398743772721)
                      ·
                        rfl

theorem cell23_962680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 3, 2, 4].length) (baseStart_962680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_962680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_962680 prefixEnd_962680 := by exact prefixLift 962680
  have htrace : WordTrace (prefixWord ++ tailWord_962680) baseStart_962680 baseEnd_962680 := by
    simpa [prefixWord, tailWord_962680, baseEnd_962680] using wordTrace_append hprefix tailTrace_962680
  have hstable : (prefixWord ++ tailWord_962680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962680).length < 2 ^ (prefixWord ++ tailWord_962680).sum := by decide
  have hdescent : baseEnd_962680 < baseStart_962680 := by decide
  rcases family_descends (prefixWord ++ tailWord_962680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962718 : List Nat := [4, 3, 1, 1, 3, 2, 1, 2, 1, 1, 4]
def baseStart_962718 : Nat := 118140960795 + 962718 * 2 ^ 59
def prefixEnd_962718 : Nat := 4983230072969 + 3 ^ 40 * 962718 * 2
def baseEnd_962718 : Nat := 494337068735269595097547

theorem tailTrace_962718 : CollatzResearch.WordTrace tailWord_962718 prefixEnd_962718 494337068735269595097547 := by
  unfold tailWord_962718
  simp only [CollatzResearch.WordTrace]
  refine ⟨4389151265780572498679101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23408806750829719992955205 4389151265780572498679101)
  ·
    refine ⟨1645931724667714687004663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4389151265780572498679101 1645931724667714687004663)
    ·
      refine ⟨2468897587001572030506995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1645931724667714687004663 2468897587001572030506995)
      ·
        refine ⟨3703346380502358045760493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2468897587001572030506995 3703346380502358045760493)
        ·
          refine ⟨1388754892688384267160185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3703346380502358045760493 1388754892688384267160185)
          ·
            refine ⟨1041566169516288200370139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1388754892688384267160185 1041566169516288200370139)
            ·
              refine ⟨1562349254274432300555209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1041566169516288200370139 1562349254274432300555209)
              ·
                refine ⟨1171761940705824225416407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1562349254274432300555209 1171761940705824225416407)
                ·
                  refine ⟨1757642911058736338124611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1171761940705824225416407 1757642911058736338124611)
                  ·
                    refine ⟨2636464366588104507186917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1757642911058736338124611 2636464366588104507186917)
                    ·
                      refine ⟨494337068735269595097547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2636464366588104507186917 494337068735269595097547)
                      ·
                        rfl

theorem cell23_962718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_962718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_962718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_962718 prefixEnd_962718 := by exact prefixLift 962718
  have htrace : WordTrace (prefixWord ++ tailWord_962718) baseStart_962718 baseEnd_962718 := by
    simpa [prefixWord, tailWord_962718, baseEnd_962718] using wordTrace_append hprefix tailTrace_962718
  have hstable : (prefixWord ++ tailWord_962718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962718).length < 2 ^ (prefixWord ++ tailWord_962718).sum := by decide
  have hdescent : baseEnd_962718 < baseStart_962718 := by decide
  rcases family_descends (prefixWord ++ tailWord_962718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962721 : List Nat := [1, 2, 3, 3, 1, 4, 1, 2, 1, 2, 3]
def baseStart_962721 : Nat := 118140960795 + 962721 * 2 ^ 59
def prefixEnd_962721 : Nat := 4983230072969 + 3 ^ 40 * 962721 * 2
def baseEnd_962721 : Nat := 494338609177233083360033

theorem tailTrace_962721 : CollatzResearch.WordTrace tailWord_962721 prefixEnd_962721 494338609177233083360033 := by
  unfold tailWord_962721
  simp only [CollatzResearch.WordTrace]
  refine ⟨35113319545233711501792017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23408879696822474334528011 35113319545233711501792017)
  ·
    refine ⟨26334989658925283626344013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35113319545233711501792017 26334989658925283626344013)
    ·
      refine ⟨9875621122096981359879005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26334989658925283626344013 9875621122096981359879005)
      ·
        refine ⟨3703357920786368009954627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9875621122096981359879005 3703357920786368009954627)
        ·
          refine ⟨5555036881179552014931941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3703357920786368009954627 5555036881179552014931941)
          ·
            refine ⟨1041569415221166002799739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5555036881179552014931941 1041569415221166002799739)
            ·
              refine ⟨1562354122831749004199609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1041569415221166002799739 1562354122831749004199609)
              ·
                refine ⟨1171765592123811753149707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1562354122831749004199609 1171765592123811753149707)
                ·
                  refine ⟨1757648388185717629724561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1171765592123811753149707 1757648388185717629724561)
                  ·
                    refine ⟨1318236291139288222293421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1757648388185717629724561 1318236291139288222293421)
                    ·
                      refine ⟨494338609177233083360033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1318236291139288222293421 494338609177233083360033)
                      ·
                        rfl

theorem cell23_962721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_962721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_962721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_962721 prefixEnd_962721 := by exact prefixLift 962721
  have htrace : WordTrace (prefixWord ++ tailWord_962721) baseStart_962721 baseEnd_962721 := by
    simpa [prefixWord, tailWord_962721, baseEnd_962721] using wordTrace_append hprefix tailTrace_962721
  have hstable : (prefixWord ++ tailWord_962721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962721).length < 2 ^ (prefixWord ++ tailWord_962721).sum := by decide
  have hdescent : baseEnd_962721 < baseStart_962721 := by decide
  rcases family_descends (prefixWord ++ tailWord_962721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962791 : List Nat := [1, 1, 5, 3, 1, 1, 2, 2, 1, 4, 2]
def baseStart_962791 : Nat := 118140960795 + 962791 * 2 ^ 59
def prefixEnd_962791 : Nat := 4983230072969 + 3 ^ 40 * 962791 * 2
def baseEnd_962791 : Nat := 494374552823047809484711

theorem tailTrace_962791 : CollatzResearch.WordTrace tailWord_962791 prefixEnd_962791 494374552823047809484711 := by
  unfold tailWord_962791
  simp only [CollatzResearch.WordTrace]
  refine ⟨35115872654980113456840227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23410581769986742304560151 35115872654980113456840227)
  ·
    refine ⟨52673808982470170185260341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35115872654980113456840227 52673808982470170185260341)
    ·
      refine ⟨4938169592106578454868157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52673808982470170185260341 4938169592106578454868157)
      ·
        refine ⟨1851813597039966920575559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4938169592106578454868157 1851813597039966920575559)
        ·
          refine ⟨2777720395559950380863339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1851813597039966920575559 2777720395559950380863339)
          ·
            refine ⟨4166580593339925571295009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2777720395559950380863339 4166580593339925571295009)
            ·
              refine ⟨3124935445004944178471257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4166580593339925571295009 3124935445004944178471257)
              ·
                refine ⟨2343701583753708133853443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3124935445004944178471257 2343701583753708133853443)
                ·
                  refine ⟨3515552375630562200780165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2343701583753708133853443 3515552375630562200780165)
                  ·
                    refine ⟨659166070430730412646281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3515552375630562200780165 659166070430730412646281)
                    ·
                      refine ⟨494374552823047809484711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 659166070430730412646281 494374552823047809484711)
                      ·
                        rfl

theorem cell23_962791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_962791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_962791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_962791 prefixEnd_962791 := by exact prefixLift 962791
  have htrace : WordTrace (prefixWord ++ tailWord_962791) baseStart_962791 baseEnd_962791 := by
    simpa [prefixWord, tailWord_962791, baseEnd_962791] using wordTrace_append hprefix tailTrace_962791
  have hstable : (prefixWord ++ tailWord_962791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962791).length < 2 ^ (prefixWord ++ tailWord_962791).sum := by decide
  have hdescent : baseEnd_962791 < baseStart_962791 := by decide
  rcases family_descends (prefixWord ++ tailWord_962791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962814 : List Nat := [4, 2, 2, 1, 1, 1, 4, 1, 7]
def baseStart_962814 : Nat := 118140960795 + 962814 * 2 ^ 59
def prefixEnd_962814 : Nat := 4983230072969 + 3 ^ 40 * 962814 * 2
def baseEnd_962814 : Nat := 54931818097566802166345

theorem tailTrace_962814 : CollatzResearch.WordTrace tailWord_962814 prefixEnd_962814 54931818097566802166345 := by
  unfold tailWord_962814
  simp only [CollatzResearch.WordTrace]
  refine ⟨4389588941737098548115937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23411141022597858923284997 4389588941737098548115937)
  ·
    refine ⟨3292191706302823911086953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4389588941737098548115937 3292191706302823911086953)
    ·
      refine ⟨2469143779727117933315215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3292191706302823911086953 2469143779727117933315215)
      ·
        refine ⟨3703715669590676899972823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2469143779727117933315215 3703715669590676899972823)
        ·
          refine ⟨5555573504386015349959235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3703715669590676899972823 5555573504386015349959235)
          ·
            refine ⟨8333360256579023024938853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5555573504386015349959235 8333360256579023024938853)
            ·
              refine ⟨1562505048108566817176035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8333360256579023024938853 1562505048108566817176035)
              ·
                refine ⟨2343757572162850225764053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1562505048108566817176035 2343757572162850225764053)
                ·
                  refine ⟨54931818097566802166345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2343757572162850225764053 54931818097566802166345)
                  ·
                    rfl

theorem cell23_962814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 1, 7].length) (baseStart_962814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_962814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_962814 prefixEnd_962814 := by exact prefixLift 962814
  have htrace : WordTrace (prefixWord ++ tailWord_962814) baseStart_962814 baseEnd_962814 := by
    simpa [prefixWord, tailWord_962814, baseEnd_962814] using wordTrace_append hprefix tailTrace_962814
  have hstable : (prefixWord ++ tailWord_962814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962814).length < 2 ^ (prefixWord ++ tailWord_962814).sum := by decide
  have hdescent : baseEnd_962814 < baseStart_962814 := by decide
  rcases family_descends (prefixWord ++ tailWord_962814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962824 : List Nat := [2, 1, 3, 2, 3, 1, 2, 1, 2, 3, 3]
def baseStart_962824 : Nat := 118140960795 + 962824 * 2 ^ 59
def prefixEnd_962824 : Nat := 4983230072969 + 3 ^ 40 * 962824 * 2
def baseEnd_962824 : Nat := 494391497684646180372059

theorem tailTrace_962824 : CollatzResearch.WordTrace tailWord_962824 prefixEnd_962824 494391497684646180372059 := by
  unfold tailWord_962824
  simp only [CollatzResearch.WordTrace]
  refine ⟨17558538131930280046395763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23411384175907040061861017 17558538131930280046395763)
  ·
    refine ⟨26337807197895420069593645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17558538131930280046395763 26337807197895420069593645)
    ·
      refine ⟨9876677699210782526097617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26337807197895420069593645 9876677699210782526097617)
      ·
        refine ⟨7407508274408086894573213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9876677699210782526097617 7407508274408086894573213)
        ·
          refine ⟨2777815602903032585464955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7407508274408086894573213 2777815602903032585464955)
          ·
            refine ⟨4166723404354548878197433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2777815602903032585464955 4166723404354548878197433)
            ·
              refine ⟨3125042553265911658648075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4166723404354548878197433 3125042553265911658648075)
              ·
                refine ⟨4687563829898867487972113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3125042553265911658648075 4687563829898867487972113)
                ·
                  refine ⟨3515672872424150615979085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4687563829898867487972113 3515672872424150615979085)
                  ·
                    refine ⟨1318377327159056480992157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3515672872424150615979085 1318377327159056480992157)
                    ·
                      refine ⟨494391497684646180372059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1318377327159056480992157 494391497684646180372059)
                      ·
                        rfl

theorem cell23_962824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 2, 3, 3].length) (baseStart_962824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_962824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_962824 prefixEnd_962824 := by exact prefixLift 962824
  have htrace : WordTrace (prefixWord ++ tailWord_962824) baseStart_962824 baseEnd_962824 := by
    simpa [prefixWord, tailWord_962824, baseEnd_962824] using wordTrace_append hprefix tailTrace_962824
  have hstable : (prefixWord ++ tailWord_962824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962824).length < 2 ^ (prefixWord ++ tailWord_962824).sum := by decide
  have hdescent : baseEnd_962824 < baseStart_962824 := by decide
  rcases family_descends (prefixWord ++ tailWord_962824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962864 : List Nat := [2, 1, 1, 1, 2, 2, 2, 4, 2, 4, 2]
def baseStart_962864 : Nat := 118140960795 + 962864 * 2 ^ 59
def prefixEnd_962864 : Nat := 4983230072969 + 3 ^ 40 * 962864 * 2
def baseEnd_962864 : Nat := 494412036910826023871875

theorem tailTrace_962864 : CollatzResearch.WordTrace tailWord_962864 prefixEnd_962864 494412036910826023871875 := by
  unfold tailWord_962864
  simp only [CollatzResearch.WordTrace]
  refine ⟨17559267591857823462123823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23412356789143764616165097 17559267591857823462123823)
  ·
    refine ⟨26338901387786735193185735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17559267591857823462123823 26338901387786735193185735)
    ·
      refine ⟨39508352081680102789778603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26338901387786735193185735 39508352081680102789778603)
      ·
        refine ⟨59262528122520154184667905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39508352081680102789778603 59262528122520154184667905)
        ·
          refine ⟨44446896091890115638500929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59262528122520154184667905 44446896091890115638500929)
          ·
            refine ⟨33335172068917586728875697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44446896091890115638500929 33335172068917586728875697)
            ·
              refine ⟨25001379051688190046656773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33335172068917586728875697 25001379051688190046656773)
              ·
                refine ⟨4687758572191535633748145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25001379051688190046656773 4687758572191535633748145)
                ·
                  refine ⟨3515818929143651725311109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4687758572191535633748145 3515818929143651725311109)
                  ·
                    refine ⟨659216049214434698495833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3515818929143651725311109 659216049214434698495833)
                    ·
                      refine ⟨494412036910826023871875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 659216049214434698495833 494412036910826023871875)
                      ·
                        rfl

theorem cell23_962864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 2, 4, 2].length) (baseStart_962864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_962864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_962864 prefixEnd_962864 := by exact prefixLift 962864
  have htrace : WordTrace (prefixWord ++ tailWord_962864) baseStart_962864 baseEnd_962864 := by
    simpa [prefixWord, tailWord_962864, baseEnd_962864] using wordTrace_append hprefix tailTrace_962864
  have hstable : (prefixWord ++ tailWord_962864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962864).length < 2 ^ (prefixWord ++ tailWord_962864).sum := by decide
  have hdescent : baseEnd_962864 < baseStart_962864 := by decide
  rcases family_descends (prefixWord ++ tailWord_962864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962958 : List Nat := [4, 1, 1, 4, 1, 2, 1, 1, 1, 5, 2]
def baseStart_962958 : Nat := 118140960795 + 962958 * 2 ^ 59
def prefixEnd_962958 : Nat := 4983230072969 + 3 ^ 40 * 962958 * 2
def baseEnd_962958 : Nat := 494460304092348656096443

theorem tailTrace_962958 : CollatzResearch.WordTrace tailWord_962958 prefixEnd_962958 494460304092348656096443 := by
  unfold tailWord_962958
  simp only [CollatzResearch.WordTrace]
  refine ⟨4390245455671887622271191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23414642430250067318779685 4390245455671887622271191)
  ·
    refine ⟨6585368183507831433406787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4390245455671887622271191 6585368183507831433406787)
    ·
      refine ⟨9878052275261747150110181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6585368183507831433406787 9878052275261747150110181)
      ·
        refine ⟨1852134801611577590645659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9878052275261747150110181 1852134801611577590645659)
        ·
          refine ⟨2778202202417366385968489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1852134801611577590645659 2778202202417366385968489)
          ·
            refine ⟨2083651651813024789476367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2778202202417366385968489 2083651651813024789476367)
            ·
              refine ⟨3125477477719537184214551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2083651651813024789476367 3125477477719537184214551)
              ·
                refine ⟨4688216216579305776321827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3125477477719537184214551 4688216216579305776321827)
                ·
                  refine ⟨7032324324868958664482741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4688216216579305776321827 7032324324868958664482741)
                  ·
                    refine ⟨659280405456464874795257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7032324324868958664482741 659280405456464874795257)
                    ·
                      refine ⟨494460304092348656096443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 659280405456464874795257 494460304092348656096443)
                      ·
                        rfl

theorem cell23_962958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_962958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_962958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_962958 prefixEnd_962958 := by exact prefixLift 962958
  have htrace : WordTrace (prefixWord ++ tailWord_962958) baseStart_962958 baseEnd_962958 := by
    simpa [prefixWord, tailWord_962958, baseEnd_962958] using wordTrace_append hprefix tailTrace_962958
  have hstable : (prefixWord ++ tailWord_962958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962958).length < 2 ^ (prefixWord ++ tailWord_962958).sum := by decide
  have hdescent : baseEnd_962958 < baseStart_962958 := by decide
  rcases family_descends (prefixWord ++ tailWord_962958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962968 : List Nat := [2, 1, 2, 5, 1, 1, 4, 1, 1, 5]
def baseStart_962968 : Nat := 118140960795 + 962968 * 2 ^ 59
def prefixEnd_962968 : Nat := 4983230072969 + 3 ^ 40 * 962968 * 2
def baseEnd_962968 : Nat := 164821812966297872323799

theorem tailTrace_962968 : CollatzResearch.WordTrace tailWord_962968 prefixEnd_962968 164821812966297872323799 := by
  unfold tailWord_962968
  simp only [CollatzResearch.WordTrace]
  refine ⟨17561164187669436343016779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23414885583559248457355705 17561164187669436343016779)
  ·
    refine ⟨26341746281504154514525169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17561164187669436343016779 26341746281504154514525169)
    ·
      refine ⟨19756309711128115885893877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26341746281504154514525169 19756309711128115885893877)
      ·
        refine ⟨1852154035418260864302551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19756309711128115885893877 1852154035418260864302551)
        ·
          refine ⟨2778231053127391296453827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1852154035418260864302551 2778231053127391296453827)
          ·
            refine ⟨4167346579691086944680741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2778231053127391296453827 4167346579691086944680741)
            ·
              refine ⟨781377483692078802127639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4167346579691086944680741 781377483692078802127639)
              ·
                refine ⟨1172066225538118203191459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 781377483692078802127639 1172066225538118203191459)
                ·
                  refine ⟨1758099338307177304787189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1172066225538118203191459 1758099338307177304787189)
                  ·
                    refine ⟨164821812966297872323799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1758099338307177304787189 164821812966297872323799)
                    ·
                      rfl

theorem cell23_962968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 4, 1, 1, 5].length) (baseStart_962968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_962968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_962968 prefixEnd_962968 := by exact prefixLift 962968
  have htrace : WordTrace (prefixWord ++ tailWord_962968) baseStart_962968 baseEnd_962968 := by
    simpa [prefixWord, tailWord_962968, baseEnd_962968] using wordTrace_append hprefix tailTrace_962968
  have hstable : (prefixWord ++ tailWord_962968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962968).length < 2 ^ (prefixWord ++ tailWord_962968).sum := by decide
  have hdescent : baseEnd_962968 < baseStart_962968 := by decide
  rcases family_descends (prefixWord ++ tailWord_962968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963001 : List Nat := [1, 2, 1, 4, 3, 1, 3, 1, 1, 2, 4]
def baseStart_963001 : Nat := 118140960795 + 963001 * 2 ^ 59
def prefixEnd_963001 : Nat := 4983230072969 + 3 ^ 40 * 963001 * 2
def baseEnd_963001 : Nat := 494482383760491987858745

theorem tailTrace_963001 : CollatzResearch.WordTrace tailWord_963001 prefixEnd_963001 494482383760491987858745 := by
  unfold tailWord_963001
  simp only [CollatzResearch.WordTrace]
  refine ⟨35123531984219319321984857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23415687989479546214656571 35123531984219319321984857)
  ·
    refine ⟨26342648988164489491488643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35123531984219319321984857 26342648988164489491488643)
    ·
      refine ⟨39513973482246734237232965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26342648988164489491488643 39513973482246734237232965)
      ·
        refine ⟨7408870027921262669481181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39513973482246734237232965 7408870027921262669481181)
        ·
          refine ⟨2778326260470473501055443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7408870027921262669481181 2778326260470473501055443)
          ·
            refine ⟨4167489390705710251583165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2778326260470473501055443 4167489390705710251583165)
            ·
              refine ⟨1562808521514641344343687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4167489390705710251583165 1562808521514641344343687)
              ·
                refine ⟨2344212782271962016515531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1562808521514641344343687 2344212782271962016515531)
                ·
                  refine ⟨3516319173407943024773297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2344212782271962016515531 3516319173407943024773297)
                  ·
                    refine ⟨2637239380055957268579973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3516319173407943024773297 2637239380055957268579973)
                    ·
                      refine ⟨494482383760491987858745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2637239380055957268579973 494482383760491987858745)
                      ·
                        rfl

theorem cell23_963001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 1, 1, 2, 4].length) (baseStart_963001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_963001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_963001 prefixEnd_963001 := by exact prefixLift 963001
  have htrace : WordTrace (prefixWord ++ tailWord_963001) baseStart_963001 baseEnd_963001 := by
    simpa [prefixWord, tailWord_963001, baseEnd_963001] using wordTrace_append hprefix tailTrace_963001
  have hstable : (prefixWord ++ tailWord_963001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963001).length < 2 ^ (prefixWord ++ tailWord_963001).sum := by decide
  have hdescent : baseEnd_963001 < baseStart_963001 := by decide
  rcases family_descends (prefixWord ++ tailWord_963001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963031 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 7, 3, 2]
def baseStart_963031 : Nat := 118140960795 + 963031 * 2 ^ 59
def prefixEnd_963031 : Nat := 4983230072969 + 3 ^ 40 * 963031 * 2
def baseEnd_963031 : Nat := 494497788180126870483607

theorem tailTrace_963031 : CollatzResearch.WordTrace tailWord_963031 prefixEnd_963031 494497788180126870483607 := by
  unfold tailWord_963031
  simp only [CollatzResearch.WordTrace]
  refine ⟨35124626174110634445576947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23416417449407089630384631 35124626174110634445576947)
  ·
    refine ⟨52686939261165951668365421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35124626174110634445576947 52686939261165951668365421)
    ·
      refine ⟨19757602222937231875637033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52686939261165951668365421 19757602222937231875637033)
      ·
        refine ⟨14818201667202923906727775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19757602222937231875637033 14818201667202923906727775)
        ·
          refine ⟨22227302500804385860091663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14818201667202923906727775 22227302500804385860091663)
          ·
            refine ⟨33340953751206578790137495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22227302500804385860091663 33340953751206578790137495)
            ·
              refine ⟨50011430626809868185206243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33340953751206578790137495 50011430626809868185206243)
              ·
                refine ⟨75017145940214802277809365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50011430626809868185206243 75017145940214802277809365)
                ·
                  refine ⟨1758214357973784428386157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 75017145940214802277809365 1758214357973784428386157)
                  ·
                    refine ⟨659330384240169160644809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1758214357973784428386157 659330384240169160644809)
                    ·
                      refine ⟨494497788180126870483607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 659330384240169160644809 494497788180126870483607)
                      ·
                        rfl

theorem cell23_963031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 7, 3, 2].length) (baseStart_963031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_963031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_963031 prefixEnd_963031 := by exact prefixLift 963031
  have htrace : WordTrace (prefixWord ++ tailWord_963031) baseStart_963031 baseEnd_963031 := by
    simpa [prefixWord, tailWord_963031, baseEnd_963031] using wordTrace_append hprefix tailTrace_963031
  have hstable : (prefixWord ++ tailWord_963031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963031).length < 2 ^ (prefixWord ++ tailWord_963031).sum := by decide
  have hdescent : baseEnd_963031 < baseStart_963031 := by decide
  rcases family_descends (prefixWord ++ tailWord_963031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963034 : List Nat := [3, 1, 1, 2, 3, 1, 1, 2, 2, 2, 5]
def baseStart_963034 : Nat := 118140960795 + 963034 * 2 ^ 59
def prefixEnd_963034 : Nat := 4983230072969 + 3 ^ 40 * 963034 * 2
def baseEnd_963034 : Nat := 494499328622090358746093

theorem tailTrace_963034 : CollatzResearch.WordTrace tailWord_963034 prefixEnd_963034 494499328622090358746093 := by
  unfold tailWord_963034
  simp only [CollatzResearch.WordTrace]
  refine ⟨8781183898274941489484039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23416490395399843971957437 8781183898274941489484039)
  ·
    refine ⟨13171775847412412234226059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8781183898274941489484039 13171775847412412234226059)
    ·
      refine ⟨19757663771118618351339089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13171775847412412234226059 19757663771118618351339089)
      ·
        refine ⟨14818247828338963763504317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19757663771118618351339089 14818247828338963763504317)
        ·
          refine ⟨5556842935627111411314119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14818247828338963763504317 5556842935627111411314119)
          ·
            refine ⟨8335264403440667116971179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5556842935627111411314119 8335264403440667116971179)
            ·
              refine ⟨12502896605161000675456769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8335264403440667116971179 12502896605161000675456769)
              ·
                refine ⟨9377172453870750506592577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12502896605161000675456769 9377172453870750506592577)
                ·
                  refine ⟨7032879340403062879944433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9377172453870750506592577 7032879340403062879944433)
                  ·
                    refine ⟨5274659505302297159958325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7032879340403062879944433 5274659505302297159958325)
                    ·
                      refine ⟨494499328622090358746093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5274659505302297159958325 494499328622090358746093)
                      ·
                        rfl

theorem cell23_963034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_963034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_963034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_963034 prefixEnd_963034 := by exact prefixLift 963034
  have htrace : WordTrace (prefixWord ++ tailWord_963034) baseStart_963034 baseEnd_963034 := by
    simpa [prefixWord, tailWord_963034, baseEnd_963034] using wordTrace_append hprefix tailTrace_963034
  have hstable : (prefixWord ++ tailWord_963034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963034).length < 2 ^ (prefixWord ++ tailWord_963034).sum := by decide
  have hdescent : baseEnd_963034 < baseStart_963034 := by decide
  rcases family_descends (prefixWord ++ tailWord_963034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963064 : List Nat := [2, 1, 2, 1, 1, 4, 1, 1, 4, 1, 5]
def baseStart_963064 : Nat := 118140960795 + 963064 * 2 ^ 59
def prefixEnd_963064 : Nat := 4983230072969 + 3 ^ 40 * 963064 * 2
def baseEnd_963064 : Nat := 494514733041725241370955

theorem tailTrace_963064 : CollatzResearch.WordTrace tailWord_963064 prefixEnd_963064 494514733041725241370955 := by
  unfold tailWord_963064
  simp only [CollatzResearch.WordTrace]
  refine ⟨17562914891495540540764123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23417219855327387387685497 17562914891495540540764123)
  ·
    refine ⟨26344372337243310811146185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17562914891495540540764123 26344372337243310811146185)
    ·
      refine ⟨19758279252932483108359639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26344372337243310811146185 19758279252932483108359639)
      ·
        refine ⟨29637418879398724662539459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19758279252932483108359639 29637418879398724662539459)
        ·
          refine ⟨44456128319098086993809189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29637418879398724662539459 44456128319098086993809189)
          ·
            refine ⟨8335524059830891311339223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44456128319098086993809189 8335524059830891311339223)
            ·
              refine ⟨12503286089746336967008835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8335524059830891311339223 12503286089746336967008835)
              ·
                refine ⟨18754929134619505450513253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12503286089746336967008835 18754929134619505450513253)
                ·
                  refine ⟨3516549212741157271971235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18754929134619505450513253 3516549212741157271971235)
                  ·
                    refine ⟨5274823819111735907956853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3516549212741157271971235 5274823819111735907956853)
                    ·
                      refine ⟨494514733041725241370955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5274823819111735907956853 494514733041725241370955)
                      ·
                        rfl

theorem cell23_963064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 4, 1, 5].length) (baseStart_963064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_963064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_963064 prefixEnd_963064 := by exact prefixLift 963064
  have htrace : WordTrace (prefixWord ++ tailWord_963064) baseStart_963064 baseEnd_963064 := by
    simpa [prefixWord, tailWord_963064, baseEnd_963064] using wordTrace_append hprefix tailTrace_963064
  have hstable : (prefixWord ++ tailWord_963064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963064).length < 2 ^ (prefixWord ++ tailWord_963064).sum := by decide
  have hdescent : baseEnd_963064 < baseStart_963064 := by decide
  rcases family_descends (prefixWord ++ tailWord_963064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963112 : List Nat := [2, 1, 5, 2, 1, 1, 2, 3, 2, 2, 2]
def baseStart_963112 : Nat := 118140960795 + 963112 * 2 ^ 59
def prefixEnd_963112 : Nat := 4983230072969 + 3 ^ 40 * 963112 * 2
def baseEnd_963112 : Nat := 494539380113141053570735

theorem tailTrace_963112 : CollatzResearch.WordTrace tailWord_963112 prefixEnd_963112 494539380113141053570735 := by
  unfold tailWord_963112
  simp only [CollatzResearch.WordTrace]
  refine ⟨17563790243408592639637795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23418386991211456852850393 17563790243408592639637795)
  ·
    refine ⟨26345685365112888959456693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17563790243408592639637795 26345685365112888959456693)
    ·
      refine ⟨2469908002979333339949065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26345685365112888959456693 2469908002979333339949065)
      ·
        refine ⟨1852431002234500004961799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2469908002979333339949065 1852431002234500004961799)
        ·
          refine ⟨2778646503351750007442699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1852431002234500004961799 2778646503351750007442699)
          ·
            refine ⟨4167969755027625011164049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2778646503351750007442699 4167969755027625011164049)
            ·
              refine ⟨3125977316270718758373037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4167969755027625011164049 3125977316270718758373037)
              ·
                refine ⟨1172241493601519534389889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3125977316270718758373037 1172241493601519534389889)
                ·
                  refine ⟨879181120201139650792417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1172241493601519534389889 879181120201139650792417)
                  ·
                    refine ⟨659385840150854738094313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 879181120201139650792417 659385840150854738094313)
                    ·
                      refine ⟨494539380113141053570735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 659385840150854738094313 494539380113141053570735)
                      ·
                        rfl

theorem cell23_963112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_963112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_963112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_963112 prefixEnd_963112 := by exact prefixLift 963112
  have htrace : WordTrace (prefixWord ++ tailWord_963112) baseStart_963112 baseEnd_963112 := by
    simpa [prefixWord, tailWord_963112, baseEnd_963112] using wordTrace_append hprefix tailTrace_963112
  have hstable : (prefixWord ++ tailWord_963112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963112).length < 2 ^ (prefixWord ++ tailWord_963112).sum := by decide
  have hdescent : baseEnd_963112 < baseStart_963112 := by decide
  rcases family_descends (prefixWord ++ tailWord_963112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963118 : List Nat := [4, 1, 3, 1, 3, 1, 1, 2, 7]
def baseStart_963118 : Nat := 118140960795 + 963118 * 2 ^ 59
def prefixEnd_963118 : Nat := 4983230072969 + 3 ^ 40 * 963118 * 2
def baseEnd_963118 : Nat := 54949162333007558899523

theorem tailTrace_963118 : CollatzResearch.WordTrace tailWord_963118 prefixEnd_963118 54949162333007558899523 := by
  unfold tailWord_963118
  simp only [CollatzResearch.WordTrace]
  refine ⟨4390974915599431037999251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23418532883196965535996005 4390974915599431037999251)
  ·
    refine ⟨6586462373399146556998877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4390974915599431037999251 6586462373399146556998877)
    ·
      refine ⟨2469923390024679958874579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6586462373399146556998877 2469923390024679958874579)
      ·
        refine ⟨3704885085037019938311869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2469923390024679958874579 3704885085037019938311869)
        ·
          refine ⟨1389331906888882476866951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3704885085037019938311869 1389331906888882476866951)
          ·
            refine ⟨2083997860333323715300427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1389331906888882476866951 2083997860333323715300427)
            ·
              refine ⟨3125996790499985572950641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2083997860333323715300427 3125996790499985572950641)
              ·
                refine ⟨2344497592874989179712981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3125996790499985572950641 2344497592874989179712981)
                ·
                  refine ⟨54949162333007558899523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2344497592874989179712981 54949162333007558899523)
                  ·
                    rfl

theorem cell23_963118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 2, 7].length) (baseStart_963118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_963118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_963118 prefixEnd_963118 := by exact prefixLift 963118
  have htrace : WordTrace (prefixWord ++ tailWord_963118) baseStart_963118 baseEnd_963118 := by
    simpa [prefixWord, tailWord_963118, baseEnd_963118] using wordTrace_append hprefix tailTrace_963118
  have hstable : (prefixWord ++ tailWord_963118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963118).length < 2 ^ (prefixWord ++ tailWord_963118).sum := by decide
  have hdescent : baseEnd_963118 < baseStart_963118 := by decide
  rcases family_descends (prefixWord ++ tailWord_963118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963144 : List Nat := [2, 1, 3, 1, 1, 1, 1, 2, 1, 10]
def baseStart_963144 : Nat := 118140960795 + 963144 * 2 ^ 59
def prefixEnd_963144 : Nat := 4983230072969 + 3 ^ 40 * 963144 * 2
def baseEnd_963144 : Nat := 164851937164694976123529

theorem tailTrace_963144 : CollatzResearch.WordTrace tailWord_963144 prefixEnd_963144 164851937164694976123529 := by
  unfold tailWord_963144
  simp only [CollatzResearch.WordTrace]
  refine ⟨17564373811350627372220243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23419165081800836496293657 17564373811350627372220243)
  ·
    refine ⟨26346560717025941058330365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17564373811350627372220243 26346560717025941058330365)
    ·
      refine ⟨9879960268884727896873887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26346560717025941058330365 9879960268884727896873887)
      ·
        refine ⟨14819940403327091845310831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9879960268884727896873887 14819940403327091845310831)
        ·
          refine ⟨22229910604990637767966247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14819940403327091845310831 22229910604990637767966247)
          ·
            refine ⟨33344865907485956651949371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22229910604990637767966247 33344865907485956651949371)
            ·
              refine ⟨50017298861228934977924057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33344865907485956651949371 50017298861228934977924057)
              ·
                refine ⟨37512974145921701233443043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50017298861228934977924057 37512974145921701233443043)
                ·
                  refine ⟨56269461218882551850164565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37512974145921701233443043 56269461218882551850164565)
                  ·
                    refine ⟨164851937164694976123529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 56269461218882551850164565 164851937164694976123529)
                    ·
                      rfl

theorem cell23_963144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 1, 10].length) (baseStart_963144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_963144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_963144 prefixEnd_963144 := by exact prefixLift 963144
  have htrace : WordTrace (prefixWord ++ tailWord_963144) baseStart_963144 baseEnd_963144 := by
    simpa [prefixWord, tailWord_963144, baseEnd_963144] using wordTrace_append hprefix tailTrace_963144
  have hstable : (prefixWord ++ tailWord_963144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963144).length < 2 ^ (prefixWord ++ tailWord_963144).sum := by decide
  have hdescent : baseEnd_963144 < baseStart_963144 := by decide
  rcases family_descends (prefixWord ++ tailWord_963144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963151 : List Nat := [1, 1, 2, 1, 1, 2, 4, 4, 2, 1, 4]
def baseStart_963151 : Nat := 118140960795 + 963151 * 2 ^ 59
def prefixEnd_963151 : Nat := 4983230072969 + 3 ^ 40 * 963151 * 2
def baseEnd_963151 : Nat := 494559405858666400983055

theorem tailTrace_963151 : CollatzResearch.WordTrace tailWord_963151 prefixEnd_963151 494559405858666400983055 := by
  unfold tailWord_963151
  simp only [CollatzResearch.WordTrace]
  refine ⟨35129002933675894939945307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23419335289117263293296871 35129002933675894939945307)
  ·
    refine ⟨52693504400513842409917961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35129002933675894939945307 52693504400513842409917961)
    ·
      refine ⟨39520128300385381807438471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52693504400513842409917961 39520128300385381807438471)
      ·
        refine ⟨59280192450578072711157707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39520128300385381807438471 59280192450578072711157707)
        ·
          refine ⟨88920288675867109066736561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59280192450578072711157707 88920288675867109066736561)
          ·
            refine ⟨66690216506900331800052421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88920288675867109066736561 66690216506900331800052421)
            ·
              refine ⟨12504415595043812212509829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66690216506900331800052421 12504415595043812212509829)
              ·
                refine ⟨2344577924070714789845593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12504415595043812212509829 2344577924070714789845593)
                ·
                  refine ⟨1758433443053036092384195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2344577924070714789845593 1758433443053036092384195)
                  ·
                    refine ⟨2637650164579554138576293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1758433443053036092384195 2637650164579554138576293)
                    ·
                      refine ⟨494559405858666400983055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2637650164579554138576293 494559405858666400983055)
                      ·
                        rfl

theorem cell23_963151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 4, 2, 1, 4].length) (baseStart_963151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_963151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_963151 prefixEnd_963151 := by exact prefixLift 963151
  have htrace : WordTrace (prefixWord ++ tailWord_963151) baseStart_963151 baseEnd_963151 := by
    simpa [prefixWord, tailWord_963151, baseEnd_963151] using wordTrace_append hprefix tailTrace_963151
  have hstable : (prefixWord ++ tailWord_963151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963151).length < 2 ^ (prefixWord ++ tailWord_963151).sum := by decide
  have hdescent : baseEnd_963151 < baseStart_963151 := by decide
  rcases family_descends (prefixWord ++ tailWord_963151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963168 : List Nat := [2, 1, 1, 3, 2, 1, 4, 1, 2, 4, 2]
def baseStart_963168 : Nat := 118140960795 + 963168 * 2 ^ 59
def prefixEnd_963168 : Nat := 4983230072969 + 3 ^ 40 * 963168 * 2
def baseEnd_963168 : Nat := 494568135029792834470477

theorem tailTrace_963168 : CollatzResearch.WordTrace tailWord_963168 prefixEnd_963168 494568135029792834470477 := by
  unfold tailWord_963168
  simp only [CollatzResearch.WordTrace]
  refine ⟨17564811487307153421657079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23419748649742871228876105 17564811487307153421657079)
  ·
    refine ⟨26347217230960730132485619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17564811487307153421657079 26347217230960730132485619)
    ·
      refine ⟨39520825846441095198728429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26347217230960730132485619 39520825846441095198728429)
      ·
        refine ⟨14820309692415410699523161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39520825846441095198728429 14820309692415410699523161)
        ·
          refine ⟨11115232269311558024642371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14820309692415410699523161 11115232269311558024642371)
          ·
            refine ⟨16672848403967337036963557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11115232269311558024642371 16672848403967337036963557)
            ·
              refine ⟨3126159075743875694430667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16672848403967337036963557 3126159075743875694430667)
              ·
                refine ⟨4689238613615813541646001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3126159075743875694430667 4689238613615813541646001)
                ·
                  refine ⟨3516928960211860156234501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4689238613615813541646001 3516928960211860156234501)
                  ·
                    refine ⟨659424180039723779293969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3516928960211860156234501 659424180039723779293969)
                    ·
                      refine ⟨494568135029792834470477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 659424180039723779293969 494568135029792834470477)
                      ·
                        rfl

theorem cell23_963168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 2, 4, 2].length) (baseStart_963168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_963168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_963168 prefixEnd_963168 := by exact prefixLift 963168
  have htrace : WordTrace (prefixWord ++ tailWord_963168) baseStart_963168 baseEnd_963168 := by
    simpa [prefixWord, tailWord_963168, baseEnd_963168] using wordTrace_append hprefix tailTrace_963168
  have hstable : (prefixWord ++ tailWord_963168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963168).length < 2 ^ (prefixWord ++ tailWord_963168).sum := by decide
  have hdescent : baseEnd_963168 < baseStart_963168 := by decide
  rcases family_descends (prefixWord ++ tailWord_963168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963171 : List Nat := [1, 1, 1, 5, 1, 2, 1, 1, 3, 4, 3]
def baseStart_963171 : Nat := 118140960795 + 963171 * 2 ^ 59
def prefixEnd_963171 : Nat := 4983230072969 + 3 ^ 40 * 963171 * 2
def baseEnd_963171 : Nat := 494569675471756322732963

theorem tailTrace_963171 : CollatzResearch.WordTrace tailWord_963171 prefixEnd_963171 494569675471756322732963 := by
  unfold tailWord_963171
  simp only [CollatzResearch.WordTrace]
  refine ⟨35129732393603438355673367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23419821595735625570448911 35129732393603438355673367)
  ·
    refine ⟨52694598590405157533510051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35129732393603438355673367 52694598590405157533510051)
    ·
      refine ⟨79041897885607736300265077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52694598590405157533510051 79041897885607736300265077)
      ·
        refine ⟨7410177926775725278149851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79041897885607736300265077 7410177926775725278149851)
        ·
          refine ⟨11115266890163587917224777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7410177926775725278149851 11115266890163587917224777)
          ·
            refine ⟨8336450167622690937918583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11115266890163587917224777 8336450167622690937918583)
            ·
              refine ⟨12504675251434036406877875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8336450167622690937918583 12504675251434036406877875)
              ·
                refine ⟨18757012877151054610316813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12504675251434036406877875 18757012877151054610316813)
                ·
                  refine ⟨7033879828931645478868805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18757012877151054610316813 7033879828931645478868805)
                  ·
                    refine ⟨1318852467924683527287901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7033879828931645478868805 1318852467924683527287901)
                    ·
                      refine ⟨494569675471756322732963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1318852467924683527287901 494569675471756322732963)
                      ·
                        rfl

theorem cell23_963171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 4, 3].length) (baseStart_963171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_963171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_963171 prefixEnd_963171 := by exact prefixLift 963171
  have htrace : WordTrace (prefixWord ++ tailWord_963171) baseStart_963171 baseEnd_963171 := by
    simpa [prefixWord, tailWord_963171, baseEnd_963171] using wordTrace_append hprefix tailTrace_963171
  have hstable : (prefixWord ++ tailWord_963171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963171).length < 2 ^ (prefixWord ++ tailWord_963171).sum := by decide
  have hdescent : baseEnd_963171 < baseStart_963171 := by decide
  rcases family_descends (prefixWord ++ tailWord_963171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963178 : List Nat := [3, 1, 3, 2, 1, 1, 1, 4, 3, 4]
def baseStart_963178 : Nat := 118140960795 + 963178 * 2 ^ 59
def prefixEnd_963178 : Nat := 4983230072969 + 3 ^ 40 * 963178 * 2
def baseEnd_963178 : Nat := 164857756612112598448477

theorem tailTrace_963178 : CollatzResearch.WordTrace tailWord_963178 prefixEnd_963178 164857756612112598448477 := by
  unfold tailWord_963178
  simp only [CollatzResearch.WordTrace]
  refine ⟨8782496926144519637794547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23419991803052052367452125 8782496926144519637794547)
  ·
    refine ⟨13173745389216779456691821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8782496926144519637794547 13173745389216779456691821)
    ·
      refine ⟨4940154520956292296259433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13173745389216779456691821 4940154520956292296259433)
      ·
        refine ⟨3705115890717219222194575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4940154520956292296259433 3705115890717219222194575)
        ·
          refine ⟨5557673836075828833291863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3705115890717219222194575 5557673836075828833291863)
          ·
            refine ⟨8336510754113743249937795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5557673836075828833291863 8336510754113743249937795)
            ·
              refine ⟨12504766131170614874906693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8336510754113743249937795 12504766131170614874906693)
              ·
                refine ⟨2344643649594490289045005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12504766131170614874906693 2344643649594490289045005)
                ·
                  refine ⟨879241368597933858391877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2344643649594490289045005 879241368597933858391877)
                  ·
                    refine ⟨164857756612112598448477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 879241368597933858391877 164857756612112598448477)
                    ·
                      rfl

theorem cell23_963178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 4, 3, 4].length) (baseStart_963178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_963178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_963178 prefixEnd_963178 := by exact prefixLift 963178
  have htrace : WordTrace (prefixWord ++ tailWord_963178) baseStart_963178 baseEnd_963178 := by
    simpa [prefixWord, tailWord_963178, baseEnd_963178] using wordTrace_append hprefix tailTrace_963178
  have hstable : (prefixWord ++ tailWord_963178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963178).length < 2 ^ (prefixWord ++ tailWord_963178).sum := by decide
  have hdescent : baseEnd_963178 < baseStart_963178 := by decide
  rcases family_descends (prefixWord ++ tailWord_963178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963251 : List Nat := [1, 1, 1, 2, 3, 4, 1, 1, 3, 6]
def baseStart_963251 : Nat := 118140960795 + 963251 * 2 ^ 59
def prefixEnd_963251 : Nat := 4983230072969 + 3 ^ 40 * 963251 * 2
def baseEnd_963251 : Nat := 164870251308038669910865

theorem tailTrace_963251 : CollatzResearch.WordTrace tailWord_963251 prefixEnd_963251 164870251308038669910865 := by
  unfold tailWord_963251
  simp only [CollatzResearch.WordTrace]
  refine ⟨35132650233313612018585607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23421766822209074679057071 35132650233313612018585607)
  ·
    refine ⟨52698975349970418027878411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35132650233313612018585607 52698975349970418027878411)
    ·
      refine ⟨79048463024955627041817617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52698975349970418027878411 79048463024955627041817617)
      ·
        refine ⟨59286347268716720281363213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79048463024955627041817617 59286347268716720281363213)
        ·
          refine ⟨22232380225768770105511205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59286347268716720281363213 22232380225768770105511205)
          ·
            refine ⟨4168571292331644394783351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22232380225768770105511205 4168571292331644394783351)
            ·
              refine ⟨6252856938497466592175027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4168571292331644394783351 6252856938497466592175027)
              ·
                refine ⟨9379285407746199888262541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6252856938497466592175027 9379285407746199888262541)
                ·
                  refine ⟨3517232027904824958098453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9379285407746199888262541 3517232027904824958098453)
                  ·
                    refine ⟨164870251308038669910865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3517232027904824958098453 164870251308038669910865)
                    ·
                      rfl

theorem cell23_963251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 3, 6].length) (baseStart_963251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_963251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_963251 prefixEnd_963251 := by exact prefixLift 963251
  have htrace : WordTrace (prefixWord ++ tailWord_963251) baseStart_963251 baseEnd_963251 := by
    simpa [prefixWord, tailWord_963251, baseEnd_963251] using wordTrace_append hprefix tailTrace_963251
  have hstable : (prefixWord ++ tailWord_963251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963251).length < 2 ^ (prefixWord ++ tailWord_963251).sum := by decide
  have hdescent : baseEnd_963251 < baseStart_963251 := by decide
  rcases family_descends (prefixWord ++ tailWord_963251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963271 : List Nat := [1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 6]
def baseStart_963271 : Nat := 118140960795 + 963271 * 2 ^ 59
def prefixEnd_963271 : Nat := 4983230072969 + 3 ^ 40 * 963271 * 2
def baseEnd_963271 : Nat := 494621023537205931482503

theorem tailTrace_963271 : CollatzResearch.WordTrace tailWord_963271 prefixEnd_963271 494621023537205931482503 := by
  unfold tailWord_963271
  simp only [CollatzResearch.WordTrace]
  refine ⟨35133379693241155434313667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23422253128827436956209111 35133379693241155434313667)
  ·
    refine ⟨52700069539861733151470501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35133379693241155434313667 52700069539861733151470501)
    ·
      refine ⟨9881263038724074965900719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52700069539861733151470501 9881263038724074965900719)
      ·
        refine ⟨14821894558086112448851079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9881263038724074965900719 14821894558086112448851079)
        ·
          refine ⟨22232841837129168673276619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14821894558086112448851079 22232841837129168673276619)
          ·
            refine ⟨33349262755693753009914929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22232841837129168673276619 33349262755693753009914929)
            ·
              refine ⟨25011947066770314757436197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33349262755693753009914929 25011947066770314757436197)
              ·
                refine ⟨4689740075019434017019287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25011947066770314757436197 4689740075019434017019287)
                ·
                  refine ⟨7034610112529151025528931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4689740075019434017019287 7034610112529151025528931)
                  ·
                    refine ⟨10551915168793726538293397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7034610112529151025528931 10551915168793726538293397)
                    ·
                      refine ⟨494621023537205931482503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10551915168793726538293397 494621023537205931482503)
                      ·
                        rfl

theorem cell23_963271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 6].length) (baseStart_963271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_963271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_963271 prefixEnd_963271 := by exact prefixLift 963271
  have htrace : WordTrace (prefixWord ++ tailWord_963271) baseStart_963271 baseEnd_963271 := by
    simpa [prefixWord, tailWord_963271, baseEnd_963271] using wordTrace_append hprefix tailTrace_963271
  have hstable : (prefixWord ++ tailWord_963271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963271).length < 2 ^ (prefixWord ++ tailWord_963271).sum := by decide
  have hdescent : baseEnd_963271 < baseStart_963271 := by decide
  rcases family_descends (prefixWord ++ tailWord_963271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963288 : List Nat := [2, 1, 2, 2, 3, 2, 1, 3, 1, 2, 4]
def baseStart_963288 : Nat := 118140960795 + 963288 * 2 ^ 59
def prefixEnd_963288 : Nat := 4983230072969 + 3 ^ 40 * 963288 * 2
def baseEnd_963288 : Nat := 494629752708332364969925

theorem tailTrace_963288 : CollatzResearch.WordTrace tailWord_963288 prefixEnd_963288 494629752708332364969925 := by
  unfold tailWord_963288
  simp only [CollatzResearch.WordTrace]
  refine ⟨17566999867089783668841259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23422666489453044891788345 17566999867089783668841259)
  ·
    refine ⟨26350499800634675503261889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17566999867089783668841259 26350499800634675503261889)
    ·
      refine ⟨19762874850476006627446417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26350499800634675503261889 19762874850476006627446417)
      ·
        refine ⟨14822156137857004970584813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19762874850476006627446417 14822156137857004970584813)
        ·
          refine ⟨5558308551696376863969305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14822156137857004970584813 5558308551696376863969305)
          ·
            refine ⟨4168731413772282647976979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5558308551696376863969305 4168731413772282647976979)
            ·
              refine ⟨6253097120658423971965469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4168731413772282647976979 6253097120658423971965469)
              ·
                refine ⟨2344911420246908989487051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6253097120658423971965469 2344911420246908989487051)
                ·
                  refine ⟨3517367130370363484230577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2344911420246908989487051 3517367130370363484230577)
                  ·
                    refine ⟨2638025347777772613172933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3517367130370363484230577 2638025347777772613172933)
                    ·
                      refine ⟨494629752708332364969925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2638025347777772613172933 494629752708332364969925)
                      ·
                        rfl

theorem cell23_963288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 3, 1, 2, 4].length) (baseStart_963288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_963288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_963288 prefixEnd_963288 := by exact prefixLift 963288
  have htrace : WordTrace (prefixWord ++ tailWord_963288) baseStart_963288 baseEnd_963288 := by
    simpa [prefixWord, tailWord_963288, baseEnd_963288] using wordTrace_append hprefix tailTrace_963288
  have hstable : (prefixWord ++ tailWord_963288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963288).length < 2 ^ (prefixWord ++ tailWord_963288).sum := by decide
  have hdescent : baseEnd_963288 < baseStart_963288 := by decide
  rcases family_descends (prefixWord ++ tailWord_963288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963325 : List Nat := [1, 4, 1, 1, 1, 1, 5, 1, 4, 1, 3]
def baseStart_963325 : Nat := 118140960795 + 963325 * 2 ^ 59
def prefixEnd_963325 : Nat := 4983230072969 + 3 ^ 40 * 963325 * 2
def baseEnd_963325 : Nat := 494648751492548720207255

theorem tailTrace_963325 : CollatzResearch.WordTrace tailWord_963325 prefixEnd_963325 494648751492548720207255 := by
  unfold tailWord_963325
  simp only [CollatzResearch.WordTrace]
  refine ⟨35135349235045522656779429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23423566156697015104519619 35135349235045522656779429)
  ·
    refine ⟨6587877981571035498146143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35135349235045522656779429 6587877981571035498146143)
    ·
      refine ⟨9881816972356553247219215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6587877981571035498146143 9881816972356553247219215)
      ·
        refine ⟨14822725458534829870828823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9881816972356553247219215 14822725458534829870828823)
        ·
          refine ⟨22234088187802244806243235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14822725458534829870828823 22234088187802244806243235)
          ·
            refine ⟨33351132281703367209364853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22234088187802244806243235 33351132281703367209364853)
            ·
              refine ⟨3126668651409690675877955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33351132281703367209364853 3126668651409690675877955)
              ·
                refine ⟨4690002977114536013816933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3126668651409690675877955 4690002977114536013816933)
                ·
                  refine ⟨879375558208975502590675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4690002977114536013816933 879375558208975502590675)
                  ·
                    refine ⟨1319063337313463253886013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 879375558208975502590675 1319063337313463253886013)
                    ·
                      refine ⟨494648751492548720207255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1319063337313463253886013 494648751492548720207255)
                      ·
                        rfl

theorem cell23_963325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 4, 1, 3].length) (baseStart_963325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_963325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_963325 prefixEnd_963325 := by exact prefixLift 963325
  have htrace : WordTrace (prefixWord ++ tailWord_963325) baseStart_963325 baseEnd_963325 := by
    simpa [prefixWord, tailWord_963325, baseEnd_963325] using wordTrace_append hprefix tailTrace_963325
  have hstable : (prefixWord ++ tailWord_963325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963325).length < 2 ^ (prefixWord ++ tailWord_963325).sum := by decide
  have hdescent : baseEnd_963325 < baseStart_963325 := by decide
  rcases family_descends (prefixWord ++ tailWord_963325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963326 : List Nat := [4, 2, 2, 1, 2, 1, 2, 4, 1, 2, 2]
def baseStart_963326 : Nat := 118140960795 + 963326 * 2 ^ 59
def prefixEnd_963326 : Nat := 4983230072969 + 3 ^ 40 * 963326 * 2
def baseEnd_963326 : Nat := 494649264973203216294751

theorem tailTrace_963326 : CollatzResearch.WordTrace tailWord_963326 prefixEnd_963326 494649264973203216294751 := by
  unfold tailWord_963326
  simp only [CollatzResearch.WordTrace]
  refine ⟨4391923213505237478445729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23423590472027933218377221 4391923213505237478445729)
  ·
    refine ⟨3293942410128928108834297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4391923213505237478445729 3293942410128928108834297)
    ·
      refine ⟨2470456807596696081625723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3293942410128928108834297 2470456807596696081625723)
      ·
        refine ⟨3705685211395044122438585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2470456807596696081625723 3705685211395044122438585)
        ·
          refine ⟨2779263908546283091828939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3705685211395044122438585 2779263908546283091828939)
          ·
            refine ⟨4168895862819424637743409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2779263908546283091828939 4168895862819424637743409)
            ·
              refine ⟨3126671897114568478307557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4168895862819424637743409 3126671897114568478307557)
              ·
                refine ⟨586250980708981589682667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3126671897114568478307557 586250980708981589682667)
                ·
                  refine ⟨879376471063472384524001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 586250980708981589682667 879376471063472384524001)
                  ·
                    refine ⟨659532353297604288393001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 879376471063472384524001 659532353297604288393001)
                    ·
                      refine ⟨494649264973203216294751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 659532353297604288393001 494649264973203216294751)
                      ·
                        rfl

theorem cell23_963326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 4, 1, 2, 2].length) (baseStart_963326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_963326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_963326 prefixEnd_963326 := by exact prefixLift 963326
  have htrace : WordTrace (prefixWord ++ tailWord_963326) baseStart_963326 baseEnd_963326 := by
    simpa [prefixWord, tailWord_963326, baseEnd_963326] using wordTrace_append hprefix tailTrace_963326
  have hstable : (prefixWord ++ tailWord_963326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963326).length < 2 ^ (prefixWord ++ tailWord_963326).sum := by decide
  have hdescent : baseEnd_963326 < baseStart_963326 := by decide
  rcases family_descends (prefixWord ++ tailWord_963326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963365 : List Nat := [1, 3, 1, 2, 3, 1, 2, 1, 3, 4, 2]
def baseStart_963365 : Nat := 118140960795 + 963365 * 2 ^ 59
def prefixEnd_963365 : Nat := 4983230072969 + 3 ^ 40 * 963365 * 2
def baseEnd_963365 : Nat := 494669290718728563707071

theorem tailTrace_963365 : CollatzResearch.WordTrace tailWord_963365 prefixEnd_963365 494669290718728563707071 := by
  unfold tailWord_963365
  simp only [CollatzResearch.WordTrace]
  refine ⟨35136808154900609488235549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23424538769933739658823699 35136808154900609488235549)
  ·
    refine ⟨13176303058087728558088331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35136808154900609488235549 13176303058087728558088331)
    ·
      refine ⟨19764454587131592837132497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13176303058087728558088331 19764454587131592837132497)
      ·
        refine ⟨14823340940348694627849373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19764454587131592837132497 14823340940348694627849373)
        ·
          refine ⟨5558752852630760485443515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14823340940348694627849373 5558752852630760485443515)
          ·
            refine ⟨8338129278946140728165273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5558752852630760485443515 8338129278946140728165273)
            ·
              refine ⟨6253596959209605546123955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8338129278946140728165273 6253596959209605546123955)
              ·
                refine ⟨9380395438814408319185933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6253596959209605546123955 9380395438814408319185933)
                ·
                  refine ⟨3517648289555403119694725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9380395438814408319185933 3517648289555403119694725)
                  ·
                    refine ⟨659559054291638084942761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3517648289555403119694725 659559054291638084942761)
                    ·
                      refine ⟨494669290718728563707071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 659559054291638084942761 494669290718728563707071)
                      ·
                        rfl

theorem cell23_963365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 3, 4, 2].length) (baseStart_963365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_963365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_963365 prefixEnd_963365 := by exact prefixLift 963365
  have htrace : WordTrace (prefixWord ++ tailWord_963365) baseStart_963365 baseEnd_963365 := by
    simpa [prefixWord, tailWord_963365, baseEnd_963365] using wordTrace_append hprefix tailTrace_963365
  have hstable : (prefixWord ++ tailWord_963365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963365).length < 2 ^ (prefixWord ++ tailWord_963365).sum := by decide
  have hdescent : baseEnd_963365 < baseStart_963365 := by decide
  rcases family_descends (prefixWord ++ tailWord_963365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963371 : List Nat := [1, 1, 1, 1, 2, 1, 2, 3, 11]
def baseStart_963371 : Nat := 118140960795 + 963371 * 2 ^ 59
def prefixEnd_963371 : Nat := 4983230072969 + 3 ^ 40 * 963371 * 2
def baseEnd_963371 : Nat := 54963596844739504470227

theorem tailTrace_963371 : CollatzResearch.WordTrace tailWord_963371 prefixEnd_963371 54963596844739504470227 := by
  unfold tailWord_963371
  simp only [CollatzResearch.WordTrace]
  refine ⟨35137026992878872512953967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23424684661919248341969311 35137026992878872512953967)
  ·
    refine ⟨52705540489318308769430951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35137026992878872512953967 52705540489318308769430951)
    ·
      refine ⟨79058310733977463154146427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52705540489318308769430951 79058310733977463154146427)
      ·
        refine ⟨118587466100966194731219641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79058310733977463154146427 118587466100966194731219641)
        ·
          refine ⟨88940599575724646048414731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118587466100966194731219641 88940599575724646048414731)
          ·
            refine ⟨133410899363586969072622097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88940599575724646048414731 133410899363586969072622097)
            ·
              refine ⟨100058174522690226804466573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133410899363586969072622097 100058174522690226804466573)
              ·
                refine ⟨37521815446008835051674965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100058174522690226804466573 37521815446008835051674965)
                ·
                  refine ⟨54963596844739504470227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 37521815446008835051674965 54963596844739504470227)
                  ·
                    rfl

theorem cell23_963371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 11].length) (baseStart_963371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_963371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_963371 prefixEnd_963371 := by exact prefixLift 963371
  have htrace : WordTrace (prefixWord ++ tailWord_963371) baseStart_963371 baseEnd_963371 := by
    simpa [prefixWord, tailWord_963371, baseEnd_963371] using wordTrace_append hprefix tailTrace_963371
  have hstable : (prefixWord ++ tailWord_963371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963371).length < 2 ^ (prefixWord ++ tailWord_963371).sum := by decide
  have hdescent : baseEnd_963371 < baseStart_963371 := by decide
  rcases family_descends (prefixWord ++ tailWord_963371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963393 : List Nat := [1, 2, 5, 3, 1, 2, 2, 1, 2, 1, 3]
def baseStart_963393 : Nat := 118140960795 + 963393 * 2 ^ 59
def prefixEnd_963393 : Nat := 4983230072969 + 3 ^ 40 * 963393 * 2
def baseEnd_963393 : Nat := 494683668177054454156943

theorem tailTrace_963393 : CollatzResearch.WordTrace tailWord_963393 prefixEnd_963393 494683668177054454156943 := by
  unfold tailWord_963393
  simp only [CollatzResearch.WordTrace]
  refine ⟨35137829398799170270254833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23425219599199446846836555 35137829398799170270254833)
  ·
    refine ⟨26353372049099377702691125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35137829398799170270254833 26353372049099377702691125)
    ·
      refine ⟨2470628629603066659627293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26353372049099377702691125 2470628629603066659627293)
      ·
        refine ⟨926485736101149997360235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2470628629603066659627293 926485736101149997360235)
        ·
          refine ⟨1389728604151724996040353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 926485736101149997360235 1389728604151724996040353)
          ·
            refine ⟨1042296453113793747030265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1389728604151724996040353 1042296453113793747030265)
            ·
              refine ⟨781722339835345310272699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1042296453113793747030265 781722339835345310272699)
              ·
                refine ⟨1172583509753017965409049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 781722339835345310272699 1172583509753017965409049)
                ·
                  refine ⟨879437632314763474056787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1172583509753017965409049 879437632314763474056787)
                  ·
                    refine ⟨1319156448472145211085181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 879437632314763474056787 1319156448472145211085181)
                    ·
                      refine ⟨494683668177054454156943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1319156448472145211085181 494683668177054454156943)
                      ·
                        rfl

theorem cell23_963393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_963393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_963393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_963393 prefixEnd_963393 := by exact prefixLift 963393
  have htrace : WordTrace (prefixWord ++ tailWord_963393) baseStart_963393 baseEnd_963393 := by
    simpa [prefixWord, tailWord_963393, baseEnd_963393] using wordTrace_append hprefix tailTrace_963393
  have hstable : (prefixWord ++ tailWord_963393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963393).length < 2 ^ (prefixWord ++ tailWord_963393).sum := by decide
  have hdescent : baseEnd_963393 < baseStart_963393 := by decide
  rcases family_descends (prefixWord ++ tailWord_963393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963445 : List Nat := [1, 3, 4, 1, 1, 2, 2, 1, 1, 2, 5]
def baseStart_963445 : Nat := 118140960795 + 963445 * 2 ^ 59
def prefixEnd_963445 : Nat := 4983230072969 + 3 ^ 40 * 963445 * 2
def baseEnd_963445 : Nat := 494710369171088250706703

theorem tailTrace_963445 : CollatzResearch.WordTrace tailWord_963445 prefixEnd_963445 494710369171088250706703 := by
  unfold tailWord_963445
  simp only [CollatzResearch.WordTrace]
  refine ⟨35139725994610783151147789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23426483996407188767431859 35139725994610783151147789)
  ·
    refine ⟨13177397247979043681680421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35139725994610783151147789 13177397247979043681680421)
    ·
      refine ⟨2470761983996070690315079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13177397247979043681680421 2470761983996070690315079)
      ·
        refine ⟨3706142975994106035472619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2470761983996070690315079 3706142975994106035472619)
        ·
          refine ⟨5559214463991159053208929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3706142975994106035472619 5559214463991159053208929)
          ·
            refine ⟨4169410847993369289906697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5559214463991159053208929 4169410847993369289906697)
            ·
              refine ⟨3127058135995026967430023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4169410847993369289906697 3127058135995026967430023)
              ·
                refine ⟨4690587203992540451145035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3127058135995026967430023 4690587203992540451145035)
                ·
                  refine ⟨7035880805988810676717553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4690587203992540451145035 7035880805988810676717553)
                  ·
                    refine ⟨5276910604491608007538165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7035880805988810676717553 5276910604491608007538165)
                    ·
                      refine ⟨494710369171088250706703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5276910604491608007538165 494710369171088250706703)
                      ·
                        rfl

theorem cell23_963445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_963445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_963445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_963445 prefixEnd_963445 := by exact prefixLift 963445
  have htrace : WordTrace (prefixWord ++ tailWord_963445) baseStart_963445 baseEnd_963445 := by
    simpa [prefixWord, tailWord_963445, baseEnd_963445] using wordTrace_append hprefix tailTrace_963445
  have hstable : (prefixWord ++ tailWord_963445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963445).length < 2 ^ (prefixWord ++ tailWord_963445).sum := by decide
  have hdescent : baseEnd_963445 < baseStart_963445 := by decide
  rcases family_descends (prefixWord ++ tailWord_963445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963455 : List Nat := [1, 1, 2, 2, 1, 1, 5, 1, 1, 6, 2]
def baseStart_963455 : Nat := 118140960795 + 963455 * 2 ^ 59
def prefixEnd_963455 : Nat := 4983230072969 + 3 ^ 40 * 963455 * 2
def baseEnd_963455 : Nat := 494715503977633211581657

theorem tailTrace_963455 : CollatzResearch.WordTrace tailWord_963455 prefixEnd_963455 494715503977633211581657 := by
  unfold tailWord_963455
  simp only [CollatzResearch.WordTrace]
  refine ⟨35140090724574554859011819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23426727149716369906007879 35140090724574554859011819)
  ·
    refine ⟨52710136086861832288517729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35140090724574554859011819 52710136086861832288517729)
    ·
      refine ⟨39532602065146374216388297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52710136086861832288517729 39532602065146374216388297)
      ·
        refine ⟨29649451548859780662291223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39532602065146374216388297 29649451548859780662291223)
        ·
          refine ⟨44474177323289670993436835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29649451548859780662291223 44474177323289670993436835)
          ·
            refine ⟨66711265984934506490155253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44474177323289670993436835 66711265984934506490155253)
            ·
              refine ⟨6254181186087609983452055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66711265984934506490155253 6254181186087609983452055)
              ·
                refine ⟨9381271779131414975178083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6254181186087609983452055 9381271779131414975178083)
                ·
                  refine ⟨14071907668697122462767125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9381271779131414975178083 14071907668697122462767125)
                  ·
                    refine ⟨659620671970177615442209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14071907668697122462767125 659620671970177615442209)
                    ·
                      refine ⟨494715503977633211581657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 659620671970177615442209 494715503977633211581657)
                      ·
                        rfl

theorem cell23_963455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 6, 2].length) (baseStart_963455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_963455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_963455 prefixEnd_963455 := by exact prefixLift 963455
  have htrace : WordTrace (prefixWord ++ tailWord_963455) baseStart_963455 baseEnd_963455 := by
    simpa [prefixWord, tailWord_963455, baseEnd_963455] using wordTrace_append hprefix tailTrace_963455
  have hstable : (prefixWord ++ tailWord_963455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963455).length < 2 ^ (prefixWord ++ tailWord_963455).sum := by decide
  have hdescent : baseEnd_963455 < baseStart_963455 := by decide
  rcases family_descends (prefixWord ++ tailWord_963455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963465 : List Nat := [1, 2, 1, 1, 5, 2, 1, 1, 5, 4]
def baseStart_963465 : Nat := 118140960795 + 963465 * 2 ^ 59
def prefixEnd_963465 : Nat := 4983230072969 + 3 ^ 40 * 963465 * 2
def baseEnd_963465 : Nat := 164906879594726057485537

theorem tailTrace_963465 : CollatzResearch.WordTrace tailWord_963465 prefixEnd_963465 164906879594726057485537 := by
  unfold tailWord_963465
  simp only [CollatzResearch.WordTrace]
  refine ⟨35140455454538326566875849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23426970303025551044583899 35140455454538326566875849)
  ·
    refine ⟨26355341590903744925156887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35140455454538326566875849 26355341590903744925156887)
    ·
      refine ⟨39533012386355617387735331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26355341590903744925156887 39533012386355617387735331)
      ·
        refine ⟨59299518579533426081602997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39533012386355617387735331 59299518579533426081602997)
        ·
          refine ⟨5559329866831258695150281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59299518579533426081602997 5559329866831258695150281)
          ·
            refine ⟨4169497400123444021362711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5559329866831258695150281 4169497400123444021362711)
            ·
              refine ⟨6254246100185166032044067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4169497400123444021362711 6254246100185166032044067)
              ·
                refine ⟨9381369150277749048066101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6254246100185166032044067 9381369150277749048066101)
                ·
                  refine ⟨879503357838538973256197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9381369150277749048066101 879503357838538973256197)
                  ·
                    refine ⟨164906879594726057485537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 879503357838538973256197 164906879594726057485537)
                    ·
                      rfl

theorem cell23_963465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 5, 4].length) (baseStart_963465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_963465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_963465 prefixEnd_963465 := by exact prefixLift 963465
  have htrace : WordTrace (prefixWord ++ tailWord_963465) baseStart_963465 baseEnd_963465 := by
    simpa [prefixWord, tailWord_963465, baseEnd_963465] using wordTrace_append hprefix tailTrace_963465
  have hstable : (prefixWord ++ tailWord_963465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963465).length < 2 ^ (prefixWord ++ tailWord_963465).sum := by decide
  have hdescent : baseEnd_963465 < baseStart_963465 := by decide
  rcases family_descends (prefixWord ++ tailWord_963465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963475 : List Nat := [1, 1, 1, 2, 1, 2, 1, 7, 2, 2, 3]
def baseStart_963475 : Nat := 118140960795 + 963475 * 2 ^ 59
def prefixEnd_963475 : Nat := 4983230072969 + 3 ^ 40 * 963475 * 2
def baseEnd_963475 : Nat := 494725773590723133331565

theorem tailTrace_963475 : CollatzResearch.WordTrace tailWord_963475 prefixEnd_963475 494725773590723133331565 := by
  unfold tailWord_963475
  simp only [CollatzResearch.WordTrace]
  refine ⟨35140820184502098274739879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23427213456334732183159919 35140820184502098274739879)
  ·
    refine ⟨52711230276753147412109819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35140820184502098274739879 52711230276753147412109819)
    ·
      refine ⟨79066845415129721118164729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52711230276753147412109819 79066845415129721118164729)
      ·
        refine ⟨59300134061347290838623547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79066845415129721118164729 59300134061347290838623547)
        ·
          refine ⟨88950201092020936257935321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59300134061347290838623547 88950201092020936257935321)
          ·
            refine ⟨66712650819015702193451491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88950201092020936257935321 66712650819015702193451491)
            ·
              refine ⟨100068976228523553290177237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66712650819015702193451491 100068976228523553290177237)
              ·
                refine ⟨2345366630356020780238529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 100068976228523553290177237 2345366630356020780238529)
                ·
                  refine ⟨1759024972767015585178897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2345366630356020780238529 1759024972767015585178897)
                  ·
                    refine ⟨1319268729575261688884173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1759024972767015585178897 1319268729575261688884173)
                    ·
                      refine ⟨494725773590723133331565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1319268729575261688884173 494725773590723133331565)
                      ·
                        rfl

theorem cell23_963475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 7, 2, 2, 3].length) (baseStart_963475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_963475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_963475 prefixEnd_963475 := by exact prefixLift 963475
  have htrace : WordTrace (prefixWord ++ tailWord_963475) baseStart_963475 baseEnd_963475 := by
    simpa [prefixWord, tailWord_963475, baseEnd_963475] using wordTrace_append hprefix tailTrace_963475
  have hstable : (prefixWord ++ tailWord_963475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963475).length < 2 ^ (prefixWord ++ tailWord_963475).sum := by decide
  have hdescent : baseEnd_963475 < baseStart_963475 := by decide
  rcases family_descends (prefixWord ++ tailWord_963475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963512 : List Nat := [2, 1, 2, 1, 2, 5, 3, 1, 6]
def baseStart_963512 : Nat := 118140960795 + 963512 * 2 ^ 59
def prefixEnd_963512 : Nat := 4983230072969 + 3 ^ 40 * 963512 * 2
def baseEnd_963512 : Nat := 54971641374993276507655

theorem tailTrace_963512 : CollatzResearch.WordTrace tailWord_963512 prefixEnd_963512 54971641374993276507655 := by
  unfold tailWord_963512
  simp only [CollatzResearch.WordTrace]
  refine ⟨17571084842684026796918395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23428113123578702395891193 17571084842684026796918395)
  ·
    refine ⟨26356627264026040195377593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17571084842684026796918395 26356627264026040195377593)
    ·
      refine ⟨19767470448019530146533195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26356627264026040195377593 19767470448019530146533195)
      ·
        refine ⟨29651205672029295219799793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19767470448019530146533195 29651205672029295219799793)
        ·
          refine ⟨22238404254021971414849845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29651205672029295219799793 22238404254021971414849845)
          ·
            refine ⟨2084850398814559820142173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22238404254021971414849845 2084850398814559820142173)
            ·
              refine ⟨781818899555459932553315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2084850398814559820142173 781818899555459932553315)
              ·
                refine ⟨1172728349333189898829973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 781818899555459932553315 1172728349333189898829973)
                ·
                  refine ⟨54971641374993276507655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1172728349333189898829973 54971641374993276507655)
                  ·
                    rfl

theorem cell23_963512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 3, 1, 6].length) (baseStart_963512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_963512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_963512 prefixEnd_963512 := by exact prefixLift 963512
  have htrace : WordTrace (prefixWord ++ tailWord_963512) baseStart_963512 baseEnd_963512 := by
    simpa [prefixWord, tailWord_963512, baseEnd_963512] using wordTrace_append hprefix tailTrace_963512
  have hstable : (prefixWord ++ tailWord_963512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963512).length < 2 ^ (prefixWord ++ tailWord_963512).sum := by decide
  have hdescent : baseEnd_963512 < baseStart_963512 := by decide
  rcases family_descends (prefixWord ++ tailWord_963512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963532 : List Nat := [2, 2, 1, 4, 1, 1, 1, 3, 1, 5, 2]
def baseStart_963532 : Nat := 118140960795 + 963532 * 2 ^ 59
def prefixEnd_963532 : Nat := 4983230072969 + 3 ^ 40 * 963532 * 2
def baseEnd_963532 : Nat := 494755041988029410318803

theorem tailTrace_963532 : CollatzResearch.WordTrace tailWord_963532 prefixEnd_963532 494755041988029410318803 := by
  unfold tailWord_963532
  simp only [CollatzResearch.WordTrace]
  refine ⟨17571449572647798504782425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23428599430197064673043233 17571449572647798504782425)
  ·
    refine ⟨13178587179485848878586819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17571449572647798504782425 13178587179485848878586819)
    ·
      refine ⟨19767880769228773317880229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13178587179485848878586819 19767880769228773317880229)
      ·
        refine ⟨3706477644230394997102543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19767880769228773317880229 3706477644230394997102543)
        ·
          refine ⟨5559716466345592495653815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3706477644230394997102543 5559716466345592495653815)
          ·
            refine ⟨8339574699518388743480723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5559716466345592495653815 8339574699518388743480723)
            ·
              refine ⟨12509362049277583115221085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8339574699518388743480723 12509362049277583115221085)
              ·
                refine ⟨4691010768479093668207907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12509362049277583115221085 4691010768479093668207907)
                ·
                  refine ⟨7036516152718640502311861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4691010768479093668207907 7036516152718640502311861)
                  ·
                    refine ⟨659673389317372547091737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7036516152718640502311861 659673389317372547091737)
                    ·
                      refine ⟨494755041988029410318803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 659673389317372547091737 494755041988029410318803)
                      ·
                        rfl

theorem cell23_963532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 1, 5, 2].length) (baseStart_963532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_963532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_963532 prefixEnd_963532 := by exact prefixLift 963532
  have htrace : WordTrace (prefixWord ++ tailWord_963532) baseStart_963532 baseEnd_963532 := by
    simpa [prefixWord, tailWord_963532, baseEnd_963532] using wordTrace_append hprefix tailTrace_963532
  have hstable : (prefixWord ++ tailWord_963532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963532).length < 2 ^ (prefixWord ++ tailWord_963532).sum := by decide
  have hdescent : baseEnd_963532 < baseStart_963532 := by decide
  rcases family_descends (prefixWord ++ tailWord_963532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963549 : List Nat := [1, 4, 3, 1, 2, 1, 1, 1, 4, 3, 2]
def baseStart_963549 : Nat := 118140960795 + 963549 * 2 ^ 59
def prefixEnd_963549 : Nat := 4983230072969 + 3 ^ 40 * 963549 * 2
def baseEnd_963549 : Nat := 494763771159155843806225

theorem tailTrace_963549 : CollatzResearch.WordTrace tailWord_963549 prefixEnd_963549 494763771159155843806225 := by
  unfold tailWord_963549
  simp only [CollatzResearch.WordTrace]
  refine ⟨35143519186234008912933701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23429012790822672608622467 35143519186234008912933701)
  ·
    refine ⟨6589409847418876671175069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35143519186234008912933701 6589409847418876671175069)
    ·
      refine ⟨2471028692782078751690651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6589409847418876671175069 2471028692782078751690651)
      ·
        refine ⟨3706543039173118127535977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2471028692782078751690651 3706543039173118127535977)
        ·
          refine ⟨2779907279379838595651983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3706543039173118127535977 2779907279379838595651983)
          ·
            refine ⟨4169860919069757893477975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2779907279379838595651983 4169860919069757893477975)
            ·
              refine ⟨6254791378604636840216963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4169860919069757893477975 6254791378604636840216963)
              ·
                refine ⟨9382187067906955260325445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6254791378604636840216963 9382187067906955260325445)
                ·
                  refine ⟨1759160075232554111311021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9382187067906955260325445 1759160075232554111311021)
                  ·
                    refine ⟨659685028212207791741633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1759160075232554111311021 659685028212207791741633)
                    ·
                      refine ⟨494763771159155843806225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 659685028212207791741633 494763771159155843806225)
                      ·
                        rfl

theorem cell23_963549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 4, 3, 2].length) (baseStart_963549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_963549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_963549 prefixEnd_963549 := by exact prefixLift 963549
  have htrace : WordTrace (prefixWord ++ tailWord_963549) baseStart_963549 baseEnd_963549 := by
    simpa [prefixWord, tailWord_963549, baseEnd_963549] using wordTrace_append hprefix tailTrace_963549
  have hstable : (prefixWord ++ tailWord_963549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963549).length < 2 ^ (prefixWord ++ tailWord_963549).sum := by decide
  have hdescent : baseEnd_963549 < baseStart_963549 := by decide
  rcases family_descends (prefixWord ++ tailWord_963549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963585 : List Nat := [1, 2, 4, 1, 2, 2, 2, 9]
def baseStart_963585 : Nat := 118140960795 + 963585 * 2 ^ 59
def prefixEnd_963585 : Nat := 4983230072969 + 3 ^ 40 * 963585 * 2
def baseEnd_963585 : Nat := 18325268757878433442817

theorem tailTrace_963585 : CollatzResearch.WordTrace tailWord_963585 prefixEnd_963585 18325268757878433442817 := by
  unfold tailWord_963585
  simp only [CollatzResearch.WordTrace]
  refine ⟨35144832214103587061244209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23429888142735724707496139 35144832214103587061244209)
  ·
    refine ⟨26358624160577690295933157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35144832214103587061244209 26358624160577690295933157)
    ·
      refine ⟨4942242030108316930487467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26358624160577690295933157 4942242030108316930487467)
      ·
        refine ⟨7413363045162475395731201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4942242030108316930487467 7413363045162475395731201)
        ·
          refine ⟨5560022283871856546798401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7413363045162475395731201 5560022283871856546798401)
          ·
            refine ⟨4170016712903892410098801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5560022283871856546798401 4170016712903892410098801)
            ·
              refine ⟨3127512534677919307574101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4170016712903892410098801 3127512534677919307574101)
              ·
                refine ⟨18325268757878433442817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3127512534677919307574101 18325268757878433442817)
                ·
                  rfl

theorem cell23_963585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 9].length) (baseStart_963585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_963585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_963585 prefixEnd_963585 := by exact prefixLift 963585
  have htrace : WordTrace (prefixWord ++ tailWord_963585) baseStart_963585 baseEnd_963585 := by
    simpa [prefixWord, tailWord_963585, baseEnd_963585] using wordTrace_append hprefix tailTrace_963585
  have hstable : (prefixWord ++ tailWord_963585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963585).length < 2 ^ (prefixWord ++ tailWord_963585).sum := by decide
  have hdescent : baseEnd_963585 < baseStart_963585 := by decide
  rcases family_descends (prefixWord ++ tailWord_963585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963592 : List Nat := [2, 1, 3, 2, 1, 4, 1, 2, 1, 2, 4]
def baseStart_963592 : Nat := 118140960795 + 963592 * 2 ^ 59
def prefixEnd_963592 : Nat := 4983230072969 + 3 ^ 40 * 963592 * 2
def baseEnd_963592 : Nat := 494785850827299175568527

theorem tailTrace_963592 : CollatzResearch.WordTrace tailWord_963592 prefixEnd_963592 494785850827299175568527 := by
  unfold tailWord_963592
  simp only [CollatzResearch.WordTrace]
  refine ⟨17572543762539113628374515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23430058350052151504499353 17572543762539113628374515)
  ·
    refine ⟨26358815643808670442561773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17572543762539113628374515 26358815643808670442561773)
    ·
      refine ⟨9884555866428251415960665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26358815643808670442561773 9884555866428251415960665)
      ·
        refine ⟨7413416899821188561970499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9884555866428251415960665 7413416899821188561970499)
        ·
          refine ⟨11120125349731782842955749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7413416899821188561970499 11120125349731782842955749)
          ·
            refine ⟨2085023503074709283054203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11120125349731782842955749 2085023503074709283054203)
            ·
              refine ⟨3127535254612063924581305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2085023503074709283054203 3127535254612063924581305)
              ·
                refine ⟨2345651440959047943435979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3127535254612063924581305 2345651440959047943435979)
                ·
                  refine ⟨3518477161438571915153969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2345651440959047943435979 3518477161438571915153969)
                  ·
                    refine ⟨2638857871078928936365477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3518477161438571915153969 2638857871078928936365477)
                    ·
                      refine ⟨494785850827299175568527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2638857871078928936365477 494785850827299175568527)
                      ·
                        rfl

theorem cell23_963592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_963592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_963592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_963592 prefixEnd_963592 := by exact prefixLift 963592
  have htrace : WordTrace (prefixWord ++ tailWord_963592) baseStart_963592 baseEnd_963592 := by
    simpa [prefixWord, tailWord_963592, baseEnd_963592] using wordTrace_append hprefix tailTrace_963592
  have hstable : (prefixWord ++ tailWord_963592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963592).length < 2 ^ (prefixWord ++ tailWord_963592).sum := by decide
  have hdescent : baseEnd_963592 < baseStart_963592 := by decide
  rcases family_descends (prefixWord ++ tailWord_963592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963615 : List Nat := [1, 1, 2, 4, 1, 3, 1, 1, 2, 7]
def baseStart_963615 : Nat := 118140960795 + 963615 * 2 ^ 59
def prefixEnd_963615 : Nat := 4983230072969 + 3 ^ 40 * 963615 * 2
def baseEnd_963615 : Nat := 164932553627450861860307

theorem tailTrace_963615 : CollatzResearch.WordTrace tailWord_963615 prefixEnd_963615 164932553627450861860307 := by
  unfold tailWord_963615
  simp only [CollatzResearch.WordTrace]
  refine ⟨35145926403994902184836299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23430617602663268123224199 35145926403994902184836299)
  ·
    refine ⟨52718889605992353277254449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35145926403994902184836299 52718889605992353277254449)
    ·
      refine ⟨39539167204494264957940837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52718889605992353277254449 39539167204494264957940837)
      ·
        refine ⟨7413593850842674679613907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39539167204494264957940837 7413593850842674679613907)
        ·
          refine ⟨11120390776264012019420861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7413593850842674679613907 11120390776264012019420861)
          ·
            refine ⟨4170146541099004507282823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11120390776264012019420861 4170146541099004507282823)
            ·
              refine ⟨6255219811648506760924235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4170146541099004507282823 6255219811648506760924235)
              ·
                refine ⟨9382829717472760141386353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6255219811648506760924235 9382829717472760141386353)
                ·
                  refine ⟨7037122288104570106039765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9382829717472760141386353 7037122288104570106039765)
                  ·
                    refine ⟨164932553627450861860307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7037122288104570106039765 164932553627450861860307)
                    ·
                      rfl

theorem cell23_963615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 7].length) (baseStart_963615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_963615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_963615 prefixEnd_963615 := by exact prefixLift 963615
  have htrace : WordTrace (prefixWord ++ tailWord_963615) baseStart_963615 baseEnd_963615 := by
    simpa [prefixWord, tailWord_963615, baseEnd_963615] using wordTrace_append hprefix tailTrace_963615
  have hstable : (prefixWord ++ tailWord_963615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963615).length < 2 ^ (prefixWord ++ tailWord_963615).sum := by decide
  have hdescent : baseEnd_963615 < baseStart_963615 := by decide
  rcases family_descends (prefixWord ++ tailWord_963615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963635 : List Nat := [1, 1, 1, 2, 4, 1, 1, 1, 4, 3, 4]
def baseStart_963635 : Nat := 118140960795 + 963635 * 2 ^ 59
def prefixEnd_963635 : Nat := 4983230072969 + 3 ^ 40 * 963635 * 2
def baseEnd_963635 : Nat := 494807930495442507330829

theorem tailTrace_963635 : CollatzResearch.WordTrace tailWord_963635 prefixEnd_963635 494807930495442507330829 := by
  unfold tailWord_963635
  simp only [CollatzResearch.WordTrace]
  refine ⟨35146655863922445600564359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23431103909281630400376239 35146655863922445600564359)
  ·
    refine ⟨52719983795883668400846539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35146655863922445600564359 52719983795883668400846539)
    ·
      refine ⟨79079975693825502601269809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52719983795883668400846539 79079975693825502601269809)
      ·
        refine ⟨59309981770369126950952357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79079975693825502601269809 59309981770369126950952357)
        ·
          refine ⟨11120621581944211303303567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59309981770369126950952357 11120621581944211303303567)
          ·
            refine ⟨16680932372916316954955351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11120621581944211303303567 16680932372916316954955351)
            ·
              refine ⟨25021398559374475432433027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16680932372916316954955351 25021398559374475432433027)
              ·
                refine ⟨37532097839061713148649541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25021398559374475432433027 37532097839061713148649541)
                ·
                  refine ⟨7037268344824071215371789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37532097839061713148649541 7037268344824071215371789)
                  ·
                    refine ⟨2638975629309026705764421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7037268344824071215371789 2638975629309026705764421)
                    ·
                      refine ⟨494807930495442507330829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2638975629309026705764421 494807930495442507330829)
                      ·
                        rfl

theorem cell23_963635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 3, 4].length) (baseStart_963635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_963635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_963635 prefixEnd_963635 := by exact prefixLift 963635
  have htrace : WordTrace (prefixWord ++ tailWord_963635) baseStart_963635 baseEnd_963635 := by
    simpa [prefixWord, tailWord_963635, baseEnd_963635] using wordTrace_append hprefix tailTrace_963635
  have hstable : (prefixWord ++ tailWord_963635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963635).length < 2 ^ (prefixWord ++ tailWord_963635).sum := by decide
  have hdescent : baseEnd_963635 < baseStart_963635 := by decide
  rcases family_descends (prefixWord ++ tailWord_963635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963639 : List Nat := [1, 1, 3, 1, 2, 2, 1, 6, 1, 3, 2]
def baseStart_963639 : Nat := 118140960795 + 963639 * 2 ^ 59
def prefixEnd_963639 : Nat := 4983230072969 + 3 ^ 40 * 963639 * 2
def baseEnd_963639 : Nat := 494809984418060491680811

theorem tailTrace_963639 : CollatzResearch.WordTrace tailWord_963639 prefixEnd_963639 494809984418060491680811 := by
  unfold tailWord_963639
  simp only [CollatzResearch.WordTrace]
  refine ⟨35146801755907954283709971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23431201170605302855806647 35146801755907954283709971)
  ·
    refine ⟨52720202633861931425564957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35146801755907954283709971 52720202633861931425564957)
    ·
      refine ⟨19770075987698224284586859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52720202633861931425564957 19770075987698224284586859)
      ·
        refine ⟨29655113981547336426880289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19770075987698224284586859 29655113981547336426880289)
        ·
          refine ⟨22241335486160502320160217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29655113981547336426880289 22241335486160502320160217)
          ·
            refine ⟨16681001614620376740120163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22241335486160502320160217 16681001614620376740120163)
            ·
              refine ⟨25021502421930565110180245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16681001614620376740120163 25021502421930565110180245)
              ·
                refine ⟨1172882926027995239539699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25021502421930565110180245 1172882926027995239539699)
                ·
                  refine ⟨1759324389041992859309549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1172882926027995239539699 1759324389041992859309549)
                  ·
                    refine ⟨659746645890747322241081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1759324389041992859309549 659746645890747322241081)
                    ·
                      refine ⟨494809984418060491680811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 659746645890747322241081 494809984418060491680811)
                      ·
                        rfl

theorem cell23_963639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 6, 1, 3, 2].length) (baseStart_963639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_963639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_963639 prefixEnd_963639 := by exact prefixLift 963639
  have htrace : WordTrace (prefixWord ++ tailWord_963639) baseStart_963639 baseEnd_963639 := by
    simpa [prefixWord, tailWord_963639, baseEnd_963639] using wordTrace_append hprefix tailTrace_963639
  have hstable : (prefixWord ++ tailWord_963639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963639).length < 2 ^ (prefixWord ++ tailWord_963639).sum := by decide
  have hdescent : baseEnd_963639 < baseStart_963639 := by decide
  rcases family_descends (prefixWord ++ tailWord_963639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963813 : List Nat := [1, 3, 1, 4, 3, 2, 1, 1, 2, 2, 3]
def baseStart_963813 : Nat := 118140960795 + 963813 * 2 ^ 59
def prefixEnd_963813 : Nat := 4983230072969 + 3 ^ 40 * 963813 * 2
def baseEnd_963813 : Nat := 494899330051942810905011

theorem tailTrace_963813 : CollatzResearch.WordTrace tailWord_963813 prefixEnd_963813 494899330051942810905011 := by
  unfold tailWord_963813
  simp only [CollatzResearch.WordTrace]
  refine ⟨35153148057277582000544093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23435432038185054667029395 35153148057277582000544093)
  ·
    refine ⟨13182430521479093250204035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35153148057277582000544093 13182430521479093250204035)
    ·
      refine ⟨19773645782218639875306053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13182430521479093250204035 19773645782218639875306053)
      ·
        refine ⟨3707558584165994976619885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19773645782218639875306053 3707558584165994976619885)
        ·
          refine ⟨1390334469062248116232457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3707558584165994976619885 1390334469062248116232457)
          ·
            refine ⟨1042750851796686087174343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1390334469062248116232457 1042750851796686087174343)
            ·
              refine ⟨1564126277695029130761515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1042750851796686087174343 1564126277695029130761515)
              ·
                refine ⟨2346189416542543696142273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1564126277695029130761515 2346189416542543696142273)
                ·
                  refine ⟨1759642062406907772106705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2346189416542543696142273 1759642062406907772106705)
                  ·
                    refine ⟨1319731546805180829080029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1759642062406907772106705 1319731546805180829080029)
                    ·
                      refine ⟨494899330051942810905011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1319731546805180829080029 494899330051942810905011)
                      ·
                        rfl

theorem cell23_963813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_963813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_963813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_963813 prefixEnd_963813 := by exact prefixLift 963813
  have htrace : WordTrace (prefixWord ++ tailWord_963813) baseStart_963813 baseEnd_963813 := by
    simpa [prefixWord, tailWord_963813, baseEnd_963813] using wordTrace_append hprefix tailTrace_963813
  have hstable : (prefixWord ++ tailWord_963813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963813).length < 2 ^ (prefixWord ++ tailWord_963813).sum := by decide
  have hdescent : baseEnd_963813 < baseStart_963813 := by decide
  rcases family_descends (prefixWord ++ tailWord_963813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963843 : List Nat := [1, 1, 1, 3, 2, 4, 2, 4, 1, 1, 3]
def baseStart_963843 : Nat := 118140960795 + 963843 * 2 ^ 59
def prefixEnd_963843 : Nat := 4983230072969 + 3 ^ 40 * 963843 * 2
def baseEnd_963843 : Nat := 494914734471577693529873

theorem tailTrace_963843 : CollatzResearch.WordTrace tailWord_963843 prefixEnd_963843 494914734471577693529873 := by
  unfold tailWord_963843
  simp only [CollatzResearch.WordTrace]
  refine ⟨35154242247168897124136183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23436161498112598082757455 35154242247168897124136183)
  ·
    refine ⟨52731363370753345686204275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35154242247168897124136183 52731363370753345686204275)
    ·
      refine ⟨79097045056130018529306413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52731363370753345686204275 79097045056130018529306413)
      ·
        refine ⟨29661391896048756948489905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79097045056130018529306413 29661391896048756948489905)
        ·
          refine ⟨22246043922036567711367429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29661391896048756948489905 22246043922036567711367429)
          ·
            refine ⟨4171133235381856445881393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22246043922036567711367429 4171133235381856445881393)
            ·
              refine ⟨3128349926536392334411045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4171133235381856445881393 3128349926536392334411045)
              ·
                refine ⟨586565611225573562702071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3128349926536392334411045 586565611225573562702071)
                ·
                  refine ⟨879848416838360344053107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 586565611225573562702071 879848416838360344053107)
                  ·
                    refine ⟨1319772625257540516079661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 879848416838360344053107 1319772625257540516079661)
                    ·
                      refine ⟨494914734471577693529873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1319772625257540516079661 494914734471577693529873)
                      ·
                        rfl

theorem cell23_963843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 4, 1, 1, 3].length) (baseStart_963843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_963843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_963843 prefixEnd_963843 := by exact prefixLift 963843
  have htrace : WordTrace (prefixWord ++ tailWord_963843) baseStart_963843 baseEnd_963843 := by
    simpa [prefixWord, tailWord_963843, baseEnd_963843] using wordTrace_append hprefix tailTrace_963843
  have hstable : (prefixWord ++ tailWord_963843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963843).length < 2 ^ (prefixWord ++ tailWord_963843).sum := by decide
  have hdescent : baseEnd_963843 < baseStart_963843 := by decide
  rcases family_descends (prefixWord ++ tailWord_963843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963866 : List Nat := [3, 1, 1, 3, 3, 1, 1, 4, 1, 1, 4]
def baseStart_963866 : Nat := 118140960795 + 963866 * 2 ^ 59
def prefixEnd_963866 : Nat := 4983230072969 + 3 ^ 40 * 963866 * 2
def baseEnd_963866 : Nat := 494926544526631103542267

theorem tailTrace_963866 : CollatzResearch.WordTrace tailWord_963866 prefixEnd_963866 494926544526631103542267 := by
  unfold tailWord_963866
  simp only [CollatzResearch.WordTrace]
  refine ⟨8788770281521393013055863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23436720750723714701482301 8788770281521393013055863)
  ·
    refine ⟨13183155422282089519583795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8788770281521393013055863 13183155422282089519583795)
    ·
      refine ⟨19774733133423134279375693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13183155422282089519583795 19774733133423134279375693)
      ·
        refine ⟨7415524925033675354765885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19774733133423134279375693 7415524925033675354765885)
        ·
          refine ⟨2780821846887628258037207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7415524925033675354765885 2780821846887628258037207)
          ·
            refine ⟨4171232770331442387055811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2780821846887628258037207 4171232770331442387055811)
            ·
              refine ⟨6256849155497163580583717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4171232770331442387055811 6256849155497163580583717)
              ·
                refine ⟨1173159216655718171359447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6256849155497163580583717 1173159216655718171359447)
                ·
                  refine ⟨1759738824983577257039171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1173159216655718171359447 1759738824983577257039171)
                  ·
                    refine ⟨2639608237475365885558757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1759738824983577257039171 2639608237475365885558757)
                    ·
                      refine ⟨494926544526631103542267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2639608237475365885558757 494926544526631103542267)
                      ·
                        rfl

theorem cell23_963866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 4, 1, 1, 4].length) (baseStart_963866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_963866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_963866 prefixEnd_963866 := by exact prefixLift 963866
  have htrace : WordTrace (prefixWord ++ tailWord_963866) baseStart_963866 baseEnd_963866 := by
    simpa [prefixWord, tailWord_963866, baseEnd_963866] using wordTrace_append hprefix tailTrace_963866
  have hstable : (prefixWord ++ tailWord_963866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963866).length < 2 ^ (prefixWord ++ tailWord_963866).sum := by decide
  have hdescent : baseEnd_963866 < baseStart_963866 := by decide
  rcases family_descends (prefixWord ++ tailWord_963866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963889 : List Nat := [1, 2, 2, 3, 3, 3, 9]
def baseStart_963889 : Nat := 118140960795 + 963889 * 2 ^ 59
def prefixEnd_963889 : Nat := 4983230072969 + 3 ^ 40 * 963889 * 2
def baseEnd_963889 : Nat := 6110350056564006340181

theorem tailTrace_963889 : CollatzResearch.WordTrace tailWord_963889 prefixEnd_963889 6110350056564006340181 := by
  unfold tailWord_963889
  simp only [CollatzResearch.WordTrace]
  refine ⟨35155920005002246980310721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23437280003334831320207147 35155920005002246980310721)
  ·
    refine ⟨26366940003751685235233041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35155920005002246980310721 26366940003751685235233041)
    ·
      refine ⟨19775205002813763926424781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26366940003751685235233041 19775205002813763926424781)
      ·
        refine ⟨7415701876055161472409293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19775205002813763926424781 7415701876055161472409293)
        ·
          refine ⟨2780888203520685552153485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7415701876055161472409293 2780888203520685552153485)
          ·
            refine ⟨1042833076320257082057557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2780888203520685552153485 1042833076320257082057557)
            ·
              refine ⟨6110350056564006340181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1042833076320257082057557 6110350056564006340181)
              ·
                rfl

theorem cell23_963889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 9].length) (baseStart_963889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_963889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_963889 prefixEnd_963889 := by exact prefixLift 963889
  have htrace : WordTrace (prefixWord ++ tailWord_963889) baseStart_963889 baseEnd_963889 := by
    simpa [prefixWord, tailWord_963889, baseEnd_963889] using wordTrace_append hprefix tailTrace_963889
  have hstable : (prefixWord ++ tailWord_963889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963889).length < 2 ^ (prefixWord ++ tailWord_963889).sum := by decide
  have hdescent : baseEnd_963889 < baseStart_963889 := by decide
  rcases family_descends (prefixWord ++ tailWord_963889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963894 : List Nat := [5, 1, 2, 3, 2, 1, 1, 1, 3, 1, 3]
def baseStart_963894 : Nat := 118140960795 + 963894 * 2 ^ 59
def prefixEnd_963894 : Nat := 4983230072969 + 3 ^ 40 * 963894 * 2
def baseEnd_963894 : Nat := 494940921984956993992139

theorem tailTrace_963894 : CollatzResearch.WordTrace tailWord_963894 prefixEnd_963894 494940921984956993992139 := by
  unfold tailWord_963894
  simp only [CollatzResearch.WordTrace]
  refine ⟨2197256398124008302140171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23437401579989421889495157 2197256398124008302140171)
  ·
    refine ⟨3295884597186012453210257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2197256398124008302140171 3295884597186012453210257)
    ·
      refine ⟨2471913447889509339907693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3295884597186012453210257 2471913447889509339907693)
      ·
        refine ⟨926967542958566002465385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2471913447889509339907693 926967542958566002465385)
        ·
          refine ⟨695225657218924501849039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 926967542958566002465385 695225657218924501849039)
          ·
            refine ⟨1042838485828386752773559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 695225657218924501849039 1042838485828386752773559)
            ·
              refine ⟨1564257728742580129160339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1042838485828386752773559 1564257728742580129160339)
              ·
                refine ⟨2346386593113870193740509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1564257728742580129160339 2346386593113870193740509)
                ·
                  refine ⟨879894972417701322652691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2346386593113870193740509 879894972417701322652691)
                  ·
                    refine ⟨1319842458626551983979037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 879894972417701322652691 1319842458626551983979037)
                    ·
                      refine ⟨494940921984956993992139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1319842458626551983979037 494940921984956993992139)
                      ·
                        rfl

theorem cell23_963894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_963894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_963894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_963894 prefixEnd_963894 := by exact prefixLift 963894
  have htrace : WordTrace (prefixWord ++ tailWord_963894) baseStart_963894 baseEnd_963894 := by
    simpa [prefixWord, tailWord_963894, baseEnd_963894] using wordTrace_append hprefix tailTrace_963894
  have hstable : (prefixWord ++ tailWord_963894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963894).length < 2 ^ (prefixWord ++ tailWord_963894).sum := by decide
  have hdescent : baseEnd_963894 < baseStart_963894 := by decide
  rcases family_descends (prefixWord ++ tailWord_963894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963900 : List Nat := [2, 2, 2, 2, 1, 5, 1, 1, 3, 2, 2]
def baseStart_963900 : Nat := 118140960795 + 963900 * 2 ^ 59
def prefixEnd_963900 : Nat := 4983230072969 + 3 ^ 40 * 963900 * 2
def baseEnd_963900 : Nat := 494944002868883970517111

theorem tailTrace_963900 : CollatzResearch.WordTrace tailWord_963900 prefixEnd_963900 494944002868883970517111 := by
  unfold tailWord_963900
  simp only [CollatzResearch.WordTrace]
  refine ⟨17578160603981197929480577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23437547471974930572640769 17578160603981197929480577)
  ·
    refine ⟨13183620452985898447110433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17578160603981197929480577 13183620452985898447110433)
    ·
      refine ⟨9887715339739423835332825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13183620452985898447110433 9887715339739423835332825)
      ·
        refine ⟨7415786504804567876499619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9887715339739423835332825 7415786504804567876499619)
        ·
          refine ⟨11123679757206851814749429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7415786504804567876499619 11123679757206851814749429)
          ·
            refine ⟨1042844977238142357632759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11123679757206851814749429 1042844977238142357632759)
            ·
              refine ⟨1564267465857213536449139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1042844977238142357632759 1564267465857213536449139)
              ·
                refine ⟨2346401198785820304673709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1564267465857213536449139 2346401198785820304673709)
                ·
                  refine ⟨879900449544682614252641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2346401198785820304673709 879900449544682614252641)
                  ·
                    refine ⟨659925337158511960689481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 879900449544682614252641 659925337158511960689481)
                    ·
                      refine ⟨494944002868883970517111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 659925337158511960689481 494944002868883970517111)
                      ·
                        rfl

theorem cell23_963900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 1, 3, 2, 2].length) (baseStart_963900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_963900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_963900 prefixEnd_963900 := by exact prefixLift 963900
  have htrace : WordTrace (prefixWord ++ tailWord_963900) baseStart_963900 baseEnd_963900 := by
    simpa [prefixWord, tailWord_963900, baseEnd_963900] using wordTrace_append hprefix tailTrace_963900
  have hstable : (prefixWord ++ tailWord_963900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963900).length < 2 ^ (prefixWord ++ tailWord_963900).sum := by decide
  have hdescent : baseEnd_963900 < baseStart_963900 := by decide
  rcases family_descends (prefixWord ++ tailWord_963900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963917 : List Nat := [1, 6, 1, 3, 1, 2, 1, 2, 1, 1, 4]
def baseStart_963917 : Nat := 118140960795 + 963917 * 2 ^ 59
def prefixEnd_963917 : Nat := 4983230072969 + 3 ^ 40 * 963917 * 2
def baseEnd_963917 : Nat := 494952732040010404004533

theorem tailTrace_963917 : CollatzResearch.WordTrace tailWord_963917 prefixEnd_963917 494952732040010404004533 := by
  unfold tailWord_963917
  simp only [CollatzResearch.WordTrace]
  refine ⟨35156941248900807762330005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23437960832600538508220003 35156941248900807762330005)
  ·
    refine ⟨1647981621042225363859219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 35156941248900807762330005 1647981621042225363859219)
    ·
      refine ⟨2471972431563338045788829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1647981621042225363859219 2471972431563338045788829)
      ·
        refine ⟨926989661836251767170811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2471972431563338045788829 926989661836251767170811)
        ·
          refine ⟨1390484492754377650756217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 926989661836251767170811 1390484492754377650756217)
          ·
            refine ⟨1042863369565783238067163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1390484492754377650756217 1042863369565783238067163)
            ·
              refine ⟨1564295054348674857100745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1042863369565783238067163 1564295054348674857100745)
              ·
                refine ⟨1173221290761506142825559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1564295054348674857100745 1173221290761506142825559)
                ·
                  refine ⟨1759831936142259214238339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1173221290761506142825559 1759831936142259214238339)
                  ·
                    refine ⟨2639747904213388821357509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1759831936142259214238339 2639747904213388821357509)
                    ·
                      refine ⟨494952732040010404004533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2639747904213388821357509 494952732040010404004533)
                      ·
                        rfl

theorem cell23_963917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_963917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_963917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_963917 prefixEnd_963917 := by exact prefixLift 963917
  have htrace : WordTrace (prefixWord ++ tailWord_963917) baseStart_963917 baseEnd_963917 := by
    simpa [prefixWord, tailWord_963917, baseEnd_963917] using wordTrace_append hprefix tailTrace_963917
  have hstable : (prefixWord ++ tailWord_963917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963917).length < 2 ^ (prefixWord ++ tailWord_963917).sum := by decide
  have hdescent : baseEnd_963917 < baseStart_963917 := by decide
  rcases family_descends (prefixWord ++ tailWord_963917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963959 : List Nat := [1, 1, 3, 1, 1, 2, 3, 1, 1, 6, 3]
def baseStart_963959 : Nat := 118140960795 + 963959 * 2 ^ 59
def prefixEnd_963959 : Nat := 4983230072969 + 3 ^ 40 * 963959 * 2
def baseEnd_963959 : Nat := 494974298227499239679339

theorem tailTrace_963959 : CollatzResearch.WordTrace tailWord_963959 prefixEnd_963959 494974298227499239679339 := by
  unfold tailWord_963959
  simp only [CollatzResearch.WordTrace]
  refine ⟨35158473114748648935358931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23438982076499099290239287 35158473114748648935358931)
  ·
    refine ⟨52737709672122973403038397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35158473114748648935358931 52737709672122973403038397)
    ·
      refine ⟨19776641127046115026139399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52737709672122973403038397 19776641127046115026139399)
      ·
        refine ⟨29664961690569172539209099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19776641127046115026139399 29664961690569172539209099)
        ·
          refine ⟨44497442535853758808813649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29664961690569172539209099 44497442535853758808813649)
          ·
            refine ⟨33373081901890319106610237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44497442535853758808813649 33373081901890319106610237)
            ·
              refine ⟨12514905713208869664978839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33373081901890319106610237 12514905713208869664978839)
              ·
                refine ⟨18772358569813304497468259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12514905713208869664978839 18772358569813304497468259)
                ·
                  refine ⟨28158537854719956746202389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18772358569813304497468259 28158537854719956746202389)
                  ·
                    refine ⟨1319931461939997972478237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28158537854719956746202389 1319931461939997972478237)
                    ·
                      refine ⟨494974298227499239679339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1319931461939997972478237 494974298227499239679339)
                      ·
                        rfl

theorem cell23_963959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 6, 3].length) (baseStart_963959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_963959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_963959 prefixEnd_963959 := by exact prefixLift 963959
  have htrace : WordTrace (prefixWord ++ tailWord_963959) baseStart_963959 baseEnd_963959 := by
    simpa [prefixWord, tailWord_963959, baseEnd_963959] using wordTrace_append hprefix tailTrace_963959
  have hstable : (prefixWord ++ tailWord_963959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963959).length < 2 ^ (prefixWord ++ tailWord_963959).sum := by decide
  have hdescent : baseEnd_963959 < baseStart_963959 := by decide
  rcases family_descends (prefixWord ++ tailWord_963959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963979 : List Nat := [1, 1, 1, 1, 4, 3, 3, 2, 7]
def baseStart_963979 : Nat := 118140960795 + 963979 * 2 ^ 59
def prefixEnd_963979 : Nat := 4983230072969 + 3 ^ 40 * 963979 * 2
def baseEnd_963979 : Nat := 54998285315621017936583

theorem tailTrace_963979 : CollatzResearch.WordTrace tailWord_963979 prefixEnd_963979 54998285315621017936583 := by
  unfold tailWord_963979
  simp only [CollatzResearch.WordTrace]
  refine ⟨35159202574676192351086991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23439468383117461567391327 35159202574676192351086991)
  ·
    refine ⟨52738803862014288526630487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35159202574676192351086991 52738803862014288526630487)
    ·
      refine ⟨79108205793021432789945731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52738803862014288526630487 79108205793021432789945731)
      ·
        refine ⟨118662308689532149184918597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79108205793021432789945731 118662308689532149184918597)
        ·
          refine ⟨22249182879287277972172237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118662308689532149184918597 22249182879287277972172237)
          ·
            refine ⟨8343443579732729239564589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22249182879287277972172237 8343443579732729239564589)
            ·
              refine ⟨3128791342399773464836721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8343443579732729239564589 3128791342399773464836721)
              ·
                refine ⟨2346593506799830098627541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3128791342399773464836721 2346593506799830098627541)
                ·
                  refine ⟨54998285315621017936583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2346593506799830098627541 54998285315621017936583)
                  ·
                    rfl

theorem cell23_963979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 2, 7].length) (baseStart_963979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_963979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_963979 prefixEnd_963979 := by exact prefixLift 963979
  have htrace : WordTrace (prefixWord ++ tailWord_963979) baseStart_963979 baseEnd_963979 := by
    simpa [prefixWord, tailWord_963979, baseEnd_963979] using wordTrace_append hprefix tailTrace_963979
  have hstable : (prefixWord ++ tailWord_963979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963979).length < 2 ^ (prefixWord ++ tailWord_963979).sum := by decide
  have hdescent : baseEnd_963979 < baseStart_963979 := by decide
  rcases family_descends (prefixWord ++ tailWord_963979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964013 : List Nat := [1, 5, 2, 2, 1, 2, 2, 1, 7]
def baseStart_964013 : Nat := 118140960795 + 964013 * 2 ^ 59
def prefixEnd_964013 : Nat := 4983230072969 + 3 ^ 40 * 964013 * 2
def baseEnd_964013 : Nat := 55000225131426892044899

theorem tailTrace_964013 : CollatzResearch.WordTrace tailWord_964013 prefixEnd_964013 55000225131426892044899 := by
  unfold tailWord_964013
  simp only [CollatzResearch.WordTrace]
  refine ⟨35160442656553016157824693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23440295104368677438549795 35160442656553016157824693)
  ·
    refine ⟨3296291499051845264796065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35160442656553016157824693 3296291499051845264796065)
    ·
      refine ⟨2472218624288883948597049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3296291499051845264796065 2472218624288883948597049)
      ·
        refine ⟨1854163968216662961447787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2472218624288883948597049 1854163968216662961447787)
        ·
          refine ⟨2781245952324994442171681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1854163968216662961447787 2781245952324994442171681)
          ·
            refine ⟨2085934464243745831628761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2781245952324994442171681 2085934464243745831628761)
            ·
              refine ⟨1564450848182809373721571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2085934464243745831628761 1564450848182809373721571)
              ·
                refine ⟨2346676272274214060582357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1564450848182809373721571 2346676272274214060582357)
                ·
                  refine ⟨55000225131426892044899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2346676272274214060582357 55000225131426892044899)
                  ·
                    rfl

theorem cell23_964013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 1, 7].length) (baseStart_964013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_964013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_964013 prefixEnd_964013 := by exact prefixLift 964013
  have htrace : WordTrace (prefixWord ++ tailWord_964013) baseStart_964013 baseEnd_964013 := by
    simpa [prefixWord, tailWord_964013, baseEnd_964013] using wordTrace_append hprefix tailTrace_964013
  have hstable : (prefixWord ++ tailWord_964013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964013).length < 2 ^ (prefixWord ++ tailWord_964013).sum := by decide
  have hdescent : baseEnd_964013 < baseStart_964013 := by decide
  rcases family_descends (prefixWord ++ tailWord_964013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964016 : List Nat := [2, 1, 1, 1, 2, 1, 1, 5, 2, 5, 2]
def baseStart_964016 : Nat := 118140960795 + 964016 * 2 ^ 59
def prefixEnd_964016 : Nat := 4983230072969 + 3 ^ 40 * 964016 * 2
def baseEnd_964016 : Nat := 495003566624805516666577

theorem tailTrace_964016 : CollatzResearch.WordTrace tailWord_964016 prefixEnd_964016 495003566624805516666577 := by
  unfold tailWord_964016
  simp only [CollatzResearch.WordTrace]
  refine ⟨17580276037771073835091951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23440368050361431780122601 17580276037771073835091951)
  ·
    refine ⟨26370414056656610752637927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17580276037771073835091951 26370414056656610752637927)
    ·
      refine ⟨39555621084984916128956891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26370414056656610752637927 39555621084984916128956891)
      ·
        refine ⟨59333431627477374193435337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39555621084984916128956891 59333431627477374193435337)
        ·
          refine ⟨44500073720608030645076503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59333431627477374193435337 44500073720608030645076503)
          ·
            refine ⟨66750110580912045967614755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44500073720608030645076503 66750110580912045967614755)
            ·
              refine ⟨100125165871368068951422133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66750110580912045967614755 100125165871368068951422133)
              ·
                refine ⟨9386734300440756464195825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 100125165871368068951422133 9386734300440756464195825)
                ·
                  refine ⟨7040050725330567348146869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9386734300440756464195825 7040050725330567348146869)
                  ·
                    refine ⟨660004755499740688888769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7040050725330567348146869 660004755499740688888769)
                    ·
                      refine ⟨495003566624805516666577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 660004755499740688888769 495003566624805516666577)
                      ·
                        rfl

theorem cell23_964016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 2, 5, 2].length) (baseStart_964016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_964016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_964016 prefixEnd_964016 := by exact prefixLift 964016
  have htrace : WordTrace (prefixWord ++ tailWord_964016) baseStart_964016 baseEnd_964016 := by
    simpa [prefixWord, tailWord_964016, baseEnd_964016] using wordTrace_append hprefix tailTrace_964016
  have hstable : (prefixWord ++ tailWord_964016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964016).length < 2 ^ (prefixWord ++ tailWord_964016).sum := by decide
  have hdescent : baseEnd_964016 < baseStart_964016 := by decide
  rcases family_descends (prefixWord ++ tailWord_964016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964019 : List Nat := [1, 1, 1, 2, 3, 1, 1, 5, 1, 2, 5]
def baseStart_964019 : Nat := 118140960795 + 964019 * 2 ^ 59
def prefixEnd_964019 : Nat := 4983230072969 + 3 ^ 40 * 964019 * 2
def baseEnd_964019 : Nat := 495005107066769004929063

theorem tailTrace_964019 : CollatzResearch.WordTrace tailWord_964019 prefixEnd_964019 495005107066769004929063 := by
  unfold tailWord_964019
  simp only [CollatzResearch.WordTrace]
  refine ⟨35160661494531279182543111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23440440996354186121695407 35160661494531279182543111)
  ·
    refine ⟨52740992241796918773814667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35160661494531279182543111 52740992241796918773814667)
    ·
      refine ⟨79111488362695378160722001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52740992241796918773814667 79111488362695378160722001)
      ·
        refine ⟨59333616272021533620541501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79111488362695378160722001 59333616272021533620541501)
        ·
          refine ⟨22250106102008075107703063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59333616272021533620541501 22250106102008075107703063)
          ·
            refine ⟨33375159153012112661554595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22250106102008075107703063 33375159153012112661554595)
            ·
              refine ⟨50062738729518168992331893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33375159153012112661554595 50062738729518168992331893)
              ·
                refine ⟨4693381755892328343031115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50062738729518168992331893 4693381755892328343031115)
                ·
                  refine ⟨7040072633838492514546673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4693381755892328343031115 7040072633838492514546673)
                  ·
                    refine ⟨5280054475378869385910005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7040072633838492514546673 5280054475378869385910005)
                    ·
                      refine ⟨495005107066769004929063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5280054475378869385910005 495005107066769004929063)
                      ·
                        rfl

theorem cell23_964019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 2, 5].length) (baseStart_964019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_964019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_964019 prefixEnd_964019 := by exact prefixLift 964019
  have htrace : WordTrace (prefixWord ++ tailWord_964019) baseStart_964019 baseEnd_964019 := by
    simpa [prefixWord, tailWord_964019, baseEnd_964019] using wordTrace_append hprefix tailTrace_964019
  have hstable : (prefixWord ++ tailWord_964019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964019).length < 2 ^ (prefixWord ++ tailWord_964019).sum := by decide
  have hdescent : baseEnd_964019 < baseStart_964019 := by decide
  rcases family_descends (prefixWord ++ tailWord_964019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964039 : List Nat := [1, 1, 4, 1, 1, 3, 1, 1, 2, 8]
def baseStart_964039 : Nat := 118140960795 + 964039 * 2 ^ 59
def prefixEnd_964039 : Nat := 4983230072969 + 3 ^ 40 * 964039 * 2
def baseEnd_964039 : Nat := 165005125559952975559657

theorem tailTrace_964039 : CollatzResearch.WordTrace tailWord_964039 prefixEnd_964039 165005125559952975559657 := by
  unfold tailWord_964039
  simp only [CollatzResearch.WordTrace]
  refine ⟨35161390954458822598271171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23440927302972548398847447 35161390954458822598271171)
  ·
    refine ⟨52742086431688233897406757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35161390954458822598271171 52742086431688233897406757)
    ·
      refine ⟨9889141205941543855763767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52742086431688233897406757 9889141205941543855763767)
      ·
        refine ⟨14833711808912315783645651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9889141205941543855763767 14833711808912315783645651)
        ·
          refine ⟨22250567713368473675468477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14833711808912315783645651 22250567713368473675468477)
          ·
            refine ⟨8343962892513177628300679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22250567713368473675468477 8343962892513177628300679)
            ·
              refine ⟨12515944338769766442451019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8343962892513177628300679 12515944338769766442451019)
              ·
                refine ⟨18773916508154649663676529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12515944338769766442451019 18773916508154649663676529)
                ·
                  refine ⟨14080437381115987247757397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18773916508154649663676529 14080437381115987247757397)
                  ·
                    refine ⟨165005125559952975559657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 14080437381115987247757397 165005125559952975559657)
                    ·
                      rfl

theorem cell23_964039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 8].length) (baseStart_964039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_964039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_964039 prefixEnd_964039 := by exact prefixLift 964039
  have htrace : WordTrace (prefixWord ++ tailWord_964039) baseStart_964039 baseEnd_964039 := by
    simpa [prefixWord, tailWord_964039, baseEnd_964039] using wordTrace_append hprefix tailTrace_964039
  have hstable : (prefixWord ++ tailWord_964039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964039).length < 2 ^ (prefixWord ++ tailWord_964039).sum := by decide
  have hdescent : baseEnd_964039 < baseStart_964039 := by decide
  rcases family_descends (prefixWord ++ tailWord_964039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964046 : List Nat := [4, 1, 1, 1, 2, 1, 4, 1, 1, 3, 4]
def baseStart_964046 : Nat := 118140960795 + 964046 * 2 ^ 59
def prefixEnd_964046 : Nat := 4983230072969 + 3 ^ 40 * 964046 * 2
def baseEnd_964046 : Nat := 495018971044440399291439

theorem tailTrace_964046 : CollatzResearch.WordTrace tailWord_964046 prefixEnd_964046 495018971044440399291439 := by
  unfold tailWord_964046
  simp only [CollatzResearch.WordTrace]
  refine ⟨4395205783179182849221999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23441097510288975195850661 4395205783179182849221999)
  ·
    refine ⟨6592808674768774273832999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4395205783179182849221999 6592808674768774273832999)
    ·
      refine ⟨9889213012153161410749499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6592808674768774273832999 9889213012153161410749499)
      ·
        refine ⟨14833819518229742116124249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9889213012153161410749499 14833819518229742116124249)
        ·
          refine ⟨11125364638672306587093187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14833819518229742116124249 11125364638672306587093187)
          ·
            refine ⟨16688046958008459880639781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11125364638672306587093187 16688046958008459880639781)
            ·
              refine ⟨3129008804626586227619959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16688046958008459880639781 3129008804626586227619959)
              ·
                refine ⟨4693513206939879341429939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3129008804626586227619959 4693513206939879341429939)
                ·
                  refine ⟨7040269810409819012144909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4693513206939879341429939 7040269810409819012144909)
                  ·
                    refine ⟨2640101178903682129554341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7040269810409819012144909 2640101178903682129554341)
                    ·
                      refine ⟨495018971044440399291439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2640101178903682129554341 495018971044440399291439)
                      ·
                        rfl

theorem cell23_964046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 1, 3, 4].length) (baseStart_964046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_964046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_964046 prefixEnd_964046 := by exact prefixLift 964046
  have htrace : WordTrace (prefixWord ++ tailWord_964046) baseStart_964046 baseEnd_964046 := by
    simpa [prefixWord, tailWord_964046, baseEnd_964046] using wordTrace_append hprefix tailTrace_964046
  have hstable : (prefixWord ++ tailWord_964046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964046).length < 2 ^ (prefixWord ++ tailWord_964046).sum := by decide
  have hdescent : baseEnd_964046 < baseStart_964046 := by decide
  rcases family_descends (prefixWord ++ tailWord_964046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964049 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 4, 3, 5]
def baseStart_964049 : Nat := 118140960795 + 964049 * 2 ^ 59
def prefixEnd_964049 : Nat := 4983230072969 + 3 ^ 40 * 964049 * 2
def baseEnd_964049 : Nat := 495020511486403887553925

theorem tailTrace_964049 : CollatzResearch.WordTrace tailWord_964049 prefixEnd_964049 495020511486403887553925 := by
  unfold tailWord_964049
  simp only [CollatzResearch.WordTrace]
  refine ⟨35161755684422594306135201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23441170456281729537423467 35161755684422594306135201)
  ·
    refine ⟨26371316763316945729601401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35161755684422594306135201 26371316763316945729601401)
    ·
      refine ⟨19778487572487709297201051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26371316763316945729601401 19778487572487709297201051)
      ·
        refine ⟨29667731358731563945801577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19778487572487709297201051 29667731358731563945801577)
        ·
          refine ⟨22250798519048672959351183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29667731358731563945801577 22250798519048672959351183)
          ·
            refine ⟨33376197778573009439026775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22250798519048672959351183 33376197778573009439026775)
            ·
              refine ⟨50064296667859514158540163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33376197778573009439026775 50064296667859514158540163)
              ·
                refine ⟨75096445001789271237810245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50064296667859514158540163 75096445001789271237810245)
                ·
                  refine ⟨14080583437835488357089421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75096445001789271237810245 14080583437835488357089421)
                  ·
                    refine ⟨5280218789188308133908533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14080583437835488357089421 5280218789188308133908533)
                    ·
                      refine ⟨495020511486403887553925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5280218789188308133908533 495020511486403887553925)
                      ·
                        rfl

theorem cell23_964049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 3, 5].length) (baseStart_964049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_964049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_964049 prefixEnd_964049 := by exact prefixLift 964049
  have htrace : WordTrace (prefixWord ++ tailWord_964049) baseStart_964049 baseEnd_964049 := by
    simpa [prefixWord, tailWord_964049, baseEnd_964049] using wordTrace_append hprefix tailTrace_964049
  have hstable : (prefixWord ++ tailWord_964049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964049).length < 2 ^ (prefixWord ++ tailWord_964049).sum := by decide
  have hdescent : baseEnd_964049 < baseStart_964049 := by decide
  rcases family_descends (prefixWord ++ tailWord_964049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964056 : List Nat := [2, 1, 2, 2, 2, 1, 2, 2, 5, 4]
def baseStart_964056 : Nat := 118140960795 + 964056 * 2 ^ 59
def prefixEnd_964056 : Nat := 4983230072969 + 3 ^ 40 * 964056 * 2
def baseEnd_964056 : Nat := 165008035283661786722131

theorem tailTrace_964056 : CollatzResearch.WordTrace tailWord_964056 prefixEnd_964056 165008035283661786722131 := by
  unfold tailWord_964056
  simp only [CollatzResearch.WordTrace]
  refine ⟨17581005497698617250820011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23441340663598156334426681 17581005497698617250820011)
  ·
    refine ⟨26371508246547925876230017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17581005497698617250820011 26371508246547925876230017)
    ·
      refine ⟨19778631184910944407172513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26371508246547925876230017 19778631184910944407172513)
      ·
        refine ⟨14833973388683208305379385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19778631184910944407172513 14833973388683208305379385)
        ·
          refine ⟨11125480041512406229034539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14833973388683208305379385 11125480041512406229034539)
          ·
            refine ⟨16688220062268609343551809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11125480041512406229034539 16688220062268609343551809)
            ·
              refine ⟨12516165046701457007663857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16688220062268609343551809 12516165046701457007663857)
              ·
                refine ⟨9387123785026092755747893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12516165046701457007663857 9387123785026092755747893)
                ·
                  refine ⟨880042854846196195851365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9387123785026092755747893 880042854846196195851365)
                  ·
                    refine ⟨165008035283661786722131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 880042854846196195851365 165008035283661786722131)
                    ·
                      rfl

theorem cell23_964056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 5, 4].length) (baseStart_964056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_964056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_964056 prefixEnd_964056 := by exact prefixLift 964056
  have htrace : WordTrace (prefixWord ++ tailWord_964056) baseStart_964056 baseEnd_964056 := by
    simpa [prefixWord, tailWord_964056, baseEnd_964056] using wordTrace_append hprefix tailTrace_964056
  have hstable : (prefixWord ++ tailWord_964056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964056).length < 2 ^ (prefixWord ++ tailWord_964056).sum := by decide
  have hdescent : baseEnd_964056 < baseStart_964056 := by decide
  rcases family_descends (prefixWord ++ tailWord_964056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964153 : List Nat := [1, 2, 1, 5, 1, 2, 2, 1, 3, 1, 4]
def baseStart_964153 : Nat := 118140960795 + 964153 * 2 ^ 59
def prefixEnd_964153 : Nat := 4983230072969 + 3 ^ 40 * 964153 * 2
def baseEnd_964153 : Nat := 495073913474471480653447

theorem tailTrace_964153 : CollatzResearch.WordTrace tailWord_964153 prefixEnd_964153 495073913474471480653447 := by
  unfold tailWord_964153
  simp only [CollatzResearch.WordTrace]
  refine ⟨35165548876045820067921113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23443699250697213378614075 35165548876045820067921113)
  ·
    refine ⟨26374161657034365050940835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35165548876045820067921113 26374161657034365050940835)
    ·
      refine ⟨39561242485551547576411253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26374161657034365050940835 39561242485551547576411253)
      ·
        refine ⟨3708866483020457585288555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39561242485551547576411253 3708866483020457585288555)
        ·
          refine ⟨5563299724530686377932833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3708866483020457585288555 5563299724530686377932833)
          ·
            refine ⟨4172474793398014783449625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5563299724530686377932833 4172474793398014783449625)
            ·
              refine ⟨3129356095048511087587219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4172474793398014783449625 3129356095048511087587219)
              ·
                refine ⟨4694034142572766631380829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3129356095048511087587219 4694034142572766631380829)
                ·
                  refine ⟨1760262803464787486767811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4694034142572766631380829 1760262803464787486767811)
                  ·
                    refine ⟨2640394205197181230151717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1760262803464787486767811 2640394205197181230151717)
                    ·
                      refine ⟨495073913474471480653447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2640394205197181230151717 495073913474471480653447)
                      ·
                        rfl

theorem cell23_964153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_964153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_964153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_964153 prefixEnd_964153 := by exact prefixLift 964153
  have htrace : WordTrace (prefixWord ++ tailWord_964153) baseStart_964153 baseEnd_964153 := by
    simpa [prefixWord, tailWord_964153, baseEnd_964153] using wordTrace_append hprefix tailTrace_964153
  have hstable : (prefixWord ++ tailWord_964153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964153).length < 2 ^ (prefixWord ++ tailWord_964153).sum := by decide
  have hdescent : baseEnd_964153 < baseStart_964153 := by decide
  rcases family_descends (prefixWord ++ tailWord_964153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964167 : List Nat := [1, 1, 4, 1, 5, 2, 2, 1, 1, 5]
def baseStart_964167 : Nat := 118140960795 + 964167 * 2 ^ 59
def prefixEnd_964167 : Nat := 4983230072969 + 3 ^ 40 * 964167 * 2
def baseEnd_964167 : Nat := 165027034067878141959461

theorem tailTrace_964167 : CollatzResearch.WordTrace tailWord_964167 prefixEnd_964167 165027034067878141959461 := by
  unfold tailWord_964167
  simp only [CollatzResearch.WordTrace]
  refine ⟨35166059497995100458930755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23444039665330066972620503 35166059497995100458930755)
  ·
    refine ⟨52749089246992650688396133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35166059497995100458930755 52749089246992650688396133)
    ·
      refine ⟨9890454233811122004074275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52749089246992650688396133 9890454233811122004074275)
      ·
        refine ⟨14835681350716683006111413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9890454233811122004074275 14835681350716683006111413)
        ·
          refine ⟨1390845126629689031822945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14835681350716683006111413 1390845126629689031822945)
          ·
            refine ⟨1043133844972266773867209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1390845126629689031822945 1043133844972266773867209)
            ·
              refine ⟨782350383729200080400407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1043133844972266773867209 782350383729200080400407)
              ·
                refine ⟨1173525575593800120600611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 782350383729200080400407 1173525575593800120600611)
                ·
                  refine ⟨1760288363390700180900917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1173525575593800120600611 1760288363390700180900917)
                  ·
                    refine ⟨165027034067878141959461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1760288363390700180900917 165027034067878141959461)
                    ·
                      rfl

theorem cell23_964167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 2, 1, 1, 5].length) (baseStart_964167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_964167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_964167 prefixEnd_964167 := by exact prefixLift 964167
  have htrace : WordTrace (prefixWord ++ tailWord_964167) baseStart_964167 baseEnd_964167 := by
    simpa [prefixWord, tailWord_964167, baseEnd_964167] using wordTrace_append hprefix tailTrace_964167
  have hstable : (prefixWord ++ tailWord_964167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964167).length < 2 ^ (prefixWord ++ tailWord_964167).sum := by decide
  have hdescent : baseEnd_964167 < baseStart_964167 := by decide
  rcases family_descends (prefixWord ++ tailWord_964167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964170 : List Nat := [3, 1, 2, 1, 1, 3, 1, 2, 5, 2, 2]
def baseStart_964170 : Nat := 118140960795 + 964170 * 2 ^ 59
def prefixEnd_964170 : Nat := 4983230072969 + 3 ^ 40 * 964170 * 2
def baseEnd_964170 : Nat := 495082642645597914140869

theorem tailTrace_964170 : CollatzResearch.WordTrace tailWord_964170 prefixEnd_964170 495082642645597914140869 := by
  unfold tailWord_964170
  simp only [CollatzResearch.WordTrace]
  refine ⟨8791542229246057992822491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23444112611322821314193309 8791542229246057992822491)
  ·
    refine ⟨13187313343869086989233737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8791542229246057992822491 13187313343869086989233737)
    ·
      refine ⟨9890485007901815241925303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13187313343869086989233737 9890485007901815241925303)
      ·
        refine ⟨14835727511852722862887955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9890485007901815241925303 14835727511852722862887955)
        ·
          refine ⟨22253591267779084294331933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14835727511852722862887955 22253591267779084294331933)
          ·
            refine ⟨8345096725417156610374475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22253591267779084294331933 8345096725417156610374475)
            ·
              refine ⟨12517645088125734915561713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8345096725417156610374475 12517645088125734915561713)
              ·
                refine ⟨9388233816094301186671285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12517645088125734915561713 9388233816094301186671285)
                ·
                  refine ⟨880146920258840736250433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9388233816094301186671285 880146920258840736250433)
                  ·
                    refine ⟨660110190194130552187825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 880146920258840736250433 660110190194130552187825)
                    ·
                      refine ⟨495082642645597914140869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 660110190194130552187825 495082642645597914140869)
                      ·
                        rfl

theorem cell23_964170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 5, 2, 2].length) (baseStart_964170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_964170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_964170 prefixEnd_964170 := by exact prefixLift 964170
  have htrace : WordTrace (prefixWord ++ tailWord_964170) baseStart_964170 baseEnd_964170 := by
    simpa [prefixWord, tailWord_964170, baseEnd_964170] using wordTrace_append hprefix tailTrace_964170
  have hstable : (prefixWord ++ tailWord_964170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964170).length < 2 ^ (prefixWord ++ tailWord_964170).sum := by decide
  have hdescent : baseEnd_964170 < baseStart_964170 := by decide
  rcases family_descends (prefixWord ++ tailWord_964170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964197 : List Nat := [1, 3, 1, 3, 3, 2, 3, 1, 2, 4]
def baseStart_964197 : Nat := 118140960795 + 964197 * 2 ^ 59
def prefixEnd_964197 : Nat := 4983230072969 + 3 ^ 40 * 964197 * 2
def baseEnd_964197 : Nat := 165032168874423102834415

theorem tailTrace_964197 : CollatzResearch.WordTrace tailWord_964197 prefixEnd_964197 165032168874423102834415 := by
  unfold tailWord_964197
  simp only [CollatzResearch.WordTrace]
  refine ⟨35167153687886415582522845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23444769125257610388348563 35167153687886415582522845)
  ·
    refine ⟨13187682632957405843446067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35167153687886415582522845 13187682632957405843446067)
    ·
      refine ⟨19781523949436108765169101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13187682632957405843446067 19781523949436108765169101)
      ·
        refine ⟨7418071481038540786938413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19781523949436108765169101 7418071481038540786938413)
        ·
          refine ⟨2781776805389452795101905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7418071481038540786938413 2781776805389452795101905)
          ·
            refine ⟨2086332604042089596326429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2781776805389452795101905 2086332604042089596326429)
            ·
              refine ⟨782374726515783598622411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2086332604042089596326429 782374726515783598622411)
              ·
                refine ⟨1173562089773675397933617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 782374726515783598622411 1173562089773675397933617)
                ·
                  refine ⟨880171567330256548450213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1173562089773675397933617 880171567330256548450213)
                  ·
                    refine ⟨165032168874423102834415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 880171567330256548450213 165032168874423102834415)
                    ·
                      rfl

theorem cell23_964197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 3, 1, 2, 4].length) (baseStart_964197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_964197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_964197 prefixEnd_964197 := by exact prefixLift 964197
  have htrace : WordTrace (prefixWord ++ tailWord_964197) baseStart_964197 baseEnd_964197 := by
    simpa [prefixWord, tailWord_964197, baseEnd_964197] using wordTrace_append hprefix tailTrace_964197
  have hstable : (prefixWord ++ tailWord_964197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964197).length < 2 ^ (prefixWord ++ tailWord_964197).sum := by decide
  have hdescent : baseEnd_964197 < baseStart_964197 := by decide
  rcases family_descends (prefixWord ++ tailWord_964197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964200 : List Nat := [2, 1, 4, 3, 1, 1, 3, 1, 1, 2, 4]
def baseStart_964200 : Nat := 118140960795 + 964200 * 2 ^ 59
def prefixEnd_964200 : Nat := 4983230072969 + 3 ^ 40 * 964200 * 2
def baseEnd_964200 : Nat := 495098047065232796765731

theorem tailTrace_964200 : CollatzResearch.WordTrace tailWord_964200 prefixEnd_964200 495098047065232796765731 := by
  unfold tailWord_964200
  simp only [CollatzResearch.WordTrace]
  refine ⟨17583631553437773547441027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23444842071250364729921369 17583631553437773547441027)
  ·
    refine ⟨26375447330156660321161541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17583631553437773547441027 26375447330156660321161541)
    ·
      refine ⟨4945396374404373810217789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26375447330156660321161541 4945396374404373810217789)
      ·
        refine ⟨1854523640401640178831671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4945396374404373810217789 1854523640401640178831671)
        ·
          refine ⟨2781785460602460268247507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1854523640401640178831671 2781785460602460268247507)
          ·
            refine ⟨4172678190903690402371261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2781785460602460268247507 4172678190903690402371261)
            ·
              refine ⟨1564754321588883900889223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4172678190903690402371261 1564754321588883900889223)
              ·
                refine ⟨2347131482383325851333835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1564754321588883900889223 2347131482383325851333835)
                ·
                  refine ⟨3520697223574988777000753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2347131482383325851333835 3520697223574988777000753)
                  ·
                    refine ⟨2640522917681241582750565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3520697223574988777000753 2640522917681241582750565)
                    ·
                      refine ⟨495098047065232796765731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2640522917681241582750565 495098047065232796765731)
                      ·
                        rfl

theorem cell23_964200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_964200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_964200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_964200 prefixEnd_964200 := by exact prefixLift 964200
  have htrace : WordTrace (prefixWord ++ tailWord_964200) baseStart_964200 baseEnd_964200 := by
    simpa [prefixWord, tailWord_964200, baseEnd_964200] using wordTrace_append hprefix tailTrace_964200
  have hstable : (prefixWord ++ tailWord_964200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964200).length < 2 ^ (prefixWord ++ tailWord_964200).sum := by decide
  have hdescent : baseEnd_964200 < baseStart_964200 := by decide
  rcases family_descends (prefixWord ++ tailWord_964200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964210 : List Nat := [3, 2, 1, 2, 3, 3, 2, 7]
def baseStart_964210 : Nat := 118140960795 + 964210 * 2 ^ 59
def prefixEnd_964210 : Nat := 4983230072969 + 3 ^ 40 * 964210 * 2
def baseEnd_964210 : Nat := 18337154884139916949655

theorem tailTrace_964210 : CollatzResearch.WordTrace tailWord_964210 prefixEnd_964210 18337154884139916949655 := by
  unfold tailWord_964210
  simp only [CollatzResearch.WordTrace]
  refine ⟨8791906959209829700686521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23445085224559545868497389 8791906959209829700686521)
  ·
    refine ⟨6593930219407372275514891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8791906959209829700686521 6593930219407372275514891)
    ·
      refine ⟨9890895329111058413272337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6593930219407372275514891 9890895329111058413272337)
      ·
        refine ⟨7418171496833293809954253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9890895329111058413272337 7418171496833293809954253)
        ·
          refine ⟨2781814311312485178732845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7418171496833293809954253 2781814311312485178732845)
          ·
            refine ⟨1043180366742181942024817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2781814311312485178732845 1043180366742181942024817)
            ·
              refine ⟨782385275056636456518613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1043180366742181942024817 782385275056636456518613)
              ·
                refine ⟨18337154884139916949655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 782385275056636456518613 18337154884139916949655)
                ·
                  rfl

theorem cell23_964210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 2, 7].length) (baseStart_964210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_964210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_964210 prefixEnd_964210 := by exact prefixLift 964210
  have htrace : WordTrace (prefixWord ++ tailWord_964210) baseStart_964210 baseEnd_964210 := by
    simpa [prefixWord, tailWord_964210, baseEnd_964210] using wordTrace_append hprefix tailTrace_964210
  have hstable : (prefixWord ++ tailWord_964210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964210).length < 2 ^ (prefixWord ++ tailWord_964210).sum := by decide
  have hdescent : baseEnd_964210 < baseStart_964210 := by decide
  rcases family_descends (prefixWord ++ tailWord_964210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964221 : List Nat := [1, 4, 1, 1, 4, 3, 1, 3, 1, 2, 2]
def baseStart_964221 : Nat := 118140960795 + 964221 * 2 ^ 59
def prefixEnd_964221 : Nat := 4983230072969 + 3 ^ 40 * 964221 * 2
def baseEnd_964221 : Nat := 495108830158977214603135

theorem tailTrace_964221 : CollatzResearch.WordTrace tailWord_964221 prefixEnd_964221 495108830158977214603135 := by
  unfold tailWord_964221
  simp only [CollatzResearch.WordTrace]
  refine ⟨35168029039799467681396517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23445352693199645120931011 35168029039799467681396517)
  ·
    refine ⟨6594005444962400190261847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35168029039799467681396517 6594005444962400190261847)
    ·
      refine ⟨9891008167443600285392771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6594005444962400190261847 9891008167443600285392771)
      ·
        refine ⟨14836512251165400428089157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9891008167443600285392771 14836512251165400428089157)
        ·
          refine ⟨2781846047093512580266717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14836512251165400428089157 2781846047093512580266717)
          ·
            refine ⟨1043192267660067217600019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2781846047093512580266717 1043192267660067217600019)
            ·
              refine ⟨1564788401490100826400029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1043192267660067217600019 1564788401490100826400029)
              ·
                refine ⟨586795650558787809900011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1564788401490100826400029 586795650558787809900011)
                ·
                  refine ⟨880193475838181714850017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 586795650558787809900011 880193475838181714850017)
                  ·
                    refine ⟨660145106878636286137513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 880193475838181714850017 660145106878636286137513)
                    ·
                      refine ⟨495108830158977214603135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 660145106878636286137513 495108830158977214603135)
                      ·
                        rfl

theorem cell23_964221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 3, 1, 2, 2].length) (baseStart_964221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_964221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_964221 prefixEnd_964221 := by exact prefixLift 964221
  have htrace : WordTrace (prefixWord ++ tailWord_964221) baseStart_964221 baseEnd_964221 := by
    simpa [prefixWord, tailWord_964221, baseEnd_964221] using wordTrace_append hprefix tailTrace_964221
  have hstable : (prefixWord ++ tailWord_964221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964221).length < 2 ^ (prefixWord ++ tailWord_964221).sum := by decide
  have hdescent : baseEnd_964221 < baseStart_964221 := by decide
  rcases family_descends (prefixWord ++ tailWord_964221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964243 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 2, 8, 2]
def baseStart_964243 : Nat := 118140960795 + 964243 * 2 ^ 59
def prefixEnd_964243 : Nat := 4983230072969 + 3 ^ 40 * 964243 * 2
def baseEnd_964243 : Nat := 495120126733376128528033

theorem tailTrace_964243 : CollatzResearch.WordTrace tailWord_964243 prefixEnd_964243 495120126733376128528033 := by
  unfold tailWord_964243
  simp only [CollatzResearch.WordTrace]
  refine ⟨35168831445719765438697383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23445887630479843625798255 35168831445719765438697383)
  ·
    refine ⟨52753247168579648158046075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35168831445719765438697383 52753247168579648158046075)
    ·
      refine ⟨79129870752869472237069113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52753247168579648158046075 79129870752869472237069113)
      ·
        refine ⟨59347403064652104177801835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79129870752869472237069113 59347403064652104177801835)
        ·
          refine ⟨89021104596978156266702753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59347403064652104177801835 89021104596978156266702753)
          ·
            refine ⟨66765828447733617200027065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89021104596978156266702753 66765828447733617200027065)
            ·
              refine ⟨50074371335800212900020299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66765828447733617200027065 50074371335800212900020299)
              ·
                refine ⟨75111557003700319350030449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50074371335800212900020299 75111557003700319350030449)
                ·
                  refine ⟨56333667752775239512522837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75111557003700319350030449 56333667752775239512522837)
                  ·
                    refine ⟨660160168977834838037377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 56333667752775239512522837 660160168977834838037377)
                    ·
                      refine ⟨495120126733376128528033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 660160168977834838037377 495120126733376128528033)
                      ·
                        rfl

theorem cell23_964243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 8, 2].length) (baseStart_964243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_964243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_964243 prefixEnd_964243 := by exact prefixLift 964243
  have htrace : WordTrace (prefixWord ++ tailWord_964243) baseStart_964243 baseEnd_964243 := by
    simpa [prefixWord, tailWord_964243, baseEnd_964243] using wordTrace_append hprefix tailTrace_964243
  have hstable : (prefixWord ++ tailWord_964243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964243).length < 2 ^ (prefixWord ++ tailWord_964243).sum := by decide
  have hdescent : baseEnd_964243 < baseStart_964243 := by decide
  rcases family_descends (prefixWord ++ tailWord_964243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964254 : List Nat := [4, 3, 1, 1, 1, 3, 1, 3, 2, 1, 3]
def baseStart_964254 : Nat := 118140960795 + 964254 * 2 ^ 59
def prefixEnd_964254 : Nat := 4983230072969 + 3 ^ 40 * 964254 * 2
def baseEnd_964254 : Nat := 495125775020575585490483

theorem tailTrace_964254 : CollatzResearch.WordTrace tailWord_964254 prefixEnd_964254 495125775020575585490483 := by
  unfold tailWord_964254
  simp only [CollatzResearch.WordTrace]
  refine ⟨4396154081084989289668477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23446155099119942878231877 4396154081084989289668477)
  ·
    refine ⟨1648557780406870983625679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4396154081084989289668477 1648557780406870983625679)
    ·
      refine ⟨2472836670610306475438519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1648557780406870983625679 2472836670610306475438519)
      ·
        refine ⟨3709255005915459713157779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2472836670610306475438519 3709255005915459713157779)
        ·
          refine ⟨5563882508873189569736669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3709255005915459713157779 5563882508873189569736669)
          ·
            refine ⟨2086455940827446088651251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5563882508873189569736669 2086455940827446088651251)
            ·
              refine ⟨3129683911241169132976877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2086455940827446088651251 3129683911241169132976877)
              ·
                refine ⟨1173631466715438424866329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3129683911241169132976877 1173631466715438424866329)
                ·
                  refine ⟨880223600036578818649747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1173631466715438424866329 880223600036578818649747)
                  ·
                    refine ⟨1320335400054868227974621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 880223600036578818649747 1320335400054868227974621)
                    ·
                      refine ⟨495125775020575585490483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1320335400054868227974621 495125775020575585490483)
                      ·
                        rfl

theorem cell23_964254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_964254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_964254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_964254 prefixEnd_964254 := by exact prefixLift 964254
  have htrace : WordTrace (prefixWord ++ tailWord_964254) baseStart_964254 baseEnd_964254 := by
    simpa [prefixWord, tailWord_964254, baseEnd_964254] using wordTrace_append hprefix tailTrace_964254
  have hstable : (prefixWord ++ tailWord_964254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964254).length < 2 ^ (prefixWord ++ tailWord_964254).sum := by decide
  have hdescent : baseEnd_964254 < baseStart_964254 := by decide
  rcases family_descends (prefixWord ++ tailWord_964254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964293 : List Nat := [1, 3, 1, 1, 1, 1, 2, 3, 4, 3, 3]
def baseStart_964293 : Nat := 118140960795 + 964293 * 2 ^ 59
def prefixEnd_964293 : Nat := 4983230072969 + 3 ^ 40 * 964293 * 2
def baseEnd_964293 : Nat := 495145800766100932902803

theorem tailTrace_964293 : CollatzResearch.WordTrace tailWord_964293 prefixEnd_964293 495145800766100932902803 := by
  unfold tailWord_964293
  simp only [CollatzResearch.WordTrace]
  refine ⟨35170655095538623978017533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23447103397025749318678355 35170655095538623978017533)
  ·
    refine ⟨13188995660826983991756575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35170655095538623978017533 13188995660826983991756575)
    ·
      refine ⟨19783493491240475987634863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13188995660826983991756575 19783493491240475987634863)
      ·
        refine ⟨29675240236860713981452295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19783493491240475987634863 29675240236860713981452295)
        ·
          refine ⟨44512860355291070972178443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29675240236860713981452295 44512860355291070972178443)
          ·
            refine ⟨66769290532936606458267665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44512860355291070972178443 66769290532936606458267665)
            ·
              refine ⟨50076967899702454843700749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66769290532936606458267665 50076967899702454843700749)
              ·
                refine ⟨18778862962388420566387781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50076967899702454843700749 18778862962388420566387781)
                ·
                  refine ⟨3521036805447828856197709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18778862962388420566387781 3521036805447828856197709)
                  ·
                    refine ⟨1320388802042935821074141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3521036805447828856197709 1320388802042935821074141)
                    ·
                      refine ⟨495145800766100932902803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1320388802042935821074141 495145800766100932902803)
                      ·
                        rfl

theorem cell23_964293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 4, 3, 3].length) (baseStart_964293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_964293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_964293 prefixEnd_964293 := by exact prefixLift 964293
  have htrace : WordTrace (prefixWord ++ tailWord_964293) baseStart_964293 baseEnd_964293 := by
    simpa [prefixWord, tailWord_964293, baseEnd_964293] using wordTrace_append hprefix tailTrace_964293
  have hstable : (prefixWord ++ tailWord_964293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964293).length < 2 ^ (prefixWord ++ tailWord_964293).sum := by decide
  have hdescent : baseEnd_964293 < baseStart_964293 := by decide
  rcases family_descends (prefixWord ++ tailWord_964293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964317 : List Nat := [1, 4, 3, 3, 1, 1, 1, 2, 7]
def baseStart_964317 : Nat := 118140960795 + 964317 * 2 ^ 59
def prefixEnd_964317 : Nat := 4983230072969 + 3 ^ 40 * 964317 * 2
def baseEnd_964317 : Nat := 55017569366867648778077

theorem tailTrace_964317 : CollatzResearch.WordTrace tailWord_964317 prefixEnd_964317 55017569366867648778077 := by
  unfold tailWord_964317
  simp only [CollatzResearch.WordTrace]
  refine ⟨35171530447451676076891205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23447686964967784051260803 35171530447451676076891205)
  ·
    refine ⟨6594661958897189264417101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35171530447451676076891205 6594661958897189264417101)
    ·
      refine ⟨2472998234586445974156413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6594661958897189264417101 2472998234586445974156413)
      ·
        refine ⟨927374337969917240308655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2472998234586445974156413 927374337969917240308655)
        ·
          refine ⟨1391061506954875860462983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 927374337969917240308655 1391061506954875860462983)
          ·
            refine ⟨2086592260432313790694475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1391061506954875860462983 2086592260432313790694475)
            ·
              refine ⟨3129888390648470686041713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2086592260432313790694475 3129888390648470686041713)
              ·
                refine ⟨2347416292986353014531285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3129888390648470686041713 2347416292986353014531285)
                ·
                  refine ⟨55017569366867648778077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2347416292986353014531285 55017569366867648778077)
                  ·
                    rfl

theorem cell23_964317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 2, 7].length) (baseStart_964317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_964317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_964317 prefixEnd_964317 := by exact prefixLift 964317
  have htrace : WordTrace (prefixWord ++ tailWord_964317) baseStart_964317 baseEnd_964317 := by
    simpa [prefixWord, tailWord_964317, baseEnd_964317] using wordTrace_append hprefix tailTrace_964317
  have hstable : (prefixWord ++ tailWord_964317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964317).length < 2 ^ (prefixWord ++ tailWord_964317).sum := by decide
  have hdescent : baseEnd_964317 < baseStart_964317 := by decide
  rcases family_descends (prefixWord ++ tailWord_964317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964330 : List Nat := [3, 1, 3, 1, 1, 1, 5, 1, 2, 5]
def baseStart_964330 : Nat := 118140960795 + 964330 * 2 ^ 59
def prefixEnd_964330 : Nat := 4983230072969 + 3 ^ 40 * 964330 * 2
def baseEnd_964330 : Nat := 165054933183439096046711

theorem tailTrace_964330 : CollatzResearch.WordTrace tailWord_964330 prefixEnd_964330 165054933183439096046711 := by
  unfold tailWord_964330
  simp only [CollatzResearch.WordTrace]
  refine ⟨8793001149101144824278611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23448003064269719531409629 8793001149101144824278611)
  ·
    refine ⟨13189501723651717236417917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8793001149101144824278611 13189501723651717236417917)
    ·
      refine ⟨4946063146369393963656719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13189501723651717236417917 4946063146369393963656719)
      ·
        refine ⟨7419094719554090945485079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4946063146369393963656719 7419094719554090945485079)
        ·
          refine ⟨11128642079331136418227619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7419094719554090945485079 11128642079331136418227619)
          ·
            refine ⟨16692963118996704627341429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11128642079331136418227619 16692963118996704627341429)
            ·
              refine ⟨1564965292405941058813259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16692963118996704627341429 1564965292405941058813259)
              ·
                refine ⟨2347447938608911588219889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1564965292405941058813259 2347447938608911588219889)
                ·
                  refine ⟨1760585953956683691164917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2347447938608911588219889 1760585953956683691164917)
                  ·
                    refine ⟨165054933183439096046711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1760585953956683691164917 165054933183439096046711)
                    ·
                      rfl

theorem cell23_964330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 1, 2, 5].length) (baseStart_964330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_964330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_964330 prefixEnd_964330 := by exact prefixLift 964330
  have htrace : WordTrace (prefixWord ++ tailWord_964330) baseStart_964330 baseEnd_964330 := by
    simpa [prefixWord, tailWord_964330, baseEnd_964330] using wordTrace_append hprefix tailTrace_964330
  have hstable : (prefixWord ++ tailWord_964330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964330).length < 2 ^ (prefixWord ++ tailWord_964330).sum := by decide
  have hdescent : baseEnd_964330 < baseStart_964330 := by decide
  rcases family_descends (prefixWord ++ tailWord_964330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964353 : List Nat := [1, 2, 4, 1, 1, 1, 2, 1, 2, 3, 5]
def baseStart_964353 : Nat := 118140960795 + 964353 * 2 ^ 59
def prefixEnd_964353 : Nat := 4983230072969 + 3 ^ 40 * 964353 * 2
def baseEnd_964353 : Nat := 495176609605370698152527

theorem tailTrace_964353 : CollatzResearch.WordTrace tailWord_964353 prefixEnd_964353 495176609605370698152527 := by
  unfold tailWord_964353
  simp only [CollatzResearch.WordTrace]
  refine ⟨35172843475321254225201713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23448562316880836150134475 35172843475321254225201713)
  ·
    refine ⟨26379632606490940668901285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35172843475321254225201713 26379632606490940668901285)
    ·
      refine ⟨4946181113717051375418991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26379632606490940668901285 4946181113717051375418991)
      ·
        refine ⟨7419271670575577063128487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4946181113717051375418991 7419271670575577063128487)
        ·
          refine ⟨11128907505863365594692731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7419271670575577063128487 11128907505863365594692731)
          ·
            refine ⟨16693361258795048392039097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11128907505863365594692731 16693361258795048392039097)
            ·
              refine ⟨12520020944096286294029323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16693361258795048392039097 12520020944096286294029323)
              ·
                refine ⟨18780031416144429441043985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12520020944096286294029323 18780031416144429441043985)
                ·
                  refine ⟨14085023562108322080782989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18780031416144429441043985 14085023562108322080782989)
                  ·
                    refine ⟨5281883835790620780293621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14085023562108322080782989 5281883835790620780293621)
                    ·
                      refine ⟨495176609605370698152527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5281883835790620780293621 495176609605370698152527)
                      ·
                        rfl

theorem cell23_964353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_964353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_964353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_964353 prefixEnd_964353 := by exact prefixLift 964353
  have htrace : WordTrace (prefixWord ++ tailWord_964353) baseStart_964353 baseEnd_964353 := by
    simpa [prefixWord, tailWord_964353, baseEnd_964353] using wordTrace_append hprefix tailTrace_964353
  have hstable : (prefixWord ++ tailWord_964353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964353).length < 2 ^ (prefixWord ++ tailWord_964353).sum := by decide
  have hdescent : baseEnd_964353 < baseStart_964353 := by decide
  rcases family_descends (prefixWord ++ tailWord_964353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964404 : List Nat := [2, 5, 1, 1, 2, 2, 1, 2, 2, 2, 3]
def baseStart_964404 : Nat := 118140960795 + 964404 * 2 ^ 59
def prefixEnd_964404 : Nat := 4983230072969 + 3 ^ 40 * 964404 * 2
def baseEnd_964404 : Nat := 495202797118749998614793

theorem tailTrace_964404 : CollatzResearch.WordTrace tailWord_964404 prefixEnd_964404 495202797118749998614793 := by
  unfold tailWord_964404
  simp only [CollatzResearch.WordTrace]
  refine ⟨17587351799068244967654133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23449802398757659956872177 17587351799068244967654133)
  ·
    refine ⟨1648814231162647965717575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17587351799068244967654133 1648814231162647965717575)
    ·
      refine ⟨2473221346743971948576363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1648814231162647965717575 2473221346743971948576363)
      ·
        refine ⟨3709832020115957922864545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2473221346743971948576363 3709832020115957922864545)
        ·
          refine ⟨2782374015086968442148409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3709832020115957922864545 2782374015086968442148409)
          ·
            refine ⟨2086780511315226331611307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2782374015086968442148409 2086780511315226331611307)
            ·
              refine ⟨3130170766972839497416961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2086780511315226331611307 3130170766972839497416961)
              ·
                refine ⟨2347628075229629623062721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3130170766972839497416961 2347628075229629623062721)
                ·
                  refine ⟨1760721056422222217297041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2347628075229629623062721 1760721056422222217297041)
                  ·
                    refine ⟨1320540792316666662972781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1760721056422222217297041 1320540792316666662972781)
                    ·
                      refine ⟨495202797118749998614793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1320540792316666662972781 495202797118749998614793)
                      ·
                        rfl

theorem cell23_964404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_964404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_964404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_964404 prefixEnd_964404 := by exact prefixLift 964404
  have htrace : WordTrace (prefixWord ++ tailWord_964404) baseStart_964404 baseEnd_964404 := by
    simpa [prefixWord, tailWord_964404, baseEnd_964404] using wordTrace_append hprefix tailTrace_964404
  have hstable : (prefixWord ++ tailWord_964404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964404).length < 2 ^ (prefixWord ++ tailWord_964404).sum := by decide
  have hdescent : baseEnd_964404 < baseStart_964404 := by decide
  rcases family_descends (prefixWord ++ tailWord_964404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964437 : List Nat := [1, 3, 2, 2, 2, 2, 3, 2, 1, 5]
def baseStart_964437 : Nat := 118140960795 + 964437 * 2 ^ 59
def prefixEnd_964437 : Nat := 4983230072969 + 3 ^ 40 * 964437 * 2
def baseEnd_964437 : Nat := 165073247326782789834047

theorem tailTrace_964437 : CollatzResearch.WordTrace tailWord_964437 prefixEnd_964437 165073247326782789834047 := by
  unfold tailWord_964437
  simp only [CollatzResearch.WordTrace]
  refine ⟨35175907207016936571259565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23450604804677957714173043 35175907207016936571259565)
  ·
    refine ⟨13190965202631351214222337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35175907207016936571259565 13190965202631351214222337)
    ·
      refine ⟨9893223901973513410666753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13190965202631351214222337 9893223901973513410666753)
      ·
        refine ⟨7419917926480135058000065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9893223901973513410666753 7419917926480135058000065)
        ·
          refine ⟨5564938444860101293500049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7419917926480135058000065 5564938444860101293500049)
          ·
            refine ⟨4173703833645075970125037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5564938444860101293500049 4173703833645075970125037)
            ·
              refine ⟨1565138937616903488796889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4173703833645075970125037 1565138937616903488796889)
              ·
                refine ⟨1173854203212677616597667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1565138937616903488796889 1173854203212677616597667)
                ·
                  refine ⟨1760781304819016424896501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1173854203212677616597667 1760781304819016424896501)
                  ·
                    refine ⟨165073247326782789834047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1760781304819016424896501 165073247326782789834047)
                    ·
                      rfl

theorem cell23_964437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 2, 1, 5].length) (baseStart_964437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_964437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_964437 prefixEnd_964437 := by exact prefixLift 964437
  have htrace : WordTrace (prefixWord ++ tailWord_964437) baseStart_964437 baseEnd_964437 := by
    simpa [prefixWord, tailWord_964437, baseEnd_964437] using wordTrace_append hprefix tailTrace_964437
  have hstable : (prefixWord ++ tailWord_964437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964437).length < 2 ^ (prefixWord ++ tailWord_964437).sum := by decide
  have hdescent : baseEnd_964437 < baseStart_964437 := by decide
  rcases family_descends (prefixWord ++ tailWord_964437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964502 : List Nat := [5, 3, 1, 1, 2, 1, 2, 3, 1, 1, 3]
def baseStart_964502 : Nat := 118140960795 + 964502 * 2 ^ 59
def prefixEnd_964502 : Nat := 4983230072969 + 3 ^ 40 * 964502 * 2
def baseEnd_964502 : Nat := 495253118222890615189343

theorem tailTrace_964502 : CollatzResearch.WordTrace tailWord_964502 prefixEnd_964502 495253118222890615189343 := by
  unfold tailWord_964502
  simp only [CollatzResearch.WordTrace]
  refine ⟨2198642371986340792023485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23452185301187635114917173 2198642371986340792023485)
  ·
    refine ⟨824490889494877797008807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2198642371986340792023485 824490889494877797008807)
    ·
      refine ⟨1236736334242316695513211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 824490889494877797008807 1236736334242316695513211)
      ·
        refine ⟨1855104501363475043269817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1236736334242316695513211 1855104501363475043269817)
        ·
          refine ⟨1391328376022606282452363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1855104501363475043269817 1391328376022606282452363)
          ·
            refine ⟨2086992564033909423678545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1391328376022606282452363 2086992564033909423678545)
            ·
              refine ⟨1565244423025432067758909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2086992564033909423678545 1565244423025432067758909)
              ·
                refine ⟨586966658634537025409591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1565244423025432067758909 586966658634537025409591)
                ·
                  refine ⟨880449987951805538114387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 586966658634537025409591 880449987951805538114387)
                  ·
                    refine ⟨1320674981927708307171581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 880449987951805538114387 1320674981927708307171581)
                    ·
                      refine ⟨495253118222890615189343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1320674981927708307171581 495253118222890615189343)
                      ·
                        rfl

theorem cell23_964502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_964502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_964502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_964502 prefixEnd_964502 := by exact prefixLift 964502
  have htrace : WordTrace (prefixWord ++ tailWord_964502) baseStart_964502 baseEnd_964502 := by
    simpa [prefixWord, tailWord_964502, baseEnd_964502] using wordTrace_append hprefix tailTrace_964502
  have hstable : (prefixWord ++ tailWord_964502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964502).length < 2 ^ (prefixWord ++ tailWord_964502).sum := by decide
  have hdescent : baseEnd_964502 < baseStart_964502 := by decide
  rcases family_descends (prefixWord ++ tailWord_964502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964508 : List Nat := [2, 2, 3, 3, 1, 1, 1, 5, 1, 2, 2]
def baseStart_964508 : Nat := 118140960795 + 964508 * 2 ^ 59
def prefixEnd_964508 : Nat := 4983230072969 + 3 ^ 40 * 964508 * 2
def baseEnd_964508 : Nat := 495256199106817591714315

theorem tailTrace_964508 : CollatzResearch.WordTrace tailWord_964508 prefixEnd_964508 495256199106817591714315 := by
  unfold tailWord_964508
  simp only [CollatzResearch.WordTrace]
  refine ⟨17589248394879857848547089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23452331193173143798062785 17589248394879857848547089)
  ·
    refine ⟨13191936296159893386410317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17589248394879857848547089 13191936296159893386410317)
    ·
      refine ⟨4946976111059960019903869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13191936296159893386410317 4946976111059960019903869)
      ·
        refine ⟨1855116041647485007463951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4946976111059960019903869 1855116041647485007463951)
        ·
          refine ⟨2782674062471227511195927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1855116041647485007463951 2782674062471227511195927)
          ·
            refine ⟨4174011093706841266793891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2782674062471227511195927 4174011093706841266793891)
            ·
              refine ⟨6261016640560261900190837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4174011093706841266793891 6261016640560261900190837)
              ·
                refine ⟨586970310052524553142891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6261016640560261900190837 586970310052524553142891)
                ·
                  refine ⟨880455465078786829714337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 586970310052524553142891 880455465078786829714337)
                  ·
                    refine ⟨660341598809090122285753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 880455465078786829714337 660341598809090122285753)
                    ·
                      refine ⟨495256199106817591714315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 660341598809090122285753 495256199106817591714315)
                      ·
                        rfl

theorem cell23_964508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_964508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_964508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_964508 prefixEnd_964508 := by exact prefixLift 964508
  have htrace : WordTrace (prefixWord ++ tailWord_964508) baseStart_964508 baseEnd_964508 := by
    simpa [prefixWord, tailWord_964508, baseEnd_964508] using wordTrace_append hprefix tailTrace_964508
  have hstable : (prefixWord ++ tailWord_964508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964508).length < 2 ^ (prefixWord ++ tailWord_964508).sum := by decide
  have hdescent : baseEnd_964508 < baseStart_964508 := by decide
  rcases family_descends (prefixWord ++ tailWord_964508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964530 : List Nat := [3, 2, 1, 1, 1, 1, 1, 3, 1, 5, 4]
def baseStart_964530 : Nat := 118140960795 + 964530 * 2 ^ 59
def prefixEnd_964530 : Nat := 4983230072969 + 3 ^ 40 * 964530 * 2
def baseEnd_964530 : Nat := 495267495681216505639213

theorem tailTrace_964530 : CollatzResearch.WordTrace tailWord_964530 prefixEnd_964530 495267495681216505639213 := by
  unfold tailWord_964530
  simp only [CollatzResearch.WordTrace]
  refine ⟨8794824798920003363598761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23452866130453342302930029 8794824798920003363598761)
  ·
    refine ⟨6596118599190002522699071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8794824798920003363598761 6596118599190002522699071)
    ·
      refine ⟨9894177898785003784048607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6596118599190002522699071 9894177898785003784048607)
      ·
        refine ⟨14841266848177505676072911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9894177898785003784048607 14841266848177505676072911)
        ·
          refine ⟨22261900272266258514109367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14841266848177505676072911 22261900272266258514109367)
          ·
            refine ⟨33392850408399387771164051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22261900272266258514109367 33392850408399387771164051)
            ·
              refine ⟨50089275612599081656746077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33392850408399387771164051 50089275612599081656746077)
              ·
                refine ⟨18783478354724655621279779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50089275612599081656746077 18783478354724655621279779)
                ·
                  refine ⟨28175217532086983431919669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18783478354724655621279779 28175217532086983431919669)
                  ·
                    refine ⟨2641426643633154696742469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28175217532086983431919669 2641426643633154696742469)
                    ·
                      refine ⟨495267495681216505639213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2641426643633154696742469 495267495681216505639213)
                      ·
                        rfl

theorem cell23_964530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 1, 5, 4].length) (baseStart_964530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_964530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_964530 prefixEnd_964530 := by exact prefixLift 964530
  have htrace : WordTrace (prefixWord ++ tailWord_964530) baseStart_964530 baseEnd_964530 := by
    simpa [prefixWord, tailWord_964530, baseEnd_964530] using wordTrace_append hprefix tailTrace_964530
  have hstable : (prefixWord ++ tailWord_964530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964530).length < 2 ^ (prefixWord ++ tailWord_964530).sum := by decide
  have hdescent : baseEnd_964530 < baseStart_964530 := by decide
  rcases family_descends (prefixWord ++ tailWord_964530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964560 : List Nat := [2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 4]
def baseStart_964560 : Nat := 118140960795 + 964560 * 2 ^ 59
def prefixEnd_964560 : Nat := 4983230072969 + 3 ^ 40 * 964560 * 2
def baseEnd_964560 : Nat := 495282900100851388264075

theorem tailTrace_964560 : CollatzResearch.WordTrace tailWord_964560 prefixEnd_964560 495282900100851388264075 := by
  unfold tailWord_964560
  simp only [CollatzResearch.WordTrace]
  refine ⟨17590196692785664288993567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23453595590380885718658089 17590196692785664288993567)
  ·
    refine ⟨26385295039178496433490351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17590196692785664288993567 26385295039178496433490351)
    ·
      refine ⟨39577942558767744650235527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26385295039178496433490351 39577942558767744650235527)
      ·
        refine ⟨59366913838151616975353291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39577942558767744650235527 59366913838151616975353291)
        ·
          refine ⟨89050370757227425463029937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59366913838151616975353291 89050370757227425463029937)
          ·
            refine ⟨66787778067920569097272453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89050370757227425463029937 66787778067920569097272453)
            ·
              refine ⟨12522708387735106705738585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66787778067920569097272453 12522708387735106705738585)
              ·
                refine ⟨9392031290801330029303939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12522708387735106705738585 9392031290801330029303939)
                ·
                  refine ⟨14088046936201995043955909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9392031290801330029303939 14088046936201995043955909)
                  ·
                    refine ⟨2641508800537874070741733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14088046936201995043955909 2641508800537874070741733)
                    ·
                      refine ⟨495282900100851388264075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2641508800537874070741733 495282900100851388264075)
                      ·
                        rfl

theorem cell23_964560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 4].length) (baseStart_964560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_964560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_964560 prefixEnd_964560 := by exact prefixLift 964560
  have htrace : WordTrace (prefixWord ++ tailWord_964560) baseStart_964560 baseEnd_964560 := by
    simpa [prefixWord, tailWord_964560, baseEnd_964560] using wordTrace_append hprefix tailTrace_964560
  have hstable : (prefixWord ++ tailWord_964560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964560).length < 2 ^ (prefixWord ++ tailWord_964560).sum := by decide
  have hdescent : baseEnd_964560 < baseStart_964560 := by decide
  rcases family_descends (prefixWord ++ tailWord_964560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964564 : List Nat := [2, 4, 1, 2, 1, 1, 2, 1, 3, 4, 2]
def baseStart_964564 : Nat := 118140960795 + 964564 * 2 ^ 59
def prefixEnd_964564 : Nat := 4983230072969 + 3 ^ 40 * 964564 * 2
def baseEnd_964564 : Nat := 495284954023469372614057

theorem tailTrace_964564 : CollatzResearch.WordTrace tailWord_964564 prefixEnd_964564 495284954023469372614057 := by
  unfold tailWord_964564
  simp only [CollatzResearch.WordTrace]
  refine ⟨17590269638778418630566373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23453692851704558174088497 17590269638778418630566373)
  ·
    refine ⟨3298175557270953493231195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17590269638778418630566373 3298175557270953493231195)
    ·
      refine ⟨4947263335906430239846793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3298175557270953493231195 4947263335906430239846793)
      ·
        refine ⟨3710447501929822679885095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4947263335906430239846793 3710447501929822679885095)
        ·
          refine ⟨5565671252894734019827643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3710447501929822679885095 5565671252894734019827643)
          ·
            refine ⟨8348506879342101029741465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5565671252894734019827643 8348506879342101029741465)
            ·
              refine ⟨6261380159506575772306099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8348506879342101029741465 6261380159506575772306099)
              ·
                refine ⟨9392070239259863658459149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6261380159506575772306099 9392070239259863658459149)
                ·
                  refine ⟨3522026339722448871922181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9392070239259863658459149 3522026339722448871922181)
                  ·
                    refine ⟨660379938697959163485409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3522026339722448871922181 660379938697959163485409)
                    ·
                      refine ⟨495284954023469372614057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 660379938697959163485409 495284954023469372614057)
                      ·
                        rfl

theorem cell23_964564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 3, 4, 2].length) (baseStart_964564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_964564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_964564 prefixEnd_964564 := by exact prefixLift 964564
  have htrace : WordTrace (prefixWord ++ tailWord_964564) baseStart_964564 baseEnd_964564 := by
    simpa [prefixWord, tailWord_964564, baseEnd_964564] using wordTrace_append hprefix tailTrace_964564
  have hstable : (prefixWord ++ tailWord_964564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964564).length < 2 ^ (prefixWord ++ tailWord_964564).sum := by decide
  have hdescent : baseEnd_964564 < baseStart_964564 := by decide
  rcases family_descends (prefixWord ++ tailWord_964564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964580 : List Nat := [2, 3, 1, 1, 1, 1, 3, 1, 1, 2, 7]
def baseStart_964580 : Nat := 118140960795 + 964580 * 2 ^ 59
def prefixEnd_964580 : Nat := 4983230072969 + 3 ^ 40 * 964580 * 2
def baseEnd_964580 : Nat := 495293169713941310013983

theorem tailTrace_964580 : CollatzResearch.WordTrace tailWord_964580 prefixEnd_964580 495293169713941310013983 := by
  unfold tailWord_964580
  simp only [CollatzResearch.WordTrace]
  refine ⟨17590561422749435996857597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23454081896999247995810129 17590561422749435996857597)
  ·
    refine ⟨6596460533531038498821599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17590561422749435996857597 6596460533531038498821599)
    ·
      refine ⟨9894690800296557748232399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6596460533531038498821599 9894690800296557748232399)
      ·
        refine ⟨14842036200444836622348599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9894690800296557748232399 14842036200444836622348599)
        ·
          refine ⟨22263054300667254933522899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14842036200444836622348599 22263054300667254933522899)
          ·
            refine ⟨33394581451000882400284349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22263054300667254933522899 33394581451000882400284349)
            ·
              refine ⟨12522968044125330900106631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33394581451000882400284349 12522968044125330900106631)
              ·
                refine ⟨18784452066187996350159947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12522968044125330900106631 18784452066187996350159947)
                ·
                  refine ⟨28176678099281994525239921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18784452066187996350159947 28176678099281994525239921)
                  ·
                    refine ⟨21132508574461495893929941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28176678099281994525239921 21132508574461495893929941)
                    ·
                      refine ⟨495293169713941310013983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 21132508574461495893929941 495293169713941310013983)
                      ·
                        rfl

theorem cell23_964580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_964580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_964580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_964580 prefixEnd_964580 := by exact prefixLift 964580
  have htrace : WordTrace (prefixWord ++ tailWord_964580) baseStart_964580 baseEnd_964580 := by
    simpa [prefixWord, tailWord_964580, baseEnd_964580] using wordTrace_append hprefix tailTrace_964580
  have hstable : (prefixWord ++ tailWord_964580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964580).length < 2 ^ (prefixWord ++ tailWord_964580).sum := by decide
  have hdescent : baseEnd_964580 < baseStart_964580 := by decide
  rcases family_descends (prefixWord ++ tailWord_964580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964587 : List Nat := [1, 1, 1, 1, 2, 3, 1, 8, 5]
def baseStart_964587 : Nat := 118140960795 + 964587 * 2 ^ 59
def prefixEnd_964587 : Nat := 4983230072969 + 3 ^ 40 * 964587 * 2
def baseEnd_964587 : Nat := 55032973786502531402939

theorem tailTrace_964587 : CollatzResearch.WordTrace tailWord_964587 prefixEnd_964587 55032973786502531402939 := by
  unfold tailWord_964587
  simp only [CollatzResearch.WordTrace]
  refine ⟨35181378156473512189220015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23454252104315674792813343 35181378156473512189220015)
  ·
    refine ⟨52772067234710268283830023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35181378156473512189220015 52772067234710268283830023)
    ·
      refine ⟨79158100852065402425745035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52772067234710268283830023 79158100852065402425745035)
      ·
        refine ⟨118737151278098103638617553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79158100852065402425745035 118737151278098103638617553)
        ·
          refine ⟨89052863458573577728963165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118737151278098103638617553 89052863458573577728963165)
          ·
            refine ⟨33394823796965091648361187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89052863458573577728963165 33394823796965091648361187)
            ·
              refine ⟨50092235695447637472541781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33394823796965091648361187 50092235695447637472541781)
              ·
                refine ⟨587018387056027001631349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 50092235695447637472541781 587018387056027001631349)
                ·
                  refine ⟨55032973786502531402939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 587018387056027001631349 55032973786502531402939)
                  ·
                    rfl

theorem cell23_964587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 8, 5].length) (baseStart_964587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_964587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_964587 prefixEnd_964587 := by exact prefixLift 964587
  have htrace : WordTrace (prefixWord ++ tailWord_964587) baseStart_964587 baseEnd_964587 := by
    simpa [prefixWord, tailWord_964587, baseEnd_964587] using wordTrace_append hprefix tailTrace_964587
  have hstable : (prefixWord ++ tailWord_964587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964587).length < 2 ^ (prefixWord ++ tailWord_964587).sum := by decide
  have hdescent : baseEnd_964587 < baseStart_964587 := by decide
  rcases family_descends (prefixWord ++ tailWord_964587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964600 : List Nat := [2, 1, 2, 1, 1, 3, 2, 1, 3, 7]
def baseStart_964600 : Nat := 118140960795 + 964600 * 2 ^ 59
def prefixEnd_964600 : Nat := 4983230072969 + 3 ^ 40 * 964600 * 2
def baseEnd_964600 : Nat := 165101146442343743921297

theorem tailTrace_964600 : CollatzResearch.WordTrace tailWord_964600 prefixEnd_964600 165101146442343743921297 := by
  unfold tailWord_964600
  simp only [CollatzResearch.WordTrace]
  refine ⟨17590926152713207704721627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23454568203617610272962169 17590926152713207704721627)
  ·
    refine ⟨26386389229069811557082441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17590926152713207704721627 26386389229069811557082441)
    ·
      refine ⟨19789791921802358667811831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26386389229069811557082441 19789791921802358667811831)
      ·
        refine ⟨29684687882703538001717747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19789791921802358667811831 29684687882703538001717747)
        ·
          refine ⟨44527031824055307002576621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29684687882703538001717747 44527031824055307002576621)
          ·
            refine ⟨16697636934020740125966233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44527031824055307002576621 16697636934020740125966233)
            ·
              refine ⟨12523227700515555094474675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16697636934020740125966233 12523227700515555094474675)
              ·
                refine ⟨18784841550773332641712013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12523227700515555094474675 18784841550773332641712013)
                ·
                  refine ⟨7044315581539999740642005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18784841550773332641712013 7044315581539999740642005)
                  ·
                    refine ⟨165101146442343743921297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7044315581539999740642005 165101146442343743921297)
                    ·
                      rfl

theorem cell23_964600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 3, 7].length) (baseStart_964600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_964600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_964600 prefixEnd_964600 := by exact prefixLift 964600
  have htrace : WordTrace (prefixWord ++ tailWord_964600) baseStart_964600 baseEnd_964600 := by
    simpa [prefixWord, tailWord_964600, baseEnd_964600] using wordTrace_append hprefix tailTrace_964600
  have hstable : (prefixWord ++ tailWord_964600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964600).length < 2 ^ (prefixWord ++ tailWord_964600).sum := by decide
  have hdescent : baseEnd_964600 < baseStart_964600 := by decide
  rcases family_descends (prefixWord ++ tailWord_964600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964681 : List Nat := [1, 2, 1, 1, 2, 2, 6, 3, 1, 4]
def baseStart_964681 : Nat := 118140960795 + 964681 * 2 ^ 59
def prefixEnd_964681 : Nat := 4983230072969 + 3 ^ 40 * 964681 * 2
def baseEnd_964681 : Nat := 165115010420015138283673

theorem tailTrace_964681 : CollatzResearch.WordTrace tailWord_964681 prefixEnd_964681 165115010420015138283673 := by
  unfold tailWord_964681
  simp only [CollatzResearch.WordTrace]
  refine ⟨35184806618132966243141897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23456537745421977495427931 35184806618132966243141897)
  ·
    refine ⟨26388604963599724682356423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35184806618132966243141897 26388604963599724682356423)
    ·
      refine ⟨39582907445399587023534635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26388604963599724682356423 39582907445399587023534635)
      ·
        refine ⟨59374361168099380535301953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39582907445399587023534635 59374361168099380535301953)
        ·
          refine ⟨44530770876074535401476465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59374361168099380535301953 44530770876074535401476465)
          ·
            refine ⟨33398078157055901551107349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44530770876074535401476465 33398078157055901551107349)
            ·
              refine ⟨1565534913611995385208157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 33398078157055901551107349 1565534913611995385208157)
              ·
                refine ⟨587075592604498269453059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1565534913611995385208157 587075592604498269453059)
                ·
                  refine ⟨880613388906747404179589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 587075592604498269453059 880613388906747404179589)
                  ·
                    refine ⟨165115010420015138283673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 880613388906747404179589 165115010420015138283673)
                    ·
                      rfl

theorem cell23_964681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 3, 1, 4].length) (baseStart_964681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_964681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_964681 prefixEnd_964681 := by exact prefixLift 964681
  have htrace : WordTrace (prefixWord ++ tailWord_964681) baseStart_964681 baseEnd_964681 := by
    simpa [prefixWord, tailWord_964681, baseEnd_964681] using wordTrace_append hprefix tailTrace_964681
  have hstable : (prefixWord ++ tailWord_964681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964681).length < 2 ^ (prefixWord ++ tailWord_964681).sum := by decide
  have hdescent : baseEnd_964681 < baseStart_964681 := by decide
  rcases family_descends (prefixWord ++ tailWord_964681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
