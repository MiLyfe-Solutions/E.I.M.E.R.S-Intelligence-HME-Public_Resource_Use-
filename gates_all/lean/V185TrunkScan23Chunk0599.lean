import V185TrunkScan23Chunk0598

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3540703 : List Nat := [1, 1, 2, 3, 2, 2, 3, 1, 8]
def baseStart_3540703 : Nat := 118140960795 + 3540703 * 2 ^ 59
def prefixEnd_3540703 : Nat := 4983230072969 + 3 ^ 40 * 3540703 * 2
def baseEnd_3540703 : Nat := 202009165979596190769901

theorem tailTrace_3540703 : CollatzResearch.WordTrace tailWord_3540703 prefixEnd_3540703 202009165979596190769901 := by
  unfold tailWord_3540703
  simp only [CollatzResearch.WordTrace]
  refine ⟨129140047691645209774570763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86093365127763473183047175 129140047691645209774570763)
  ·
    refine ⟨193710071537467814661856145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129140047691645209774570763 193710071537467814661856145)
    ·
      refine ⟨145282553653100860996392109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193710071537467814661856145 145282553653100860996392109)
      ·
        refine ⟨54480957619912822873647041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145282553653100860996392109 54480957619912822873647041)
        ·
          refine ⟨40860718214934617155235281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54480957619912822873647041 40860718214934617155235281)
          ·
            refine ⟨30645538661200962866426461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40860718214934617155235281 30645538661200962866426461)
            ·
              refine ⟨11492076997950361074909923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30645538661200962866426461 11492076997950361074909923)
              ·
                refine ⟨17238115496925541612364885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11492076997950361074909923 17238115496925541612364885)
                ·
                  refine ⟨202009165979596190769901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17238115496925541612364885 202009165979596190769901)
                  ·
                    rfl

theorem cell23_3540703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 8].length) (baseStart_3540703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3540703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3540703 prefixEnd_3540703 := by exact prefixLift 3540703
  have htrace : WordTrace (prefixWord ++ tailWord_3540703) baseStart_3540703 baseEnd_3540703 := by
    simpa [prefixWord, tailWord_3540703, baseEnd_3540703] using wordTrace_append hprefix tailTrace_3540703
  have hstable : (prefixWord ++ tailWord_3540703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540703).length < 2 ^ (prefixWord ++ tailWord_3540703).sum := by decide
  have hdescent : baseEnd_3540703 < baseStart_3540703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540757 : List Nat := [1, 3, 2, 1, 2, 3, 1, 1, 4, 3, 2]
def baseStart_3540757 : Nat := 118140960795 + 3540757 * 2 ^ 59
def prefixEnd_3540757 : Nat := 4983230072969 + 3 ^ 40 * 3540757 * 2
def baseEnd_3540757 : Nat := 1818110221771708505653861

theorem tailTrace_3540757 : CollatzResearch.WordTrace tailWord_3540757 prefixEnd_3540757 1818110221771708505653861 := by
  unfold tailWord_3540757
  simp only [CollatzResearch.WordTrace]
  refine ⟨129142017233449576997036525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86094678155633051331357683 129142017233449576997036525)
  ·
    refine ⟨48428256462543591373888697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129142017233449576997036525 48428256462543591373888697)
    ·
      refine ⟨36321192346907693530416523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48428256462543591373888697 36321192346907693530416523)
      ·
        refine ⟨54481788520361540295624785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36321192346907693530416523 54481788520361540295624785)
        ·
          refine ⟨40861341390271155221718589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54481788520361540295624785 40861341390271155221718589)
          ·
            refine ⟨15323003021351683208144471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40861341390271155221718589 15323003021351683208144471)
            ·
              refine ⟨22984504532027524812216707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15323003021351683208144471 22984504532027524812216707)
              ·
                refine ⟨34476756798041287218325061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22984504532027524812216707 34476756798041287218325061)
                ·
                  refine ⟨6464391899632741353435949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34476756798041287218325061 6464391899632741353435949)
                  ·
                    refine ⟨2424146962362278007538481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6464391899632741353435949 2424146962362278007538481)
                    ·
                      refine ⟨1818110221771708505653861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2424146962362278007538481 1818110221771708505653861)
                      ·
                        rfl

theorem cell23_3540757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 4, 3, 2].length) (baseStart_3540757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3540757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3540757 prefixEnd_3540757 := by exact prefixLift 3540757
  have htrace : WordTrace (prefixWord ++ tailWord_3540757) baseStart_3540757 baseEnd_3540757 := by
    simpa [prefixWord, tailWord_3540757, baseEnd_3540757] using wordTrace_append hprefix tailTrace_3540757
  have hstable : (prefixWord ++ tailWord_3540757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540757).length < 2 ^ (prefixWord ++ tailWord_3540757).sum := by decide
  have hdescent : baseEnd_3540757 < baseStart_3540757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540763 : List Nat := [1, 1, 1, 1, 1, 1, 4, 4, 3, 6]
def baseStart_3540763 : Nat := 118140960795 + 3540763 * 2 ^ 59
def prefixEnd_3540763 : Nat := 4983230072969 + 3 ^ 40 * 3540763 * 2
def baseEnd_3540763 : Nat := 606037767551878494059611

theorem tailTrace_3540763 : CollatzResearch.WordTrace tailWord_3540763 prefixEnd_3540763 606037767551878494059611 := by
  unfold tailWord_3540763
  simp only [CollatzResearch.WordTrace]
  refine ⟨129142236071427840021754943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86094824047618560014503295 129142236071427840021754943)
  ·
    refine ⟨193713354107141760032632415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129142236071427840021754943 193713354107141760032632415)
    ·
      refine ⟨290570031160712640048948623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193713354107141760032632415 290570031160712640048948623)
      ·
        refine ⟨435855046741068960073422935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290570031160712640048948623 435855046741068960073422935)
        ·
          refine ⟨653782570111603440110134403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 435855046741068960073422935 653782570111603440110134403)
          ·
            refine ⟨980673855167405160165201605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 653782570111603440110134403 980673855167405160165201605)
            ·
              refine ⟨183876347843888467530975301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 980673855167405160165201605 183876347843888467530975301)
              ·
                refine ⟨34476815220729087662057869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 183876347843888467530975301 34476815220729087662057869)
                ·
                  refine ⟨12928805707773407873271701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34476815220729087662057869 12928805707773407873271701)
                  ·
                    refine ⟨606037767551878494059611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12928805707773407873271701 606037767551878494059611)
                    ·
                      rfl

theorem cell23_3540763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 3, 6].length) (baseStart_3540763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3540763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3540763 prefixEnd_3540763 := by exact prefixLift 3540763
  have htrace : WordTrace (prefixWord ++ tailWord_3540763) baseStart_3540763 baseEnd_3540763 := by
    simpa [prefixWord, tailWord_3540763, baseEnd_3540763] using wordTrace_append hprefix tailTrace_3540763
  have hstable : (prefixWord ++ tailWord_3540763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540763).length < 2 ^ (prefixWord ++ tailWord_3540763).sum := by decide
  have hdescent : baseEnd_3540763 < baseStart_3540763 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540787 : List Nat := [1, 1, 1, 2, 7, 1, 1, 1, 3, 1, 4]
def baseStart_3540787 : Nat := 118140960795 + 3540787 * 2 ^ 59
def prefixEnd_3540787 : Nat := 4983230072969 + 3 ^ 40 * 3540787 * 2
def baseEnd_3540787 : Nat := 1818125626191343388278723

theorem tailTrace_3540787 : CollatzResearch.WordTrace tailWord_3540787 prefixEnd_3540787 1818125626191343388278723 := by
  unfold tailWord_3540787
  simp only [CollatzResearch.WordTrace]
  refine ⟨129143111423340892120628615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86095407615560594747085743 129143111423340892120628615)
  ·
    refine ⟨193714667135011338180942923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129143111423340892120628615 193714667135011338180942923)
    ·
      refine ⟨290572000702517007271414385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193714667135011338180942923 290572000702517007271414385)
      ·
        refine ⟨217929000526887755453560789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290572000702517007271414385 217929000526887755453560789)
        ·
          refine ⟨5107710949848931768442831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 217929000526887755453560789 5107710949848931768442831)
          ·
            refine ⟨7661566424773397652664247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5107710949848931768442831 7661566424773397652664247)
            ·
              refine ⟨11492349637160096478996371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7661566424773397652664247 11492349637160096478996371)
              ·
                refine ⟨17238524455740144718494557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11492349637160096478996371 17238524455740144718494557)
                ·
                  refine ⟨6464446670902554269435459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17238524455740144718494557 6464446670902554269435459)
                  ·
                    refine ⟨9696670006353831404153189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6464446670902554269435459 9696670006353831404153189)
                    ·
                      refine ⟨1818125626191343388278723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9696670006353831404153189 1818125626191343388278723)
                      ·
                        rfl

theorem cell23_3540787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 3, 1, 4].length) (baseStart_3540787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3540787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3540787 prefixEnd_3540787 := by exact prefixLift 3540787
  have htrace : WordTrace (prefixWord ++ tailWord_3540787) baseStart_3540787 baseEnd_3540787 := by
    simpa [prefixWord, tailWord_3540787, baseEnd_3540787] using wordTrace_append hprefix tailTrace_3540787
  have hstable : (prefixWord ++ tailWord_3540787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540787).length < 2 ^ (prefixWord ++ tailWord_3540787).sum := by decide
  have hdescent : baseEnd_3540787 < baseStart_3540787 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540797 : List Nat := [1, 4, 1, 4, 1, 2, 1, 2, 1, 6]
def baseStart_3540797 : Nat := 118140960795 + 3540797 * 2 ^ 59
def prefixEnd_3540797 : Nat := 4983230072969 + 3 ^ 40 * 3540797 * 2
def baseEnd_3540797 : Nat := 606043586999296116384559

theorem tailTrace_3540797 : CollatzResearch.WordTrace tailWord_3540797 prefixEnd_3540797 606043586999296116384559 := by
  unfold tailWord_3540797
  simp only [CollatzResearch.WordTrace]
  refine ⟨129143476153304663828492645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86095650768869775885661763 129143476153304663828492645)
  ·
    refine ⟨24214401778744624467842371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129143476153304663828492645 24214401778744624467842371)
    ·
      refine ⟨36321602668116936701763557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24214401778744624467842371 36321602668116936701763557)
      ·
        refine ⟨6810300500271925631580667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36321602668116936701763557 6810300500271925631580667)
        ·
          refine ⟨10215450750407888447371001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6810300500271925631580667 10215450750407888447371001)
          ·
            refine ⟨7661588062805916335528251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10215450750407888447371001 7661588062805916335528251)
            ·
              refine ⟨11492382094208874503292377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7661588062805916335528251 11492382094208874503292377)
              ·
                refine ⟨8619286570656655877469283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11492382094208874503292377 8619286570656655877469283)
                ·
                  refine ⟨12928929855984983816203925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8619286570656655877469283 12928929855984983816203925)
                  ·
                    refine ⟨606043586999296116384559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12928929855984983816203925 606043586999296116384559)
                    ·
                      rfl

theorem cell23_3540797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 2, 1, 6].length) (baseStart_3540797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3540797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3540797 prefixEnd_3540797 := by exact prefixLift 3540797
  have htrace : WordTrace (prefixWord ++ tailWord_3540797) baseStart_3540797 baseEnd_3540797 := by
    simpa [prefixWord, tailWord_3540797, baseEnd_3540797] using wordTrace_append hprefix tailTrace_3540797
  have hstable : (prefixWord ++ tailWord_3540797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540797).length < 2 ^ (prefixWord ++ tailWord_3540797).sum := by decide
  have hdescent : baseEnd_3540797 < baseStart_3540797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540807 : List Nat := [1, 1, 4, 1, 2, 1, 2, 5, 1, 2, 3]
def baseStart_3540807 : Nat := 118140960795 + 3540807 * 2 ^ 59
def prefixEnd_3540807 : Nat := 4983230072969 + 3 ^ 40 * 3540807 * 2
def baseEnd_3540807 : Nat := 1818135895804433310028631

theorem tailTrace_3540807 : CollatzResearch.WordTrace tailWord_3540807 prefixEnd_3540807 1818135895804433310028631 := by
  unfold tailWord_3540807
  simp only [CollatzResearch.WordTrace]
  refine ⟨129143840883268435536356675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86095893922178957024237783 129143840883268435536356675)
  ·
    refine ⟨193715761324902653304535013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129143840883268435536356675 193715761324902653304535013)
    ·
      refine ⟨36321705248419247494600315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 193715761324902653304535013 36321705248419247494600315)
      ·
        refine ⟨54482557872628871241900473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36321705248419247494600315 54482557872628871241900473)
        ·
          refine ⟨40861918404471653431425355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54482557872628871241900473 40861918404471653431425355)
          ·
            refine ⟨61292877606707480147138033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40861918404471653431425355 61292877606707480147138033)
            ·
              refine ⟨45969658205030610110353525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61292877606707480147138033 45969658205030610110353525)
              ·
                refine ⟨4309655456721619697845643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45969658205030610110353525 4309655456721619697845643)
                ·
                  refine ⟨6464483185082429546768465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4309655456721619697845643 6464483185082429546768465)
                  ·
                    refine ⟨4848362388811822160076349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6464483185082429546768465 4848362388811822160076349)
                    ·
                      refine ⟨1818135895804433310028631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4848362388811822160076349 1818135895804433310028631)
                      ·
                        rfl

theorem cell23_3540807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 5, 1, 2, 3].length) (baseStart_3540807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3540807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3540807 prefixEnd_3540807 := by exact prefixLift 3540807
  have htrace : WordTrace (prefixWord ++ tailWord_3540807) baseStart_3540807 baseEnd_3540807 := by
    simpa [prefixWord, tailWord_3540807, baseEnd_3540807] using wordTrace_append hprefix tailTrace_3540807
  have hstable : (prefixWord ++ tailWord_3540807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540807).length < 2 ^ (prefixWord ++ tailWord_3540807).sum := by decide
  have hdescent : baseEnd_3540807 < baseStart_3540807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540834 : List Nat := [3, 3, 2, 1, 2, 2, 2, 1, 1, 2, 4]
def baseStart_3540834 : Nat := 118140960795 + 3540834 * 2 ^ 59
def prefixEnd_3540834 : Nat := 4983230072969 + 3 ^ 40 * 3540834 * 2
def baseEnd_3540834 : Nat := 1818149759782104704391007

theorem tailTrace_3540834 : CollatzResearch.WordTrace tailWord_3540834 prefixEnd_3540834 1818149759782104704391007 := by
  unfold tailWord_3540834
  simp only [CollatzResearch.WordTrace]
  refine ⟨32286206413542654786897389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86096550436113746098393037 32286206413542654786897389)
  ·
    refine ⟨12107327405078495545086521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32286206413542654786897389 12107327405078495545086521)
    ·
      refine ⟨9080495553808871658814891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12107327405078495545086521 9080495553808871658814891)
      ·
        refine ⟨13620743330713307488222337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9080495553808871658814891 13620743330713307488222337)
        ·
          refine ⟨10215557498034980616166753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13620743330713307488222337 10215557498034980616166753)
          ·
            refine ⟨7661668123526235462125065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10215557498034980616166753 7661668123526235462125065)
            ·
              refine ⟨5746251092644676596593799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7661668123526235462125065 5746251092644676596593799)
              ·
                refine ⟨8619376638967014894890699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5746251092644676596593799 8619376638967014894890699)
                ·
                  refine ⟨12929064958450522342336049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8619376638967014894890699 12929064958450522342336049)
                  ·
                    refine ⟨9696798718837891756752037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12929064958450522342336049 9696798718837891756752037)
                    ·
                      refine ⟨1818149759782104704391007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9696798718837891756752037 1818149759782104704391007)
                      ·
                        rfl

theorem cell23_3540834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_3540834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3540834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3540834 prefixEnd_3540834 := by exact prefixLift 3540834
  have htrace : WordTrace (prefixWord ++ tailWord_3540834) baseStart_3540834 baseEnd_3540834 := by
    simpa [prefixWord, tailWord_3540834, baseEnd_3540834] using wordTrace_append hprefix tailTrace_3540834
  have hstable : (prefixWord ++ tailWord_3540834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540834).length < 2 ^ (prefixWord ++ tailWord_3540834).sum := by decide
  have hdescent : baseEnd_3540834 < baseStart_3540834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540837 : List Nat := [1, 3, 1, 3, 1, 1, 1, 2, 6, 1, 3]
def baseStart_3540837 : Nat := 118140960795 + 3540837 * 2 ^ 59
def prefixEnd_3540837 : Nat := 4983230072969 + 3 ^ 40 * 3540837 * 2
def baseEnd_3540837 : Nat := 1818151300224068192653493

theorem tailTrace_3540837 : CollatzResearch.WordTrace tailWord_3540837 prefixEnd_3540837 1818151300224068192653493 := by
  unfold tailWord_3540837
  simp only [CollatzResearch.WordTrace]
  refine ⟨129144935073159750659948765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86096623382106500439965843 129144935073159750659948765)
  ·
    refine ⟨48429350652434906497480787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129144935073159750659948765 48429350652434906497480787)
    ·
      refine ⟨72644025978652359746221181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48429350652434906497480787 72644025978652359746221181)
      ·
        refine ⟨27241509741994634904832943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72644025978652359746221181 27241509741994634904832943)
        ·
          refine ⟨40862264612991952357249415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27241509741994634904832943 40862264612991952357249415)
          ·
            refine ⟨61293396919487928535874123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40862264612991952357249415 61293396919487928535874123)
            ·
              refine ⟨91940095379231892803811185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61293396919487928535874123 91940095379231892803811185)
              ·
                refine ⟨68955071534423919602858389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91940095379231892803811185 68955071534423919602858389)
                ·
                  refine ⟨3232268978176121231383987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 68955071534423919602858389 3232268978176121231383987)
                  ·
                    refine ⟨4848403467264181847075981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3232268978176121231383987 4848403467264181847075981)
                    ·
                      refine ⟨1818151300224068192653493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4848403467264181847075981 1818151300224068192653493)
                      ·
                        rfl

theorem cell23_3540837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 6, 1, 3].length) (baseStart_3540837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3540837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3540837 prefixEnd_3540837 := by exact prefixLift 3540837
  have htrace : WordTrace (prefixWord ++ tailWord_3540837) baseStart_3540837 baseEnd_3540837 := by
    simpa [prefixWord, tailWord_3540837, baseEnd_3540837] using wordTrace_append hprefix tailTrace_3540837
  have hstable : (prefixWord ++ tailWord_3540837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540837).length < 2 ^ (prefixWord ++ tailWord_3540837).sum := by decide
  have hdescent : baseEnd_3540837 < baseStart_3540837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540840 : List Nat := [2, 1, 4, 2, 1, 1, 1, 2, 2, 7]
def baseStart_3540840 : Nat := 118140960795 + 3540840 * 2 ^ 59
def prefixEnd_3540840 : Nat := 4983230072969 + 3 ^ 40 * 3540840 * 2
def baseEnd_3540840 : Nat := 606050946888677226971993

theorem tailTrace_3540840 : CollatzResearch.WordTrace tailWord_3540840 prefixEnd_3540840 606050946888677226971993 := by
  unfold tailWord_3540840
  simp only [CollatzResearch.WordTrace]
  refine ⟨64572522246074441086153987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86096696328099254781538649 64572522246074441086153987)
  ·
    refine ⟨96858783369111661629230981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64572522246074441086153987 96858783369111661629230981)
    ·
      refine ⟨18161021881708436555480809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96858783369111661629230981 18161021881708436555480809)
      ·
        refine ⟨13620766411281327416610607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18161021881708436555480809 13620766411281327416610607)
        ·
          refine ⟨20431149616921991124915911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13620766411281327416610607 20431149616921991124915911)
          ·
            refine ⟨30646724425382986687373867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20431149616921991124915911 30646724425382986687373867)
            ·
              refine ⟨45970086638074480031060801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30646724425382986687373867 45970086638074480031060801)
              ·
                refine ⟨34477564978555860023295601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45970086638074480031060801 34477564978555860023295601)
                ·
                  refine ⟨25858173733916895017471701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34477564978555860023295601 25858173733916895017471701)
                  ·
                    refine ⟨606050946888677226971993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25858173733916895017471701 606050946888677226971993)
                    ·
                      rfl

theorem cell23_3540840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_3540840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3540840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3540840 prefixEnd_3540840 := by exact prefixLift 3540840
  have htrace : WordTrace (prefixWord ++ tailWord_3540840) baseStart_3540840 baseEnd_3540840 := by
    simpa [prefixWord, tailWord_3540840, baseEnd_3540840] using wordTrace_append hprefix tailTrace_3540840
  have hstable : (prefixWord ++ tailWord_3540840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540840).length < 2 ^ (prefixWord ++ tailWord_3540840).sum := by decide
  have hdescent : baseEnd_3540840 < baseStart_3540840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540850 : List Nat := [3, 2, 1, 2, 1, 1, 1, 3, 2, 2, 5]
def baseStart_3540850 : Nat := 118140960795 + 3540850 * 2 ^ 59
def prefixEnd_3540850 : Nat := 4983230072969 + 3 ^ 40 * 3540850 * 2
def baseEnd_3540850 : Nat := 1818157975472576641790933

theorem tailTrace_3540850 : CollatzResearch.WordTrace tailWord_3540850 prefixEnd_3540850 1818157975472576641790933 := by
  unfold tailWord_3540850
  simp only [CollatzResearch.WordTrace]
  refine ⟨32286352305528163470043001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86096939481408435920114669 32286352305528163470043001)
  ·
    refine ⟨24214764229146122602532251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32286352305528163470043001 24214764229146122602532251)
    ·
      refine ⟨36322146343719183903798377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24214764229146122602532251 36322146343719183903798377)
      ·
        refine ⟨27241609757789387927848783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36322146343719183903798377 27241609757789387927848783)
        ·
          refine ⟨40862414636684081891773175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27241609757789387927848783 40862414636684081891773175)
          ·
            refine ⟨61293621955026122837659763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40862414636684081891773175 61293621955026122837659763)
            ·
              refine ⟨91940432932539184256489645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61293621955026122837659763 91940432932539184256489645)
              ·
                refine ⟨34477662349702194096183617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91940432932539184256489645 34477662349702194096183617)
                ·
                  refine ⟨25858246762276645572137713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34477662349702194096183617 25858246762276645572137713)
                  ·
                    refine ⟨19393685071707484179103285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25858246762276645572137713 19393685071707484179103285)
                    ·
                      refine ⟨1818157975472576641790933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19393685071707484179103285 1818157975472576641790933)
                      ·
                        rfl

theorem cell23_3540850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_3540850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3540850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3540850 prefixEnd_3540850 := by exact prefixLift 3540850
  have htrace : WordTrace (prefixWord ++ tailWord_3540850) baseStart_3540850 baseEnd_3540850 := by
    simpa [prefixWord, tailWord_3540850, baseEnd_3540850] using wordTrace_append hprefix tailTrace_3540850
  have hstable : (prefixWord ++ tailWord_3540850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540850).length < 2 ^ (prefixWord ++ tailWord_3540850).sum := by decide
  have hdescent : baseEnd_3540850 < baseStart_3540850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540864 : List Nat := [2, 1, 1, 2, 1, 2, 5, 3, 1, 3, 2]
def baseStart_3540864 : Nat := 118140960795 + 3540864 * 2 ^ 59
def prefixEnd_3540864 : Nat := 4983230072969 + 3 ^ 40 * 3540864 * 2
def baseEnd_3540864 : Nat := 1818165164201739587015869

theorem tailTrace_3540864 : CollatzResearch.WordTrace tailWord_3540864 prefixEnd_3540864 1818165164201739587015869 := by
  unfold tailWord_3540864
  simp only [CollatzResearch.WordTrace]
  refine ⟨64572959922030967135590823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86097279896041289514121097 64572959922030967135590823)
  ·
    refine ⟨96859439883046450703386235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64572959922030967135590823 96859439883046450703386235)
    ·
      refine ⟨145289159824569676055079353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96859439883046450703386235 145289159824569676055079353)
      ·
        refine ⟨108966869868427257041309515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145289159824569676055079353 108966869868427257041309515)
        ·
          refine ⟨163450304802640885561964273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108966869868427257041309515 163450304802640885561964273)
          ·
            refine ⟨122587728601980664171473205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163450304802640885561964273 122587728601980664171473205)
            ·
              refine ⟨11492599556435687266075613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 122587728601980664171473205 11492599556435687266075613)
              ·
                refine ⟨4309724833663382724778355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11492599556435687266075613 4309724833663382724778355)
                ·
                  refine ⟨6464587250495074087167533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4309724833663382724778355 6464587250495074087167533)
                  ·
                    refine ⟨2424220218935652782687825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6464587250495074087167533 2424220218935652782687825)
                    ·
                      refine ⟨1818165164201739587015869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2424220218935652782687825 1818165164201739587015869)
                      ·
                        rfl

theorem cell23_3540864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 3, 1, 3, 2].length) (baseStart_3540864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3540864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3540864 prefixEnd_3540864 := by exact prefixLift 3540864
  have htrace : WordTrace (prefixWord ++ tailWord_3540864) baseStart_3540864 baseEnd_3540864 := by
    simpa [prefixWord, tailWord_3540864, baseEnd_3540864] using wordTrace_append hprefix tailTrace_3540864
  have hstable : (prefixWord ++ tailWord_3540864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540864).length < 2 ^ (prefixWord ++ tailWord_3540864).sum := by decide
  have hdescent : baseEnd_3540864 < baseStart_3540864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540888 : List Nat := [2, 1, 2, 6, 2, 1, 1, 1, 1, 3, 3]
def baseStart_3540888 : Nat := 118140960795 + 3540888 * 2 ^ 59
def prefixEnd_3540888 : Nat := 4983230072969 + 3 ^ 40 * 3540888 * 2
def baseEnd_3540888 : Nat := 1818177487737447493115759

theorem tailTrace_3540888 : CollatzResearch.WordTrace tailWord_3540888 prefixEnd_3540888 1818177487737447493115759 := by
  unfold tailWord_3540888
  simp only [CollatzResearch.WordTrace]
  refine ⟨64573397597987493185027659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86097863463983324246703545 64573397597987493185027659)
  ·
    refine ⟨96860096396981239777541489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64573397597987493185027659 96860096396981239777541489)
    ·
      refine ⟨72645072297735929833156117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96860096396981239777541489 72645072297735929833156117)
      ·
        refine ⟨3405237763956371710929193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 72645072297735929833156117 3405237763956371710929193)
        ·
          refine ⟨2553928322967278783196895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3405237763956371710929193 2553928322967278783196895)
          ·
            refine ⟨3830892484450918174795343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2553928322967278783196895 3830892484450918174795343)
            ·
              refine ⟨5746338726676377262193015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3830892484450918174795343 5746338726676377262193015)
              ·
                refine ⟨8619508090014565893289523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5746338726676377262193015 8619508090014565893289523)
                ·
                  refine ⟨12929262135021848839934285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8619508090014565893289523 12929262135021848839934285)
                  ·
                    refine ⟨4848473300633193314975357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12929262135021848839934285 4848473300633193314975357)
                    ·
                      refine ⟨1818177487737447493115759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4848473300633193314975357 1818177487737447493115759)
                      ·
                        rfl

theorem cell23_3540888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_3540888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3540888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3540888 prefixEnd_3540888 := by exact prefixLift 3540888
  have htrace : WordTrace (prefixWord ++ tailWord_3540888) baseStart_3540888 baseEnd_3540888 := by
    simpa [prefixWord, tailWord_3540888, baseEnd_3540888] using wordTrace_append hprefix tailTrace_3540888
  have hstable : (prefixWord ++ tailWord_3540888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540888).length < 2 ^ (prefixWord ++ tailWord_3540888).sum := by decide
  have hdescent : baseEnd_3540888 < baseStart_3540888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540898 : List Nat := [3, 3, 1, 2, 3, 1, 2, 2, 1, 3, 2]
def baseStart_3540898 : Nat := 118140960795 + 3540898 * 2 ^ 59
def prefixEnd_3540898 : Nat := 4983230072969 + 3 ^ 40 * 3540898 * 2
def baseEnd_3540898 : Nat := 1818182622543992453990713

theorem tailTrace_3540898 : CollatzResearch.WordTrace tailWord_3540898 prefixEnd_3540898 1818182622543992453990713 := by
  unfold tailWord_3540898
  simp only [CollatzResearch.WordTrace]
  refine ⟨32286789981484689519479837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86098106617292505385279565 32286789981484689519479837)
  ·
    refine ⟨12107546243056758569804939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32286789981484689519479837 12107546243056758569804939)
    ·
      refine ⟨18161319364585137854707409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12107546243056758569804939 18161319364585137854707409)
      ·
        refine ⟨13620989523438853391030557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18161319364585137854707409 13620989523438853391030557)
        ·
          refine ⟨5107871071289570021636459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13620989523438853391030557 5107871071289570021636459)
          ·
            refine ⟨7661806606934355032454689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5107871071289570021636459 7661806606934355032454689)
            ·
              refine ⟨5746354955200766274341017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7661806606934355032454689 5746354955200766274341017)
              ·
                refine ⟨4309766216400574705755763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5746354955200766274341017 4309766216400574705755763)
                ·
                  refine ⟨6464649324600862058633645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4309766216400574705755763 6464649324600862058633645)
                  ·
                    refine ⟨2424243496725323271987617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6464649324600862058633645 2424243496725323271987617)
                    ·
                      refine ⟨1818182622543992453990713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2424243496725323271987617 1818182622543992453990713)
                      ·
                        rfl

theorem cell23_3540898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 2, 1, 3, 2].length) (baseStart_3540898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3540898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3540898 prefixEnd_3540898 := by exact prefixLift 3540898
  have htrace : WordTrace (prefixWord ++ tailWord_3540898) baseStart_3540898 baseEnd_3540898 := by
    simpa [prefixWord, tailWord_3540898, baseEnd_3540898] using wordTrace_append hprefix tailTrace_3540898
  have hstable : (prefixWord ++ tailWord_3540898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540898).length < 2 ^ (prefixWord ++ tailWord_3540898).sum := by decide
  have hdescent : baseEnd_3540898 < baseStart_3540898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540937 : List Nat := [1, 2, 1, 1, 2, 1, 2, 3, 1, 7, 2]
def baseStart_3540937 : Nat := 118140960795 + 3540937 * 2 ^ 59
def prefixEnd_3540937 : Nat := 4983230072969 + 3 ^ 40 * 3540937 * 2
def baseEnd_3540937 : Nat := 1818202648289517801403033

theorem tailTrace_3540937 : CollatzResearch.WordTrace tailWord_3540937 prefixEnd_3540937 1818202648289517801403033 := by
  unfold tailWord_3540937
  simp only [CollatzResearch.WordTrace]
  refine ⟨129148582372797467738589065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86099054915198311825726043 129148582372797467738589065)
  ·
    refine ⟨96861436779598100803941799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129148582372797467738589065 96861436779598100803941799)
    ·
      refine ⟨145292155169397151205912699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96861436779598100803941799 145292155169397151205912699)
      ·
        refine ⟨217938232754095726808869049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145292155169397151205912699 217938232754095726808869049)
        ·
          refine ⟨163453674565571795106651787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217938232754095726808869049 163453674565571795106651787)
          ·
            refine ⟨245180511848357692659977681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163453674565571795106651787 245180511848357692659977681)
            ·
              refine ⟨183885383886268269494983261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 245180511848357692659977681 183885383886268269494983261)
              ·
                refine ⟨68957018957350601060618723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 183885383886268269494983261 68957018957350601060618723)
                ·
                  refine ⟨103435528436025901590928085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68957018957350601060618723 103435528436025901590928085)
                  ·
                    refine ⟨2424270197719357068537377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 103435528436025901590928085 2424270197719357068537377)
                    ·
                      refine ⟨1818202648289517801403033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2424270197719357068537377 1818202648289517801403033)
                      ·
                        rfl

theorem cell23_3540937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 7, 2].length) (baseStart_3540937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3540937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3540937 prefixEnd_3540937 := by exact prefixLift 3540937
  have htrace : WordTrace (prefixWord ++ tailWord_3540937) baseStart_3540937 baseEnd_3540937 := by
    simpa [prefixWord, tailWord_3540937, baseEnd_3540937] using wordTrace_append hprefix tailTrace_3540937
  have hstable : (prefixWord ++ tailWord_3540937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540937).length < 2 ^ (prefixWord ++ tailWord_3540937).sum := by decide
  have hdescent : baseEnd_3540937 < baseStart_3540937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540960 : List Nat := [2, 1, 1, 3, 1, 1, 1, 3, 2, 8]
def baseStart_3540960 : Nat := 118140960795 + 3540960 * 2 ^ 59
def prefixEnd_3540960 : Nat := 4983230072969 + 3 ^ 40 * 3540960 * 2
def baseEnd_3540960 : Nat := 606071486114857070471809

theorem tailTrace_3540960 : CollatzResearch.WordTrace tailWord_3540960 prefixEnd_3540960 606071486114857070471809 := by
  unfold tailWord_3540960
  simp only [CollatzResearch.WordTrace]
  refine ⟨64574710625857071333338167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86099614167809428444450889 64574710625857071333338167)
  ·
    refine ⟨96862065938785607000007251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64574710625857071333338167 96862065938785607000007251)
    ·
      refine ⟨145293098908178410500010877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96862065938785607000007251 145293098908178410500010877)
      ·
        refine ⟨54484912090566903937504079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145293098908178410500010877 54484912090566903937504079)
        ·
          refine ⟨81727368135850355906256119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54484912090566903937504079 81727368135850355906256119)
          ·
            refine ⟨122591052203775533859384179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81727368135850355906256119 122591052203775533859384179)
            ·
              refine ⟨183886578305663300789076269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122591052203775533859384179 183886578305663300789076269)
              ·
                refine ⟨68957466864623737795903601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 183886578305663300789076269 68957466864623737795903601)
                ·
                  refine ⟨51718100148467803346927701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68957466864623737795903601 51718100148467803346927701)
                  ·
                    refine ⟨606071486114857070471809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 51718100148467803346927701 606071486114857070471809)
                    ·
                      rfl

theorem cell23_3540960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 2, 8].length) (baseStart_3540960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3540960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3540960 prefixEnd_3540960 := by exact prefixLift 3540960
  have htrace : WordTrace (prefixWord ++ tailWord_3540960) baseStart_3540960 baseEnd_3540960 := by
    simpa [prefixWord, tailWord_3540960, baseEnd_3540960] using wordTrace_append hprefix tailTrace_3540960
  have hstable : (prefixWord ++ tailWord_3540960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540960).length < 2 ^ (prefixWord ++ tailWord_3540960).sum := by decide
  have hdescent : baseEnd_3540960 < baseStart_3540960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541021 : List Nat := [1, 4, 2, 2, 2, 1, 3, 1, 2, 2, 3]
def baseStart_3541021 : Nat := 118140960795 + 3541021 * 2 ^ 59
def prefixEnd_3541021 : Nat := 4983230072969 + 3 ^ 40 * 3541021 * 2
def baseEnd_3541021 : Nat := 1818245780664495472752647

theorem tailTrace_3541021 : CollatzResearch.WordTrace tailWord_3541021 prefixEnd_3541021 1818245780664495472752647 := by
  unfold tailWord_3541021
  simp only [CollatzResearch.WordTrace]
  refine ⟨129151646104493150084646917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86101097402995433389764611 129151646104493150084646917)
  ·
    refine ⟨24215933644592465640871297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129151646104493150084646917 24215933644592465640871297)
    ·
      refine ⟨18161950233444349230653473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24215933644592465640871297 18161950233444349230653473)
      ·
        refine ⟨13621462675083261922990105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18161950233444349230653473 13621462675083261922990105)
        ·
          refine ⟨10216097006312446442242579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13621462675083261922990105 10216097006312446442242579)
          ·
            refine ⟨15324145509468669663363869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10216097006312446442242579 15324145509468669663363869)
            ·
              refine ⟨5746554566050751123761451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15324145509468669663363869 5746554566050751123761451)
              ·
                refine ⟨8619831849076126685642177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5746554566050751123761451 8619831849076126685642177)
                ·
                  refine ⟨6464873886807095014231633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8619831849076126685642177 6464873886807095014231633)
                  ·
                    refine ⟨4848655415105321260673725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6464873886807095014231633 4848655415105321260673725)
                    ·
                      refine ⟨1818245780664495472752647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4848655415105321260673725 1818245780664495472752647)
                      ·
                        rfl

theorem cell23_3541021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_3541021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3541021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3541021 prefixEnd_3541021 := by exact prefixLift 3541021
  have htrace : WordTrace (prefixWord ++ tailWord_3541021) baseStart_3541021 baseEnd_3541021 := by
    simpa [prefixWord, tailWord_3541021, baseEnd_3541021] using wordTrace_append hprefix tailTrace_3541021
  have hstable : (prefixWord ++ tailWord_3541021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541021).length < 2 ^ (prefixWord ++ tailWord_3541021).sum := by decide
  have hdescent : baseEnd_3541021 < baseStart_3541021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541091 : List Nat := [1, 1, 1, 5, 1, 1, 2, 2, 5, 2, 2]
def baseStart_3541091 : Nat := 118140960795 + 3541091 * 2 ^ 59
def prefixEnd_3541091 : Nat := 4983230072969 + 3 ^ 40 * 3541091 * 2
def baseEnd_3541091 : Nat := 1818281724310310198877325

theorem tailTrace_3541091 : CollatzResearch.WordTrace tailWord_3541091 prefixEnd_3541091 1818281724310310198877325 := by
  unfold tailWord_3541091
  simp only [CollatzResearch.WordTrace]
  refine ⟨129154199214239552039695127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86102799476159701359796751 129154199214239552039695127)
  ·
    refine ⟨193731298821359328059542691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129154199214239552039695127 193731298821359328059542691)
    ·
      refine ⟨290596948232038992089314037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193731298821359328059542691 290596948232038992089314037)
      ·
        refine ⟨27243463896753655508373191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 290596948232038992089314037 27243463896753655508373191)
        ·
          refine ⟨40865195845130483262559787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27243463896753655508373191 40865195845130483262559787)
          ·
            refine ⟨61297793767695724893839681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40865195845130483262559787 61297793767695724893839681)
            ·
              refine ⟨45973345325771793670379761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61297793767695724893839681 45973345325771793670379761)
              ·
                refine ⟨34480008994328845252784821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45973345325771793670379761 34480008994328845252784821)
                ·
                  refine ⟨3232500843218329242448577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34480008994328845252784821 3232500843218329242448577)
                  ·
                    refine ⟨2424375632413746931836433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3232500843218329242448577 2424375632413746931836433)
                    ·
                      refine ⟨1818281724310310198877325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2424375632413746931836433 1818281724310310198877325)
                      ·
                        rfl

theorem cell23_3541091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 5, 2, 2].length) (baseStart_3541091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3541091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3541091 prefixEnd_3541091 := by exact prefixLift 3541091
  have htrace : WordTrace (prefixWord ++ tailWord_3541091) baseStart_3541091 baseEnd_3541091 := by
    simpa [prefixWord, tailWord_3541091, baseEnd_3541091] using wordTrace_append hprefix tailTrace_3541091
  have hstable : (prefixWord ++ tailWord_3541091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541091).length < 2 ^ (prefixWord ++ tailWord_3541091).sum := by decide
  have hdescent : baseEnd_3541091 < baseStart_3541091 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541101 : List Nat := [1, 5, 1, 1, 2, 1, 2, 4, 2, 4]
def baseStart_3541101 : Nat := 118140960795 + 3541101 * 2 ^ 59
def prefixEnd_3541101 : Nat := 4983230072969 + 3 ^ 40 * 3541101 * 2
def baseEnd_3541101 : Nat := 606095619705618386584093

theorem tailTrace_3541101 : CollatzResearch.WordTrace tailWord_3541101 prefixEnd_3541101 606095619705618386584093 := by
  unfold tailWord_3541101
  simp only [CollatzResearch.WordTrace]
  refine ⟨129154563944203323747559157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86103042629468882498372771 129154563944203323747559157)
  ·
    refine ⟨12108240369769061601333671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 129154563944203323747559157 12108240369769061601333671)
    ·
      refine ⟨18162360554653592402000507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12108240369769061601333671 18162360554653592402000507)
      ·
        refine ⟨27243540831980388603000761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18162360554653592402000507 27243540831980388603000761)
        ·
          refine ⟨20432655623985291452250571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27243540831980388603000761 20432655623985291452250571)
          ·
            refine ⟨30648983435977937178375857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20432655623985291452250571 30648983435977937178375857)
            ·
              refine ⟨22986737576983452883781893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30648983435977937178375857 22986737576983452883781893)
              ·
                refine ⟨4310013295684397415709105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22986737576983452883781893 4310013295684397415709105)
                ·
                  refine ⟨3232509971763298061781829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4310013295684397415709105 3232509971763298061781829)
                  ·
                    refine ⟨606095619705618386584093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3232509971763298061781829 606095619705618386584093)
                    ·
                      rfl

theorem cell23_3541101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 4, 2, 4].length) (baseStart_3541101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3541101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3541101 prefixEnd_3541101 := by exact prefixLift 3541101
  have htrace : WordTrace (prefixWord ++ tailWord_3541101) baseStart_3541101 baseEnd_3541101 := by
    simpa [prefixWord, tailWord_3541101, baseEnd_3541101] using wordTrace_append hprefix tailTrace_3541101
  have hstable : (prefixWord ++ tailWord_3541101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541101).length < 2 ^ (prefixWord ++ tailWord_3541101).sum := by decide
  have hdescent : baseEnd_3541101 < baseStart_3541101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541128 : List Nat := [2, 1, 3, 4, 1, 1, 3, 2, 1, 2, 3]
def baseStart_3541128 : Nat := 118140960795 + 3541128 * 2 ^ 59
def prefixEnd_3541128 : Nat := 4983230072969 + 3 ^ 40 * 3541128 * 2
def baseEnd_3541128 : Nat := 1818300723094526554114655

theorem tailTrace_3541128 : CollatzResearch.WordTrace tailWord_3541128 prefixEnd_3541128 1818300723094526554114655 := by
  unfold tailWord_3541128
  simp only [CollatzResearch.WordTrace]
  refine ⟨64577774357552753679396019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86103699143403671572528025 64577774357552753679396019)
  ·
    refine ⟨96866661536329130519094029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64577774357552753679396019 96866661536329130519094029)
    ·
      refine ⟨36324998076123423944660261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96866661536329130519094029 36324998076123423944660261)
      ·
        refine ⟨6810937139273141989623799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36324998076123423944660261 6810937139273141989623799)
        ·
          refine ⟨10216405708909712984435699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6810937139273141989623799 10216405708909712984435699)
          ·
            refine ⟨15324608563364569476653549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10216405708909712984435699 15324608563364569476653549)
            ·
              refine ⟨5746728211261713553745081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15324608563364569476653549 5746728211261713553745081)
              ·
                refine ⟨4310046158446285165308811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5746728211261713553745081 4310046158446285165308811)
                ·
                  refine ⟨6465069237669427747963217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4310046158446285165308811 6465069237669427747963217)
                  ·
                    refine ⟨4848801928252070810972413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6465069237669427747963217 4848801928252070810972413)
                    ·
                      refine ⟨1818300723094526554114655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4848801928252070810972413 1818300723094526554114655)
                      ·
                        rfl

theorem cell23_3541128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_3541128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3541128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3541128 prefixEnd_3541128 := by exact prefixLift 3541128
  have htrace : WordTrace (prefixWord ++ tailWord_3541128) baseStart_3541128 baseEnd_3541128 := by
    simpa [prefixWord, tailWord_3541128, baseEnd_3541128] using wordTrace_append hprefix tailTrace_3541128
  have hstable : (prefixWord ++ tailWord_3541128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541128).length < 2 ^ (prefixWord ++ tailWord_3541128).sum := by decide
  have hdescent : baseEnd_3541128 < baseStart_3541128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541172 : List Nat := [2, 5, 3, 1, 1, 1, 2, 1, 1, 2, 4]
def baseStart_3541172 : Nat := 118140960795 + 3541172 * 2 ^ 59
def prefixEnd_3541172 : Nat := 4983230072969 + 3 ^ 40 * 3541172 * 2
def baseEnd_3541172 : Nat := 1818323316243324381964453

theorem tailTrace_3541172 : CollatzResearch.WordTrace tailWord_3541172 prefixEnd_3541172 1818323316243324381964453 := by
  unfold tailWord_3541172
  simp only [CollatzResearch.WordTrace]
  refine ⟨64578576763473051436696885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86104769017964068582262513 64578576763473051436696885)
  ·
    refine ⟨6054241571575598572190333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64578576763473051436696885 6054241571575598572190333)
    ·
      refine ⟨2270340589340849464571375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6054241571575598572190333 2270340589340849464571375)
      ·
        refine ⟨3405510884011274196857063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2270340589340849464571375 3405510884011274196857063)
        ·
          refine ⟨5108266326016911295285595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3405510884011274196857063 5108266326016911295285595)
          ·
            refine ⟨7662399489025366942928393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5108266326016911295285595 7662399489025366942928393)
            ·
              refine ⟨5746799616769025207196295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7662399489025366942928393 5746799616769025207196295)
              ·
                refine ⟨8620199425153537810794443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5746799616769025207196295 8620199425153537810794443)
                ·
                  refine ⟨12930299137730306716191665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8620199425153537810794443 12930299137730306716191665)
                  ·
                    refine ⟨9697724353297730037143749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12930299137730306716191665 9697724353297730037143749)
                    ·
                      refine ⟨1818323316243324381964453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9697724353297730037143749 1818323316243324381964453)
                      ·
                        rfl

theorem cell23_3541172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_3541172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3541172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3541172 prefixEnd_3541172 := by exact prefixLift 3541172
  have htrace : WordTrace (prefixWord ++ tailWord_3541172) baseStart_3541172 baseEnd_3541172 := by
    simpa [prefixWord, tailWord_3541172, baseEnd_3541172] using wordTrace_append hprefix tailTrace_3541172
  have hstable : (prefixWord ++ tailWord_3541172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541172).length < 2 ^ (prefixWord ++ tailWord_3541172).sum := by decide
  have hdescent : baseEnd_3541172 < baseStart_3541172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541194 : List Nat := [3, 1, 2, 1, 3, 1, 1, 2, 1, 4, 4]
def baseStart_3541194 : Nat := 118140960795 + 3541194 * 2 ^ 59
def prefixEnd_3541194 : Nat := 4983230072969 + 3 ^ 40 * 3541194 * 2
def baseEnd_3541194 : Nat := 1818334612817723295889351

theorem tailTrace_3541194 : CollatzResearch.WordTrace tailWord_3541194 prefixEnd_3541194 1818334612817723295889351 := by
  unfold tailWord_3541194
  simp only [CollatzResearch.WordTrace]
  refine ⟨32289488983216600157673659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86105303955244267087129757 32289488983216600157673659)
  ·
    refine ⟨48434233474824900236510489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32289488983216600157673659 48434233474824900236510489)
    ·
      refine ⟨36325675106118675177382867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48434233474824900236510489 36325675106118675177382867)
      ·
        refine ⟨54488512659178012766074301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36325675106118675177382867 54488512659178012766074301)
        ·
          refine ⟨20433192247191754787277863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54488512659178012766074301 20433192247191754787277863)
          ·
            refine ⟨30649788370787632180916795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20433192247191754787277863 30649788370787632180916795)
            ·
              refine ⟨45974682556181448271375193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30649788370787632180916795 45974682556181448271375193)
              ·
                refine ⟨34481011917136086203531395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45974682556181448271375193 34481011917136086203531395)
                ·
                  refine ⟨51721517875704129305297093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34481011917136086203531395 51721517875704129305297093)
                  ·
                    refine ⟨9697784601694524244743205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51721517875704129305297093 9697784601694524244743205)
                    ·
                      refine ⟨1818334612817723295889351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9697784601694524244743205 1818334612817723295889351)
                      ·
                        rfl

theorem cell23_3541194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 1, 4, 4].length) (baseStart_3541194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3541194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3541194 prefixEnd_3541194 := by exact prefixLift 3541194
  have htrace : WordTrace (prefixWord ++ tailWord_3541194) baseStart_3541194 baseEnd_3541194 := by
    simpa [prefixWord, tailWord_3541194, baseEnd_3541194] using wordTrace_append hprefix tailTrace_3541194
  have hstable : (prefixWord ++ tailWord_3541194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541194).length < 2 ^ (prefixWord ++ tailWord_3541194).sum := by decide
  have hdescent : baseEnd_3541194 < baseStart_3541194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541198 : List Nat := [4, 1, 1, 1, 4, 1, 2, 2, 1, 4, 2]
def baseStart_3541198 : Nat := 118140960795 + 3541198 * 2 ^ 59
def prefixEnd_3541198 : Nat := 4983230072969 + 3 ^ 40 * 3541198 * 2
def baseEnd_3541198 : Nat := 1818336666740341280239333

theorem tailTrace_3541198 : CollatzResearch.WordTrace tailWord_3541198 prefixEnd_3541198 1818336666740341280239333 := by
  unfold tailWord_3541198
  simp only [CollatzResearch.WordTrace]
  refine ⟨16144762728106488664230031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86105401216567939542560165 16144762728106488664230031)
  ·
    refine ⟨24217144092159732996345047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16144762728106488664230031 24217144092159732996345047)
    ·
      refine ⟨36325716138239599494517571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24217144092159732996345047 36325716138239599494517571)
      ·
        refine ⟨54488574207359399241776357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36325716138239599494517571 54488574207359399241776357)
        ·
          refine ⟨10216607663879887357833067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54488574207359399241776357 10216607663879887357833067)
          ·
            refine ⟨15324911495819831036749601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10216607663879887357833067 15324911495819831036749601)
            ·
              refine ⟨11493683621864873277562201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15324911495819831036749601 11493683621864873277562201)
              ·
                refine ⟨8620262716398654958171651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11493683621864873277562201 8620262716398654958171651)
                ·
                  refine ⟨12930394074597982437257477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8620262716398654958171651 12930394074597982437257477)
                  ·
                    refine ⟨2424448888987121706985777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12930394074597982437257477 2424448888987121706985777)
                    ·
                      refine ⟨1818336666740341280239333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2424448888987121706985777 1818336666740341280239333)
                      ·
                        rfl

theorem cell23_3541198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 2, 1, 4, 2].length) (baseStart_3541198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3541198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3541198 prefixEnd_3541198 := by exact prefixLift 3541198
  have htrace : WordTrace (prefixWord ++ tailWord_3541198) baseStart_3541198 baseEnd_3541198 := by
    simpa [prefixWord, tailWord_3541198, baseEnd_3541198] using wordTrace_append hprefix tailTrace_3541198
  have hstable : (prefixWord ++ tailWord_3541198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541198).length < 2 ^ (prefixWord ++ tailWord_3541198).sum := by decide
  have hdescent : baseEnd_3541198 < baseStart_3541198 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541202 : List Nat := [3, 2, 2, 2, 1, 4, 2, 1, 1, 3, 2]
def baseStart_3541202 : Nat := 118140960795 + 3541202 * 2 ^ 59
def prefixEnd_3541202 : Nat := 4983230072969 + 3 ^ 40 * 3541202 * 2
def baseEnd_3541202 : Nat := 1818338720662959264589315

theorem tailTrace_3541202 : CollatzResearch.WordTrace tailWord_3541202 prefixEnd_3541202 1818338720662959264589315 := by
  unfold tailWord_3541202
  simp only [CollatzResearch.WordTrace]
  refine ⟨32289561929209354499246465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86105498477891611997990573 32289561929209354499246465)
  ·
    refine ⟨24217171446907015874434849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32289561929209354499246465 24217171446907015874434849)
    ·
      refine ⟨18162878585180261905826137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24217171446907015874434849 18162878585180261905826137)
      ·
        refine ⟨13622158938885196429369603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18162878585180261905826137 13622158938885196429369603)
        ·
          refine ⟨20433238408327794644054405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13622158938885196429369603 20433238408327794644054405)
          ·
            refine ⟨3831232201561461495760201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20433238408327794644054405 3831232201561461495760201)
            ·
              refine ⟨2873424151171096121820151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3831232201561461495760201 2873424151171096121820151)
              ·
                refine ⟨4310136226756644182730227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2873424151171096121820151 4310136226756644182730227)
                ·
                  refine ⟨6465204340134966274095341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4310136226756644182730227 6465204340134966274095341)
                  ·
                    refine ⟨2424451627550612352785753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6465204340134966274095341 2424451627550612352785753)
                    ·
                      refine ⟨1818338720662959264589315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2424451627550612352785753 1818338720662959264589315)
                      ·
                        rfl

theorem cell23_3541202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 2, 1, 1, 3, 2].length) (baseStart_3541202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3541202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3541202 prefixEnd_3541202 := by exact prefixLift 3541202
  have htrace : WordTrace (prefixWord ++ tailWord_3541202) baseStart_3541202 baseEnd_3541202 := by
    simpa [prefixWord, tailWord_3541202, baseEnd_3541202] using wordTrace_append hprefix tailTrace_3541202
  have hstable : (prefixWord ++ tailWord_3541202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541202).length < 2 ^ (prefixWord ++ tailWord_3541202).sum := by decide
  have hdescent : baseEnd_3541202 < baseStart_3541202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541221 : List Nat := [1, 3, 1, 4, 2, 2, 2, 1, 7]
def baseStart_3541221 : Nat := 118140960795 + 3541221 * 2 ^ 59
def prefixEnd_3541221 : Nat := 4983230072969 + 3 ^ 40 * 3541221 * 2
def baseEnd_3541221 : Nat := 202038719643932743361303

theorem tailTrace_3541221 : CollatzResearch.WordTrace tailWord_3541221 prefixEnd_3541221 202038719643932743361303 := by
  unfold tailWord_3541221
  simp only [CollatzResearch.WordTrace]
  refine ⟨129158940703768584241927517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86105960469179056161285011 129158940703768584241927517)
  ·
    refine ⟨48434602763913219090722819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129158940703768584241927517 48434602763913219090722819)
    ·
      refine ⟨72651904145869828636084229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48434602763913219090722819 72651904145869828636084229)
      ·
        refine ⟨13622232027350592869265793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72651904145869828636084229 13622232027350592869265793)
        ·
          refine ⟨10216674020512944651949345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13622232027350592869265793 10216674020512944651949345)
          ·
            refine ⟨7662505515384708488962009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10216674020512944651949345 7662505515384708488962009)
            ·
              refine ⟨5746879136538531366721507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7662505515384708488962009 5746879136538531366721507)
              ·
                refine ⟨8620318704807797050082261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5746879136538531366721507 8620318704807797050082261)
                ·
                  refine ⟨202038719643932743361303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8620318704807797050082261 202038719643932743361303)
                  ·
                    rfl

theorem cell23_3541221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 1, 7].length) (baseStart_3541221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3541221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3541221 prefixEnd_3541221 := by exact prefixLift 3541221
  have htrace : WordTrace (prefixWord ++ tailWord_3541221) baseStart_3541221 baseEnd_3541221 := by
    simpa [prefixWord, tailWord_3541221, baseEnd_3541221] using wordTrace_append hprefix tailTrace_3541221
  have hstable : (prefixWord ++ tailWord_3541221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541221).length < 2 ^ (prefixWord ++ tailWord_3541221).sum := by decide
  have hdescent : baseEnd_3541221 < baseStart_3541221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541231 : List Nat := [1, 1, 2, 1, 6, 1, 2, 1, 2, 3, 3]
def baseStart_3541231 : Nat := 118140960795 + 3541231 * 2 ^ 59
def prefixEnd_3541231 : Nat := 4983230072969 + 3 ^ 40 * 3541231 * 2
def baseEnd_3541231 : Nat := 1818353611601939651126681

theorem tailTrace_3541231 : CollatzResearch.WordTrace tailWord_3541231 prefixEnd_3541231 1818353611601939651126681 := by
  unfold tailWord_3541231
  simp only [CollatzResearch.WordTrace]
  refine ⟨129159305433732355949791547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86106203622488237299861031 129159305433732355949791547)
  ·
    refine ⟨193738958150598533924687321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129159305433732355949791547 193738958150598533924687321)
    ·
      refine ⟨145304218612948900443515491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193738958150598533924687321 145304218612948900443515491)
      ·
        refine ⟨217956327919423350665273237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145304218612948900443515491 217956327919423350665273237)
        ·
          refine ⟨10216702871222969562434683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 217956327919423350665273237 10216702871222969562434683)
          ·
            refine ⟨15325054306834454343652025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10216702871222969562434683 15325054306834454343652025)
            ·
              refine ⟨11493790730125840757739019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15325054306834454343652025 11493790730125840757739019)
              ·
                refine ⟨17240686095188761136608529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11493790730125840757739019 17240686095188761136608529)
                ·
                  refine ⟨12930514571391570852456397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17240686095188761136608529 12930514571391570852456397)
                  ·
                    refine ⟨4848942964271839069671149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12930514571391570852456397 4848942964271839069671149)
                    ·
                      refine ⟨1818353611601939651126681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4848942964271839069671149 1818353611601939651126681)
                      ·
                        rfl

theorem cell23_3541231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 2, 3, 3].length) (baseStart_3541231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3541231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3541231 prefixEnd_3541231 := by exact prefixLift 3541231
  have htrace : WordTrace (prefixWord ++ tailWord_3541231) baseStart_3541231 baseEnd_3541231 := by
    simpa [prefixWord, tailWord_3541231, baseEnd_3541231] using wordTrace_append hprefix tailTrace_3541231
  have hstable : (prefixWord ++ tailWord_3541231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541231).length < 2 ^ (prefixWord ++ tailWord_3541231).sum := by decide
  have hdescent : baseEnd_3541231 < baseStart_3541231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541271 : List Nat := [1, 1, 3, 4, 1, 2, 1, 1, 4, 1, 4]
def baseStart_3541271 : Nat := 118140960795 + 3541271 * 2 ^ 59
def prefixEnd_3541271 : Nat := 4983230072969 + 3 ^ 40 * 3541271 * 2
def baseEnd_3541271 : Nat := 1818374150828119494626497

theorem tailTrace_3541271 : CollatzResearch.WordTrace tailWord_3541271 prefixEnd_3541271 1818374150828119494626497 := by
  unfold tailWord_3541271
  simp only [CollatzResearch.WordTrace]
  refine ⟨129160764353587442781247667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86107176235724961854165111 129160764353587442781247667)
  ·
    refine ⟨193741146530381164171871501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129160764353587442781247667 193741146530381164171871501)
    ·
      refine ⟨72652929948892936564451813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193741146530381164171871501 72652929948892936564451813)
      ·
        refine ⟨13622424365417425605834715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72652929948892936564451813 13622424365417425605834715)
        ·
          refine ⟨20433636548126138408752073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13622424365417425605834715 20433636548126138408752073)
          ·
            refine ⟨15325227411094603806564055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20433636548126138408752073 15325227411094603806564055)
            ·
              refine ⟨22987841116641905709846083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15325227411094603806564055 22987841116641905709846083)
              ·
                refine ⟨34481761674962858564769125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22987841116641905709846083 34481761674962858564769125)
                ·
                  refine ⟨6465330314055535980894211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34481761674962858564769125 6465330314055535980894211)
                  ·
                    refine ⟨9697995471083303971341317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6465330314055535980894211 9697995471083303971341317)
                    ·
                      refine ⟨1818374150828119494626497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9697995471083303971341317 1818374150828119494626497)
                      ·
                        rfl

theorem cell23_3541271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_3541271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3541271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3541271 prefixEnd_3541271 := by exact prefixLift 3541271
  have htrace : WordTrace (prefixWord ++ tailWord_3541271) baseStart_3541271 baseEnd_3541271 := by
    simpa [prefixWord, tailWord_3541271, baseEnd_3541271] using wordTrace_append hprefix tailTrace_3541271
  have hstable : (prefixWord ++ tailWord_3541271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541271).length < 2 ^ (prefixWord ++ tailWord_3541271).sum := by decide
  have hdescent : baseEnd_3541271 < baseStart_3541271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541278 : List Nat := [4, 3, 2, 1, 1, 1, 1, 1, 1, 1, 7]
def baseStart_3541278 : Nat := 118140960795 + 3541278 * 2 ^ 59
def prefixEnd_3541278 : Nat := 4983230072969 + 3 ^ 40 * 3541278 * 2
def baseEnd_3541278 : Nat := 1818377745192700967238965

theorem tailTrace_3541278 : CollatzResearch.WordTrace tailWord_3541278 prefixEnd_3541278 1818377745192700967238965 := by
  unfold tailWord_3541278
  simp only [CollatzResearch.WordTrace]
  refine ⟨16145127458070260372094061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86107346443041388651168325 16145127458070260372094061)
  ·
    refine ⟨6054422796776347639535273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16145127458070260372094061 6054422796776347639535273)
    ·
      refine ⟨4540817097582260729651455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6054422796776347639535273 4540817097582260729651455)
      ·
        refine ⟨6811225646373391094477183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4540817097582260729651455 6811225646373391094477183)
        ·
          refine ⟨10216838469560086641715775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6811225646373391094477183 10216838469560086641715775)
          ·
            refine ⟨15325257704340129962573663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10216838469560086641715775 15325257704340129962573663)
            ·
              refine ⟨22987886556510194943860495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15325257704340129962573663 22987886556510194943860495)
              ·
                refine ⟨34481829834765292415790743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22987886556510194943860495 34481829834765292415790743)
                ·
                  refine ⟨51722744752147938623686115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34481829834765292415790743 51722744752147938623686115)
                  ·
                    refine ⟨77584117128221907935529173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51722744752147938623686115 77584117128221907935529173)
                    ·
                      refine ⟨1818377745192700967238965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 77584117128221907935529173 1818377745192700967238965)
                      ·
                        rfl

theorem cell23_3541278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_3541278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3541278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3541278 prefixEnd_3541278 := by exact prefixLift 3541278
  have htrace : WordTrace (prefixWord ++ tailWord_3541278) baseStart_3541278 baseEnd_3541278 := by
    simpa [prefixWord, tailWord_3541278, baseEnd_3541278] using wordTrace_append hprefix tailTrace_3541278
  have hstable : (prefixWord ++ tailWord_3541278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541278).length < 2 ^ (prefixWord ++ tailWord_3541278).sum := by decide
  have hdescent : baseEnd_3541278 < baseStart_3541278 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541308 : List Nat := [2, 2, 2, 2, 1, 2, 4, 1, 2, 2, 3]
def baseStart_3541308 : Nat := 118140960795 + 3541308 * 2 ^ 59
def prefixEnd_3541308 : Nat := 4983230072969 + 3 ^ 40 * 3541308 * 2
def baseEnd_3541308 : Nat := 1818393149612335849863827

theorem tailTrace_3541308 : CollatzResearch.WordTrace tailWord_3541308 prefixEnd_3541308 1818393149612335849863827 := by
  unfold tailWord_3541308
  simp only [CollatzResearch.WordTrace]
  refine ⟨64581056927226699050172289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86108075902968932066896385 64581056927226699050172289)
  ·
    refine ⟨48435792695420024287629217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64581056927226699050172289 48435792695420024287629217)
    ·
      refine ⟨36326844521565018215721913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48435792695420024287629217 36326844521565018215721913)
      ·
        refine ⟨27245133391173763661791435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36326844521565018215721913 27245133391173763661791435)
        ·
          refine ⟨40867700086760645492687153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27245133391173763661791435 40867700086760645492687153)
          ·
            refine ⟨30650775065070484119515365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40867700086760645492687153 30650775065070484119515365)
            ·
              refine ⟨5747020324700715772409131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30650775065070484119515365 5747020324700715772409131)
              ·
                refine ⟨8620530487051073658613697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5747020324700715772409131 8620530487051073658613697)
                ·
                  refine ⟨6465397865288305243960273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8620530487051073658613697 6465397865288305243960273)
                  ·
                    refine ⟨4849048398966228932970205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6465397865288305243960273 4849048398966228932970205)
                    ·
                      refine ⟨1818393149612335849863827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4849048398966228932970205 1818393149612335849863827)
                      ·
                        rfl

theorem cell23_3541308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 1, 2, 2, 3].length) (baseStart_3541308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3541308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3541308 prefixEnd_3541308 := by exact prefixLift 3541308
  have htrace : WordTrace (prefixWord ++ tailWord_3541308) baseStart_3541308 baseEnd_3541308 := by
    simpa [prefixWord, tailWord_3541308, baseEnd_3541308] using wordTrace_append hprefix tailTrace_3541308
  have hstable : (prefixWord ++ tailWord_3541308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541308).length < 2 ^ (prefixWord ++ tailWord_3541308).sum := by decide
  have hdescent : baseEnd_3541308 < baseStart_3541308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541332 : List Nat := [2, 4, 1, 1, 2, 2, 4, 2, 1, 4]
def baseStart_3541332 : Nat := 118140960795 + 3541332 * 2 ^ 59
def prefixEnd_3541332 : Nat := 4983230072969 + 3 ^ 40 * 3541332 * 2
def baseEnd_3541332 : Nat := 606135157716014585321239

theorem tailTrace_3541332 : CollatzResearch.WordTrace tailWord_3541332 prefixEnd_3541332 606135157716014585321239 := by
  unfold tailWord_3541332
  simp only [CollatzResearch.WordTrace]
  refine ⟨64581494603183225099609125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86108659470910966799478833 64581494603183225099609125)
  ·
    refine ⟨12109030238096854706176711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64581494603183225099609125 12109030238096854706176711)
    ·
      refine ⟨18163545357145282059265067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12109030238096854706176711 18163545357145282059265067)
      ·
        refine ⟨27245318035717923088897601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18163545357145282059265067 27245318035717923088897601)
        ·
          refine ⟨20433988526788442316673201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27245318035717923088897601 20433988526788442316673201)
          ·
            refine ⟨15325491395091331737504901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20433988526788442316673201 15325491395091331737504901)
            ·
              refine ⟨2873529636579624700782169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15325491395091331737504901 2873529636579624700782169)
              ·
                refine ⟨2155147227434718525586627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2873529636579624700782169 2155147227434718525586627)
                ·
                  refine ⟨3232720841152077788379941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2155147227434718525586627 3232720841152077788379941)
                  ·
                    refine ⟨606135157716014585321239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3232720841152077788379941 606135157716014585321239)
                    ·
                      rfl

theorem cell23_3541332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 4, 2, 1, 4].length) (baseStart_3541332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3541332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3541332 prefixEnd_3541332 := by exact prefixLift 3541332
  have htrace : WordTrace (prefixWord ++ tailWord_3541332) baseStart_3541332 baseEnd_3541332 := by
    simpa [prefixWord, tailWord_3541332, baseEnd_3541332] using wordTrace_append hprefix tailTrace_3541332
  have hstable : (prefixWord ++ tailWord_3541332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541332).length < 2 ^ (prefixWord ++ tailWord_3541332).sum := by decide
  have hdescent : baseEnd_3541332 < baseStart_3541332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541338 : List Nat := [3, 1, 1, 2, 1, 2, 1, 5, 3, 1, 3]
def baseStart_3541338 : Nat := 118140960795 + 3541338 * 2 ^ 59
def prefixEnd_3541338 : Nat := 4983230072969 + 3 ^ 40 * 3541338 * 2
def baseEnd_3541338 : Nat := 1818408554031970732488689

theorem tailTrace_3541338 : CollatzResearch.WordTrace tailWord_3541338 prefixEnd_3541338 1818408554031970732488689 := by
  unfold tailWord_3541338
  simp only [CollatzResearch.WordTrace]
  refine ⟨32290802011086178305984167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86108805362896475482624445 32290802011086178305984167)
  ·
    refine ⟨48436203016629267458976251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32290802011086178305984167 48436203016629267458976251)
    ·
      refine ⟨72654304524943901188464377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48436203016629267458976251 72654304524943901188464377)
      ·
        refine ⟨54490728393707925891348283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72654304524943901188464377 54490728393707925891348283)
        ·
          refine ⟨81736092590561888837022425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54490728393707925891348283 81736092590561888837022425)
          ·
            refine ⟨61302069442921416627766819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81736092590561888837022425 61302069442921416627766819)
            ·
              refine ⟨91953104164382124941650229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61302069442921416627766819 91953104164382124941650229)
              ·
                refine ⟨8620603515410824213279709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91953104164382124941650229 8620603515410824213279709)
                ·
                  refine ⟨3232726318279059079979891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8620603515410824213279709 3232726318279059079979891)
                  ·
                    refine ⟨4849089477418588619969837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3232726318279059079979891 4849089477418588619969837)
                    ·
                      refine ⟨1818408554031970732488689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4849089477418588619969837 1818408554031970732488689)
                      ·
                        rfl

theorem cell23_3541338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 5, 3, 1, 3].length) (baseStart_3541338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3541338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3541338 prefixEnd_3541338 := by exact prefixLift 3541338
  have htrace : WordTrace (prefixWord ++ tailWord_3541338) baseStart_3541338 baseEnd_3541338 := by
    simpa [prefixWord, tailWord_3541338, baseEnd_3541338] using wordTrace_append hprefix tailTrace_3541338
  have hstable : (prefixWord ++ tailWord_3541338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541338).length < 2 ^ (prefixWord ++ tailWord_3541338).sum := by decide
  have hdescent : baseEnd_3541338 < baseStart_3541338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541348 : List Nat := [2, 3, 1, 1, 3, 1, 2, 2, 1, 5, 2]
def baseStart_3541348 : Nat := 118140960795 + 3541348 * 2 ^ 59
def prefixEnd_3541348 : Nat := 4983230072969 + 3 ^ 40 * 3541348 * 2
def baseEnd_3541348 : Nat := 1818413688838515693363643

theorem tailTrace_3541348 : CollatzResearch.WordTrace tailWord_3541348 prefixEnd_3541348 1818413688838515693363643 := by
  unfold tailWord_3541348
  simp only [CollatzResearch.WordTrace]
  refine ⟨64581786387154242465900349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86109048516205656621200465 64581786387154242465900349)
  ·
    refine ⟨24218169895182840924712631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64581786387154242465900349 24218169895182840924712631)
    ·
      refine ⟨36327254842774261387068947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24218169895182840924712631 36327254842774261387068947)
      ·
        refine ⟨54490882264161392080603421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36327254842774261387068947 54490882264161392080603421)
        ·
          refine ⟨20434080849060522030226283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54490882264161392080603421 20434080849060522030226283)
          ·
            refine ⟨30651121273590783045339425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20434080849060522030226283 30651121273590783045339425)
            ·
              refine ⟨22988340955193087284004569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30651121273590783045339425 22988340955193087284004569)
              ·
                refine ⟨17241255716394815463003427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22988340955193087284004569 17241255716394815463003427)
                ·
                  refine ⟨25861883574592223194505141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17241255716394815463003427 25861883574592223194505141)
                  ·
                    refine ⟨2424551585118020924484857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25861883574592223194505141 2424551585118020924484857)
                    ·
                      refine ⟨1818413688838515693363643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2424551585118020924484857 1818413688838515693363643)
                      ·
                        rfl

theorem cell23_3541348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 1, 5, 2].length) (baseStart_3541348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3541348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3541348 prefixEnd_3541348 := by exact prefixLift 3541348
  have htrace : WordTrace (prefixWord ++ tailWord_3541348) baseStart_3541348 baseEnd_3541348 := by
    simpa [prefixWord, tailWord_3541348, baseEnd_3541348] using wordTrace_append hprefix tailTrace_3541348
  have hstable : (prefixWord ++ tailWord_3541348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541348).length < 2 ^ (prefixWord ++ tailWord_3541348).sum := by decide
  have hdescent : baseEnd_3541348 < baseStart_3541348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541365 : List Nat := [1, 3, 4, 1, 2, 2, 1, 1, 1, 5, 2]
def baseStart_3541365 : Nat := 118140960795 + 3541365 * 2 ^ 59
def prefixEnd_3541365 : Nat := 4983230072969 + 3 ^ 40 * 3541365 * 2
def baseEnd_3541365 : Nat := 1818422418009642126851065

theorem tailTrace_3541365 : CollatzResearch.WordTrace tailWord_3541365 prefixEnd_3541365 1818422418009642126851065 := by
  unfold tailWord_3541365
  simp only [CollatzResearch.WordTrace]
  refine ⟨129164192815246896835169549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86109461876831264556779699 129164192815246896835169549)
  ·
    refine ⟨48436572305717586313188581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129164192815246896835169549 48436572305717586313188581)
    ·
      refine ⟨9081857307322047433722859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48436572305717586313188581 9081857307322047433722859)
      ·
        refine ⟨13622785960983071150584289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9081857307322047433722859 13622785960983071150584289)
        ·
          refine ⟨10217089470737303362938217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13622785960983071150584289 10217089470737303362938217)
          ·
            refine ⟨7662817103052977522203663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10217089470737303362938217 7662817103052977522203663)
            ·
              refine ⟨11494225654579466283305495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7662817103052977522203663 11494225654579466283305495)
              ·
                refine ⟨17241338481869199424958243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11494225654579466283305495 17241338481869199424958243)
                ·
                  refine ⟨25862007722803799137437365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17241338481869199424958243 25862007722803799137437365)
                  ·
                    refine ⟨2424563224012856169134753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25862007722803799137437365 2424563224012856169134753)
                    ·
                      refine ⟨1818422418009642126851065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2424563224012856169134753 1818422418009642126851065)
                      ·
                        rfl

theorem cell23_3541365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 5, 2].length) (baseStart_3541365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3541365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3541365 prefixEnd_3541365 := by exact prefixLift 3541365
  have htrace : WordTrace (prefixWord ++ tailWord_3541365) baseStart_3541365 baseEnd_3541365 := by
    simpa [prefixWord, tailWord_3541365, baseEnd_3541365] using wordTrace_append hprefix tailTrace_3541365
  have hstable : (prefixWord ++ tailWord_3541365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541365).length < 2 ^ (prefixWord ++ tailWord_3541365).sum := by decide
  have hdescent : baseEnd_3541365 < baseStart_3541365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541371 : List Nat := [1, 1, 1, 1, 1, 7, 2, 2, 1, 6]
def baseStart_3541371 : Nat := 118140960795 + 3541371 * 2 ^ 59
def prefixEnd_3541371 : Nat := 4983230072969 + 3 ^ 40 * 3541371 * 2
def baseEnd_3541371 : Nat := 606141832964523034458679

theorem tailTrace_3541371 : CollatzResearch.WordTrace tailWord_3541371 prefixEnd_3541371 606141832964523034458679 := by
  unfold tailWord_3541371
  simp only [CollatzResearch.WordTrace]
  refine ⟨129164411653225159859887967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86109607768816773239925311 129164411653225159859887967)
  ·
    refine ⟨193746617479837739789831951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129164411653225159859887967 193746617479837739789831951)
    ·
      refine ⟨290619926219756609684747927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193746617479837739789831951 290619926219756609684747927)
      ·
        refine ⟨435929889329634914527121891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290619926219756609684747927 435929889329634914527121891)
        ·
          refine ⟨653894833994452371790682837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 435929889329634914527121891 653894833994452371790682837)
          ·
            refine ⟨15325660171744977463844129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 653894833994452371790682837 15325660171744977463844129)
            ·
              refine ⟨11494245128808733097883097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15325660171744977463844129 11494245128808733097883097)
              ·
                refine ⟨8620683846606549823412323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11494245128808733097883097 8620683846606549823412323)
                ·
                  refine ⟨12931025769909824735118485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8620683846606549823412323 12931025769909824735118485)
                  ·
                    refine ⟨606141832964523034458679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12931025769909824735118485 606141832964523034458679)
                    ·
                      rfl

theorem cell23_3541371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 2, 1, 6].length) (baseStart_3541371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3541371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3541371 prefixEnd_3541371 := by exact prefixLift 3541371
  have htrace : WordTrace (prefixWord ++ tailWord_3541371) baseStart_3541371 baseEnd_3541371 := by
    simpa [prefixWord, tailWord_3541371, baseEnd_3541371] using wordTrace_append hprefix tailTrace_3541371
  have hstable : (prefixWord ++ tailWord_3541371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541371).length < 2 ^ (prefixWord ++ tailWord_3541371).sum := by decide
  have hdescent : baseEnd_3541371 < baseStart_3541371 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541381 : List Nat := [1, 3, 1, 1, 3, 1, 1, 5, 1, 1, 5]
def baseStart_3541381 : Nat := 118140960795 + 3541381 * 2 ^ 59
def prefixEnd_3541381 : Nat := 4983230072969 + 3 ^ 40 * 3541381 * 2
def baseEnd_3541381 : Nat := 1818430633700114064250991

theorem tailTrace_3541381 : CollatzResearch.WordTrace tailWord_3541381 prefixEnd_3541381 1818430633700114064250991 := by
  unfold tailWord_3541381
  simp only [CollatzResearch.WordTrace]
  refine ⟨129164776383188931567751997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86109850922125954378501331 129164776383188931567751997)
  ·
    refine ⟨48436791143695849337906999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129164776383188931567751997 48436791143695849337906999)
    ·
      refine ⟨72655186715543774006860499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48436791143695849337906999 72655186715543774006860499)
      ·
        refine ⟨108982780073315661010290749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72655186715543774006860499 108982780073315661010290749)
        ·
          refine ⟨40868542527493372878859031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108982780073315661010290749 40868542527493372878859031)
          ·
            refine ⟨61302813791240059318288547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40868542527493372878859031 61302813791240059318288547)
            ·
              refine ⟨91954220686860088977432821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61302813791240059318288547 91954220686860088977432821)
              ·
                refine ⟨8620708189393133341634327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91954220686860088977432821 8620708189393133341634327)
                ·
                  refine ⟨12931062284089700012451491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8620708189393133341634327 12931062284089700012451491)
                  ·
                    refine ⟨19396593426134550018677237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12931062284089700012451491 19396593426134550018677237)
                    ·
                      refine ⟨1818430633700114064250991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19396593426134550018677237 1818430633700114064250991)
                      ·
                        rfl

theorem cell23_3541381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 5, 1, 1, 5].length) (baseStart_3541381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3541381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3541381 prefixEnd_3541381 := by exact prefixLift 3541381
  have htrace : WordTrace (prefixWord ++ tailWord_3541381) baseStart_3541381 baseEnd_3541381 := by
    simpa [prefixWord, tailWord_3541381, baseEnd_3541381] using wordTrace_append hprefix tailTrace_3541381
  have hstable : (prefixWord ++ tailWord_3541381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541381).length < 2 ^ (prefixWord ++ tailWord_3541381).sum := by decide
  have hdescent : baseEnd_3541381 < baseStart_3541381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541388 : List Nat := [2, 2, 1, 2, 1, 5, 1, 1, 4, 4]
def baseStart_3541388 : Nat := 118140960795 + 3541388 * 2 ^ 59
def prefixEnd_3541388 : Nat := 4983230072969 + 3 ^ 40 * 3541388 * 2
def baseEnd_3541388 : Nat := 606144742688231845621153

theorem tailTrace_3541388 : CollatzResearch.WordTrace tailWord_3541388 prefixEnd_3541388 606144742688231845621153 := by
  unfold tailWord_3541388
  simp only [CollatzResearch.WordTrace]
  refine ⟨64582515847081785881628409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86110021129442381175504545 64582515847081785881628409)
  ·
    refine ⟨48436886885311339411221307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64582515847081785881628409 48436886885311339411221307)
    ·
      refine ⟨72655330327967009116831961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48436886885311339411221307 72655330327967009116831961)
      ·
        refine ⟨54491497745975256837623971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72655330327967009116831961 54491497745975256837623971)
        ·
          refine ⟨81737246618962885256435957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54491497745975256837623971 81737246618962885256435957)
          ·
            refine ⟨7662866870527770492790871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81737246618962885256435957 7662866870527770492790871)
            ·
              refine ⟨11494300305791655739186307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7662866870527770492790871 11494300305791655739186307)
              ·
                refine ⟨17241450458687483608779461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11494300305791655739186307 17241450458687483608779461)
                ·
                  refine ⟨3232771961003903176646149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17241450458687483608779461 3232771961003903176646149)
                  ·
                    refine ⟨606144742688231845621153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3232771961003903176646149 606144742688231845621153)
                    ·
                      rfl

theorem cell23_3541388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 4, 4].length) (baseStart_3541388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3541388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3541388 prefixEnd_3541388 := by exact prefixLift 3541388
  have htrace : WordTrace (prefixWord ++ tailWord_3541388) baseStart_3541388 baseEnd_3541388 := by
    simpa [prefixWord, tailWord_3541388, baseEnd_3541388] using wordTrace_append hprefix tailTrace_3541388
  have hstable : (prefixWord ++ tailWord_3541388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541388).length < 2 ^ (prefixWord ++ tailWord_3541388).sum := by decide
  have hdescent : baseEnd_3541388 < baseStart_3541388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541405 : List Nat := [1, 4, 2, 1, 4, 2, 1, 1, 1, 6]
def baseStart_3541405 : Nat := 118140960795 + 3541405 * 2 ^ 59
def prefixEnd_3541405 : Nat := 4983230072969 + 3 ^ 40 * 3541405 * 2
def baseEnd_3541405 : Nat := 606147652411940656783627

theorem tailTrace_3541405 : CollatzResearch.WordTrace tailWord_3541405 prefixEnd_3541405 606147652411940656783627 := by
  unfold tailWord_3541405
  simp only [CollatzResearch.WordTrace]
  refine ⟨129165651735101983666625669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86110434490067989111083779 129165651735101983666625669)
  ·
    refine ⟨24218559700331621937492313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129165651735101983666625669 24218559700331621937492313)
    ·
      refine ⟨18163919775248716453119235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24218559700331621937492313 18163919775248716453119235)
      ·
        refine ⟨27245879662873074679678853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18163919775248716453119235 27245879662873074679678853)
        ·
          refine ⟨5108602436788701502439785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27245879662873074679678853 5108602436788701502439785)
          ·
            refine ⟨3831451827591526126829839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5108602436788701502439785 3831451827591526126829839)
            ·
              refine ⟨5747177741387289190244759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3831451827591526126829839 5747177741387289190244759)
              ·
                refine ⟨8620766612080933785367139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5747177741387289190244759 8620766612080933785367139)
                ·
                  refine ⟨12931149918121400678050709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8620766612080933785367139 12931149918121400678050709)
                  ·
                    refine ⟨606147652411940656783627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12931149918121400678050709 606147652411940656783627)
                    ·
                      rfl

theorem cell23_3541405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 1, 1, 6].length) (baseStart_3541405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3541405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3541405 prefixEnd_3541405 := by exact prefixLift 3541405
  have htrace : WordTrace (prefixWord ++ tailWord_3541405) baseStart_3541405 baseEnd_3541405 := by
    simpa [prefixWord, tailWord_3541405, baseEnd_3541405] using wordTrace_append hprefix tailTrace_3541405
  have hstable : (prefixWord ++ tailWord_3541405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541405).length < 2 ^ (prefixWord ++ tailWord_3541405).sum := by decide
  have hdescent : baseEnd_3541405 < baseStart_3541405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541408 : List Nat := [2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 4]
def baseStart_3541408 : Nat := 118140960795 + 3541408 * 2 ^ 59
def prefixEnd_3541408 : Nat := 4983230072969 + 3 ^ 40 * 3541408 * 2
def baseEnd_3541408 : Nat := 1818444497677785458613367

theorem tailTrace_3541408 : CollatzResearch.WordTrace tailWord_3541408 prefixEnd_3541408 1818444497677785458613367 := by
  unfold tailWord_3541408
  simp only [CollatzResearch.WordTrace]
  refine ⟨64582880577045557589492439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86110507436060743452656585 64582880577045557589492439)
  ·
    refine ⟨96874320865568336384238659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64582880577045557589492439 96874320865568336384238659)
    ·
      refine ⟨145311481298352504576357989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96874320865568336384238659 145311481298352504576357989)
      ·
        refine ⟨27245902743441094608067123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145311481298352504576357989 27245902743441094608067123)
        ·
          refine ⟨40868854115161641912100685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27245902743441094608067123 40868854115161641912100685)
          ·
            refine ⟨15325820293185615717037757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40868854115161641912100685 15325820293185615717037757)
            ·
              refine ⟨5747182609944605893889159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15325820293185615717037757 5747182609944605893889159)
              ·
                refine ⟨8620773914916908840833739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5747182609944605893889159 8620773914916908840833739)
                ·
                  refine ⟨12931160872375363261250609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8620773914916908840833739 12931160872375363261250609)
                  ·
                    refine ⟨9698370654281522445937957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12931160872375363261250609 9698370654281522445937957)
                    ·
                      refine ⟨1818444497677785458613367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9698370654281522445937957 1818444497677785458613367)
                      ·
                        rfl

theorem cell23_3541408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 4].length) (baseStart_3541408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3541408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3541408 prefixEnd_3541408 := by exact prefixLift 3541408
  have htrace : WordTrace (prefixWord ++ tailWord_3541408) baseStart_3541408 baseEnd_3541408 := by
    simpa [prefixWord, tailWord_3541408, baseEnd_3541408] using wordTrace_append hprefix tailTrace_3541408
  have hstable : (prefixWord ++ tailWord_3541408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541408).length < 2 ^ (prefixWord ++ tailWord_3541408).sum := by decide
  have hdescent : baseEnd_3541408 < baseStart_3541408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541415 : List Nat := [1, 1, 6, 1, 1, 2, 1, 4, 1, 2, 3]
def baseStart_3541415 : Nat := 118140960795 + 3541415 * 2 ^ 59
def prefixEnd_3541415 : Nat := 4983230072969 + 3 ^ 40 * 3541415 * 2
def baseEnd_3541415 : Nat := 1818448092042366931225835

theorem tailTrace_3541415 : CollatzResearch.WordTrace tailWord_3541415 prefixEnd_3541415 1818448092042366931225835 := by
  unfold tailWord_3541415
  simp only [CollatzResearch.WordTrace]
  refine ⟨129166016465065755374489699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86110677643377170249659799 129166016465065755374489699)
  ·
    refine ⟨193749024697598633061734549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129166016465065755374489699 193749024697598633061734549)
    ·
      refine ⟨9081985532699935924768807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 193749024697598633061734549 9081985532699935924768807)
      ·
        refine ⟨13622978299049903887153211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9081985532699935924768807 13622978299049903887153211)
        ·
          refine ⟨20434467448574855830729817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13622978299049903887153211 20434467448574855830729817)
          ·
            refine ⟨15325850586431141873047363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20434467448574855830729817 15325850586431141873047363)
            ·
              refine ⟨22988775879646712809571045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15325850586431141873047363 22988775879646712809571045)
              ·
                refine ⟨4310395477433758651794571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22988775879646712809571045 4310395477433758651794571)
                ·
                  refine ⟨6465593216150637977691857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4310395477433758651794571 6465593216150637977691857)
                  ·
                    refine ⟨4849194912112978483268893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6465593216150637977691857 4849194912112978483268893)
                    ·
                      refine ⟨1818448092042366931225835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4849194912112978483268893 1818448092042366931225835)
                      ·
                        rfl

theorem cell23_3541415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_3541415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3541415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3541415 prefixEnd_3541415 := by exact prefixLift 3541415
  have htrace : WordTrace (prefixWord ++ tailWord_3541415) baseStart_3541415 baseEnd_3541415 := by
    simpa [prefixWord, tailWord_3541415, baseEnd_3541415] using wordTrace_append hprefix tailTrace_3541415
  have hstable : (prefixWord ++ tailWord_3541415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541415).length < 2 ^ (prefixWord ++ tailWord_3541415).sum := by decide
  have hdescent : baseEnd_3541415 < baseStart_3541415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541451 : List Nat := [1, 1, 1, 1, 3, 3, 1, 3, 2, 3, 4]
def baseStart_3541451 : Nat := 118140960795 + 3541451 * 2 ^ 59
def prefixEnd_3541451 : Nat := 4983230072969 + 3 ^ 40 * 3541451 * 2
def baseEnd_3541451 : Nat := 1818466577345928790375669

theorem tailTrace_3541451 : CollatzResearch.WordTrace tailWord_3541451 prefixEnd_3541451 1818466577345928790375669 := by
  unfold tailWord_3541451
  simp only [CollatzResearch.WordTrace]
  refine ⟨129167329492935333522800207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86111552995290222348533471 129167329492935333522800207)
  ·
    refine ⟨193750994239403000284200311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129167329492935333522800207 193750994239403000284200311)
    ·
      refine ⟨290626491359104500426300467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193750994239403000284200311 290626491359104500426300467)
      ·
        refine ⟨435939737038656750639450701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290626491359104500426300467 435939737038656750639450701)
        ·
          refine ⟨163477401389496281489794013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 435939737038656750639450701 163477401389496281489794013)
          ·
            refine ⟨61304025521061105558672755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163477401389496281489794013 61304025521061105558672755)
            ·
              refine ⟨91956038281591658338009133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61304025521061105558672755 91956038281591658338009133)
              ·
                refine ⟨34483514355596871876753425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91956038281591658338009133 34483514355596871876753425)
                ·
                  refine ⟨25862635766697653907565069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34483514355596871876753425 25862635766697653907565069)
                  ·
                    refine ⟨9698488412511620215336901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25862635766697653907565069 9698488412511620215336901)
                    ·
                      refine ⟨1818466577345928790375669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9698488412511620215336901 1818466577345928790375669)
                      ·
                        rfl

theorem cell23_3541451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 3, 4].length) (baseStart_3541451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3541451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3541451 prefixEnd_3541451 := by exact prefixLift 3541451
  have htrace : WordTrace (prefixWord ++ tailWord_3541451) baseStart_3541451 baseEnd_3541451 := by
    simpa [prefixWord, tailWord_3541451, baseEnd_3541451] using wordTrace_append hprefix tailTrace_3541451
  have hstable : (prefixWord ++ tailWord_3541451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541451).length < 2 ^ (prefixWord ++ tailWord_3541451).sum := by decide
  have hdescent : baseEnd_3541451 < baseStart_3541451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541481 : List Nat := [1, 2, 1, 1, 1, 2, 1, 3, 3, 4, 4]
def baseStart_3541481 : Nat := 118140960795 + 3541481 * 2 ^ 59
def prefixEnd_3541481 : Nat := 4983230072969 + 3 ^ 40 * 3541481 * 2
def baseEnd_3541481 : Nat := 1818481981765563673000531

theorem tailTrace_3541481 : CollatzResearch.WordTrace tailWord_3541481 prefixEnd_3541481 1818481981765563673000531 := by
  unfold tailWord_3541481
  simp only [CollatzResearch.WordTrace]
  refine ⟨129168423682826648646392297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86112282455217765764261531 129168423682826648646392297)
  ·
    refine ⟨96876317762119986484794223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129168423682826648646392297 96876317762119986484794223)
    ·
      refine ⟨145314476643179979727191335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96876317762119986484794223 145314476643179979727191335)
      ·
        refine ⟨217971714964769969590787003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145314476643179979727191335 217971714964769969590787003)
        ·
          refine ⟨326957572447154954386180505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217971714964769969590787003 326957572447154954386180505)
          ·
            refine ⟨245218179335366215789635379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 326957572447154954386180505 245218179335366215789635379)
            ·
              refine ⟨367827269003049323684453069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245218179335366215789635379 367827269003049323684453069)
              ·
                refine ⟨137935225876143496381669901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 367827269003049323684453069 137935225876143496381669901)
                ·
                  refine ⟨51725709703553811143126213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 137935225876143496381669901 51725709703553811143126213)
                  ·
                    refine ⟨9698570569416339589336165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51725709703553811143126213 9698570569416339589336165)
                    ·
                      refine ⟨1818481981765563673000531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9698570569416339589336165 1818481981765563673000531)
                      ·
                        rfl

theorem cell23_3541481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 4, 4].length) (baseStart_3541481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3541481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3541481 prefixEnd_3541481 := by exact prefixLift 3541481
  have htrace : WordTrace (prefixWord ++ tailWord_3541481) baseStart_3541481 baseEnd_3541481 := by
    simpa [prefixWord, tailWord_3541481, baseEnd_3541481] using wordTrace_append hprefix tailTrace_3541481
  have hstable : (prefixWord ++ tailWord_3541481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541481).length < 2 ^ (prefixWord ++ tailWord_3541481).sum := by decide
  have hdescent : baseEnd_3541481 < baseStart_3541481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541531 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 2, 6, 5]
def baseStart_3541531 : Nat := 118140960795 + 3541531 * 2 ^ 59
def prefixEnd_3541531 : Nat := 4983230072969 + 3 ^ 40 * 3541531 * 2
def baseEnd_3541531 : Nat := 1818507655798288477375301

theorem tailTrace_3541531 : CollatzResearch.WordTrace tailWord_3541531 prefixEnd_3541531 1818507655798288477375301 := by
  unfold tailWord_3541531
  simp only [CollatzResearch.WordTrace]
  refine ⟨129170247332645507185712447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86113498221763671457141631 129170247332645507185712447)
  ·
    refine ⟨193755370998968260778568671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129170247332645507185712447 193755370998968260778568671)
    ·
      refine ⟨290633056498452391167853007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193755370998968260778568671 290633056498452391167853007)
      ·
        refine ⟨435949584747678586751779511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290633056498452391167853007 435949584747678586751779511)
        ·
          refine ⟨653924377121517880127669267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 435949584747678586751779511 653924377121517880127669267)
          ·
            refine ⟨980886565682276820191503901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 653924377121517880127669267 980886565682276820191503901)
            ·
              refine ⟨367832462130853807571813963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 980886565682276820191503901 367832462130853807571813963)
              ·
                refine ⟨551748693196280711357720945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 367832462130853807571813963 551748693196280711357720945)
                ·
                  refine ⟨413811519897210533518290709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 551748693196280711357720945 413811519897210533518290709)
                  ·
                    refine ⟨19397414995181743758669877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 413811519897210533518290709 19397414995181743758669877)
                    ·
                      refine ⟨1818507655798288477375301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19397414995181743758669877 1818507655798288477375301)
                      ·
                        rfl

theorem cell23_3541531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 6, 5].length) (baseStart_3541531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3541531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3541531 prefixEnd_3541531 := by exact prefixLift 3541531
  have htrace : WordTrace (prefixWord ++ tailWord_3541531) baseStart_3541531 baseEnd_3541531 := by
    simpa [prefixWord, tailWord_3541531, baseEnd_3541531] using wordTrace_append hprefix tailTrace_3541531
  have hstable : (prefixWord ++ tailWord_3541531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541531).length < 2 ^ (prefixWord ++ tailWord_3541531).sum := by decide
  have hdescent : baseEnd_3541531 < baseStart_3541531 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541551 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 3, 10]
def baseStart_3541551 : Nat := 118140960795 + 3541551 * 2 ^ 59
def prefixEnd_3541551 : Nat := 4983230072969 + 3 ^ 40 * 3541551 * 2
def baseEnd_3541551 : Nat := 606172641803792799708403

theorem tailTrace_3541551 : CollatzResearch.WordTrace tailWord_3541551 prefixEnd_3541551 606172641803792799708403 := by
  unfold tailWord_3541551
  simp only [CollatzResearch.WordTrace]
  refine ⟨129170976792573050601440507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86113984528382033734293671 129170976792573050601440507)
  ·
    refine ⟨193756465188859575902160761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129170976792573050601440507 193756465188859575902160761)
    ·
      refine ⟨145317348891644681926620571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193756465188859575902160761 145317348891644681926620571)
      ·
        refine ⟨217976023337467022889930857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145317348891644681926620571 217976023337467022889930857)
        ·
          refine ⟨163482017503100267167448143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217976023337467022889930857 163482017503100267167448143)
          ·
            refine ⟨245223026254650400751172215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163482017503100267167448143 245223026254650400751172215)
            ·
              refine ⟨367834539381975601126758323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245223026254650400751172215 367834539381975601126758323)
              ·
                refine ⟨551751809072963401690137485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 367834539381975601126758323 551751809072963401690137485)
                ·
                  refine ⟨206906928402361275633801557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 551751809072963401690137485 206906928402361275633801557)
                  ·
                    refine ⟨606172641803792799708403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 206906928402361275633801557 606172641803792799708403)
                    ·
                      rfl

theorem cell23_3541551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 10].length) (baseStart_3541551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3541551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3541551 prefixEnd_3541551 := by exact prefixLift 3541551
  have htrace : WordTrace (prefixWord ++ tailWord_3541551) baseStart_3541551 baseEnd_3541551 := by
    simpa [prefixWord, tailWord_3541551, baseEnd_3541551] using wordTrace_append hprefix tailTrace_3541551
  have hstable : (prefixWord ++ tailWord_3541551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541551).length < 2 ^ (prefixWord ++ tailWord_3541551).sum := by decide
  have hdescent : baseEnd_3541551 < baseStart_3541551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541585 : List Nat := [1, 2, 2, 1, 3, 3, 2, 2, 3, 4]
def baseStart_3541585 : Nat := 118140960795 + 3541585 * 2 ^ 59
def prefixEnd_3541585 : Nat := 4983230072969 + 3 ^ 40 * 3541585 * 2
def baseEnd_3541585 : Nat := 606178461251210422033351

theorem tailTrace_3541585 : CollatzResearch.WordTrace tailWord_3541585 prefixEnd_3541585 606178461251210422033351 := by
  unfold tailWord_3541585
  simp only [CollatzResearch.WordTrace]
  refine ⟨129172216874449874408178209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86114811249633249605452139 129172216874449874408178209)
  ·
    refine ⟨96879162655837405806133657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129172216874449874408178209 96879162655837405806133657)
    ·
      refine ⟨72659371991878054354600243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96879162655837405806133657 72659371991878054354600243)
      ·
        refine ⟨108989057987817081531900365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72659371991878054354600243 108989057987817081531900365)
        ·
          refine ⟨40870896745431405574462637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108989057987817081531900365 40870896745431405574462637)
          ·
            refine ⟨15326586279536777090423489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40870896745431405574462637 15326586279536777090423489)
            ·
              refine ⟨11494939709652582817817617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15326586279536777090423489 11494939709652582817817617)
              ·
                refine ⟨8621204782239437113363213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11494939709652582817817617 8621204782239437113363213)
                ·
                  refine ⟨3232951793339788917511205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8621204782239437113363213 3232951793339788917511205)
                  ·
                    refine ⟨606178461251210422033351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3232951793339788917511205 606178461251210422033351)
                    ·
                      rfl

theorem cell23_3541585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 2, 3, 4].length) (baseStart_3541585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3541585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3541585 prefixEnd_3541585 := by exact prefixLift 3541585
  have htrace : WordTrace (prefixWord ++ tailWord_3541585) baseStart_3541585 baseEnd_3541585 := by
    simpa [prefixWord, tailWord_3541585, baseEnd_3541585] using wordTrace_append hprefix tailTrace_3541585
  have hstable : (prefixWord ++ tailWord_3541585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541585).length < 2 ^ (prefixWord ++ tailWord_3541585).sum := by decide
  have hdescent : baseEnd_3541585 < baseStart_3541585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541632 : List Nat := [2, 1, 1, 2, 1, 7, 2, 1, 6]
def baseStart_3541632 : Nat := 118140960795 + 3541632 * 2 ^ 59
def prefixEnd_3541632 : Nat := 4983230072969 + 3 ^ 40 * 3541632 * 2
def baseEnd_3541632 : Nat := 202062168593821398023593

theorem tailTrace_3541632 : CollatzResearch.WordTrace tailWord_3541632 prefixEnd_3541632 202062168593821398023593 := by
  unfold tailWord_3541632
  simp only [CollatzResearch.WordTrace]
  refine ⟨64586965552639800717569575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86115954070186400956759433 64586965552639800717569575)
  ·
    refine ⟨96880448328959701076354363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64586965552639800717569575 96880448328959701076354363)
    ·
      refine ⟨145320672493439551614531545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96880448328959701076354363 145320672493439551614531545)
      ·
        refine ⟨108990504370079663710898659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145320672493439551614531545 108990504370079663710898659)
        ·
          refine ⟨163485756555119495566347989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108990504370079663710898659 163485756555119495566347989)
          ·
            refine ⟨3831697419260613177336281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 163485756555119495566347989 3831697419260613177336281)
            ·
              refine ⟨2873773064445459883002211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3831697419260613177336281 2873773064445459883002211)
              ·
                refine ⟨4310659596668189824503317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2873773064445459883002211 4310659596668189824503317)
                ·
                  refine ⟨202062168593821398023593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4310659596668189824503317 202062168593821398023593)
                  ·
                    rfl

theorem cell23_3541632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 2, 1, 6].length) (baseStart_3541632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3541632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3541632 prefixEnd_3541632 := by exact prefixLift 3541632
  have htrace : WordTrace (prefixWord ++ tailWord_3541632) baseStart_3541632 baseEnd_3541632 := by
    simpa [prefixWord, tailWord_3541632, baseEnd_3541632] using wordTrace_append hprefix tailTrace_3541632
  have hstable : (prefixWord ++ tailWord_3541632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541632).length < 2 ^ (prefixWord ++ tailWord_3541632).sum := by decide
  have hdescent : baseEnd_3541632 < baseStart_3541632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541635 : List Nat := [1, 1, 1, 3, 3, 1, 2, 1, 3, 5, 2]
def baseStart_3541635 : Nat := 118140960795 + 3541635 * 2 ^ 59
def prefixEnd_3541635 : Nat := 4983230072969 + 3 ^ 40 * 3541635 * 2
def baseEnd_3541635 : Nat := 1818561057786356070474823

theorem tailTrace_3541635 : CollatzResearch.WordTrace tailWord_3541635 prefixEnd_3541635 1818561057786356070474823 := by
  unfold tailWord_3541635
  simp only [CollatzResearch.WordTrace]
  refine ⟨129174040524268732947498359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86116027016179155298332239 129174040524268732947498359)
  ·
    refine ⟨193761060786403099421247539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129174040524268732947498359 193761060786403099421247539)
    ·
      refine ⟨290641591179604649131871309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193761060786403099421247539 290641591179604649131871309)
      ·
        refine ⟨108990596692351743424451741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 290641591179604649131871309 108990596692351743424451741)
        ·
          refine ⟨40871473759631903784169403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108990596692351743424451741 40871473759631903784169403)
          ·
            refine ⟨61307210639447855676254105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40871473759631903784169403 61307210639447855676254105)
            ·
              refine ⟨45980407979585891757190579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61307210639447855676254105 45980407979585891757190579)
              ·
                refine ⟨68970611969378837635785869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45980407979585891757190579 68970611969378837635785869)
                ·
                  refine ⟨25863979488517064113419701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68970611969378837635785869 25863979488517064113419701)
                  ·
                    refine ⟨2424748077048474760633097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25863979488517064113419701 2424748077048474760633097)
                    ·
                      refine ⟨1818561057786356070474823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2424748077048474760633097 1818561057786356070474823)
                      ·
                        rfl

theorem cell23_3541635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 5, 2].length) (baseStart_3541635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3541635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3541635 prefixEnd_3541635 := by exact prefixLift 3541635
  have htrace : WordTrace (prefixWord ++ tailWord_3541635) baseStart_3541635 baseEnd_3541635 := by
    simpa [prefixWord, tailWord_3541635, baseEnd_3541635] using wordTrace_append hprefix tailTrace_3541635
  have hstable : (prefixWord ++ tailWord_3541635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541635).length < 2 ^ (prefixWord ++ tailWord_3541635).sum := by decide
  have hdescent : baseEnd_3541635 < baseStart_3541635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541692 : List Nat := [2, 2, 2, 3, 1, 1, 1, 5, 2, 4]
def baseStart_3541692 : Nat := 118140960795 + 3541692 * 2 ^ 59
def prefixEnd_3541692 : Nat := 4983230072969 + 3 ^ 40 * 3541692 * 2
def baseEnd_3541692 : Nat := 606196775394554115820687

theorem tailTrace_3541692 : CollatzResearch.WordTrace tailWord_3541692 prefixEnd_3541692 606196775394554115820687 := by
  unfold tailWord_3541692
  simp only [CollatzResearch.WordTrace]
  refine ⟨64588059742531115841161665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86117412990041487788215553 64588059742531115841161665)
  ·
    refine ⟨48441044806898336880871249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64588059742531115841161665 48441044806898336880871249)
    ·
      refine ⟨36330783605173752660653437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48441044806898336880871249 36330783605173752660653437)
      ·
        refine ⟨13624043851940157247745039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36330783605173752660653437 13624043851940157247745039)
        ·
          refine ⟨20436065777910235871617559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13624043851940157247745039 20436065777910235871617559)
          ·
            refine ⟨30654098666865353807426339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20436065777910235871617559 30654098666865353807426339)
            ·
              refine ⟨45981148000298030711139509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30654098666865353807426339 45981148000298030711139509)
              ·
                refine ⟨4310732625027940379169329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45981148000298030711139509 4310732625027940379169329)
                ·
                  refine ⟨3233049468770955284376997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4310732625027940379169329 3233049468770955284376997)
                  ·
                    refine ⟨606196775394554115820687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3233049468770955284376997 606196775394554115820687)
                    ·
                      rfl

theorem cell23_3541692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 5, 2, 4].length) (baseStart_3541692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3541692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3541692 prefixEnd_3541692 := by exact prefixLift 3541692
  have htrace : WordTrace (prefixWord ++ tailWord_3541692) baseStart_3541692 baseEnd_3541692 := by
    simpa [prefixWord, tailWord_3541692, baseEnd_3541692] using wordTrace_append hprefix tailTrace_3541692
  have hstable : (prefixWord ++ tailWord_3541692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541692).length < 2 ^ (prefixWord ++ tailWord_3541692).sum := by decide
  have hdescent : baseEnd_3541692 < baseStart_3541692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541695 : List Nat := [1, 1, 2, 2, 2, 4, 1, 3, 1, 2, 4]
def baseStart_3541695 : Nat := 118140960795 + 3541695 * 2 ^ 59
def prefixEnd_3541695 : Nat := 4983230072969 + 3 ^ 40 * 3541695 * 2
def baseEnd_3541695 : Nat := 1818591866625625835724547

theorem tailTrace_3541695 : CollatzResearch.WordTrace tailWord_3541695 prefixEnd_3541695 1818591866625625835724547 := by
  unfold tailWord_3541695
  simp only [CollatzResearch.WordTrace]
  refine ⟨129176228904051363194682539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86117485936034242129788359 129176228904051363194682539)
  ·
    refine ⟨193764343356077044792023809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129176228904051363194682539 193764343356077044792023809)
    ·
      refine ⟨145323257517057783594017857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193764343356077044792023809 145323257517057783594017857)
      ·
        refine ⟨108992443137793337695513393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145323257517057783594017857 108992443137793337695513393)
        ·
          refine ⟨81744332353345003271635045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108992443137793337695513393 81744332353345003271635045)
          ·
            refine ⟨15327062316252188113431571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81744332353345003271635045 15327062316252188113431571)
            ·
              refine ⟨22990593474378282170147357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15327062316252188113431571 22990593474378282170147357)
              ·
                refine ⟨8621472552891855813805259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22990593474378282170147357 8621472552891855813805259)
                ·
                  refine ⟨12932208829337783720707889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8621472552891855813805259 12932208829337783720707889)
                  ·
                    refine ⟨9699156622003337790530917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12932208829337783720707889 9699156622003337790530917)
                    ·
                      refine ⟨1818591866625625835724547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9699156622003337790530917 1818591866625625835724547)
                      ·
                        rfl

theorem cell23_3541695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 3, 1, 2, 4].length) (baseStart_3541695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3541695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3541695 prefixEnd_3541695 := by exact prefixLift 3541695
  have htrace : WordTrace (prefixWord ++ tailWord_3541695) baseStart_3541695 baseEnd_3541695 := by
    simpa [prefixWord, tailWord_3541695, baseEnd_3541695] using wordTrace_append hprefix tailTrace_3541695
  have hstable : (prefixWord ++ tailWord_3541695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541695).length < 2 ^ (prefixWord ++ tailWord_3541695).sum := by decide
  have hdescent : baseEnd_3541695 < baseStart_3541695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541719 : List Nat := [1, 1, 3, 2, 1, 4, 4, 1, 1, 2, 3]
def baseStart_3541719 : Nat := 118140960795 + 3541719 * 2 ^ 59
def prefixEnd_3541719 : Nat := 4983230072969 + 3 ^ 40 * 3541719 * 2
def baseEnd_3541719 : Nat := 1818604190161333741824437

theorem tailTrace_3541719 : CollatzResearch.WordTrace tailWord_3541719 prefixEnd_3541719 1818604190161333741824437 := by
  unfold tailWord_3541719
  simp only [CollatzResearch.WordTrace]
  refine ⟨129177104255964415293556211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86118069503976276862370807 129177104255964415293556211)
  ·
    refine ⟨193765656383946622940334317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129177104255964415293556211 193765656383946622940334317)
    ·
      refine ⟨72662121143979983602625369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193765656383946622940334317 72662121143979983602625369)
      ·
        refine ⟨54496590857984987701969027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72662121143979983602625369 54496590857984987701969027)
        ·
          refine ⟨81744886286977481552953541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54496590857984987701969027 81744886286977481552953541)
          ·
            refine ⟨15327166178808277791178789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81744886286977481552953541 15327166178808277791178789)
            ·
              refine ⟨2873843658526552085846023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15327166178808277791178789 2873843658526552085846023)
              ·
                refine ⟨4310765487789828128769035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2873843658526552085846023 4310765487789828128769035)
                ·
                  refine ⟨6466148231684742193153553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4310765487789828128769035 6466148231684742193153553)
                  ·
                    refine ⟨4849611173763556644865165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6466148231684742193153553 4849611173763556644865165)
                    ·
                      refine ⟨1818604190161333741824437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4849611173763556644865165 1818604190161333741824437)
                      ·
                        rfl

theorem cell23_3541719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 4, 1, 1, 2, 3].length) (baseStart_3541719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3541719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3541719 prefixEnd_3541719 := by exact prefixLift 3541719
  have htrace : WordTrace (prefixWord ++ tailWord_3541719) baseStart_3541719 baseEnd_3541719 := by
    simpa [prefixWord, tailWord_3541719, baseEnd_3541719] using wordTrace_append hprefix tailTrace_3541719
  have hstable : (prefixWord ++ tailWord_3541719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541719).length < 2 ^ (prefixWord ++ tailWord_3541719).sum := by decide
  have hdescent : baseEnd_3541719 < baseStart_3541719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541762 : List Nat := [3, 4, 1, 1, 1, 2, 1, 1, 2, 2, 5]
def baseStart_3541762 : Nat := 118140960795 + 3541762 * 2 ^ 59
def prefixEnd_3541762 : Nat := 4983230072969 + 3 ^ 40 * 3541762 * 2
def baseEnd_3541762 : Nat := 1818626269829477073586739

theorem tailTrace_3541762 : CollatzResearch.WordTrace tailWord_3541762 prefixEnd_3541762 1818626269829477073586739 := by
  unfold tailWord_3541762
  simp only [CollatzResearch.WordTrace]
  refine ⟨32294668148702158409342885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86119115063205755758247693 32294668148702158409342885)
  ·
    refine ⟨6055250277881654701751791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32294668148702158409342885 6055250277881654701751791)
    ·
      refine ⟨9082875416822482052627687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6055250277881654701751791 9082875416822482052627687)
      ·
        refine ⟨13624313125233723078941531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9082875416822482052627687 13624313125233723078941531)
        ·
          refine ⟨20436469687850584618412297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13624313125233723078941531 20436469687850584618412297)
          ·
            refine ⟨15327352265887938463809223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20436469687850584618412297 15327352265887938463809223)
            ·
              refine ⟨22991028398831907695713835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15327352265887938463809223 22991028398831907695713835)
              ·
                refine ⟨34486542598247861543570753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22991028398831907695713835 34486542598247861543570753)
                ·
                  refine ⟨25864906948685896157678065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34486542598247861543570753 25864906948685896157678065)
                  ·
                    refine ⟨19398680211514422118258549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25864906948685896157678065 19398680211514422118258549)
                    ·
                      refine ⟨1818626269829477073586739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19398680211514422118258549 1818626269829477073586739)
                      ·
                        rfl

theorem cell23_3541762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_3541762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3541762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3541762 prefixEnd_3541762 := by exact prefixLift 3541762
  have htrace : WordTrace (prefixWord ++ tailWord_3541762) baseStart_3541762 baseEnd_3541762 := by
    simpa [prefixWord, tailWord_3541762, baseEnd_3541762] using wordTrace_append hprefix tailTrace_3541762
  have hstable : (prefixWord ++ tailWord_3541762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541762).length < 2 ^ (prefixWord ++ tailWord_3541762).sum := by decide
  have hdescent : baseEnd_3541762 < baseStart_3541762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541772 : List Nat := [2, 2, 1, 2, 2, 1, 1, 3, 3, 4, 2]
def baseStart_3541772 : Nat := 118140960795 + 3541772 * 2 ^ 59
def prefixEnd_3541772 : Nat := 4983230072969 + 3 ^ 40 * 3541772 * 2
def baseEnd_3541772 : Nat := 1818631404636022034461693

theorem tailTrace_3541772 : CollatzResearch.WordTrace tailWord_3541772 prefixEnd_3541772 1818631404636022034461693 := by
  unfold tailWord_3541772
  simp only [CollatzResearch.WordTrace]
  refine ⟨64589518662386202672617785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86119358216514936896823713 64589518662386202672617785)
  ·
    refine ⟨48442138996789652004463339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64589518662386202672617785 48442138996789652004463339)
    ·
      refine ⟨72663208495184478006695009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48442138996789652004463339 72663208495184478006695009)
      ·
        refine ⟨54497406371388358505021257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72663208495184478006695009 54497406371388358505021257)
        ·
          refine ⟨40873054778541268878765943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54497406371388358505021257 40873054778541268878765943)
          ·
            refine ⟨61309582167811903318148915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40873054778541268878765943 61309582167811903318148915)
            ·
              refine ⟨91964373251717854977223373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61309582167811903318148915 91964373251717854977223373)
              ·
                refine ⟨34486639969394195616458765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91964373251717854977223373 34486639969394195616458765)
                ·
                  refine ⟨12932489988522823356172037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34486639969394195616458765 12932489988522823356172037)
                  ·
                    refine ⟨2424841872848029379282257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12932489988522823356172037 2424841872848029379282257)
                    ·
                      refine ⟨1818631404636022034461693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2424841872848029379282257 1818631404636022034461693)
                      ·
                        rfl

theorem cell23_3541772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 3, 4, 2].length) (baseStart_3541772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3541772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3541772 prefixEnd_3541772 := by exact prefixLift 3541772
  have htrace : WordTrace (prefixWord ++ tailWord_3541772) baseStart_3541772 baseEnd_3541772 := by
    simpa [prefixWord, tailWord_3541772, baseEnd_3541772] using wordTrace_append hprefix tailTrace_3541772
  have hstable : (prefixWord ++ tailWord_3541772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541772).length < 2 ^ (prefixWord ++ tailWord_3541772).sum := by decide
  have hdescent : baseEnd_3541772 < baseStart_3541772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541775 : List Nat := [1, 1, 2, 1, 1, 1, 7, 1, 2, 1, 5]
def baseStart_3541775 : Nat := 118140960795 + 3541775 * 2 ^ 59
def prefixEnd_3541775 : Nat := 4983230072969 + 3 ^ 40 * 3541775 * 2
def baseEnd_3541775 : Nat := 1818632945077985522724179

theorem tailTrace_3541775 : CollatzResearch.WordTrace tailWord_3541775 prefixEnd_3541775 1818632945077985522724179 := by
  unfold tailWord_3541775
  simp only [CollatzResearch.WordTrace]
  refine ⟨129179146743761536857594779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86119431162507691238396519 129179146743761536857594779)
  ·
    refine ⟨193768720115642305286392169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129179146743761536857594779 193768720115642305286392169)
    ·
      refine ⟨145326540086731728964794127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193768720115642305286392169 145326540086731728964794127)
      ·
        refine ⟨217989810130097593447191191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145326540086731728964794127 217989810130097593447191191)
        ·
          refine ⟨326984715195146390170786787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217989810130097593447191191 326984715195146390170786787)
          ·
            refine ⟨490477072792719585256180181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 326984715195146390170786787 490477072792719585256180181)
            ·
              refine ⟨11495556393579365279441723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 490477072792719585256180181 11495556393579365279441723)
              ·
                refine ⟨17243334590369047919162585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11495556393579365279441723 17243334590369047919162585)
                ·
                  refine ⟨12932500942776785939371939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17243334590369047919162585 12932500942776785939371939)
                  ·
                    refine ⟨19398751414165178909057909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12932500942776785939371939 19398751414165178909057909)
                    ·
                      refine ⟨1818632945077985522724179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19398751414165178909057909 1818632945077985522724179)
                      ·
                        rfl

theorem cell23_3541775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 2, 1, 5].length) (baseStart_3541775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3541775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3541775 prefixEnd_3541775 := by exact prefixLift 3541775
  have htrace : WordTrace (prefixWord ++ tailWord_3541775) baseStart_3541775 baseEnd_3541775 := by
    simpa [prefixWord, tailWord_3541775, baseEnd_3541775] using wordTrace_append hprefix tailTrace_3541775
  have hstable : (prefixWord ++ tailWord_3541775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541775).length < 2 ^ (prefixWord ++ tailWord_3541775).sum := by decide
  have hdescent : baseEnd_3541775 < baseStart_3541775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541785 : List Nat := [1, 2, 1, 2, 1, 1, 1, 6, 2, 2, 4]
def baseStart_3541785 : Nat := 118140960795 + 3541785 * 2 ^ 59
def prefixEnd_3541785 : Nat := 4983230072969 + 3 ^ 40 * 3541785 * 2
def baseEnd_3541785 : Nat := 1818638079884530483599133

theorem tailTrace_3541785 : CollatzResearch.WordTrace tailWord_3541785 prefixEnd_3541785 1818638079884530483599133 := by
  unfold tailWord_3541785
  simp only [CollatzResearch.WordTrace]
  refine ⟨129179511473725308565458809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86119674315816872376972539 129179511473725308565458809)
  ·
    refine ⟨96884633605293981424094107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129179511473725308565458809 96884633605293981424094107)
    ·
      refine ⟨145326950407940972136141161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96884633605293981424094107 145326950407940972136141161)
      ·
        refine ⟨108995212805955729102105871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145326950407940972136141161 108995212805955729102105871)
        ·
          refine ⟨163492819208933593653158807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108995212805955729102105871 163492819208933593653158807)
          ·
            refine ⟨245239228813400390479738211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163492819208933593653158807 245239228813400390479738211)
            ·
              refine ⟨367858843220100585719607317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245239228813400390479738211 367858843220100585719607317)
              ·
                refine ⟨17243383275942214955606593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 367858843220100585719607317 17243383275942214955606593)
                ·
                  refine ⟨12932537456956661216704945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17243383275942214955606593 12932537456956661216704945)
                  ·
                    refine ⟨9699403092717495912528709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12932537456956661216704945 9699403092717495912528709)
                    ·
                      refine ⟨1818638079884530483599133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9699403092717495912528709 1818638079884530483599133)
                      ·
                        rfl

theorem cell23_3541785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 2, 2, 4].length) (baseStart_3541785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3541785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3541785 prefixEnd_3541785 := by exact prefixLift 3541785
  have htrace : WordTrace (prefixWord ++ tailWord_3541785) baseStart_3541785 baseEnd_3541785 := by
    simpa [prefixWord, tailWord_3541785, baseEnd_3541785] using wordTrace_append hprefix tailTrace_3541785
  have hstable : (prefixWord ++ tailWord_3541785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541785).length < 2 ^ (prefixWord ++ tailWord_3541785).sum := by decide
  have hdescent : baseEnd_3541785 < baseStart_3541785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541842 : List Nat := [3, 2, 2, 1, 1, 2, 1, 4, 2, 5]
def baseStart_3541842 : Nat := 118140960795 + 3541842 * 2 ^ 59
def prefixEnd_3541842 : Nat := 4983230072969 + 3 ^ 40 * 3541842 * 2
def baseEnd_3541842 : Nat := 606222449427278920195457

theorem tailTrace_3541842 : CollatzResearch.WordTrace tailWord_3541842 prefixEnd_3541842 606222449427278920195457 := by
  unfold tailWord_3541842
  simp only [CollatzResearch.WordTrace]
  refine ⟨32295397608629701825070945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86121060289679204866855853 32295397608629701825070945)
  ·
    refine ⟨24221548206472276368803209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32295397608629701825070945 24221548206472276368803209)
    ·
      refine ⟨18166161154854207276602407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24221548206472276368803209 18166161154854207276602407)
      ·
        refine ⟨27249241732281310914903611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18166161154854207276602407 27249241732281310914903611)
        ·
          refine ⟨40873862598421966372355417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27249241732281310914903611 40873862598421966372355417)
          ·
            refine ⟨30655396948816474779266563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40873862598421966372355417 30655396948816474779266563)
            ·
              refine ⟨45983095423224712168899845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30655396948816474779266563 45983095423224712168899845)
              ·
                refine ⟨8621830391854633531668721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45983095423224712168899845 8621830391854633531668721)
                ·
                  refine ⟨6466372793890975148751541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8621830391854633531668721 6466372793890975148751541)
                  ·
                    refine ⟨606222449427278920195457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6466372793890975148751541 606222449427278920195457)
                    ·
                      rfl

theorem cell23_3541842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_3541842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3541842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3541842 prefixEnd_3541842 := by exact prefixLift 3541842
  have htrace : WordTrace (prefixWord ++ tailWord_3541842) baseStart_3541842 baseEnd_3541842 := by
    simpa [prefixWord, tailWord_3541842, baseEnd_3541842] using wordTrace_append hprefix tailTrace_3541842
  have hstable : (prefixWord ++ tailWord_3541842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541842).length < 2 ^ (prefixWord ++ tailWord_3541842).sum := by decide
  have hdescent : baseEnd_3541842 < baseStart_3541842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541872 : List Nat := [2, 1, 1, 1, 4, 1, 3, 1, 5, 4]
def baseStart_3541872 : Nat := 118140960795 + 3541872 * 2 ^ 59
def prefixEnd_3541872 : Nat := 4983230072969 + 3 ^ 40 * 3541872 * 2
def baseEnd_3541872 : Nat := 606227584233823881070411

theorem tailTrace_3541872 : CollatzResearch.WordTrace tailWord_3541872 prefixEnd_3541872 606227584233823881070411 := by
  unfold tailWord_3541872
  simp only [CollatzResearch.WordTrace]
  refine ⟨64591342312205061211937935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86121789749606748282583913 64591342312205061211937935)
  ·
    refine ⟨96887013468307591817906903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64591342312205061211937935 96887013468307591817906903)
    ·
      refine ⟨145330520202461387726860355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96887013468307591817906903 145330520202461387726860355)
      ·
        refine ⟨217995780303692081590290533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145330520202461387726860355 217995780303692081590290533)
        ·
          refine ⟨40874208806942265298179475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 217995780303692081590290533 40874208806942265298179475)
          ·
            refine ⟨61311313210413397947269213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40874208806942265298179475 61311313210413397947269213)
            ·
              refine ⟨22991742453905024230225955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61311313210413397947269213 22991742453905024230225955)
              ·
                refine ⟨34487613680857536345338933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22991742453905024230225955 34487613680857536345338933)
                ·
                  refine ⟨3233213782580394032375525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34487613680857536345338933 3233213782580394032375525)
                  ·
                    refine ⟨606227584233823881070411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3233213782580394032375525 606227584233823881070411)
                    ·
                      rfl

theorem cell23_3541872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 5, 4].length) (baseStart_3541872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3541872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3541872 prefixEnd_3541872 := by exact prefixLift 3541872
  have htrace : WordTrace (prefixWord ++ tailWord_3541872) baseStart_3541872 baseEnd_3541872 := by
    simpa [prefixWord, tailWord_3541872, baseEnd_3541872] using wordTrace_append hprefix tailTrace_3541872
  have hstable : (prefixWord ++ tailWord_3541872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541872).length < 2 ^ (prefixWord ++ tailWord_3541872).sum := by decide
  have hdescent : baseEnd_3541872 < baseStart_3541872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541929 : List Nat := [1, 2, 1, 1, 1, 1, 5, 4, 3, 1, 3]
def baseStart_3541929 : Nat := 118140960795 + 3541929 * 2 ^ 59
def prefixEnd_3541929 : Nat := 4983230072969 + 3 ^ 40 * 3541929 * 2
def baseEnd_3541929 : Nat := 1818712021098777920198471

theorem tailTrace_3541929 : CollatzResearch.WordTrace tailWord_3541929 prefixEnd_3541929 1818712021098777920198471 := by
  unfold tailWord_3541929
  simp only [CollatzResearch.WordTrace]
  refine ⟨129184763585203621158700841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86123175723469080772467227 129184763585203621158700841)
  ·
    refine ⟨96888572688902715869025631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129184763585203621158700841 96888572688902715869025631)
    ·
      refine ⟨145332859033354073803538447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96888572688902715869025631 145332859033354073803538447)
      ·
        refine ⟨217999288550031110705307671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145332859033354073803538447 217999288550031110705307671)
        ·
          refine ⟨326998932825046666057961507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217999288550031110705307671 326998932825046666057961507)
          ·
            refine ⟨490498399237569999086942261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 326998932825046666057961507 490498399237569999086942261)
            ·
              refine ⟨45984224928522187414400837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 490498399237569999086942261 45984224928522187414400837)
              ·
                refine ⟨8622042174097910140200157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45984224928522187414400837 8622042174097910140200157)
                ·
                  refine ⟨3233265815286716302575059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8622042174097910140200157 3233265815286716302575059)
                  ·
                    refine ⟨4849898722930074453862589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3233265815286716302575059 4849898722930074453862589)
                    ·
                      refine ⟨1818712021098777920198471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4849898722930074453862589 1818712021098777920198471)
                      ·
                        rfl

theorem cell23_3541929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 4, 3, 1, 3].length) (baseStart_3541929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3541929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3541929 prefixEnd_3541929 := by exact prefixLift 3541929
  have htrace : WordTrace (prefixWord ++ tailWord_3541929) baseStart_3541929 baseEnd_3541929 := by
    simpa [prefixWord, tailWord_3541929, baseEnd_3541929] using wordTrace_append hprefix tailTrace_3541929
  have hstable : (prefixWord ++ tailWord_3541929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541929).length < 2 ^ (prefixWord ++ tailWord_3541929).sum := by decide
  have hdescent : baseEnd_3541929 < baseStart_3541929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541940 : List Nat := [2, 5, 2, 1, 1, 1, 3, 3, 1, 4]
def baseStart_3541940 : Nat := 118140960795 + 3541940 * 2 ^ 59
def prefixEnd_3541940 : Nat := 4983230072969 + 3 ^ 40 * 3541940 * 2
def baseEnd_3541940 : Nat := 606239223128659125720307

theorem tailTrace_3541940 : CollatzResearch.WordTrace tailWord_3541940 prefixEnd_3541940 606239223128659125720307 := by
  unfold tailWord_3541940
  simp only [CollatzResearch.WordTrace]
  refine ⟨64592582394081885018675637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86123443192109180024900849 64592582394081885018675637)
  ·
    refine ⟨6055554599445176720500841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64592582394081885018675637 6055554599445176720500841)
    ·
      refine ⟨4541665949583882540375631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6055554599445176720500841 4541665949583882540375631)
      ·
        refine ⟨6812498924375823810563447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4541665949583882540375631 6812498924375823810563447)
        ·
          refine ⟨10218748386563735715845171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6812498924375823810563447 10218748386563735715845171)
          ·
            refine ⟨15328122579845603573767757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10218748386563735715845171 15328122579845603573767757)
            ·
              refine ⟨5748045967442101340162909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15328122579845603573767757 5748045967442101340162909)
              ·
                refine ⟨2155517237790788002561091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5748045967442101340162909 2155517237790788002561091)
                ·
                  refine ⟨3233275856686182003841637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2155517237790788002561091 3233275856686182003841637)
                  ·
                    refine ⟨606239223128659125720307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3233275856686182003841637 606239223128659125720307)
                    ·
                      rfl

theorem cell23_3541940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_3541940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3541940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3541940 prefixEnd_3541940 := by exact prefixLift 3541940
  have htrace : WordTrace (prefixWord ++ tailWord_3541940) baseStart_3541940 baseEnd_3541940 := by
    simpa [prefixWord, tailWord_3541940, baseEnd_3541940] using wordTrace_append hprefix tailTrace_3541940
  have hstable : (prefixWord ++ tailWord_3541940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541940).length < 2 ^ (prefixWord ++ tailWord_3541940).sum := by decide
  have hdescent : baseEnd_3541940 < baseStart_3541940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541983 : List Nat := [1, 1, 2, 3, 6, 1, 1, 2, 1, 5]
def baseStart_3541983 : Nat := 118140960795 + 3541983 * 2 ^ 59
def prefixEnd_3541983 : Nat := 4983230072969 + 3 ^ 40 * 3541983 * 2
def baseEnd_3541983 : Nat := 606246583018040236307741

theorem tailTrace_3541983 : CollatzResearch.WordTrace tailWord_3541983 prefixEnd_3541983 606246583018040236307741 := by
  unfold tailWord_3541983
  simp only [CollatzResearch.WordTrace]
  refine ⟨129186733127007988381166603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86124488751338658920777735 129186733127007988381166603)
  ·
    refine ⟨193780099690511982571749905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129186733127007988381166603 193780099690511982571749905)
    ·
      refine ⟨145335074767883986928812429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193780099690511982571749905 145335074767883986928812429)
      ·
        refine ⟨54500653037956495098304661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145335074767883986928812429 54500653037956495098304661)
        ·
          refine ⟨2554718111154210707733031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 54500653037956495098304661 2554718111154210707733031)
          ·
            refine ⟨3832077166731316061599547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2554718111154210707733031 3832077166731316061599547)
            ·
              refine ⟨5748115750096974092399321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3832077166731316061599547 5748115750096974092399321)
              ·
                refine ⟨4311086812572730569299491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5748115750096974092399321 4311086812572730569299491)
                ·
                  refine ⟨6466630218859095853949237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4311086812572730569299491 6466630218859095853949237)
                  ·
                    refine ⟨606246583018040236307741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6466630218859095853949237 606246583018040236307741)
                    ·
                      rfl

theorem cell23_3541983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 2, 1, 5].length) (baseStart_3541983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3541983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3541983 prefixEnd_3541983 := by exact prefixLift 3541983
  have htrace : WordTrace (prefixWord ++ tailWord_3541983) baseStart_3541983 baseEnd_3541983 := by
    simpa [prefixWord, tailWord_3541983, baseEnd_3541983] using wordTrace_append hprefix tailTrace_3541983
  have hstable : (prefixWord ++ tailWord_3541983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541983).length < 2 ^ (prefixWord ++ tailWord_3541983).sum := by decide
  have hdescent : baseEnd_3541983 < baseStart_3541983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541992 : List Nat := [2, 1, 4, 1, 1, 1, 4, 9]
def baseStart_3541992 : Nat := 118140960795 + 3541992 * 2 ^ 59
def prefixEnd_3541992 : Nat := 4983230072969 + 3 ^ 40 * 3541992 * 2
def baseEnd_3541992 : Nat := 67360902606667080507803

theorem tailTrace_3541992 : CollatzResearch.WordTrace tailWord_3541992 prefixEnd_3541992 67360902606667080507803 := by
  unfold tailWord_3541992
  simp only [CollatzResearch.WordTrace]
  refine ⟨64593530691987691459122115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86124707589316921945496153 64593530691987691459122115)
  ·
    refine ⟨96890296037981537188683173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64593530691987691459122115 96890296037981537188683173)
    ·
      refine ⟨18166930507121538222878095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96890296037981537188683173 18166930507121538222878095)
      ·
        refine ⟨27250395760682307334317143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18166930507121538222878095 27250395760682307334317143)
        ·
          refine ⟨40875593641023461001475715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27250395760682307334317143 40875593641023461001475715)
          ·
            refine ⟨61313390461535191502213573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40875593641023461001475715 61313390461535191502213573)
            ·
              refine ⟨11496260711537848406665045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61313390461535191502213573 11496260711537848406665045)
              ·
                refine ⟨67360902606667080507803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11496260711537848406665045 67360902606667080507803)
                ·
                  rfl

theorem cell23_3541992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 9].length) (baseStart_3541992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3541992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3541992 prefixEnd_3541992 := by exact prefixLift 3541992
  have htrace : WordTrace (prefixWord ++ tailWord_3541992) baseStart_3541992 baseEnd_3541992 := by
    simpa [prefixWord, tailWord_3541992, baseEnd_3541992] using wordTrace_append hprefix tailTrace_3541992
  have hstable : (prefixWord ++ tailWord_3541992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541992).length < 2 ^ (prefixWord ++ tailWord_3541992).sum := by decide
  have hdescent : baseEnd_3541992 < baseStart_3541992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541999 : List Nat := [1, 1, 2, 1, 4, 4, 1, 2, 1, 2, 4]
def baseStart_3541999 : Nat := 118140960795 + 3541999 * 2 ^ 59
def prefixEnd_3541999 : Nat := 4983230072969 + 3 ^ 40 * 3541999 * 2
def baseEnd_3541999 : Nat := 1818747964744592646323149

theorem tailTrace_3541999 : CollatzResearch.WordTrace tailWord_3541999 prefixEnd_3541999 1818747964744592646323149 := by
  unfold tailWord_3541999
  simp only [CollatzResearch.WordTrace]
  refine ⟨129187316694950023113749051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86124877796633348742499367 129187316694950023113749051)
  ·
    refine ⟨193780975042425034670623577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129187316694950023113749051 193780975042425034670623577)
    ·
      refine ⟨145335731281818776002967683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193780975042425034670623577 145335731281818776002967683)
      ·
        refine ⟨218003596922728164004451525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145335731281818776002967683 218003596922728164004451525)
        ·
          refine ⟨40875674423011530750834661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 218003596922728164004451525 40875674423011530750834661)
          ·
            refine ⟨7664188954314662015781499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40875674423011530750834661 7664188954314662015781499)
            ·
              refine ⟨11496283431471993023672249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7664188954314662015781499 11496283431471993023672249)
              ·
                refine ⟨8622212573603994767754187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11496283431471993023672249 8622212573603994767754187)
                ·
                  refine ⟨12933318860405992151631281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8622212573603994767754187 12933318860405992151631281)
                  ·
                    refine ⟨9699989145304494113723461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12933318860405992151631281 9699989145304494113723461)
                    ·
                      refine ⟨1818747964744592646323149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9699989145304494113723461 1818747964744592646323149)
                      ·
                        rfl

theorem cell23_3541999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 2, 1, 2, 4].length) (baseStart_3541999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3541999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3541999 prefixEnd_3541999 := by exact prefixLift 3541999
  have htrace : WordTrace (prefixWord ++ tailWord_3541999) baseStart_3541999 baseEnd_3541999 := by
    simpa [prefixWord, tailWord_3541999, baseEnd_3541999] using wordTrace_append hprefix tailTrace_3541999
  have hstable : (prefixWord ++ tailWord_3541999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541999).length < 2 ^ (prefixWord ++ tailWord_3541999).sum := by decide
  have hdescent : baseEnd_3541999 < baseStart_3541999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542006 : List Nat := [5, 1, 1, 1, 3, 1, 3, 1, 1, 1, 5]
def baseStart_3542006 : Nat := 118140960795 + 3542006 * 2 ^ 59
def prefixEnd_3542006 : Nat := 4983230072969 + 3 ^ 40 * 3542006 * 2
def baseEnd_3542006 : Nat := 1818751559109174118935617

theorem tailTrace_3542006 : CollatzResearch.WordTrace tailWord_3542006 prefixEnd_3542006 1818751559109174118935617 := by
  unfold tailWord_3542006
  simp only [CollatzResearch.WordTrace]
  refine ⟨8074223250370291456828367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86125048003949775539502581 8074223250370291456828367)
  ·
    refine ⟨12111334875555437185242551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8074223250370291456828367 12111334875555437185242551)
    ·
      refine ⟨18167002313333155777863827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12111334875555437185242551 18167002313333155777863827)
      ·
        refine ⟨27250503469999733666795741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18167002313333155777863827 27250503469999733666795741)
        ·
          refine ⟨10218938801249900125048403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27250503469999733666795741 10218938801249900125048403)
          ·
            refine ⟨15328408201874850187572605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10218938801249900125048403 15328408201874850187572605)
            ·
              refine ⟨5748153075703068820339727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15328408201874850187572605 5748153075703068820339727)
              ·
                refine ⟨8622229613554603230509591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5748153075703068820339727 8622229613554603230509591)
                ·
                  refine ⟨12933344420331904845764387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8622229613554603230509591 12933344420331904845764387)
                  ·
                    refine ⟨19400016630497857268646581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12933344420331904845764387 19400016630497857268646581)
                    ·
                      refine ⟨1818751559109174118935617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19400016630497857268646581 1818751559109174118935617)
                      ·
                        rfl

theorem cell23_3542006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 1, 1, 1, 5].length) (baseStart_3542006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3542006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3542006 prefixEnd_3542006 := by exact prefixLift 3542006
  have htrace : WordTrace (prefixWord ++ tailWord_3542006) baseStart_3542006 baseEnd_3542006 := by
    simpa [prefixWord, tailWord_3542006, baseEnd_3542006] using wordTrace_append hprefix tailTrace_3542006
  have hstable : (prefixWord ++ tailWord_3542006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542006).length < 2 ^ (prefixWord ++ tailWord_3542006).sum := by decide
  have hdescent : baseEnd_3542006 < baseStart_3542006 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542014 : List Nat := [4, 2, 2, 2, 2, 2, 2, 2, 1, 1, 3]
def baseStart_3542014 : Nat := 118140960795 + 3542014 * 2 ^ 59
def prefixEnd_3542014 : Nat := 4983230072969 + 3 ^ 40 * 3542014 * 2
def baseEnd_3542014 : Nat := 1818755666954410087635581

theorem tailTrace_3542014 : CollatzResearch.WordTrace tailWord_3542014 prefixEnd_3542014 1818755666954410087635581 := by
  unfold tailWord_3542014
  simp only [CollatzResearch.WordTrace]
  refine ⟨16148482973736960084443137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86125242526597120450363397 16148482973736960084443137)
  ·
    refine ⟨12111362230302720063332353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16148482973736960084443137 12111362230302720063332353)
    ·
      refine ⟨9083521672727040047499265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12111362230302720063332353 9083521672727040047499265)
      ·
        refine ⟨6812641254545280035624449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9083521672727040047499265 6812641254545280035624449)
        ·
          refine ⟨5109480940908960026718337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6812641254545280035624449 5109480940908960026718337)
          ·
            refine ⟨3832110705681720020038753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5109480940908960026718337 3832110705681720020038753)
            ·
              refine ⟨2874083029261290015029065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3832110705681720020038753 2874083029261290015029065)
              ·
                refine ⟨2155562271945967511271799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2874083029261290015029065 2155562271945967511271799)
                ·
                  refine ⟨3233343407918951266907699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2155562271945967511271799 3233343407918951266907699)
                  ·
                    refine ⟨4850015111878426900361549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3233343407918951266907699 4850015111878426900361549)
                    ·
                      refine ⟨1818755666954410087635581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4850015111878426900361549 1818755666954410087635581)
                      ·
                        rfl

theorem cell23_3542014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_3542014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3542014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3542014 prefixEnd_3542014 := by exact prefixLift 3542014
  have htrace : WordTrace (prefixWord ++ tailWord_3542014) baseStart_3542014 baseEnd_3542014 := by
    simpa [prefixWord, tailWord_3542014, baseEnd_3542014] using wordTrace_append hprefix tailTrace_3542014
  have hstable : (prefixWord ++ tailWord_3542014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542014).length < 2 ^ (prefixWord ++ tailWord_3542014).sum := by decide
  have hdescent : baseEnd_3542014 < baseStart_3542014 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542070 : List Nat := [5, 1, 2, 1, 1, 2, 3, 2, 2, 1, 3]
def baseStart_3542070 : Nat := 118140960795 + 3542070 * 2 ^ 59
def prefixEnd_3542070 : Nat := 4983230072969 + 3 ^ 40 * 3542070 * 2
def baseEnd_3542070 : Nat := 1818784421871061868535323

theorem tailTrace_3542070 : CollatzResearch.WordTrace tailWord_3542070 prefixEnd_3542070 1818784421871061868535323 := by
  unfold tailWord_3542070
  simp only [CollatzResearch.WordTrace]
  refine ⟨8074369142355800139973979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86126604185128534826389109 8074369142355800139973979)
  ·
    refine ⟨12111553713533700209960969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8074369142355800139973979 12111553713533700209960969)
    ·
      refine ⟨9083665285150275157470727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12111553713533700209960969 9083665285150275157470727)
      ·
        refine ⟨13625497927725412736206091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9083665285150275157470727 13625497927725412736206091)
        ·
          refine ⟨20438246891588119104309137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13625497927725412736206091 20438246891588119104309137)
          ·
            refine ⟨15328685168691089328231853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20438246891588119104309137 15328685168691089328231853)
            ·
              refine ⟨5748256938259158498086945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15328685168691089328231853 5748256938259158498086945)
              ·
                refine ⟨4311192703694368873565209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5748256938259158498086945 4311192703694368873565209)
                ·
                  refine ⟨3233394527770776655173907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4311192703694368873565209 3233394527770776655173907)
                  ·
                    refine ⟨4850091791656164982760861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3233394527770776655173907 4850091791656164982760861)
                    ·
                      refine ⟨1818784421871061868535323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4850091791656164982760861 1818784421871061868535323)
                      ·
                        rfl

theorem cell23_3542070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_3542070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3542070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3542070 prefixEnd_3542070 := by exact prefixLift 3542070
  have htrace : WordTrace (prefixWord ++ tailWord_3542070) baseStart_3542070 baseEnd_3542070 := by
    simpa [prefixWord, tailWord_3542070, baseEnd_3542070] using wordTrace_append hprefix tailTrace_3542070
  have hstable : (prefixWord ++ tailWord_3542070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542070).length < 2 ^ (prefixWord ++ tailWord_3542070).sum := by decide
  have hdescent : baseEnd_3542070 < baseStart_3542070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542183 : List Nat := [1, 1, 6, 2, 1, 1, 2, 2, 2, 1, 4]
def baseStart_3542183 : Nat := 118140960795 + 3542183 * 2 ^ 59
def prefixEnd_3542183 : Nat := 4983230072969 + 3 ^ 40 * 3542183 * 2
def baseEnd_3542183 : Nat := 1818842445185019926422303

theorem tailTrace_3542183 : CollatzResearch.WordTrace tailWord_3542183 prefixEnd_3542183 1818842445185019926422303 := by
  unfold tailWord_3542183
  simp only [CollatzResearch.WordTrace]
  refine ⟨129194027726283422538447203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86129351817522281692298135 129194027726283422538447203)
  ·
    refine ⟨193791041589425133807670805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129194027726283422538447203 193791041589425133807670805)
    ·
      refine ⟨9083955074504303147234569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 193791041589425133807670805 9083955074504303147234569)
      ·
        refine ⟨6812966305878227360425927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9083955074504303147234569 6812966305878227360425927)
        ·
          refine ⟨10219449458817341040638891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6812966305878227360425927 10219449458817341040638891)
          ·
            refine ⟨15329174188226011560958337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10219449458817341040638891 15329174188226011560958337)
            ·
              refine ⟨11496880641169508670718753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15329174188226011560958337 11496880641169508670718753)
              ·
                refine ⟨8622660480877131503039065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11496880641169508670718753 8622660480877131503039065)
                ·
                  refine ⟨6466995360657848627279299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8622660480877131503039065 6466995360657848627279299)
                  ·
                    refine ⟨9700493040986772940918949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6466995360657848627279299 9700493040986772940918949)
                    ·
                      refine ⟨1818842445185019926422303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9700493040986772940918949 1818842445185019926422303)
                      ·
                        rfl

theorem cell23_3542183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_3542183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3542183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3542183 prefixEnd_3542183 := by exact prefixLift 3542183
  have htrace : WordTrace (prefixWord ++ tailWord_3542183) baseStart_3542183 baseEnd_3542183 := by
    simpa [prefixWord, tailWord_3542183, baseEnd_3542183] using wordTrace_append hprefix tailTrace_3542183
  have hstable : (prefixWord ++ tailWord_3542183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542183).length < 2 ^ (prefixWord ++ tailWord_3542183).sum := by decide
  have hdescent : baseEnd_3542183 < baseStart_3542183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542214 : List Nat := [6, 1, 2, 2, 1, 2, 1, 1, 2, 5]
def baseStart_3542214 : Nat := 118140960795 + 3542214 * 2 ^ 59
def prefixEnd_3542214 : Nat := 4983230072969 + 3 ^ 40 * 3542214 * 2
def baseEnd_3542214 : Nat := 606286121028436435044887

theorem tailTrace_3542214 : CollatzResearch.WordTrace tailWord_3542214 prefixEnd_3542214 606286121028436435044887 := by
  unfold tailWord_3542214
  simp only [CollatzResearch.WordTrace]
  refine ⟨4037348699661597338525803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 86130105592780743221883797 4037348699661597338525803)
  ·
    refine ⟨6056023049492396007788705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4037348699661597338525803 6056023049492396007788705)
    ·
      refine ⟨4542017287119297005841529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6056023049492396007788705 4542017287119297005841529)
      ·
        refine ⟨3406512965339472754381147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4542017287119297005841529 3406512965339472754381147)
        ·
          refine ⟨5109769448009209131571721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3406512965339472754381147 5109769448009209131571721)
          ·
            refine ⟨3832327086006906848678791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5109769448009209131571721 3832327086006906848678791)
            ·
              refine ⟨5748490629010360273018187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3832327086006906848678791 5748490629010360273018187)
              ·
                refine ⟨8622735943515540409527281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5748490629010360273018187 8622735943515540409527281)
                ·
                  refine ⟨6467051957636655307145461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8622735943515540409527281 6467051957636655307145461)
                  ·
                    refine ⟨606286121028436435044887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6467051957636655307145461 606286121028436435044887)
                    ·
                      rfl

theorem cell23_3542214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_3542214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3542214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3542214 prefixEnd_3542214 := by exact prefixLift 3542214
  have htrace : WordTrace (prefixWord ++ tailWord_3542214) baseStart_3542214 baseEnd_3542214 := by
    simpa [prefixWord, tailWord_3542214, baseEnd_3542214] using wordTrace_append hprefix tailTrace_3542214
  have hstable : (prefixWord ++ tailWord_3542214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542214).length < 2 ^ (prefixWord ++ tailWord_3542214).sum := by decide
  have hdescent : baseEnd_3542214 < baseStart_3542214 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542250 : List Nat := [3, 1, 3, 1, 1, 4, 2, 1, 3, 1, 3]
def baseStart_3542250 : Nat := 118140960795 + 3542250 * 2 ^ 59
def prefixEnd_3542250 : Nat := 4983230072969 + 3 ^ 40 * 3542250 * 2
def baseEnd_3542250 : Nat := 1818876848388871164284495

theorem tailTrace_3542250 : CollatzResearch.WordTrace tailWord_3542250 prefixEnd_3542250 1818876848388871164284495 := by
  unfold tailWord_3542250
  simp only [CollatzResearch.WordTrace]
  refine ⟨32299117854260173245284051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86130980944693795320757469 32299117854260173245284051)
  ·
    refine ⟨48448676781390259867926077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32299117854260173245284051 48448676781390259867926077)
    ·
      refine ⟨18168253793021347450472279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48448676781390259867926077 18168253793021347450472279)
      ·
        refine ⟨27252380689532021175708419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18168253793021347450472279 27252380689532021175708419)
        ·
          refine ⟨40878571034298031763562629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27252380689532021175708419 40878571034298031763562629)
          ·
            refine ⟨7664732068930880955667993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40878571034298031763562629 7664732068930880955667993)
            ·
              refine ⟨5748549051698160716750995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7664732068930880955667993 5748549051698160716750995)
              ·
                refine ⟨8622823577547241075126493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5748549051698160716750995 8622823577547241075126493)
                ·
                  refine ⟨3233558841580215403172435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8622823577547241075126493 3233558841580215403172435)
                  ·
                    refine ⟨4850338262370323104758653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3233558841580215403172435 4850338262370323104758653)
                    ·
                      refine ⟨1818876848388871164284495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4850338262370323104758653 1818876848388871164284495)
                      ·
                        rfl

theorem cell23_3542250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 1, 3, 1, 3].length) (baseStart_3542250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3542250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3542250 prefixEnd_3542250 := by exact prefixLift 3542250
  have htrace : WordTrace (prefixWord ++ tailWord_3542250) baseStart_3542250 baseEnd_3542250 := by
    simpa [prefixWord, tailWord_3542250, baseEnd_3542250] using wordTrace_append hprefix tailTrace_3542250
  have hstable : (prefixWord ++ tailWord_3542250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542250).length < 2 ^ (prefixWord ++ tailWord_3542250).sum := by decide
  have hdescent : baseEnd_3542250 < baseStart_3542250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542270 : List Nat := [4, 2, 2, 1, 1, 3, 2, 2, 1, 5]
def baseStart_3542270 : Nat := 118140960795 + 3542270 * 2 ^ 59
def prefixEnd_3542270 : Nat := 4983230072969 + 3 ^ 40 * 3542270 * 2
def baseEnd_3542270 : Nat := 606295706000653695344801

theorem tailTrace_3542270 : CollatzResearch.WordTrace tailWord_3542270 prefixEnd_3542270 606295706000653695344801 := by
  unfold tailWord_3542270
  simp only [CollatzResearch.WordTrace]
  refine ⟨16149650109621029549608033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86131467251312157597909509 16149650109621029549608033)
  ·
    refine ⟨12112237582215772162206025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16149650109621029549608033 12112237582215772162206025)
    ·
      refine ⟨9084178186661829121654519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12112237582215772162206025 9084178186661829121654519)
      ·
        refine ⟨13626267279992743682481779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9084178186661829121654519 13626267279992743682481779)
        ·
          refine ⟨20439400919989115523722669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13626267279992743682481779 20439400919989115523722669)
          ·
            refine ⟨7664775344995918321396001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20439400919989115523722669 7664775344995918321396001)
            ·
              refine ⟨5748581508746938741047001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7664775344995918321396001 5748581508746938741047001)
              ·
                refine ⟨4311436131560204055785251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5748581508746938741047001 4311436131560204055785251)
                ·
                  refine ⟨6467154197340306083677877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4311436131560204055785251 6467154197340306083677877)
                  ·
                    refine ⟨606295706000653695344801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6467154197340306083677877 606295706000653695344801)
                    ·
                      rfl

theorem cell23_3542270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_3542270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3542270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3542270 prefixEnd_3542270 := by exact prefixLift 3542270
  have htrace : WordTrace (prefixWord ++ tailWord_3542270) baseStart_3542270 baseEnd_3542270 := by
    simpa [prefixWord, tailWord_3542270, baseEnd_3542270] using wordTrace_append hprefix tailTrace_3542270
  have hstable : (prefixWord ++ tailWord_3542270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542270).length < 2 ^ (prefixWord ++ tailWord_3542270).sum := by decide
  have hdescent : baseEnd_3542270 < baseStart_3542270 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542273 : List Nat := [1, 2, 4, 1, 1, 3, 1, 4, 1, 1, 4]
def baseStart_3542273 : Nat := 118140960795 + 3542273 * 2 ^ 59
def prefixEnd_3542273 : Nat := 4983230072969 + 3 ^ 40 * 3542273 * 2
def baseEnd_3542273 : Nat := 1818888658443924574296889

theorem tailTrace_3542273 : CollatzResearch.WordTrace tailWord_3542273 prefixEnd_3542273 1818888658443924574296889 := by
  unfold tailWord_3542273
  simp only [CollatzResearch.WordTrace]
  refine ⟨129197310295957367909223473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86131540197304911939482315 129197310295957367909223473)
  ·
    refine ⟨96897982721968025931917605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129197310295957367909223473 96897982721968025931917605)
    ·
      refine ⟨18168371760369004862234551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96897982721968025931917605 18168371760369004862234551)
      ·
        refine ⟨27252557640553507293351827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18168371760369004862234551 27252557640553507293351827)
        ·
          refine ⟨40878836460830260940027741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27252557640553507293351827 40878836460830260940027741)
          ·
            refine ⟨15329563672811347852510403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40878836460830260940027741 15329563672811347852510403)
            ·
              refine ⟨22994345509217021778765605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15329563672811347852510403 22994345509217021778765605)
              ·
                refine ⟨4311439782978191583518551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22994345509217021778765605 4311439782978191583518551)
                ·
                  refine ⟨6467159674467287375277827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4311439782978191583518551 6467159674467287375277827)
                  ·
                    refine ⟨9700739511700931062916741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6467159674467287375277827 9700739511700931062916741)
                    ·
                      refine ⟨1818888658443924574296889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9700739511700931062916741 1818888658443924574296889)
                      ·
                        rfl

theorem cell23_3542273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 4, 1, 1, 4].length) (baseStart_3542273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3542273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3542273 prefixEnd_3542273 := by exact prefixLift 3542273
  have htrace : WordTrace (prefixWord ++ tailWord_3542273) baseStart_3542273 baseEnd_3542273 := by
    simpa [prefixWord, tailWord_3542273, baseEnd_3542273] using wordTrace_append hprefix tailTrace_3542273
  have hstable : (prefixWord ++ tailWord_3542273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542273).length < 2 ^ (prefixWord ++ tailWord_3542273).sum := by decide
  have hdescent : baseEnd_3542273 < baseStart_3542273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542296 : List Nat := [2, 1, 2, 3, 1, 5, 9]
def baseStart_3542296 : Nat := 118140960795 + 3542296 * 2 ^ 59
def prefixEnd_3542296 : Nat := 4983230072969 + 3 ^ 40 * 3542296 * 2
def baseEnd_3542296 : Nat := 22455561339493555361843

theorem tailTrace_3542296 : CollatzResearch.WordTrace tailWord_3542296 prefixEnd_3542296 22455561339493555361843 := by
  unfold tailWord_3542296
  simp only [CollatzResearch.WordTrace]
  refine ⟨64599074587437021418655371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86132099449916028558207161 64599074587437021418655371)
  ·
    refine ⟨96898611881155532127983057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64599074587437021418655371 96898611881155532127983057)
    ·
      refine ⟨72673958910866649095987293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96898611881155532127983057 72673958910866649095987293)
      ·
        refine ⟨27252734591574993410995235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72673958910866649095987293 27252734591574993410995235)
        ·
          refine ⟨40879101887362490116492853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27252734591574993410995235 40879101887362490116492853)
          ·
            refine ⟨3832415801940233448421205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40879101887362490116492853 3832415801940233448421205)
            ·
              refine ⟨22455561339493555361843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3832415801940233448421205 22455561339493555361843)
              ·
                rfl

theorem cell23_3542296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 9].length) (baseStart_3542296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3542296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3542296 prefixEnd_3542296 := by exact prefixLift 3542296
  have htrace : WordTrace (prefixWord ++ tailWord_3542296) baseStart_3542296 baseEnd_3542296 := by
    simpa [prefixWord, tailWord_3542296, baseEnd_3542296] using wordTrace_append hprefix tailTrace_3542296
  have hstable : (prefixWord ++ tailWord_3542296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542296).length < 2 ^ (prefixWord ++ tailWord_3542296).sum := by decide
  have hdescent : baseEnd_3542296 < baseStart_3542296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542307 : List Nat := [1, 1, 1, 4, 2, 5, 1, 1, 3, 2, 2]
def baseStart_3542307 : Nat := 118140960795 + 3542307 * 2 ^ 59
def prefixEnd_3542307 : Nat := 4983230072969 + 3 ^ 40 * 3542307 * 2
def baseEnd_3542307 : Nat := 1818906116786177441271733

theorem tailTrace_3542307 : CollatzResearch.WordTrace tailWord_3542307 prefixEnd_3542307 1818906116786177441271733 := by
  unfold tailWord_3542307
  simp only [CollatzResearch.WordTrace]
  refine ⟨129198550377834191715961175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86132366918556127810640783 129198550377834191715961175)
  ·
    refine ⟨193797825566751287573941763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129198550377834191715961175 193797825566751287573941763)
    ·
      refine ⟨290696738350126931360912645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193797825566751287573941763 290696738350126931360912645)
      ·
        refine ⟨54505638440648799630171121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 290696738350126931360912645 54505638440648799630171121)
        ·
          refine ⟨40879228830486599722628341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54505638440648799630171121 40879228830486599722628341)
          ·
            refine ⟨3832427702858118723996407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40879228830486599722628341 3832427702858118723996407)
            ·
              refine ⟨5748641554287178085994611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3832427702858118723996407 5748641554287178085994611)
              ·
                refine ⟨8622962331430767128991917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5748641554287178085994611 8622962331430767128991917)
                ·
                  refine ⟨3233610874286537673371969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8622962331430767128991917 3233610874286537673371969)
                  ·
                    refine ⟨2425208155714903255028977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3233610874286537673371969 2425208155714903255028977)
                    ·
                      refine ⟨1818906116786177441271733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2425208155714903255028977 1818906116786177441271733)
                      ·
                        rfl

theorem cell23_3542307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 1, 3, 2, 2].length) (baseStart_3542307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3542307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3542307 prefixEnd_3542307 := by exact prefixLift 3542307
  have htrace : WordTrace (prefixWord ++ tailWord_3542307) baseStart_3542307 baseEnd_3542307 := by
    simpa [prefixWord, tailWord_3542307, baseEnd_3542307] using wordTrace_append hprefix tailTrace_3542307
  have hstable : (prefixWord ++ tailWord_3542307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542307).length < 2 ^ (prefixWord ++ tailWord_3542307).sum := by decide
  have hdescent : baseEnd_3542307 < baseStart_3542307 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542317 : List Nat := [1, 5, 3, 1, 1, 2, 1, 3, 2, 4]
def baseStart_3542317 : Nat := 118140960795 + 3542317 * 2 ^ 59
def prefixEnd_3542317 : Nat := 4983230072969 + 3 ^ 40 * 3542317 * 2
def baseEnd_3542317 : Nat := 606303750530907467382229

theorem tailTrace_3542317 : CollatzResearch.WordTrace tailWord_3542317 prefixEnd_3542317 606303750530907467382229 := by
  unfold tailWord_3542317
  simp only [CollatzResearch.WordTrace]
  refine ⟨129198915107797963423825205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86132610071865308949216803 129198915107797963423825205)
  ·
    refine ⟨12112398291356059070983613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 129198915107797963423825205 12112398291356059070983613)
    ·
      refine ⟨4542149359258522151618855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12112398291356059070983613 4542149359258522151618855)
      ·
        refine ⟨6813224038887783227428283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4542149359258522151618855 6813224038887783227428283)
        ·
          refine ⟨10219836058331674841142425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6813224038887783227428283 10219836058331674841142425)
          ·
            refine ⟨7664877043748756130856819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10219836058331674841142425 7664877043748756130856819)
            ·
              refine ⟨11497315565623134196285229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7664877043748756130856819 11497315565623134196285229)
              ·
                refine ⟨4311493337108675323606961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11497315565623134196285229 4311493337108675323606961)
                ·
                  refine ⟨3233620002831506492705221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4311493337108675323606961 3233620002831506492705221)
                  ·
                    refine ⟨606303750530907467382229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3233620002831506492705221 606303750530907467382229)
                    ·
                      rfl

theorem cell23_3542317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_3542317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3542317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3542317 prefixEnd_3542317 := by exact prefixLift 3542317
  have htrace : WordTrace (prefixWord ++ tailWord_3542317) baseStart_3542317 baseEnd_3542317 := by
    simpa [prefixWord, tailWord_3542317, baseEnd_3542317] using wordTrace_append hprefix tailTrace_3542317
  have hstable : (prefixWord ++ tailWord_3542317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542317).length < 2 ^ (prefixWord ++ tailWord_3542317).sum := by decide
  have hdescent : baseEnd_3542317 < baseStart_3542317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542340 : List Nat := [2, 3, 4, 1, 1, 1, 1, 1, 3, 3, 3]
def baseStart_3542340 : Nat := 118140960795 + 3542340 * 2 ^ 59
def prefixEnd_3542340 : Nat := 4983230072969 + 3 ^ 40 * 3542340 * 2
def baseEnd_3542340 : Nat := 1818923061647775812159081

theorem tailTrace_3542340 : CollatzResearch.WordTrace tailWord_3542340 prefixEnd_3542340 1818923061647775812159081 := by
  unfold tailWord_3542340
  simp only [CollatzResearch.WordTrace]
  refine ⟨64599876993357319175956237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86133169324476425567941649 64599876993357319175956237)
  ·
    refine ⟨24224953872508994690983589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64599876993357319175956237 24224953872508994690983589)
    ·
      refine ⟨4542178851095436504559423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24224953872508994690983589 4542178851095436504559423)
      ·
        refine ⟨6813268276643154756839135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4542178851095436504559423 6813268276643154756839135)
        ·
          refine ⟨10219902414964732135258703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6813268276643154756839135 10219902414964732135258703)
          ·
            refine ⟨15329853622447098202888055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10219902414964732135258703 15329853622447098202888055)
            ·
              refine ⟨22994780433670647304332083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15329853622447098202888055 22994780433670647304332083)
              ·
                refine ⟨34492170650505970956498125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22994780433670647304332083 34492170650505970956498125)
                ·
                  refine ⟨12934563993939739108686797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34492170650505970956498125 12934563993939739108686797)
                  ·
                    refine ⟨4850461497727402165757549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12934563993939739108686797 4850461497727402165757549)
                    ·
                      refine ⟨1818923061647775812159081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4850461497727402165757549 1818923061647775812159081)
                      ·
                        rfl

theorem cell23_3542340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_3542340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3542340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3542340 prefixEnd_3542340 := by exact prefixLift 3542340
  have htrace : WordTrace (prefixWord ++ tailWord_3542340) baseStart_3542340 baseEnd_3542340 := by
    simpa [prefixWord, tailWord_3542340, baseEnd_3542340] using wordTrace_append hprefix tailTrace_3542340
  have hstable : (prefixWord ++ tailWord_3542340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542340).length < 2 ^ (prefixWord ++ tailWord_3542340).sum := by decide
  have hdescent : baseEnd_3542340 < baseStart_3542340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542346 : List Nat := [3, 1, 2, 1, 1, 1, 1, 2, 4, 3, 4]
def baseStart_3542346 : Nat := 118140960795 + 3542346 * 2 ^ 59
def prefixEnd_3542346 : Nat := 4983230072969 + 3 ^ 40 * 3542346 * 2
def baseEnd_3542346 : Nat := 1818926142531702788684053

theorem tailTrace_3542346 : CollatzResearch.WordTrace tailWord_3542346 prefixEnd_3542346 1818926142531702788684053 := by
  unfold tailWord_3542346
  simp only [CollatzResearch.WordTrace]
  refine ⟨32299993206173225344157723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86133315216461934251087261 32299993206173225344157723)
  ·
    refine ⟨48449989809259838016236585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32299993206173225344157723 48449989809259838016236585)
    ·
      refine ⟨36337492356944878512177439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48449989809259838016236585 36337492356944878512177439)
      ·
        refine ⟨54506238535417317768266159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36337492356944878512177439 54506238535417317768266159)
        ·
          refine ⟨81759357803125976652399239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54506238535417317768266159 81759357803125976652399239)
          ·
            refine ⟨122639036704688964978598859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81759357803125976652399239 122639036704688964978598859)
            ·
              refine ⟨183958555057033447467898289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122639036704688964978598859 183958555057033447467898289)
              ·
                refine ⟨137968916292775085600923717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183958555057033447467898289 137968916292775085600923717)
                ·
                  refine ⟨25869171804895328550173197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 137968916292775085600923717 25869171804895328550173197)
                  ·
                    refine ⟨9700939426835748206314949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25869171804895328550173197 9700939426835748206314949)
                    ·
                      refine ⟨1818926142531702788684053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9700939426835748206314949 1818926142531702788684053)
                      ·
                        rfl

theorem cell23_3542346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 4, 3, 4].length) (baseStart_3542346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3542346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3542346 prefixEnd_3542346 := by exact prefixLift 3542346
  have htrace : WordTrace (prefixWord ++ tailWord_3542346) baseStart_3542346 baseEnd_3542346 := by
    simpa [prefixWord, tailWord_3542346, baseEnd_3542346] using wordTrace_append hprefix tailTrace_3542346
  have hstable : (prefixWord ++ tailWord_3542346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542346).length < 2 ^ (prefixWord ++ tailWord_3542346).sum := by decide
  have hdescent : baseEnd_3542346 < baseStart_3542346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542357 : List Nat := [1, 3, 2, 2, 3, 2, 2, 2, 2, 1, 3]
def baseStart_3542357 : Nat := 118140960795 + 3542357 * 2 ^ 59
def prefixEnd_3542357 : Nat := 4983230072969 + 3 ^ 40 * 3542357 * 2
def baseEnd_3542357 : Nat := 1818931790818902245646503

theorem tailTrace_3542357 : CollatzResearch.WordTrace tailWord_3542357 prefixEnd_3542357 1818931790818902245646503 := by
  unfold tailWord_3542357
  simp only [CollatzResearch.WordTrace]
  refine ⟨129200374027653050255281325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86133582685102033503520883 129200374027653050255281325)
  ·
    refine ⟨48450140260369893845730497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129200374027653050255281325 48450140260369893845730497)
    ·
      refine ⟨36337605195277420384297873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48450140260369893845730497 36337605195277420384297873)
      ·
        refine ⟨27253203896458065288223405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36337605195277420384297873 27253203896458065288223405)
        ·
          refine ⟨10219951461171774483083777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27253203896458065288223405 10219951461171774483083777)
          ·
            refine ⟨7664963595878830862312833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10219951461171774483083777 7664963595878830862312833)
            ·
              refine ⟨5748722696909123146734625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7664963595878830862312833 5748722696909123146734625)
              ·
                refine ⟨4311542022681842360050969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5748722696909123146734625 4311542022681842360050969)
                ·
                  refine ⟨3233656517011381770038227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4311542022681842360050969 3233656517011381770038227)
                  ·
                    refine ⟨4850484775517072655057341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3233656517011381770038227 4850484775517072655057341)
                    ·
                      refine ⟨1818931790818902245646503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4850484775517072655057341 1818931790818902245646503)
                      ·
                        rfl

theorem cell23_3542357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 2, 2, 1, 3].length) (baseStart_3542357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3542357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3542357 prefixEnd_3542357 := by exact prefixLift 3542357
  have htrace : WordTrace (prefixWord ++ tailWord_3542357) baseStart_3542357 baseEnd_3542357 := by
    simpa [prefixWord, tailWord_3542357, baseEnd_3542357] using wordTrace_append hprefix tailTrace_3542357
  have hstable : (prefixWord ++ tailWord_3542357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542357).length < 2 ^ (prefixWord ++ tailWord_3542357).sum := by decide
  have hdescent : baseEnd_3542357 < baseStart_3542357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542380 : List Nat := [2, 2, 1, 1, 5, 1, 1, 3, 1, 4, 2]
def baseStart_3542380 : Nat := 118140960795 + 3542380 * 2 ^ 59
def prefixEnd_3542380 : Nat := 4983230072969 + 3 ^ 40 * 3542380 * 2
def baseEnd_3542380 : Nat := 1818943600873955655658897

theorem tailTrace_3542380 : CollatzResearch.WordTrace tailWord_3542380 prefixEnd_3542380 1818943600873955655658897 := by
  unfold tailWord_3542380
  simp only [CollatzResearch.WordTrace]
  refine ⟨64600606453284862591684297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86134141937713150122245729 64600606453284862591684297)
  ·
    refine ⟨48450454839963646943763223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64600606453284862591684297 48450454839963646943763223)
    ·
      refine ⟨72675682259945470415644835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48450454839963646943763223 72675682259945470415644835)
      ·
        refine ⟨109013523389918205623467253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72675682259945470415644835 109013523389918205623467253)
        ·
          refine ⟨10220017817804831777200055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 109013523389918205623467253 10220017817804831777200055)
          ·
            refine ⟨15330026726707247665800083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10220017817804831777200055 15330026726707247665800083)
            ·
              refine ⟨22995040090060871498700125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15330026726707247665800083 22995040090060871498700125)
              ·
                refine ⟨8623140033772826812012547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22995040090060871498700125 8623140033772826812012547)
                ·
                  refine ⟨12934710050659240218018821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8623140033772826812012547 12934710050659240218018821)
                  ·
                    refine ⟨2425258134498607540878529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12934710050659240218018821 2425258134498607540878529)
                    ·
                      refine ⟨1818943600873955655658897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2425258134498607540878529 1818943600873955655658897)
                      ·
                        rfl

theorem cell23_3542380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 4, 2].length) (baseStart_3542380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3542380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3542380 prefixEnd_3542380 := by exact prefixLift 3542380
  have htrace : WordTrace (prefixWord ++ tailWord_3542380) baseStart_3542380 baseEnd_3542380 := by
    simpa [prefixWord, tailWord_3542380, baseEnd_3542380] using wordTrace_append hprefix tailTrace_3542380
  have hstable : (prefixWord ++ tailWord_3542380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542380).length < 2 ^ (prefixWord ++ tailWord_3542380).sum := by decide
  have hdescent : baseEnd_3542380 < baseStart_3542380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542401 : List Nat := [1, 2, 4, 3, 2, 2, 2, 1, 1, 3, 2]
def baseStart_3542401 : Nat := 118140960795 + 3542401 * 2 ^ 59
def prefixEnd_3542401 : Nat := 4983230072969 + 3 ^ 40 * 3542401 * 2
def baseEnd_3542401 : Nat := 1818954383967700073496301

theorem tailTrace_3542401 : CollatzResearch.WordTrace tailWord_3542401 prefixEnd_3542401 1818954383967700073496301 := by
  unfold tailWord_3542401
  simp only [CollatzResearch.WordTrace]
  refine ⟨129201978839493645769883057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86134652559662430513255371 129201978839493645769883057)
  ·
    refine ⟨96901484129620234327412293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129201978839493645769883057 96901484129620234327412293)
    ·
      refine ⟨18169028274303793936389805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96901484129620234327412293 18169028274303793936389805)
      ·
        refine ⟨6813385602863922726146177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18169028274303793936389805 6813385602863922726146177)
        ·
          refine ⟨5110039202147942044609633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6813385602863922726146177 5110039202147942044609633)
          ·
            refine ⟨3832529401610956533457225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5110039202147942044609633 3832529401610956533457225)
            ·
              refine ⟨2874397051208217400092919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3832529401610956533457225 2874397051208217400092919)
              ·
                refine ⟨4311595576812326100139379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2874397051208217400092919 4311595576812326100139379)
                ·
                  refine ⟨6467393365218489150209069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4311595576812326100139379 6467393365218489150209069)
                  ·
                    refine ⟨2425272511956933431328401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6467393365218489150209069 2425272511956933431328401)
                    ·
                      refine ⟨1818954383967700073496301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2425272511956933431328401 1818954383967700073496301)
                      ·
                        rfl

theorem cell23_3542401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_3542401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3542401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3542401 prefixEnd_3542401 := by exact prefixLift 3542401
  have htrace : WordTrace (prefixWord ++ tailWord_3542401) baseStart_3542401 baseEnd_3542401 := by
    simpa [prefixWord, tailWord_3542401, baseEnd_3542401] using wordTrace_append hprefix tailTrace_3542401
  have hstable : (prefixWord ++ tailWord_3542401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542401).length < 2 ^ (prefixWord ++ tailWord_3542401).sum := by decide
  have hdescent : baseEnd_3542401 < baseStart_3542401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542414 : List Nat := [4, 1, 1, 4, 2, 1, 1, 1, 4, 2, 2]
def baseStart_3542414 : Nat := 118140960795 + 3542414 * 2 ^ 59
def prefixEnd_3542414 : Nat := 4983230072969 + 3 ^ 40 * 3542414 * 2
def baseEnd_3542414 : Nat := 1818961059216208522633741

theorem tailTrace_3542414 : CollatzResearch.WordTrace tailWord_3542414 prefixEnd_3542414 1818961059216208522633741 := by
  unfold tailWord_3542414
  simp only [CollatzResearch.WordTrace]
  refine ⟨16150306623555818623763287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86134968658964365993404197 16150306623555818623763287)
  ·
    refine ⟨24225459935333727935644931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16150306623555818623763287 24225459935333727935644931)
    ·
      refine ⟨36338189903000591903467397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24225459935333727935644931 36338189903000591903467397)
      ·
        refine ⟨6813410606812610981900137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36338189903000591903467397 6813410606812610981900137)
        ·
          refine ⟨5110057955109458236425103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6813410606812610981900137 5110057955109458236425103)
          ·
            refine ⟨7665086932664187354637655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5110057955109458236425103 7665086932664187354637655)
            ·
              refine ⟨11497630398996281031956483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7665086932664187354637655 11497630398996281031956483)
              ·
                refine ⟨17246445598494421547934725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11497630398996281031956483 17246445598494421547934725)
                ·
                  refine ⟨3233708549717704040237761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17246445598494421547934725 3233708549717704040237761)
                  ·
                    refine ⟨2425281412288278030178321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3233708549717704040237761 2425281412288278030178321)
                    ·
                      refine ⟨1818961059216208522633741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2425281412288278030178321 1818961059216208522633741)
                      ·
                        rfl

theorem cell23_3542414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_3542414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3542414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3542414 prefixEnd_3542414 := by exact prefixLift 3542414
  have htrace : WordTrace (prefixWord ++ tailWord_3542414) baseStart_3542414 baseEnd_3542414 := by
    simpa [prefixWord, tailWord_3542414, baseEnd_3542414] using wordTrace_append hprefix tailTrace_3542414
  have hstable : (prefixWord ++ tailWord_3542414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542414).length < 2 ^ (prefixWord ++ tailWord_3542414).sum := by decide
  have hdescent : baseEnd_3542414 < baseStart_3542414 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542420 : List Nat := [2, 4, 2, 1, 2, 2, 2, 1, 7]
def baseStart_3542420 : Nat := 118140960795 + 3542420 * 2 ^ 59
def prefixEnd_3542420 : Nat := 4983230072969 + 3 ^ 40 * 3542420 * 2
def baseEnd_3542420 : Nat := 202107126677792833239857

theorem tailTrace_3542420 : CollatzResearch.WordTrace tailWord_3542420 prefixEnd_3542420 202107126677792833239857 := by
  unfold tailWord_3542420
  simp only [CollatzResearch.WordTrace]
  refine ⟨64601335913212406007412357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86135114550949874676549809 64601335913212406007412357)
  ·
    refine ⟨12112750483727326126389817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64601335913212406007412357 12112750483727326126389817)
    ·
      refine ⟨9084562862795494594792363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12112750483727326126389817 9084562862795494594792363)
      ·
        refine ⟨13626844294193241892188545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9084562862795494594792363 13626844294193241892188545)
        ·
          refine ⟨10220133220644931419141409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13626844294193241892188545 10220133220644931419141409)
          ·
            refine ⟨7665099915483698564356057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10220133220644931419141409 7665099915483698564356057)
            ·
              refine ⟨5748824936612773923267043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7665099915483698564356057 5748824936612773923267043)
              ·
                refine ⟨8623237404919160884900565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5748824936612773923267043 8623237404919160884900565)
                ·
                  refine ⟨202107126677792833239857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8623237404919160884900565 202107126677792833239857)
                  ·
                    rfl

theorem cell23_3542420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 1, 7].length) (baseStart_3542420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3542420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3542420 prefixEnd_3542420 := by exact prefixLift 3542420
  have htrace : WordTrace (prefixWord ++ tailWord_3542420) baseStart_3542420 baseEnd_3542420 := by
    simpa [prefixWord, tailWord_3542420, baseEnd_3542420] using wordTrace_append hprefix tailTrace_3542420
  have hstable : (prefixWord ++ tailWord_3542420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542420).length < 2 ^ (prefixWord ++ tailWord_3542420).sum := by decide
  have hdescent : baseEnd_3542420 < baseStart_3542420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542463 : List Nat := [1, 1, 2, 2, 2, 1, 1, 4, 5, 4]
def baseStart_3542463 : Nat := 118140960795 + 3542463 * 2 ^ 59
def prefixEnd_3542463 : Nat := 4983230072969 + 3 ^ 40 * 3542463 * 2
def baseEnd_3542463 : Nat := 606328739922759610307005

theorem tailTrace_3542463 : CollatzResearch.WordTrace tailWord_3542463 prefixEnd_3542463 606328739922759610307005 := by
  unfold tailWord_3542463
  simp only [CollatzResearch.WordTrace]
  refine ⟨129204240165269030358640043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86136160110179353572426695 129204240165269030358640043)
  ·
    refine ⟨193806360247903545537960065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129204240165269030358640043 193806360247903545537960065)
    ·
      refine ⟨145354770185927659153470049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193806360247903545537960065 145354770185927659153470049)
      ·
        refine ⟨109016077639445744365102537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145354770185927659153470049 109016077639445744365102537)
        ·
          refine ⟨81762058229584308273826903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109016077639445744365102537 81762058229584308273826903)
          ·
            refine ⟨122643087344376462410740355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81762058229584308273826903 122643087344376462410740355)
            ·
              refine ⟨183964631016564693616110533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122643087344376462410740355 183964631016564693616110533)
              ·
                refine ⟨34493368315605880053020725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 183964631016564693616110533 34493368315605880053020725)
                ·
                  refine ⟨3233753279588051254970693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34493368315605880053020725 3233753279588051254970693)
                  ·
                    refine ⟨606328739922759610307005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3233753279588051254970693 606328739922759610307005)
                    ·
                      rfl

theorem cell23_3542463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 5, 4].length) (baseStart_3542463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3542463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3542463 prefixEnd_3542463 := by exact prefixLift 3542463
  have htrace : WordTrace (prefixWord ++ tailWord_3542463) baseStart_3542463 baseEnd_3542463 := by
    simpa [prefixWord, tailWord_3542463, baseEnd_3542463] using wordTrace_append hprefix tailTrace_3542463
  have hstable : (prefixWord ++ tailWord_3542463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542463).length < 2 ^ (prefixWord ++ tailWord_3542463).sum := by decide
  have hdescent : baseEnd_3542463 < baseStart_3542463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542570 : List Nat := [3, 1, 4, 1, 1, 1, 1, 4, 1, 6]
def baseStart_3542570 : Nat := 118140960795 + 3542570 * 2 ^ 59
def prefixEnd_3542570 : Nat := 4983230072969 + 3 ^ 40 * 3542570 * 2
def baseEnd_3542570 : Nat := 606347054066103304094341

theorem tailTrace_3542570 : CollatzResearch.WordTrace tailWord_3542570 prefixEnd_3542570 606347054066103304094341 := by
  unfold tailWord_3542570
  simp only [CollatzResearch.WordTrace]
  refine ⟨32302035693970346908196291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86138761850587591755190109 32302035693970346908196291)
  ·
    refine ⟨48453053540955520362294437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32302035693970346908196291 48453053540955520362294437)
    ·
      refine ⟨9084947538929160067930207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48453053540955520362294437 9084947538929160067930207)
      ·
        refine ⟨13627421308393740101895311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9084947538929160067930207 13627421308393740101895311)
        ·
          refine ⟨20441131962590610152842967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13627421308393740101895311 20441131962590610152842967)
          ·
            refine ⟨30661697943885915229264451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20441131962590610152842967 30661697943885915229264451)
            ·
              refine ⟨45992546915828872843896677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30661697943885915229264451 45992546915828872843896677)
              ·
                refine ⟨8623602546717913658230627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45992546915828872843896677 8623602546717913658230627)
                ·
                  refine ⟨12935403820076870487345941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8623602546717913658230627 12935403820076870487345941)
                  ·
                    refine ⟨606347054066103304094341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12935403820076870487345941 606347054066103304094341)
                    ·
                      rfl

theorem cell23_3542570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_3542570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3542570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3542570 prefixEnd_3542570 := by exact prefixLift 3542570
  have htrace : WordTrace (prefixWord ++ tailWord_3542570) baseStart_3542570 baseEnd_3542570 := by
    simpa [prefixWord, tailWord_3542570, baseEnd_3542570] using wordTrace_append hprefix tailTrace_3542570
  have hstable : (prefixWord ++ tailWord_3542570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542570).length < 2 ^ (prefixWord ++ tailWord_3542570).sum := by decide
  have hdescent : baseEnd_3542570 < baseStart_3542570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542574 : List Nat := [4, 1, 3, 1, 2, 1, 4, 1, 1, 5]
def baseStart_3542574 : Nat := 118140960795 + 3542574 * 2 ^ 59
def prefixEnd_3542574 : Nat := 4983230072969 + 3 ^ 40 * 3542574 * 2
def baseEnd_3542574 : Nat := 606347738706975965544335

theorem tailTrace_3542574 : CollatzResearch.WordTrace tailWord_3542574 prefixEnd_3542574 606347738706975965544335 := by
  unfold tailWord_3542574
  simp only [CollatzResearch.WordTrace]
  refine ⟨16151036083483362039491347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86138859111911264210620517 16151036083483362039491347)
  ·
    refine ⟨24226554125225043059237021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16151036083483362039491347 24226554125225043059237021)
    ·
      refine ⟨9084957796959391147213883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24226554125225043059237021 9084957796959391147213883)
      ·
        refine ⟨13627436695439086720820825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9084957796959391147213883 13627436695439086720820825)
        ·
          refine ⟨10220577521579315040615619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13627436695439086720820825 10220577521579315040615619)
          ·
            refine ⟨15330866282368972560923429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10220577521579315040615619 15330866282368972560923429)
            ·
              refine ⟨2874537427944182355173143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15330866282368972560923429 2874537427944182355173143)
              ·
                refine ⟨4311806141916273532759715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2874537427944182355173143 4311806141916273532759715)
                ·
                  refine ⟨6467709212874410299139573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4311806141916273532759715 6467709212874410299139573)
                  ·
                    refine ⟨606347738706975965544335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6467709212874410299139573 606347738706975965544335)
                    ·
                      rfl

theorem cell23_3542574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_3542574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3542574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3542574 prefixEnd_3542574 := by exact prefixLift 3542574
  have htrace : WordTrace (prefixWord ++ tailWord_3542574) baseStart_3542574 baseEnd_3542574 := by
    simpa [prefixWord, tailWord_3542574, baseEnd_3542574] using wordTrace_append hprefix tailTrace_3542574
  have hstable : (prefixWord ++ tailWord_3542574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542574).length < 2 ^ (prefixWord ++ tailWord_3542574).sum := by decide
  have hdescent : baseEnd_3542574 < baseStart_3542574 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542577 : List Nat := [1, 2, 2, 3, 1, 1, 1, 1, 7, 2, 2]
def baseStart_3542577 : Nat := 118140960795 + 3542577 * 2 ^ 59
def prefixEnd_3542577 : Nat := 4983230072969 + 3 ^ 40 * 3542577 * 2
def baseEnd_3542577 : Nat := 1819044756562891384895491

theorem tailTrace_3542577 : CollatzResearch.WordTrace tailWord_3542577 prefixEnd_3542577 1819044756562891384895491 := by
  unfold tailWord_3542577
  simp only [CollatzResearch.WordTrace]
  refine ⟨129208398086856027828289985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86138932057904018552193323 129208398086856027828289985)
  ·
    refine ⟨96906298565142020871217489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129208398086856027828289985 96906298565142020871217489)
    ·
      refine ⟨72679723923856515653413117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96906298565142020871217489 72679723923856515653413117)
      ·
        refine ⟨27254896471446193370029919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72679723923856515653413117 27254896471446193370029919)
        ·
          refine ⟨40882344707169290055044879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27254896471446193370029919 40882344707169290055044879)
          ·
            refine ⟨61323517060753935082567319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40882344707169290055044879 61323517060753935082567319)
            ·
              refine ⟨91985275591130902623850979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61323517060753935082567319 91985275591130902623850979)
              ·
                refine ⟨137977913386696353935776469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91985275591130902623850979 137977913386696353935776469)
                ·
                  refine ⟨3233857345000695795369761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 137977913386696353935776469 3233857345000695795369761)
                  ·
                    refine ⟨2425393008750521846527321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3233857345000695795369761 2425393008750521846527321)
                    ·
                      refine ⟨1819044756562891384895491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2425393008750521846527321 1819044756562891384895491)
                      ·
                        rfl

theorem cell23_3542577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 7, 2, 2].length) (baseStart_3542577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3542577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3542577 prefixEnd_3542577 := by exact prefixLift 3542577
  have htrace : WordTrace (prefixWord ++ tailWord_3542577) baseStart_3542577 baseEnd_3542577 := by
    simpa [prefixWord, tailWord_3542577, baseEnd_3542577] using wordTrace_append hprefix tailTrace_3542577
  have hstable : (prefixWord ++ tailWord_3542577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542577).length < 2 ^ (prefixWord ++ tailWord_3542577).sum := by decide
  have hdescent : baseEnd_3542577 < baseStart_3542577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542583 : List Nat := [1, 1, 3, 1, 2, 5, 10]
def baseStart_3542583 : Nat := 118140960795 + 3542583 * 2 ^ 59
def prefixEnd_3542583 : Nat := 4983230072969 + 3 ^ 40 * 3542583 * 2
def baseEnd_3542583 : Nat := 22457380709219979770623

theorem tailTrace_3542583 : CollatzResearch.WordTrace tailWord_3542583 prefixEnd_3542583 22457380709219979770623 := by
  unfold tailWord_3542583
  simp only [CollatzResearch.WordTrace]
  refine ⟨129208616924834290853008403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86139077949889527235338935 129208616924834290853008403)
  ·
    refine ⟨193812925387251436279512605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129208616924834290853008403 193812925387251436279512605)
    ·
      refine ⟨72679847020219288604817227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193812925387251436279512605 72679847020219288604817227)
      ·
        refine ⟨109019770530328932907225841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72679847020219288604817227 109019770530328932907225841)
        ·
          refine ⟨81764827897746699680419381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109019770530328932907225841 81764827897746699680419381)
          ·
            refine ⟨7665452615413753095039317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81764827897746699680419381 7665452615413753095039317)
            ·
              refine ⟨22457380709219979770623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7665452615413753095039317 22457380709219979770623)
              ·
                rfl

theorem cell23_3542583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 10].length) (baseStart_3542583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3542583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3542583 prefixEnd_3542583 := by exact prefixLift 3542583
  have htrace : WordTrace (prefixWord ++ tailWord_3542583) baseStart_3542583 baseEnd_3542583 := by
    simpa [prefixWord, tailWord_3542583, baseEnd_3542583] using wordTrace_append hprefix tailTrace_3542583
  have hstable : (prefixWord ++ tailWord_3542583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542583).length < 2 ^ (prefixWord ++ tailWord_3542583).sum := by decide
  have hdescent : baseEnd_3542583 < baseStart_3542583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542604 : List Nat := [2, 2, 1, 3, 1, 4, 3, 1, 2, 4]
def baseStart_3542604 : Nat := 118140960795 + 3542604 * 2 ^ 59
def prefixEnd_3542604 : Nat := 4983230072969 + 3 ^ 40 * 3542604 * 2
def baseEnd_3542604 : Nat := 606352873513520926419289

theorem tailTrace_3542604 : CollatzResearch.WordTrace tailWord_3542604 prefixEnd_3542604 606352873513520926419289 := by
  unfold tailWord_3542604
  simp only [CollatzResearch.WordTrace]
  refine ⟨64604691428879105719761433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86139588571838807626348577 64604691428879105719761433)
  ·
    refine ⟨48453518571659329289821075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64604691428879105719761433 48453518571659329289821075)
    ·
      refine ⟨72680277857488993934731613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48453518571659329289821075 72680277857488993934731613)
      ·
        refine ⟨27255104196558372725524355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72680277857488993934731613 27255104196558372725524355)
        ·
          refine ⟨40882656294837559088286533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27255104196558372725524355 40882656294837559088286533)
          ·
            refine ⟨7665498055282042329053725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40882656294837559088286533 7665498055282042329053725)
            ·
              refine ⟨2874561770730765873395147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7665498055282042329053725 2874561770730765873395147)
              ·
                refine ⟨4311842656096148810092721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2874561770730765873395147 4311842656096148810092721)
                ·
                  refine ⟨3233881992072111607569541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4311842656096148810092721 3233881992072111607569541)
                  ·
                    refine ⟨606352873513520926419289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3233881992072111607569541 606352873513520926419289)
                    ·
                      rfl

theorem cell23_3542604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 3, 1, 2, 4].length) (baseStart_3542604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3542604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3542604 prefixEnd_3542604 := by exact prefixLift 3542604
  have htrace : WordTrace (prefixWord ++ tailWord_3542604) baseStart_3542604 baseEnd_3542604 := by
    simpa [prefixWord, tailWord_3542604, baseEnd_3542604] using wordTrace_append hprefix tailTrace_3542604
  have hstable : (prefixWord ++ tailWord_3542604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542604).length < 2 ^ (prefixWord ++ tailWord_3542604).sum := by decide
  have hdescent : baseEnd_3542604 < baseStart_3542604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542627 : List Nat := [1, 1, 1, 5, 1, 3, 1, 2, 4, 1, 3]
def baseStart_3542627 : Nat := 118140960795 + 3542627 * 2 ^ 59
def prefixEnd_3542627 : Nat := 4983230072969 + 3 ^ 40 * 3542627 * 2
def baseEnd_3542627 : Nat := 1819070430595616189270261

theorem tailTrace_3542627 : CollatzResearch.WordTrace tailWord_3542627 prefixEnd_3542627 1819070430595616189270261 := by
  unfold tailWord_3542627
  simp only [CollatzResearch.WordTrace]
  refine ⟨129210221736674886367610135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86140147824449924245073423 129210221736674886367610135)
  ·
    refine ⟨193815332605012329551415203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129210221736674886367610135 193815332605012329551415203)
    ·
      refine ⟨290722998907518494327122805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193815332605012329551415203 290722998907518494327122805)
      ·
        refine ⟨27255281147579858843167763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 290722998907518494327122805 27255281147579858843167763)
        ·
          refine ⟨40882921721369788264751645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27255281147579858843167763 40882921721369788264751645)
          ·
            refine ⟨15331095645513670599281867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40882921721369788264751645 15331095645513670599281867)
            ·
              refine ⟨22996643468270505898922801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15331095645513670599281867 22996643468270505898922801)
              ·
                refine ⟨17247482601202879424192101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22996643468270505898922801 17247482601202879424192101)
                ·
                  refine ⟨3233902987725539892036019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17247482601202879424192101 3233902987725539892036019)
                  ·
                    refine ⟨4850854481588309838054029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3233902987725539892036019 4850854481588309838054029)
                    ·
                      refine ⟨1819070430595616189270261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4850854481588309838054029 1819070430595616189270261)
                      ·
                        rfl

theorem cell23_3542627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 4, 1, 3].length) (baseStart_3542627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3542627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3542627 prefixEnd_3542627 := by exact prefixLift 3542627
  have htrace : WordTrace (prefixWord ++ tailWord_3542627) baseStart_3542627 baseEnd_3542627 := by
    simpa [prefixWord, tailWord_3542627, baseEnd_3542627] using wordTrace_append hprefix tailTrace_3542627
  have hstable : (prefixWord ++ tailWord_3542627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542627).length < 2 ^ (prefixWord ++ tailWord_3542627).sum := by decide
  have hdescent : baseEnd_3542627 < baseStart_3542627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542628 : List Nat := [2, 3, 1, 1, 2, 5, 1, 3, 1, 2, 2]
def baseStart_3542628 : Nat := 118140960795 + 3542628 * 2 ^ 59
def prefixEnd_3542628 : Nat := 4983230072969 + 3 ^ 40 * 3542628 * 2
def baseEnd_3542628 : Nat := 1819070944076270685357757

theorem tailTrace_3542628 : CollatzResearch.WordTrace tailWord_3542628 prefixEnd_3542628 1819070944076270685357757 := by
  unfold tailWord_3542628
  simp only [CollatzResearch.WordTrace]
  refine ⟨64605129104835631769198269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86140172139780842358931025 64605129104835631769198269)
  ·
    refine ⟨24226923414313361913449351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64605129104835631769198269 24226923414313361913449351)
    ·
      refine ⟨36340385121470042870174027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24226923414313361913449351 36340385121470042870174027)
      ·
        refine ⟨54510577682205064305261041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36340385121470042870174027 54510577682205064305261041)
        ·
          refine ⟨40882933261653798228945781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54510577682205064305261041 40882933261653798228945781)
          ·
            refine ⟨3832774993280043583963667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40882933261653798228945781 3832774993280043583963667)
            ·
              refine ⟨5749162489920065375945501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3832774993280043583963667 5749162489920065375945501)
              ·
                refine ⟨2155935933720024515979563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5749162489920065375945501 2155935933720024515979563)
                ·
                  refine ⟨3233903900580036773969345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2155935933720024515979563 3233903900580036773969345)
                  ·
                    refine ⟨2425427925435027580477009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3233903900580036773969345 2425427925435027580477009)
                    ·
                      refine ⟨1819070944076270685357757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2425427925435027580477009 1819070944076270685357757)
                      ·
                        rfl

theorem cell23_3542628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 3, 1, 2, 2].length) (baseStart_3542628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3542628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3542628 prefixEnd_3542628 := by exact prefixLift 3542628
  have htrace : WordTrace (prefixWord ++ tailWord_3542628) baseStart_3542628 baseEnd_3542628 := by
    simpa [prefixWord, tailWord_3542628, baseEnd_3542628] using wordTrace_append hprefix tailTrace_3542628
  have hstable : (prefixWord ++ tailWord_3542628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542628).length < 2 ^ (prefixWord ++ tailWord_3542628).sum := by decide
  have hdescent : baseEnd_3542628 < baseStart_3542628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542645 : List Nat := [1, 3, 4, 2, 1, 2, 3, 2, 1, 2, 2]
def baseStart_3542645 : Nat := 118140960795 + 3542645 * 2 ^ 59
def prefixEnd_3542645 : Nat := 4983230072969 + 3 ^ 40 * 3542645 * 2
def baseEnd_3542645 : Nat := 1819079673247397118845179

theorem tailTrace_3542645 : CollatzResearch.WordTrace tailWord_3542645 prefixEnd_3542645 1819079673247397118845179 := by
  unfold tailWord_3542645
  simp only [CollatzResearch.WordTrace]
  refine ⟨129210878250609675441765389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86140585500406450294510259 129210878250609675441765389)
  ·
    refine ⟨48454079343978628290662021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129210878250609675441765389 48454079343978628290662021)
    ·
      refine ⟨9085139876995992804499129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48454079343978628290662021 9085139876995992804499129)
      ·
        refine ⟨6813854907746994603374347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9085139876995992804499129 6813854907746994603374347)
        ·
          refine ⟨10220782361620491905061521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6813854907746994603374347 10220782361620491905061521)
          ·
            refine ⟨7665586771215368928796141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10220782361620491905061521 7665586771215368928796141)
            ·
              refine ⟨2874595039205763348298553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7665586771215368928796141 2874595039205763348298553)
              ·
                refine ⟨2155946279404322511223915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2874595039205763348298553 2155946279404322511223915)
                ·
                  refine ⟨3233919419106483766835873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2155946279404322511223915 3233919419106483766835873)
                  ·
                    refine ⟨2425439564329862825126905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3233919419106483766835873 2425439564329862825126905)
                    ·
                      refine ⟨1819079673247397118845179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2425439564329862825126905 1819079673247397118845179)
                      ·
                        rfl

theorem cell23_3542645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_3542645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3542645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3542645 prefixEnd_3542645 := by exact prefixLift 3542645
  have htrace : WordTrace (prefixWord ++ tailWord_3542645) baseStart_3542645 baseEnd_3542645 := by
    simpa [prefixWord, tailWord_3542645, baseEnd_3542645] using wordTrace_append hprefix tailTrace_3542645
  have hstable : (prefixWord ++ tailWord_3542645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542645).length < 2 ^ (prefixWord ++ tailWord_3542645).sum := by decide
  have hdescent : baseEnd_3542645 < baseStart_3542645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542667 : List Nat := [1, 1, 1, 1, 4, 1, 4, 3, 1, 4, 2]
def baseStart_3542667 : Nat := 118140960795 + 3542667 * 2 ^ 59
def prefixEnd_3542667 : Nat := 4983230072969 + 3 ^ 40 * 3542667 * 2
def baseEnd_3542667 : Nat := 1819090969821796032770077

theorem tailTrace_3542667 : CollatzResearch.WordTrace tailWord_3542667 prefixEnd_3542667 1819090969821796032770077 := by
  unfold tailWord_3542667
  simp only [CollatzResearch.WordTrace]
  refine ⟨129211680656529973199066255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86141120437686648799377503 129211680656529973199066255)
  ·
    refine ⟨193817520984794959798599383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129211680656529973199066255 193817520984794959798599383)
    ·
      refine ⟨290726281477192439697899075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193817520984794959798599383 290726281477192439697899075)
      ·
        refine ⟨436089422215788659546848613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290726281477192439697899075 436089422215788659546848613)
        ·
          refine ⟨81766766665460373665034115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 436089422215788659546848613 81766766665460373665034115)
          ·
            refine ⟨122650149998190560497551173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81766766665460373665034115 122650149998190560497551173)
            ·
              refine ⟨22996903124660730093290845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122650149998190560497551173 22996903124660730093290845)
              ·
                refine ⟨8623838671747773784984067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22996903124660730093290845 8623838671747773784984067)
                ·
                  refine ⟨12935758007621660677476101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8623838671747773784984067 12935758007621660677476101)
                  ·
                    refine ⟨2425454626429061377026769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12935758007621660677476101 2425454626429061377026769)
                    ·
                      refine ⟨1819090969821796032770077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2425454626429061377026769 1819090969821796032770077)
                      ·
                        rfl

theorem cell23_3542667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 3, 1, 4, 2].length) (baseStart_3542667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3542667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3542667 prefixEnd_3542667 := by exact prefixLift 3542667
  have htrace : WordTrace (prefixWord ++ tailWord_3542667) baseStart_3542667 baseEnd_3542667 := by
    simpa [prefixWord, tailWord_3542667, baseEnd_3542667] using wordTrace_append hprefix tailTrace_3542667
  have hstable : (prefixWord ++ tailWord_3542667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542667).length < 2 ^ (prefixWord ++ tailWord_3542667).sum := by decide
  have hdescent : baseEnd_3542667 < baseStart_3542667 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542696 : List Nat := [2, 1, 7, 1, 2, 1, 2, 2, 1, 2, 2]
def baseStart_3542696 : Nat := 118140960795 + 3542696 * 2 ^ 59
def prefixEnd_3542696 : Nat := 4983230072969 + 3 ^ 40 * 3542696 * 2
def baseEnd_3542696 : Nat := 1819105860760776419307445

theorem tailTrace_3542696 : CollatzResearch.WordTrace tailWord_3542696 prefixEnd_3542696 1819105860760776419307445 := by
  unfold tailWord_3542696
  simp only [CollatzResearch.WordTrace]
  refine ⟨64606369186712455575935971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86141825582283274101247961 64606369186712455575935971)
  ·
    refine ⟨96909553780068683363903957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64606369186712455575935971 96909553780068683363903957)
    ·
      refine ⟨2271317666720359766341499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 96909553780068683363903957 2271317666720359766341499)
      ·
        refine ⟨3406976500080539649512249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2271317666720359766341499 3406976500080539649512249)
        ·
          refine ⟨2555232375060404737134187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3406976500080539649512249 2555232375060404737134187)
          ·
            refine ⟨3832848562590607105701281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2555232375060404737134187 3832848562590607105701281)
            ·
              refine ⟨2874636421942955329275961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3832848562590607105701281 2874636421942955329275961)
              ·
                refine ⟨2155977316457216496956971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2874636421942955329275961 2155977316457216496956971)
                ·
                  refine ⟨3233965974685824745435457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2155977316457216496956971 3233965974685824745435457)
                  ·
                    refine ⟨2425474481014368559076593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3233965974685824745435457 2425474481014368559076593)
                    ·
                      refine ⟨1819105860760776419307445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2425474481014368559076593 1819105860760776419307445)
                      ·
                        rfl

theorem cell23_3542696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_3542696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3542696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3542696 prefixEnd_3542696 := by exact prefixLift 3542696
  have htrace : WordTrace (prefixWord ++ tailWord_3542696) baseStart_3542696 baseEnd_3542696 := by
    simpa [prefixWord, tailWord_3542696, baseEnd_3542696] using wordTrace_append hprefix tailTrace_3542696
  have hstable : (prefixWord ++ tailWord_3542696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542696).length < 2 ^ (prefixWord ++ tailWord_3542696).sum := by decide
  have hdescent : baseEnd_3542696 < baseStart_3542696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542700 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 3]
def baseStart_3542700 : Nat := 118140960795 + 3542700 * 2 ^ 59
def prefixEnd_3542700 : Nat := 4983230072969 + 3 ^ 40 * 3542700 * 2
def baseEnd_3542700 : Nat := 1819107914683394403657425

theorem tailTrace_3542700 : CollatzResearch.WordTrace tailWord_3542700 prefixEnd_3542700 1819107914683394403657425 := by
  unfold tailWord_3542700
  simp only [CollatzResearch.WordTrace]
  refine ⟨64606442132705209917508777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86141922843606946556678369 64606442132705209917508777)
  ·
    refine ⟨48454831599528907438131583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64606442132705209917508777 48454831599528907438131583)
    ·
      refine ⟨72682247399293361157197375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48454831599528907438131583 72682247399293361157197375)
      ·
        refine ⟨109023371098940041735796063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72682247399293361157197375 109023371098940041735796063)
        ·
          refine ⟨163535056648410062603694095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109023371098940041735796063 163535056648410062603694095)
          ·
            refine ⟨245302584972615093905541143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163535056648410062603694095 245302584972615093905541143)
            ·
              refine ⟨367953877458922640858311715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245302584972615093905541143 367953877458922640858311715)
              ·
                refine ⟨551930816188383961287467573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 367953877458922640858311715 551930816188383961287467573)
                ·
                  refine ⟨51743514017660996370700085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 551930816188383961287467573 51743514017660996370700085)
                  ·
                    refine ⟨4850954439155718409753133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51743514017660996370700085 4850954439155718409753133)
                    ·
                      refine ⟨1819107914683394403657425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4850954439155718409753133 1819107914683394403657425)
                      ·
                        rfl

theorem cell23_3542700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 3].length) (baseStart_3542700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3542700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3542700 prefixEnd_3542700 := by exact prefixLift 3542700
  have htrace : WordTrace (prefixWord ++ tailWord_3542700) baseStart_3542700 baseEnd_3542700 := by
    simpa [prefixWord, tailWord_3542700, baseEnd_3542700] using wordTrace_append hprefix tailTrace_3542700
  have hstable : (prefixWord ++ tailWord_3542700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542700).length < 2 ^ (prefixWord ++ tailWord_3542700).sum := by decide
  have hdescent : baseEnd_3542700 < baseStart_3542700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542707 : List Nat := [1, 1, 1, 2, 3, 3, 3, 4, 5]
def baseStart_3542707 : Nat := 118140960795 + 3542707 * 2 ^ 59
def prefixEnd_3542707 : Nat := 4983230072969 + 3 ^ 40 * 3542707 * 2
def baseEnd_3542707 : Nat := 202123501005330652918877

theorem tailTrace_3542707 : CollatzResearch.WordTrace tailWord_3542707 prefixEnd_3542707 202123501005330652918877 := by
  unfold tailWord_3542707
  simp only [CollatzResearch.WordTrace]
  refine ⟨129213139576385060030522375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86142093050923373353681583 129213139576385060030522375)
  ·
    refine ⟨193819709364577590045783563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129213139576385060030522375 193819709364577590045783563)
    ·
      refine ⟨290729564046866385068675345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193819709364577590045783563 290729564046866385068675345)
      ·
        refine ⟨218047173035149788801506509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290729564046866385068675345 218047173035149788801506509)
        ·
          refine ⟨81767689888181170800564941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218047173035149788801506509 81767689888181170800564941)
          ·
            refine ⟨30662883708067939050211853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81767689888181170800564941 30662883708067939050211853)
            ·
              refine ⟨11498581390525477143829445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30662883708067939050211853 11498581390525477143829445)
              ·
                refine ⟨2155984010723526964468021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11498581390525477143829445 2155984010723526964468021)
                ·
                  refine ⟨202123501005330652918877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2155984010723526964468021 202123501005330652918877)
                  ·
                    rfl

theorem cell23_3542707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 4, 5].length) (baseStart_3542707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3542707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3542707 prefixEnd_3542707 := by exact prefixLift 3542707
  have htrace : WordTrace (prefixWord ++ tailWord_3542707) baseStart_3542707 baseEnd_3542707 := by
    simpa [prefixWord, tailWord_3542707, baseEnd_3542707] using wordTrace_append hprefix tailTrace_3542707
  have hstable : (prefixWord ++ tailWord_3542707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542707).length < 2 ^ (prefixWord ++ tailWord_3542707).sum := by decide
  have hdescent : baseEnd_3542707 < baseStart_3542707 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542717 : List Nat := [1, 4, 1, 2, 1, 2, 3, 1, 2, 3, 3]
def baseStart_3542717 : Nat := 118140960795 + 3542717 * 2 ^ 59
def prefixEnd_3542717 : Nat := 4983230072969 + 3 ^ 40 * 3542717 * 2
def baseEnd_3542717 : Nat := 1819116643854520837144847

theorem tailTrace_3542717 : CollatzResearch.WordTrace tailWord_3542717 prefixEnd_3542717 1819116643854520837144847 := by
  unfold tailWord_3542717
  simp only [CollatzResearch.WordTrace]
  refine ⟨129213504306348831738386405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86142336204232554492257603 129213504306348831738386405)
  ·
    refine ⟨24227532057440405950947451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129213504306348831738386405 24227532057440405950947451)
    ·
      refine ⟨36341298086160608926421177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24227532057440405950947451 36341298086160608926421177)
      ·
        refine ⟨27255973564620456694815883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36341298086160608926421177 27255973564620456694815883)
        ·
          refine ⟨40883960346930685042223825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27255973564620456694815883 40883960346930685042223825)
          ·
            refine ⟨30662970260198013781667869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40883960346930685042223825 30662970260198013781667869)
            ·
              refine ⟨11498613847574255168125451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30662970260198013781667869 11498613847574255168125451)
              ·
                refine ⟨17247920771361382752188177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11498613847574255168125451 17247920771361382752188177)
                ·
                  refine ⟨12935940578521037064141133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17247920771361382752188177 12935940578521037064141133)
                  ·
                    refine ⟨4850977716945388899052925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12935940578521037064141133 4850977716945388899052925)
                    ·
                      refine ⟨1819116643854520837144847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4850977716945388899052925 1819116643854520837144847)
                      ·
                        rfl

theorem cell23_3542717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 2, 3, 3].length) (baseStart_3542717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3542717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3542717 prefixEnd_3542717 := by exact prefixLift 3542717
  have htrace : WordTrace (prefixWord ++ tailWord_3542717) baseStart_3542717 baseEnd_3542717 := by
    simpa [prefixWord, tailWord_3542717, baseEnd_3542717] using wordTrace_append hprefix tailTrace_3542717
  have hstable : (prefixWord ++ tailWord_3542717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542717).length < 2 ^ (prefixWord ++ tailWord_3542717).sum := by decide
  have hdescent : baseEnd_3542717 < baseStart_3542717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542720 : List Nat := [2, 1, 1, 2, 4, 1, 2, 2, 1, 7]
def baseStart_3542720 : Nat := 118140960795 + 3542720 * 2 ^ 59
def prefixEnd_3542720 : Nat := 4983230072969 + 3 ^ 40 * 3542720 * 2
def baseEnd_3542720 : Nat := 606372728098828108469111

theorem tailTrace_3542720 : CollatzResearch.WordTrace tailWord_3542720 prefixEnd_3542720 606372728098828108469111 := by
  unfold tailWord_3542720
  simp only [CollatzResearch.WordTrace]
  refine ⟨64606806862668981625372807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86142409150225308833830409 64606806862668981625372807)
  ·
    refine ⟨96910210294003472438059211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64606806862668981625372807 96910210294003472438059211)
    ·
      refine ⟨145365315441005208657088817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96910210294003472438059211 145365315441005208657088817)
      ·
        refine ⟨109023986580753906492816613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145365315441005208657088817 109023986580753906492816613)
        ·
          refine ⟨20441997483891357467403115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109023986580753906492816613 20441997483891357467403115)
          ·
            refine ⟨30662996225837036201104673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20441997483891357467403115 30662996225837036201104673)
            ·
              refine ⟨22997247169377777150828505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30662996225837036201104673 22997247169377777150828505)
              ·
                refine ⟨17247935377033332863121379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22997247169377777150828505 17247935377033332863121379)
                ·
                  refine ⟨25871903065549999294682069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17247935377033332863121379 25871903065549999294682069)
                  ·
                    refine ⟨606372728098828108469111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25871903065549999294682069 606372728098828108469111)
                    ·
                      rfl

theorem cell23_3542720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 1, 7].length) (baseStart_3542720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3542720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3542720 prefixEnd_3542720 := by exact prefixLift 3542720
  have htrace : WordTrace (prefixWord ++ tailWord_3542720) baseStart_3542720 baseEnd_3542720 := by
    simpa [prefixWord, tailWord_3542720, baseEnd_3542720] using wordTrace_append hprefix tailTrace_3542720
  have hstable : (prefixWord ++ tailWord_3542720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542720).length < 2 ^ (prefixWord ++ tailWord_3542720).sum := by decide
  have hdescent : baseEnd_3542720 < baseStart_3542720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542727 : List Nat := [1, 1, 4, 1, 1, 1, 3, 2, 2, 5, 2]
def baseStart_3542727 : Nat := 118140960795 + 3542727 * 2 ^ 59
def prefixEnd_3542727 : Nat := 4983230072969 + 3 ^ 40 * 3542727 * 2
def baseEnd_3542727 : Nat := 1819121778661065798019801

theorem tailTrace_3542727 : CollatzResearch.WordTrace tailWord_3542727 prefixEnd_3542727 1819121778661065798019801 := by
  unfold tailWord_3542727
  simp only [CollatzResearch.WordTrace]
  refine ⟨129213869036312603446250435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86142579357541735630833623 129213869036312603446250435)
  ·
    refine ⟨193820803554468905169375653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129213869036312603446250435 193820803554468905169375653)
    ·
      refine ⟨36341400666462919719257935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 193820803554468905169375653 36341400666462919719257935)
      ·
        refine ⟨54512100999694379578886903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36341400666462919719257935 54512100999694379578886903)
        ·
          refine ⟨81768151499541569368330355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54512100999694379578886903 81768151499541569368330355)
          ·
            refine ⟨122652227249312354052495533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81768151499541569368330355 122652227249312354052495533)
            ·
              refine ⟨45994585218492132769685825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122652227249312354052495533 45994585218492132769685825)
              ·
                refine ⟨34495938913869099577264369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45994585218492132769685825 34495938913869099577264369)
                ·
                  refine ⟨25871954185401824682948277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34495938913869099577264369 25871954185401824682948277)
                  ·
                    refine ⟨2425495704881421064026401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25871954185401824682948277 2425495704881421064026401)
                    ·
                      refine ⟨1819121778661065798019801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2425495704881421064026401 1819121778661065798019801)
                      ·
                        rfl

theorem cell23_3542727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 5, 2].length) (baseStart_3542727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3542727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3542727 prefixEnd_3542727 := by exact prefixLift 3542727
  have htrace : WordTrace (prefixWord ++ tailWord_3542727) baseStart_3542727 baseEnd_3542727 := by
    simpa [prefixWord, tailWord_3542727, baseEnd_3542727] using wordTrace_append hprefix tailTrace_3542727
  have hstable : (prefixWord ++ tailWord_3542727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542727).length < 2 ^ (prefixWord ++ tailWord_3542727).sum := by decide
  have hdescent : baseEnd_3542727 < baseStart_3542727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542737 : List Nat := [1, 2, 2, 1, 2, 4, 3, 1, 2, 5]
def baseStart_3542737 : Nat := 118140960795 + 3542737 * 2 ^ 59
def prefixEnd_3542737 : Nat := 4983230072969 + 3 ^ 40 * 3542737 * 2
def baseEnd_3542737 : Nat := 606375637822536919631585

theorem tailTrace_3542737 : CollatzResearch.WordTrace tailWord_3542737 prefixEnd_3542737 606375637822536919631585 := by
  unfold tailWord_3542737
  simp only [CollatzResearch.WordTrace]
  refine ⟨129214233766276375154114465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86142822510850916769409643 129214233766276375154114465)
  ·
    refine ⟨96910675324707281365585849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129214233766276375154114465 96910675324707281365585849)
    ·
      refine ⟨72683006493530461024189387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96910675324707281365585849 72683006493530461024189387)
      ·
        refine ⟨109024509740295691536284081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72683006493530461024189387 109024509740295691536284081)
        ·
          refine ⟨81768382305221768652213061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109024509740295691536284081 81768382305221768652213061)
          ·
            refine ⟨15331571682229081622289949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81768382305221768652213061 15331571682229081622289949)
            ·
              refine ⟨5749339380835905608358731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15331571682229081622289949 5749339380835905608358731)
              ·
                refine ⟨8624009071253858412538097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5749339380835905608358731 8624009071253858412538097)
                ·
                  refine ⟨6468006803440393809403573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8624009071253858412538097 6468006803440393809403573)
                  ·
                    refine ⟨606375637822536919631585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6468006803440393809403573 606375637822536919631585)
                    ·
                      rfl

theorem cell23_3542737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 1, 2, 5].length) (baseStart_3542737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3542737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3542737 prefixEnd_3542737 := by exact prefixLift 3542737
  have htrace : WordTrace (prefixWord ++ tailWord_3542737) baseStart_3542737 baseEnd_3542737 := by
    simpa [prefixWord, tailWord_3542737, baseEnd_3542737] using wordTrace_append hprefix tailTrace_3542737
  have hstable : (prefixWord ++ tailWord_3542737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542737).length < 2 ^ (prefixWord ++ tailWord_3542737).sum := by decide
  have hdescent : baseEnd_3542737 < baseStart_3542737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542757 : List Nat := [1, 3, 1, 4, 1, 1, 2, 1, 4, 1, 4]
def baseStart_3542757 : Nat := 118140960795 + 3542757 * 2 ^ 59
def prefixEnd_3542757 : Nat := 4983230072969 + 3 ^ 40 * 3542757 * 2
def baseEnd_3542757 : Nat := 1819137183080700680644663

theorem tailTrace_3542757 : CollatzResearch.WordTrace tailWord_3542757 prefixEnd_3542757 1819137183080700680644663 := by
  unfold tailWord_3542757
  simp only [CollatzResearch.WordTrace]
  refine ⟨129214963226203918569842525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86143308817469279046561683 129214963226203918569842525)
  ·
    refine ⟨48455611209826469463690947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129214963226203918569842525 48455611209826469463690947)
    ·
      refine ⟨72683416814739704195536421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48455611209826469463690947 72683416814739704195536421)
      ·
        refine ⟨13628140652763694536663079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72683416814739704195536421 13628140652763694536663079)
        ·
          refine ⟨20442210979145541804994619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13628140652763694536663079 20442210979145541804994619)
          ·
            refine ⟨30663316468718312707491929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20442210979145541804994619 30663316468718312707491929)
            ·
              refine ⟨22997487351538734530618947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30663316468718312707491929 22997487351538734530618947)
              ·
                refine ⟨34496231027308101795928421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22997487351538734530618947 34496231027308101795928421)
                ·
                  refine ⟨6468043317620269086736579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34496231027308101795928421 6468043317620269086736579)
                  ·
                    refine ⟨9702064976430403630104869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6468043317620269086736579 9702064976430403630104869)
                    ·
                      refine ⟨1819137183080700680644663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9702064976430403630104869 1819137183080700680644663)
                      ·
                        rfl

theorem cell23_3542757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_3542757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3542757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3542757 prefixEnd_3542757 := by exact prefixLift 3542757
  have htrace : WordTrace (prefixWord ++ tailWord_3542757) baseStart_3542757 baseEnd_3542757 := by
    simpa [prefixWord, tailWord_3542757, baseEnd_3542757] using wordTrace_append hprefix tailTrace_3542757
  have hstable : (prefixWord ++ tailWord_3542757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542757).length < 2 ^ (prefixWord ++ tailWord_3542757).sum := by decide
  have hdescent : baseEnd_3542757 < baseStart_3542757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542818 : List Nat := [3, 3, 1, 1, 2, 1, 5, 2, 1, 4]
def baseStart_3542818 : Nat := 118140960795 + 3542818 * 2 ^ 59
def prefixEnd_3542818 : Nat := 4983230072969 + 3 ^ 40 * 3542818 * 2
def baseEnd_3542818 : Nat := 606389501800208313993961

theorem tailTrace_3542818 : CollatzResearch.WordTrace tailWord_3542818 prefixEnd_3542818 606389501800208313993961 := by
  unfold tailWord_3542818
  simp only [CollatzResearch.WordTrace]
  refine ⟨32304297019745731496953277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86144792052655283991875405 32304297019745731496953277)
  ·
    refine ⟨12114111382404649311357479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32304297019745731496953277 12114111382404649311357479)
    ·
      refine ⟨18171167073606973967036219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12114111382404649311357479 18171167073606973967036219)
      ·
        refine ⟨27256750610410460950554329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18171167073606973967036219 27256750610410460950554329)
        ·
          refine ⟨20442562957807845712915747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27256750610410460950554329 20442562957807845712915747)
          ·
            refine ⟨30663844436711768569373621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20442562957807845712915747 30663844436711768569373621)
            ·
              refine ⟨2874735415941728303378777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30663844436711768569373621 2874735415941728303378777)
              ·
                refine ⟨2156051561956296227534083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2874735415941728303378777 2156051561956296227534083)
                ·
                  refine ⟨3234077342934444341301125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2156051561956296227534083 3234077342934444341301125)
                  ·
                    refine ⟨606389501800208313993961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3234077342934444341301125 606389501800208313993961)
                    ·
                      rfl

theorem cell23_3542818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 5, 2, 1, 4].length) (baseStart_3542818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3542818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3542818 prefixEnd_3542818 := by exact prefixLift 3542818
  have htrace : WordTrace (prefixWord ++ tailWord_3542818) baseStart_3542818 baseEnd_3542818 := by
    simpa [prefixWord, tailWord_3542818, baseEnd_3542818] using wordTrace_append hprefix tailTrace_3542818
  have hstable : (prefixWord ++ tailWord_3542818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542818).length < 2 ^ (prefixWord ++ tailWord_3542818).sum := by decide
  have hdescent : baseEnd_3542818 < baseStart_3542818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542844 : List Nat := [2, 2, 2, 2, 1, 1, 5, 2, 1, 5]
def baseStart_3542844 : Nat := 118140960795 + 3542844 * 2 ^ 59
def prefixEnd_3542844 : Nat := 4983230072969 + 3 ^ 40 * 3542844 * 2
def baseEnd_3542844 : Nat := 606393951965880613418921

theorem tailTrace_3542844 : CollatzResearch.WordTrace tailWord_3542844 prefixEnd_3542844 606393951965880613418921 := by
  unfold tailWord_3542844
  simp only [CollatzResearch.WordTrace]
  refine ⟨64609068188444366214129793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86145424251259154952173057 64609068188444366214129793)
  ·
    refine ⟨48456801141333274660597345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64609068188444366214129793 48456801141333274660597345)
    ·
      refine ⟨36342600855999955995448009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48456801141333274660597345 36342600855999955995448009)
      ·
        refine ⟨27256950641999966996586007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36342600855999955995448009 27256950641999966996586007)
        ·
          refine ⟨40885425962999950494879011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27256950641999966996586007 40885425962999950494879011)
          ·
            refine ⟨61328138944499925742318517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40885425962999950494879011 61328138944499925742318517)
            ·
              refine ⟨5749513026046868038342361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61328138944499925742318517 5749513026046868038342361)
              ·
                refine ⟨4312134769535151028756771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5749513026046868038342361 4312134769535151028756771)
                ·
                  refine ⟨6468202154302726543135157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4312134769535151028756771 6468202154302726543135157)
                  ·
                    refine ⟨606393951965880613418921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6468202154302726543135157 606393951965880613418921)
                    ·
                      rfl

theorem cell23_3542844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 2, 1, 5].length) (baseStart_3542844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3542844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3542844 prefixEnd_3542844 := by exact prefixLift 3542844
  have htrace : WordTrace (prefixWord ++ tailWord_3542844) baseStart_3542844 baseEnd_3542844 := by
    simpa [prefixWord, tailWord_3542844, baseEnd_3542844] using wordTrace_append hprefix tailTrace_3542844
  have hstable : (prefixWord ++ tailWord_3542844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542844).length < 2 ^ (prefixWord ++ tailWord_3542844).sum := by decide
  have hdescent : baseEnd_3542844 < baseStart_3542844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542851 : List Nat := [1, 1, 1, 3, 1, 6, 2, 1, 2, 3, 2]
def baseStart_3542851 : Nat := 118140960795 + 3542851 * 2 ^ 59
def prefixEnd_3542851 : Nat := 4983230072969 + 3 ^ 40 * 3542851 * 2
def baseEnd_3542851 : Nat := 1819185450262223312869231

theorem tailTrace_3542851 : CollatzResearch.WordTrace tailWord_3542851 prefixEnd_3542851 1819185450262223312869231 := by
  unfold tailWord_3542851
  simp only [CollatzResearch.WordTrace]
  refine ⟨129218391687863372623764407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86145594458575581749176271 129218391687863372623764407)
  ·
    refine ⟨193827587531795058935646611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129218391687863372623764407 193827587531795058935646611)
    ·
      refine ⟨290741381297692588403469917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193827587531795058935646611 290741381297692588403469917)
      ·
        refine ⟨109028017986634720651301219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 290741381297692588403469917 109028017986634720651301219)
        ·
          refine ⟨163542026979952080976951829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109028017986634720651301219 163542026979952080976951829)
          ·
            refine ⟨7666032514685253795794617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 163542026979952080976951829 7666032514685253795794617)
            ·
              refine ⟨5749524386013940346845963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7666032514685253795794617 5749524386013940346845963)
              ·
                refine ⟨8624286579020910520268945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5749524386013940346845963 8624286579020910520268945)
                ·
                  refine ⟨6468214934265682890201709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8624286579020910520268945 6468214934265682890201709)
                  ·
                    refine ⟨2425580600349631083825641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6468214934265682890201709 2425580600349631083825641)
                    ·
                      refine ⟨1819185450262223312869231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2425580600349631083825641 1819185450262223312869231)
                      ·
                        rfl

theorem cell23_3542851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 1, 2, 3, 2].length) (baseStart_3542851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3542851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3542851 prefixEnd_3542851 := by exact prefixLift 3542851
  have htrace : WordTrace (prefixWord ++ tailWord_3542851) baseStart_3542851 baseEnd_3542851 := by
    simpa [prefixWord, tailWord_3542851, baseEnd_3542851] using wordTrace_append hprefix tailTrace_3542851
  have hstable : (prefixWord ++ tailWord_3542851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542851).length < 2 ^ (prefixWord ++ tailWord_3542851).sum := by decide
  have hdescent : baseEnd_3542851 < baseStart_3542851 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542857 : List Nat := [1, 2, 1, 1, 2, 4, 3, 2, 1, 6]
def baseStart_3542857 : Nat := 118140960795 + 3542857 * 2 ^ 59
def prefixEnd_3542857 : Nat := 4983230072969 + 3 ^ 40 * 3542857 * 2
def baseEnd_3542857 : Nat := 606396177048716763131401

theorem tailTrace_3542857 : CollatzResearch.WordTrace tailWord_3542857 prefixEnd_3542857 606396177048716763131401 := by
  unfold tailWord_3542857
  simp only [CollatzResearch.WordTrace]
  refine ⟨129218610525841635648482825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86145740350561090432321883 129218610525841635648482825)
  ·
    refine ⟨96913957894381226736362119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129218610525841635648482825 96913957894381226736362119)
    ·
      refine ⟨145370936841571840104543179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96913957894381226736362119 145370936841571840104543179)
      ·
        refine ⟨218056405262357760156814769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145370936841571840104543179 218056405262357760156814769)
        ·
          refine ⟨163542303946768320117611077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218056405262357760156814769 163542303946768320117611077)
          ·
            refine ⟨30664181990019060022052077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 163542303946768320117611077 30664181990019060022052077)
            ·
              refine ⟨11499068246257147508269529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30664181990019060022052077 11499068246257147508269529)
              ·
                refine ⟨8624301184692860631202147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11499068246257147508269529 8624301184692860631202147)
                ·
                  refine ⟨12936451777039290946803221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8624301184692860631202147 12936451777039290946803221)
                  ·
                    refine ⟨606396177048716763131401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12936451777039290946803221 606396177048716763131401)
                    ·
                      rfl

theorem cell23_3542857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 2, 1, 6].length) (baseStart_3542857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3542857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3542857 prefixEnd_3542857 := by exact prefixLift 3542857
  have htrace : WordTrace (prefixWord ++ tailWord_3542857) baseStart_3542857 baseEnd_3542857 := by
    simpa [prefixWord, tailWord_3542857, baseEnd_3542857] using wordTrace_append hprefix tailTrace_3542857
  have hstable : (prefixWord ++ tailWord_3542857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542857).length < 2 ^ (prefixWord ++ tailWord_3542857).sum := by decide
  have hdescent : baseEnd_3542857 < baseStart_3542857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542881 : List Nat := [1, 2, 3, 1, 1, 1, 4, 3, 3, 2, 2]
def baseStart_3542881 : Nat := 118140960795 + 3542881 * 2 ^ 59
def prefixEnd_3542881 : Nat := 4983230072969 + 3 ^ 40 * 3542881 * 2
def baseEnd_3542881 : Nat := 1819200854681858195494093

theorem tailTrace_3542881 : CollatzResearch.WordTrace tailWord_3542881 prefixEnd_3542881 1819200854681858195494093 := by
  unfold tailWord_3542881
  simp only [CollatzResearch.WordTrace]
  refine ⟨129219485877754687747356497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86146323918503125164904331 129219485877754687747356497)
  ·
    refine ⟨96914614408316015810517373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129219485877754687747356497 96914614408316015810517373)
    ·
      refine ⟨36342980403118505928944015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96914614408316015810517373 36342980403118505928944015)
      ·
        refine ⟨54514470604677758893416023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36342980403118505928944015 54514470604677758893416023)
        ·
          refine ⟨81771705907016638340124035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54514470604677758893416023 81771705907016638340124035)
          ·
            refine ⟨122657558860524957510186053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81771705907016638340124035 122657558860524957510186053)
            ·
              refine ⟨22998292286348429533159885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122657558860524957510186053 22998292286348429533159885)
              ·
                refine ⟨8624359607380661074934957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22998292286348429533159885 8624359607380661074934957)
                ·
                  refine ⟨3234134852767747903100609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8624359607380661074934957 3234134852767747903100609)
                  ·
                    refine ⟨2425601139575810927325457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3234134852767747903100609 2425601139575810927325457)
                    ·
                      refine ⟨1819200854681858195494093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2425601139575810927325457 1819200854681858195494093)
                      ·
                        rfl

theorem cell23_3542881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 3, 3, 2, 2].length) (baseStart_3542881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3542881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3542881 prefixEnd_3542881 := by exact prefixLift 3542881
  have htrace : WordTrace (prefixWord ++ tailWord_3542881) baseStart_3542881 baseEnd_3542881 := by
    simpa [prefixWord, tailWord_3542881, baseEnd_3542881] using wordTrace_append hprefix tailTrace_3542881
  have hstable : (prefixWord ++ tailWord_3542881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542881).length < 2 ^ (prefixWord ++ tailWord_3542881).sum := by decide
  have hdescent : baseEnd_3542881 < baseStart_3542881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542901 : List Nat := [1, 3, 4, 1, 1, 1, 2, 4, 1, 2, 3]
def baseStart_3542901 : Nat := 118140960795 + 3542901 * 2 ^ 59
def prefixEnd_3542901 : Nat := 4983230072969 + 3 ^ 40 * 3542901 * 2
def baseEnd_3542901 : Nat := 1819211124294948117244001

theorem tailTrace_3542901 : CollatzResearch.WordTrace tailWord_3542901 prefixEnd_3542901 1819211124294948117244001 := by
  unfold tailWord_3542901
  simp only [CollatzResearch.WordTrace]
  refine ⟨129220215337682231163084557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86146810225121487442056371 129220215337682231163084557)
  ·
    refine ⟨48457580751630836686156709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129220215337682231163084557 48457580751630836686156709)
    ·
      refine ⟨9085796390930781878654383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48457580751630836686156709 9085796390930781878654383)
      ·
        refine ⟨13628694586396172817981575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9085796390930781878654383 13628694586396172817981575)
        ·
          refine ⟨20443041879594259226972363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13628694586396172817981575 20443041879594259226972363)
          ·
            refine ⟨30664562819391388840458545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20443041879594259226972363 30664562819391388840458545)
            ·
              refine ⟨22998422114543541630343909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30664562819391388840458545 22998422114543541630343909)
              ·
                refine ⟨4312204146476914055689483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22998422114543541630343909 4312204146476914055689483)
                ·
                  refine ⟨6468306219715371083534225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4312204146476914055689483 6468306219715371083534225)
                  ·
                    refine ⟨4851229664786528312650669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6468306219715371083534225 4851229664786528312650669)
                    ·
                      refine ⟨1819211124294948117244001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4851229664786528312650669 1819211124294948117244001)
                      ·
                        rfl

theorem cell23_3542901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_3542901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3542901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3542901 prefixEnd_3542901 := by exact prefixLift 3542901
  have htrace : WordTrace (prefixWord ++ tailWord_3542901) baseStart_3542901 baseEnd_3542901 := by
    simpa [prefixWord, tailWord_3542901, baseEnd_3542901] using wordTrace_append hprefix tailTrace_3542901
  have hstable : (prefixWord ++ tailWord_3542901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542901).length < 2 ^ (prefixWord ++ tailWord_3542901).sum := by decide
  have hdescent : baseEnd_3542901 < baseStart_3542901 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542902 : List Nat := [5, 1, 1, 3, 3, 1, 1, 1, 2, 3, 2]
def baseStart_3542902 : Nat := 118140960795 + 3542902 * 2 ^ 59
def prefixEnd_3542902 : Nat := 4983230072969 + 3 ^ 40 * 3542902 * 2
def baseEnd_3542902 : Nat := 1819211637775602613331497

theorem tailTrace_3542902 : CollatzResearch.WordTrace tailWord_3542902 prefixEnd_3542902 1819211637775602613331497 := by
  unfold tailWord_3542902
  simp only [CollatzResearch.WordTrace]
  refine ⟨8076265738167413020866935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86146834540452405555913973 8076265738167413020866935)
  ·
    refine ⟨12114398607251119531300403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8076265738167413020866935 12114398607251119531300403)
    ·
      refine ⟨18171597910876679296950605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12114398607251119531300403 18171597910876679296950605)
      ·
        refine ⟨6814349216578754736356477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18171597910876679296950605 6814349216578754736356477)
        ·
          refine ⟨2555380956217033026133679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6814349216578754736356477 2555380956217033026133679)
          ·
            refine ⟨3833071434325549539200519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2555380956217033026133679 3833071434325549539200519)
            ·
              refine ⟨5749607151488324308800779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3833071434325549539200519 5749607151488324308800779)
              ·
                refine ⟨8624410727232486463201169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5749607151488324308800779 8624410727232486463201169)
                ·
                  refine ⟨6468308045424364847400877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8624410727232486463201169 6468308045424364847400877)
                  ·
                    refine ⟨2425615517034136817775329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6468308045424364847400877 2425615517034136817775329)
                    ·
                      refine ⟨1819211637775602613331497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2425615517034136817775329 1819211637775602613331497)
                      ·
                        rfl

theorem cell23_3542902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_3542902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3542902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3542902 prefixEnd_3542902 := by exact prefixLift 3542902
  have htrace : WordTrace (prefixWord ++ tailWord_3542902) baseStart_3542902 baseEnd_3542902 := by
    simpa [prefixWord, tailWord_3542902, baseEnd_3542902] using wordTrace_append hprefix tailTrace_3542902
  have hstable : (prefixWord ++ tailWord_3542902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542902).length < 2 ^ (prefixWord ++ tailWord_3542902).sum := by decide
  have hdescent : baseEnd_3542902 < baseStart_3542902 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542915 : List Nat := [1, 1, 1, 3, 4, 3, 2, 3, 1, 2, 2]
def baseStart_3542915 : Nat := 118140960795 + 3542915 * 2 ^ 59
def prefixEnd_3542915 : Nat := 4983230072969 + 3 ^ 40 * 3542915 * 2
def baseEnd_3542915 : Nat := 1819218313024111062468937

theorem tailTrace_3542915 : CollatzResearch.WordTrace tailWord_3542915 prefixEnd_3542915 1819218313024111062468937 := by
  unfold tailWord_3542915
  simp only [CollatzResearch.WordTrace]
  refine ⟨129220725959631511554094199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86147150639754341036062799 129220725959631511554094199)
  ·
    refine ⟨193831088939447267331141299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129220725959631511554094199 193831088939447267331141299)
    ·
      refine ⟨290746633409170900996711949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193831088939447267331141299 290746633409170900996711949)
      ·
        refine ⟨109029987528439087873766981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 290746633409170900996711949 109029987528439087873766981)
        ·
          refine ⟨20443122661582328976331309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109029987528439087873766981 20443122661582328976331309)
          ·
            refine ⟨7666170998093373366124241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20443122661582328976331309 7666170998093373366124241)
            ·
              refine ⟨5749628248570030024593181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7666170998093373366124241 5749628248570030024593181)
              ·
                refine ⟨2156110593213761259222443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5749628248570030024593181 2156110593213761259222443)
                ·
                  refine ⟨3234165889820641888833665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2156110593213761259222443 3234165889820641888833665)
                  ·
                    refine ⟨2425624417365481416625249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3234165889820641888833665 2425624417365481416625249)
                    ·
                      refine ⟨1819218313024111062468937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2425624417365481416625249 1819218313024111062468937)
                      ·
                        rfl

theorem cell23_3542915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 3, 1, 2, 2].length) (baseStart_3542915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3542915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3542915 prefixEnd_3542915 := by exact prefixLift 3542915
  have htrace : WordTrace (prefixWord ++ tailWord_3542915) baseStart_3542915 baseEnd_3542915 := by
    simpa [prefixWord, tailWord_3542915, baseEnd_3542915] using wordTrace_append hprefix tailTrace_3542915
  have hstable : (prefixWord ++ tailWord_3542915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542915).length < 2 ^ (prefixWord ++ tailWord_3542915).sum := by decide
  have hdescent : baseEnd_3542915 < baseStart_3542915 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542937 : List Nat := [1, 2, 1, 2, 1, 3, 2, 1, 1, 5, 4]
def baseStart_3542937 : Nat := 118140960795 + 3542937 * 2 ^ 59
def prefixEnd_3542937 : Nat := 4983230072969 + 3 ^ 40 * 3542937 * 2
def baseEnd_3542937 : Nat := 1819229609598509976393835

theorem tailTrace_3542937 : CollatzResearch.WordTrace tailWord_3542937 prefixEnd_3542937 1819229609598509976393835 := by
  unfold tailWord_3542937
  simp only [CollatzResearch.WordTrace]
  refine ⟨129221528365551809311395065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86147685577034539540930043 129221528365551809311395065)
  ·
    refine ⟨96916146274163856983546299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129221528365551809311395065 96916146274163856983546299)
    ·
      refine ⟨145374219411245785475319449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96916146274163856983546299 145374219411245785475319449)
      ·
        refine ⟨109030664558434339106489587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145374219411245785475319449 109030664558434339106489587)
        ·
          refine ⟨163545996837651508659734381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109030664558434339106489587 163545996837651508659734381)
          ·
            refine ⟨61329748814119315747400393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163545996837651508659734381 61329748814119315747400393)
            ·
              refine ⟨45997311610589486810550295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61329748814119315747400393 45997311610589486810550295)
              ·
                refine ⟨68995967415884230215825443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45997311610589486810550295 68995967415884230215825443)
                ·
                  refine ⟨103493951123826345323738165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68995967415884230215825443 103493951123826345323738165)
                  ·
                    refine ⟨9702557917858719874100453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 103493951123826345323738165 9702557917858719874100453)
                    ·
                      refine ⟨1819229609598509976393835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9702557917858719874100453 1819229609598509976393835)
                      ·
                        rfl

theorem cell23_3542937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 5, 4].length) (baseStart_3542937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3542937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3542937 prefixEnd_3542937 := by exact prefixLift 3542937
  have htrace : WordTrace (prefixWord ++ tailWord_3542937) baseStart_3542937 baseEnd_3542937 := by
    simpa [prefixWord, tailWord_3542937, baseEnd_3542937] using wordTrace_append hprefix tailTrace_3542937
  have hstable : (prefixWord ++ tailWord_3542937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542937).length < 2 ^ (prefixWord ++ tailWord_3542937).sum := by decide
  have hdescent : baseEnd_3542937 < baseStart_3542937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542942 : List Nat := [4, 3, 1, 3, 1, 1, 3, 1, 2, 4]
def baseStart_3542942 : Nat := 118140960795 + 3542942 * 2 ^ 59
def prefixEnd_3542942 : Nat := 4983230072969 + 3 ^ 40 * 3542942 * 2
def baseEnd_3542942 : Nat := 606410725667260818943771

theorem tailTrace_3542942 : CollatzResearch.WordTrace tailWord_3542942 prefixEnd_3542942 606410725667260818943771 := by
  unfold tailWord_3542942
  simp only [CollatzResearch.WordTrace]
  refine ⟨16152713841316711895665885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86147807153689130110218053 16152713841316711895665885)
  ·
    refine ⟨6057267690493766960874707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16152713841316711895665885 6057267690493766960874707)
    ·
      refine ⟨9085901535740650441312061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6057267690493766960874707 9085901535740650441312061)
      ·
        refine ⟨3407213075902743915492023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9085901535740650441312061 3407213075902743915492023)
        ·
          refine ⟨5110819613854115873238035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3407213075902743915492023 5110819613854115873238035)
          ·
            refine ⟨7666229420781173809857053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5110819613854115873238035 7666229420781173809857053)
            ·
              refine ⟨2874836032792940178696395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7666229420781173809857053 2874836032792940178696395)
              ·
                refine ⟨4312254049189410268044593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2874836032792940178696395 4312254049189410268044593)
                ·
                  refine ⟨3234190536892057701033445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4312254049189410268044593 3234190536892057701033445)
                  ·
                    refine ⟨606410725667260818943771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3234190536892057701033445 606410725667260818943771)
                    ·
                      rfl

theorem cell23_3542942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_3542942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3542942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3542942 prefixEnd_3542942 := by exact prefixLift 3542942
  have htrace : WordTrace (prefixWord ++ tailWord_3542942) baseStart_3542942 baseEnd_3542942 := by
    simpa [prefixWord, tailWord_3542942, baseEnd_3542942] using wordTrace_append hprefix tailTrace_3542942
  have hstable : (prefixWord ++ tailWord_3542942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542942).length < 2 ^ (prefixWord ++ tailWord_3542942).sum := by decide
  have hdescent : baseEnd_3542942 < baseStart_3542942 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542971 : List Nat := [1, 1, 1, 1, 1, 2, 2, 6, 4, 2, 2]
def baseStart_3542971 : Nat := 118140960795 + 3542971 * 2 ^ 59
def prefixEnd_3542971 : Nat := 4983230072969 + 3 ^ 40 * 3542971 * 2
def baseEnd_3542971 : Nat := 1819247067940762843368679

theorem tailTrace_3542971 : CollatzResearch.WordTrace tailWord_3542971 prefixEnd_3542971 1819247067940762843368679 := by
  unfold tailWord_3542971
  simp only [CollatzResearch.WordTrace]
  refine ⟨129222768447428633118132767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86148512298285755412088511 129222768447428633118132767)
  ·
    refine ⟨193834152671142949677199151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129222768447428633118132767 193834152671142949677199151)
    ·
      refine ⟨290751229006714424515798727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193834152671142949677199151 290751229006714424515798727)
      ·
        refine ⟨436126843510071636773698091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290751229006714424515798727 436126843510071636773698091)
        ·
          refine ⟨654190265265107455160547137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 436126843510071636773698091 654190265265107455160547137)
          ·
            refine ⟨490642698948830591370410353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 654190265265107455160547137 490642698948830591370410353)
            ·
              refine ⟨367982024211622943527807765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 490642698948830591370410353 367982024211622943527807765)
              ·
                refine ⟨17249157384919825477865989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 367982024211622943527807765 17249157384919825477865989)
                ·
                  refine ⟨3234217009672467277099873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17249157384919825477865989 3234217009672467277099873)
                  ·
                    refine ⟨2425662757254350457824905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3234217009672467277099873 2425662757254350457824905)
                    ·
                      refine ⟨1819247067940762843368679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2425662757254350457824905 1819247067940762843368679)
                      ·
                        rfl

theorem cell23_3542971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 4, 2, 2].length) (baseStart_3542971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3542971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3542971 prefixEnd_3542971 := by exact prefixLift 3542971
  have htrace : WordTrace (prefixWord ++ tailWord_3542971) baseStart_3542971 baseEnd_3542971 := by
    simpa [prefixWord, tailWord_3542971, baseEnd_3542971] using wordTrace_append hprefix tailTrace_3542971
  have hstable : (prefixWord ++ tailWord_3542971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542971).length < 2 ^ (prefixWord ++ tailWord_3542971).sum := by decide
  have hdescent : baseEnd_3542971 < baseStart_3542971 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542974 : List Nat := [4, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5]
def baseStart_3542974 : Nat := 118140960795 + 3542974 * 2 ^ 59
def prefixEnd_3542974 : Nat := 4983230072969 + 3 ^ 40 * 3542974 * 2
def baseEnd_3542974 : Nat := 1819248608382726331631165

theorem tailTrace_3542974 : CollatzResearch.WordTrace tailWord_3542974 prefixEnd_3542974 1819248608382726331631165 := by
  unfold tailWord_3542974
  simp only [CollatzResearch.WordTrace]
  refine ⟨16152859733302220578811497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86148585244278509753661317 16152859733302220578811497)
  ·
    refine ⟨12114644799976665434108623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16152859733302220578811497 12114644799976665434108623)
    ·
      refine ⟨18171967199964998151162935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12114644799976665434108623 18171967199964998151162935)
      ·
        refine ⟨27257950799947497226744403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18171967199964998151162935 27257950799947497226744403)
        ·
          refine ⟨40886926199921245840116605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27257950799947497226744403 40886926199921245840116605)
          ·
            refine ⟨15332597324970467190043727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40886926199921245840116605 15332597324970467190043727)
            ·
              refine ⟨22998895987455700785065591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15332597324970467190043727 22998895987455700785065591)
              ·
                refine ⟨34498343981183551177598387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22998895987455700785065591 34498343981183551177598387)
                ·
                  refine ⟨51747515971775326766397581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34498343981183551177598387 51747515971775326766397581)
                  ·
                    refine ⟨19405318489415747537399093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51747515971775326766397581 19405318489415747537399093)
                    ·
                      refine ⟨1819248608382726331631165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19405318489415747537399093 1819248608382726331631165)
                      ·
                        rfl

theorem cell23_3542974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_3542974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3542974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3542974 prefixEnd_3542974 := by exact prefixLift 3542974
  have htrace : WordTrace (prefixWord ++ tailWord_3542974) baseStart_3542974 baseEnd_3542974 := by
    simpa [prefixWord, tailWord_3542974, baseEnd_3542974] using wordTrace_append hprefix tailTrace_3542974
  have hstable : (prefixWord ++ tailWord_3542974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542974).length < 2 ^ (prefixWord ++ tailWord_3542974).sum := by decide
  have hdescent : baseEnd_3542974 < baseStart_3542974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542987 : List Nat := [1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 7]
def baseStart_3542987 : Nat := 118140960795 + 3542987 * 2 ^ 59
def prefixEnd_3542987 : Nat := 4983230072969 + 3 ^ 40 * 3542987 * 2
def baseEnd_3542987 : Nat := 1819255283631234780768605

theorem tailTrace_3542987 : CollatzResearch.WordTrace tailWord_3542987 prefixEnd_3542987 1819255283631234780768605 := by
  unfold tailWord_3542987
  simp only [CollatzResearch.WordTrace]
  refine ⟨129223352015370667850715215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86148901343580445233810143 129223352015370667850715215)
  ·
    refine ⟨193835028023056001776072823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129223352015370667850715215 193835028023056001776072823)
    ·
      refine ⟨290752542034584002664109235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193835028023056001776072823 290752542034584002664109235)
      ·
        refine ⟨436128813051876003996163853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290752542034584002664109235 436128813051876003996163853)
        ·
          refine ⟨163548304894453501498561445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 436128813051876003996163853 163548304894453501498561445)
          ·
            refine ⟨30665307167710031530980271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 163548304894453501498561445 30665307167710031530980271)
            ·
              refine ⟨45997960751565047296470407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30665307167710031530980271 45997960751565047296470407)
              ·
                refine ⟨68996941127347570944705611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45997960751565047296470407 68996941127347570944705611)
                ·
                  refine ⟨103495411691021356417058417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68996941127347570944705611 103495411691021356417058417)
                  ·
                    refine ⟨77621558768266017312793813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 103495411691021356417058417 77621558768266017312793813)
                    ·
                      refine ⟨1819255283631234780768605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 77621558768266017312793813 1819255283631234780768605)
                      ·
                        rfl

theorem cell23_3542987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 7].length) (baseStart_3542987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3542987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3542987 prefixEnd_3542987 := by exact prefixLift 3542987
  have htrace : WordTrace (prefixWord ++ tailWord_3542987) baseStart_3542987 baseEnd_3542987 := by
    simpa [prefixWord, tailWord_3542987, baseEnd_3542987] using wordTrace_append hprefix tailTrace_3542987
  have hstable : (prefixWord ++ tailWord_3542987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542987).length < 2 ^ (prefixWord ++ tailWord_3542987).sum := by decide
  have hdescent : baseEnd_3542987 < baseStart_3542987 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542988 : List Nat := [2, 2, 1, 4, 1, 2, 2, 1, 4, 2, 2]
def baseStart_3542988 : Nat := 118140960795 + 3542988 * 2 ^ 59
def prefixEnd_3542988 : Nat := 4983230072969 + 3 ^ 40 * 3542988 * 2
def baseEnd_3542988 : Nat := 1819255797111889276856101

theorem tailTrace_3542988 : CollatzResearch.WordTrace tailWord_3542988 prefixEnd_3542988 1819255797111889276856101 := by
  unfold tailWord_3542988
  simp only [CollatzResearch.WordTrace]
  refine ⟨64611694244183522510750809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86148925658911363347667745 64611694244183522510750809)
  ·
    refine ⟨48458770683137641883063107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64611694244183522510750809 48458770683137641883063107)
    ·
      refine ⟨72688156024706462824594661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48458770683137641883063107 72688156024706462824594661)
      ·
        refine ⟨13629029254632461779611499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72688156024706462824594661 13629029254632461779611499)
        ·
          refine ⟨20443543881948692669417249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13629029254632461779611499 20443543881948692669417249)
          ·
            refine ⟨15332657911461519502062937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20443543881948692669417249 15332657911461519502062937)
            ·
              refine ⟨11499493433596139626547203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15332657911461519502062937 11499493433596139626547203)
              ·
                refine ⟨17249240150394209439820805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11499493433596139626547203 17249240150394209439820805)
                ·
                  refine ⟨3234232528198914269966401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17249240150394209439820805 3234232528198914269966401)
                  ·
                    refine ⟨2425674396149185702474801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3234232528198914269966401 2425674396149185702474801)
                    ·
                      refine ⟨1819255797111889276856101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2425674396149185702474801 1819255797111889276856101)
                      ·
                        rfl

theorem cell23_3542988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 4, 2, 2].length) (baseStart_3542988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3542988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3542988 prefixEnd_3542988 := by exact prefixLift 3542988
  have htrace : WordTrace (prefixWord ++ tailWord_3542988) baseStart_3542988 baseEnd_3542988 := by
    simpa [prefixWord, tailWord_3542988, baseEnd_3542988] using wordTrace_append hprefix tailTrace_3542988
  have hstable : (prefixWord ++ tailWord_3542988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542988).length < 2 ^ (prefixWord ++ tailWord_3542988).sum := by decide
  have hdescent : baseEnd_3542988 < baseStart_3542988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543024 : List Nat := [2, 1, 1, 1, 3, 2, 3, 3, 2, 5]
def baseStart_3543024 : Nat := 118140960795 + 3543024 * 2 ^ 59
def prefixEnd_3543024 : Nat := 4983230072969 + 3 ^ 40 * 3543024 * 2
def baseEnd_3543024 : Nat := 606424760805150378668645

theorem tailTrace_3543024 : CollatzResearch.WordTrace tailWord_3543024 prefixEnd_3543024 606424760805150378668645 := by
  unfold tailWord_3543024
  simp only [CollatzResearch.WordTrace]
  refine ⟨64612350758118311584906063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86149801010824415446541417 64612350758118311584906063)
  ·
    refine ⟨96918526137177467377359095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64612350758118311584906063 96918526137177467377359095)
    ·
      refine ⟨145377789205766201066038643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96918526137177467377359095 145377789205766201066038643)
      ·
        refine ⟨218066683808649301599057965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145377789205766201066038643 218066683808649301599057965)
        ·
          refine ⟨81775006428243488099646737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218066683808649301599057965 81775006428243488099646737)
          ·
            refine ⟨61331254821182616074735053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81775006428243488099646737 61331254821182616074735053)
            ·
              refine ⟨22999220557943481028025645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61331254821182616074735053 22999220557943481028025645)
              ·
                refine ⟨8624707709228805385509617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22999220557943481028025645 8624707709228805385509617)
                ·
                  refine ⟨6468530781921604039132213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8624707709228805385509617 6468530781921604039132213)
                  ·
                    refine ⟨606424760805150378668645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6468530781921604039132213 606424760805150378668645)
                    ·
                      rfl

theorem cell23_3543024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 3, 2, 5].length) (baseStart_3543024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3543024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3543024 prefixEnd_3543024 := by exact prefixLift 3543024
  have htrace : WordTrace (prefixWord ++ tailWord_3543024) baseStart_3543024 baseEnd_3543024 := by
    simpa [prefixWord, tailWord_3543024, baseEnd_3543024] using wordTrace_append hprefix tailTrace_3543024
  have hstable : (prefixWord ++ tailWord_3543024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543024).length < 2 ^ (prefixWord ++ tailWord_3543024).sum := by decide
  have hdescent : baseEnd_3543024 < baseStart_3543024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543071 : List Nat := [1, 1, 2, 4, 1, 2, 3, 2, 3, 4]
def baseStart_3543071 : Nat := 118140960795 + 3543071 * 2 ^ 59
def prefixEnd_3543071 : Nat := 4983230072969 + 3 ^ 40 * 3543071 * 2
def baseEnd_3543071 : Nat := 606432805335404150706073

theorem tailTrace_3543071 : CollatzResearch.WordTrace tailWord_3543071 prefixEnd_3543071 606432805335404150706073 := by
  unfold tailWord_3543071
  simp only [CollatzResearch.WordTrace]
  refine ⟨129226415747066350196773067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86150943831377566797848711 129226415747066350196773067)
  ·
    refine ⟨193839623620599525295159601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129226415747066350196773067 193839623620599525295159601)
    ·
      refine ⟨145379717715449643971369701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193839623620599525295159601 145379717715449643971369701)
      ·
        refine ⟨27258697071646808244631819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145379717715449643971369701 27258697071646808244631819)
        ·
          refine ⟨40888045607470212366947729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27258697071646808244631819 40888045607470212366947729)
          ·
            refine ⟨30666034205602659275210797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40888045607470212366947729 30666034205602659275210797)
            ·
              refine ⟨11499762827100997228204049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30666034205602659275210797 11499762827100997228204049)
              ·
                refine ⟨8624822120325747921153037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11499762827100997228204049 8624822120325747921153037)
                ·
                  refine ⟨3234308295122155470432389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8624822120325747921153037 3234308295122155470432389)
                  ·
                    refine ⟨606432805335404150706073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3234308295122155470432389 606432805335404150706073)
                    ·
                      rfl

theorem cell23_3543071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 2, 3, 4].length) (baseStart_3543071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3543071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3543071 prefixEnd_3543071 := by exact prefixLift 3543071
  have htrace : WordTrace (prefixWord ++ tailWord_3543071) baseStart_3543071 baseEnd_3543071 := by
    simpa [prefixWord, tailWord_3543071, baseEnd_3543071] using wordTrace_append hprefix tailTrace_3543071
  have hstable : (prefixWord ++ tailWord_3543071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543071).length < 2 ^ (prefixWord ++ tailWord_3543071).sum := by decide
  have hdescent : baseEnd_3543071 < baseStart_3543071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543088 : List Nat := [2, 1, 1, 1, 2, 5, 1, 5, 1, 4]
def baseStart_3543088 : Nat := 118140960795 + 3543088 * 2 ^ 59
def prefixEnd_3543088 : Nat := 4983230072969 + 3 ^ 40 * 3543088 * 2
def baseEnd_3543088 : Nat := 606435715059112961868547

theorem tailTrace_3543088 : CollatzResearch.WordTrace tailWord_3543088 prefixEnd_3543088 606435715059112961868547 := by
  unfold tailWord_3543088
  simp only [CollatzResearch.WordTrace]
  refine ⟨64613517894002381050070959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86151357192003174733427945 64613517894002381050070959)
  ·
    refine ⟨96920276841003571575106439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64613517894002381050070959 96920276841003571575106439)
    ·
      refine ⟨145380415261505357362659659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96920276841003571575106439 145380415261505357362659659)
      ·
        refine ⟨218070622892258036043989489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145380415261505357362659659 218070622892258036043989489)
        ·
          refine ⟨163552967169193527032992117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218070622892258036043989489 163552967169193527032992117)
          ·
            refine ⟨15333090672111893159343011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 163552967169193527032992117 15333090672111893159343011)
            ·
              refine ⟨22999636008167839739014517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15333090672111893159343011 22999636008167839739014517)
              ·
                refine ⟨2156215875765734975532611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22999636008167839739014517 2156215875765734975532611)
                ·
                  refine ⟨3234323813648602463298917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2156215875765734975532611 3234323813648602463298917)
                  ·
                    refine ⟨606435715059112961868547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3234323813648602463298917 606435715059112961868547)
                    ·
                      rfl

theorem cell23_3543088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 5, 1, 4].length) (baseStart_3543088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3543088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3543088 prefixEnd_3543088 := by exact prefixLift 3543088
  have htrace : WordTrace (prefixWord ++ tailWord_3543088) baseStart_3543088 baseEnd_3543088 := by
    simpa [prefixWord, tailWord_3543088, baseEnd_3543088] using wordTrace_append hprefix tailTrace_3543088
  have hstable : (prefixWord ++ tailWord_3543088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543088).length < 2 ^ (prefixWord ++ tailWord_3543088).sum := by decide
  have hdescent : baseEnd_3543088 < baseStart_3543088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543104 : List Nat := [2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 6]
def baseStart_3543104 : Nat := 118140960795 + 3543104 * 2 ^ 59
def prefixEnd_3543104 : Nat := 4983230072969 + 3 ^ 40 * 3543104 * 2
def baseEnd_3543104 : Nat := 1819315360867810823005567

theorem tailTrace_3543104 : CollatzResearch.WordTrace tailWord_3543104 prefixEnd_3543104 1819315360867810823005567 := by
  unfold tailWord_3543104
  simp only [CollatzResearch.WordTrace]
  refine ⟨64613809677973398416362183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86151746237297864555149577 64613809677973398416362183)
  ·
    refine ⟨96920714516960097624543275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64613809677973398416362183 96920714516960097624543275)
    ·
      refine ⟨145381071775440146436814913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96920714516960097624543275 145381071775440146436814913)
      ·
        refine ⟨109035803831580109827611185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145381071775440146436814913 109035803831580109827611185)
        ·
          refine ⟨81776852873685082370708389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109035803831580109827611185 81776852873685082370708389)
          ·
            refine ⟨15333159913815952944507823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81776852873685082370708389 15333159913815952944507823)
            ·
              refine ⟨22999739870723929416761735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15333159913815952944507823 22999739870723929416761735)
              ·
                refine ⟨34499609806085894125142603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22999739870723929416761735 34499609806085894125142603)
                ·
                  refine ⟨51749414709128841187713905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34499609806085894125142603 51749414709128841187713905)
                  ·
                    refine ⟨38812061031846630890785429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51749414709128841187713905 38812061031846630890785429)
                    ·
                      refine ⟨1819315360867810823005567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38812061031846630890785429 1819315360867810823005567)
                      ·
                        rfl

theorem cell23_3543104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 6].length) (baseStart_3543104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3543104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3543104 prefixEnd_3543104 := by exact prefixLift 3543104
  have htrace : WordTrace (prefixWord ++ tailWord_3543104) baseStart_3543104 baseEnd_3543104 := by
    simpa [prefixWord, tailWord_3543104, baseEnd_3543104] using wordTrace_append hprefix tailTrace_3543104
  have hstable : (prefixWord ++ tailWord_3543104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543104).length < 2 ^ (prefixWord ++ tailWord_3543104).sum := by decide
  have hdescent : baseEnd_3543104 < baseStart_3543104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543105 : List Nat := [1, 2, 5, 1, 2, 1, 2, 4, 1, 4]
def baseStart_3543105 : Nat := 118140960795 + 3543105 * 2 ^ 59
def prefixEnd_3543105 : Nat := 4983230072969 + 3 ^ 40 * 3543105 * 2
def baseEnd_3543105 : Nat := 606438624782821773031021

theorem tailTrace_3543105 : CollatzResearch.WordTrace tailWord_3543105 prefixEnd_3543105 606438624782821773031021 := by
  unfold tailWord_3543105
  simp only [CollatzResearch.WordTrace]
  refine ⟨129227655828943174003510769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86151770552628782669007179 129227655828943174003510769)
  ·
    refine ⟨96920741871707380502633077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129227655828943174003510769 96920741871707380502633077)
    ·
      refine ⟨9086319550472566922121851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 96920741871707380502633077 9086319550472566922121851)
      ·
        refine ⟨13629479325708850383182777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9086319550472566922121851 13629479325708850383182777)
        ·
          refine ⟨10222109494281637787387083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13629479325708850383182777 10222109494281637787387083)
          ·
            refine ⟨15333164241422456681080625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10222109494281637787387083 15333164241422456681080625)
            ·
              refine ⟨11499873181066842510810469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15333164241422456681080625 11499873181066842510810469)
              ·
                refine ⟨2156226221450032970776963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11499873181066842510810469 2156226221450032970776963)
                ·
                  refine ⟨3234339332175049456165445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2156226221450032970776963 3234339332175049456165445)
                  ·
                    refine ⟨606438624782821773031021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3234339332175049456165445 606438624782821773031021)
                    ·
                      rfl

theorem cell23_3543105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_3543105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3543105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3543105 prefixEnd_3543105 := by exact prefixLift 3543105
  have htrace : WordTrace (prefixWord ++ tailWord_3543105) baseStart_3543105 baseEnd_3543105 := by
    simpa [prefixWord, tailWord_3543105, baseEnd_3543105] using wordTrace_append hprefix tailTrace_3543105
  have hstable : (prefixWord ++ tailWord_3543105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543105).length < 2 ^ (prefixWord ++ tailWord_3543105).sum := by decide
  have hdescent : baseEnd_3543105 < baseStart_3543105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543118 : List Nat := [4, 1, 1, 1, 1, 5, 3, 1, 6]
def baseStart_3543118 : Nat := 118140960795 + 3543118 * 2 ^ 59
def prefixEnd_3543118 : Nat := 4983230072969 + 3 ^ 40 * 3543118 * 2
def baseEnd_3543118 : Nat := 202146949955219307581167

theorem tailTrace_3543118 : CollatzResearch.WordTrace tailWord_3543118 prefixEnd_3543118 202146949955219307581167 := by
  unfold tailWord_3543118
  simp only [CollatzResearch.WordTrace]
  refine ⟨16153516247237009652966751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86152086651930718149156005 16153516247237009652966751)
  ·
    refine ⟨24230274370855514479450127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16153516247237009652966751 24230274370855514479450127)
    ·
      refine ⟨36345411556283271719175191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24230274370855514479450127 36345411556283271719175191)
      ·
        refine ⟨54518117334424907578762787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36345411556283271719175191 54518117334424907578762787)
        ·
          refine ⟨81777176001637361368144181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54518117334424907578762787 81777176001637361368144181)
          ·
            refine ⟨7666610250153502628263517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81777176001637361368144181 7666610250153502628263517)
            ·
              refine ⟨2874978843807563485598819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7666610250153502628263517 2874978843807563485598819)
              ·
                refine ⟨4312468265711345228398229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2874978843807563485598819 4312468265711345228398229)
                ·
                  refine ⟨202146949955219307581167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4312468265711345228398229 202146949955219307581167)
                  ·
                    rfl

theorem cell23_3543118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 3, 1, 6].length) (baseStart_3543118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3543118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3543118 prefixEnd_3543118 := by exact prefixLift 3543118
  have htrace : WordTrace (prefixWord ++ tailWord_3543118) baseStart_3543118 baseEnd_3543118 := by
    simpa [prefixWord, tailWord_3543118, baseEnd_3543118] using wordTrace_append hprefix tailTrace_3543118
  have hstable : (prefixWord ++ tailWord_3543118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543118).length < 2 ^ (prefixWord ++ tailWord_3543118).sum := by decide
  have hdescent : baseEnd_3543118 < baseStart_3543118 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543128 : List Nat := [2, 1, 2, 2, 1, 4, 2, 2, 3, 1, 3]
def baseStart_3543128 : Nat := 118140960795 + 3543128 * 2 ^ 59
def prefixEnd_3543128 : Nat := 4983230072969 + 3 ^ 40 * 3543128 * 2
def baseEnd_3543128 : Nat := 1819327684403518729105457

theorem tailTrace_3543128 : CollatzResearch.WordTrace tailWord_3543128 prefixEnd_3543128 1819327684403518729105457 := by
  unfold tailWord_3543128
  simp only [CollatzResearch.WordTrace]
  refine ⟨64614247353929924465799019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86152329805239899287732025 64614247353929924465799019)
  ·
    refine ⟨96921371030894886698698529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64614247353929924465799019 96921371030894886698698529)
    ·
      refine ⟨72691028273171165024023897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96921371030894886698698529 72691028273171165024023897)
      ·
        refine ⟨54518271204878373768017923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72691028273171165024023897 54518271204878373768017923)
        ·
          refine ⟨81777406807317560652026885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54518271204878373768017923 81777406807317560652026885)
          ·
            refine ⟨15333263776372042622255041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81777406807317560652026885 15333263776372042622255041)
            ·
              refine ⟨11499947832279031966691281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15333263776372042622255041 11499947832279031966691281)
              ·
                refine ⟨8624960874209273975018461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11499947832279031966691281 8624960874209273975018461)
                ·
                  refine ⟨3234360327828477740631923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8624960874209273975018461 3234360327828477740631923)
                  ·
                    refine ⟨4851540491742716610947885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3234360327828477740631923 4851540491742716610947885)
                    ·
                      refine ⟨1819327684403518729105457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4851540491742716610947885 1819327684403518729105457)
                      ·
                        rfl

theorem cell23_3543128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 2, 3, 1, 3].length) (baseStart_3543128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3543128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3543128 prefixEnd_3543128 := by exact prefixLift 3543128
  have htrace : WordTrace (prefixWord ++ tailWord_3543128) baseStart_3543128 baseEnd_3543128 := by
    simpa [prefixWord, tailWord_3543128, baseEnd_3543128] using wordTrace_append hprefix tailTrace_3543128
  have hstable : (prefixWord ++ tailWord_3543128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543128).length < 2 ^ (prefixWord ++ tailWord_3543128).sum := by decide
  have hdescent : baseEnd_3543128 < baseStart_3543128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543171 : List Nat := [1, 1, 1, 3, 3, 3, 2, 2, 1, 1, 5]
def baseStart_3543171 : Nat := 118140960795 + 3543171 * 2 ^ 59
def prefixEnd_3543171 : Nat := 4983230072969 + 3 ^ 40 * 3543171 * 2
def baseEnd_3543171 : Nat := 1819349764071662060867759

theorem tailTrace_3543171 : CollatzResearch.WordTrace tailWord_3543171 prefixEnd_3543171 1819349764071662060867759 := by
  unfold tailWord_3543171
  simp only [CollatzResearch.WordTrace]
  refine ⟨129230063046704067275413367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86153375364469378183608911 129230063046704067275413367)
  ·
    refine ⟨193845094570056100913120051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129230063046704067275413367 193845094570056100913120051)
    ·
      refine ⟨290767641855084151369680077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193845094570056100913120051 290767641855084151369680077)
      ·
        refine ⟨109037865695656556763630029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 290767641855084151369680077 109037865695656556763630029)
        ·
          refine ⟨40889199635871208786361261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109037865695656556763630029 40889199635871208786361261)
          ·
            refine ⟨15333449863451703294885473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40889199635871208786361261 15333449863451703294885473)
            ·
              refine ⟨11500087397588777471164105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15333449863451703294885473 11500087397588777471164105)
              ·
                refine ⟨8625065548191583103373079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11500087397588777471164105 8625065548191583103373079)
                ·
                  refine ⟨12937598322287374655059619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8625065548191583103373079 12937598322287374655059619)
                  ·
                    refine ⟨19406397483431061982589429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12937598322287374655059619 19406397483431061982589429)
                    ·
                      refine ⟨1819349764071662060867759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19406397483431061982589429 1819349764071662060867759)
                      ·
                        rfl

theorem cell23_3543171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 2, 1, 1, 5].length) (baseStart_3543171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3543171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3543171 prefixEnd_3543171 := by exact prefixLift 3543171
  have htrace : WordTrace (prefixWord ++ tailWord_3543171) baseStart_3543171 baseEnd_3543171 := by
    simpa [prefixWord, tailWord_3543171, baseEnd_3543171] using wordTrace_append hprefix tailTrace_3543171
  have hstable : (prefixWord ++ tailWord_3543171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543171).length < 2 ^ (prefixWord ++ tailWord_3543171).sum := by decide
  have hdescent : baseEnd_3543171 < baseStart_3543171 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543182 : List Nat := [4, 1, 1, 3, 4, 1, 1, 2, 1, 5]
def baseStart_3543182 : Nat := 118140960795 + 3543182 * 2 ^ 59
def prefixEnd_3543182 : Nat := 4983230072969 + 3 ^ 40 * 3543182 * 2
def baseEnd_3543182 : Nat := 606451804119620505943403

theorem tailTrace_3543182 : CollatzResearch.WordTrace tailWord_3543182 prefixEnd_3543182 606451804119620505943403 := by
  unfold tailWord_3543182
  simp only [CollatzResearch.WordTrace]
  refine ⟨16153808031208027019257975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86153642833109477436042533 16153808031208027019257975)
  ·
    refine ⟨24230712046812040528886963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16153808031208027019257975 24230712046812040528886963)
    ·
      refine ⟨36346068070218060793330445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24230712046812040528886963 36346068070218060793330445)
      ·
        refine ⟨13629775526331772797498917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36346068070218060793330445 13629775526331772797498917)
        ·
          refine ⟨2555582911187207399531047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13629775526331772797498917 2555582911187207399531047)
          ·
            refine ⟨3833374366780811099296571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2555582911187207399531047 3833374366780811099296571)
            ·
              refine ⟨5750061550171216648944857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3833374366780811099296571 5750061550171216648944857)
              ·
                refine ⟨4312546162628412486708643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5750061550171216648944857 4312546162628412486708643)
                ·
                  refine ⟨6468819243942618730062965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4312546162628412486708643 6468819243942618730062965)
                  ·
                    refine ⟨606451804119620505943403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6468819243942618730062965 606451804119620505943403)
                    ·
                      rfl

theorem cell23_3543182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 2, 1, 5].length) (baseStart_3543182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3543182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3543182 prefixEnd_3543182 := by exact prefixLift 3543182
  have htrace : WordTrace (prefixWord ++ tailWord_3543182) baseStart_3543182 baseEnd_3543182 := by
    simpa [prefixWord, tailWord_3543182, baseEnd_3543182] using wordTrace_append hprefix tailTrace_3543182
  have hstable : (prefixWord ++ tailWord_3543182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543182).length < 2 ^ (prefixWord ++ tailWord_3543182).sum := by decide
  have hdescent : baseEnd_3543182 < baseStart_3543182 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543202 : List Nat := [3, 3, 1, 3, 1, 2, 3, 1, 1, 1, 4]
def baseStart_3543202 : Nat := 118140960795 + 3543202 * 2 ^ 59
def prefixEnd_3543202 : Nat := 4983230072969 + 3 ^ 40 * 3543202 * 2
def baseEnd_3543202 : Nat := 1819365681971951439580117

theorem tailTrace_3543202 : CollatzResearch.WordTrace tailWord_3543202 prefixEnd_3543202 1819365681971951439580117 := by
  unfold tailWord_3543202
  simp only [CollatzResearch.WordTrace]
  refine ⟨32307798427397939892447965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86154129139727839713194573 32307798427397939892447965)
  ·
    refine ⟨12115424410274227459667987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32307798427397939892447965 12115424410274227459667987)
    ·
      refine ⟨18173136615411341189501981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12115424410274227459667987 18173136615411341189501981)
      ·
        refine ⟨6814926230779252946063243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18173136615411341189501981 6814926230779252946063243)
        ·
          refine ⟨10222389346168879419094865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6814926230779252946063243 10222389346168879419094865)
          ·
            refine ⟨7666792009626659564321149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10222389346168879419094865 7666792009626659564321149)
            ·
              refine ⟨2875047003609997336620431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7666792009626659564321149 2875047003609997336620431)
              ·
                refine ⟨4312570505414996004930647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2875047003609997336620431 4312570505414996004930647)
                ·
                  refine ⟨6468855758122494007395971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4312570505414996004930647 6468855758122494007395971)
                  ·
                    refine ⟨9703283637183741011093957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6468855758122494007395971 9703283637183741011093957)
                    ·
                      refine ⟨1819365681971951439580117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9703283637183741011093957 1819365681971951439580117)
                      ·
                        rfl

theorem cell23_3543202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_3543202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3543202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3543202 prefixEnd_3543202 := by exact prefixLift 3543202
  have htrace : WordTrace (prefixWord ++ tailWord_3543202) baseStart_3543202 baseEnd_3543202 := by
    simpa [prefixWord, tailWord_3543202, baseEnd_3543202] using wordTrace_append hprefix tailTrace_3543202
  have hstable : (prefixWord ++ tailWord_3543202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543202).length < 2 ^ (prefixWord ++ tailWord_3543202).sum := by decide
  have hdescent : baseEnd_3543202 < baseStart_3543202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543205 : List Nat := [1, 3, 1, 2, 1, 3, 5, 1, 1, 2, 3]
def baseStart_3543205 : Nat := 118140960795 + 3543205 * 2 ^ 59
def prefixEnd_3543205 : Nat := 4983230072969 + 3 ^ 40 * 3543205 * 2
def baseEnd_3543205 : Nat := 1819367222413914927842603

theorem tailTrace_3543205 : CollatzResearch.WordTrace tailWord_3543205 prefixEnd_3543205 1819367222413914927842603 := by
  unfold tailWord_3543205
  simp only [CollatzResearch.WordTrace]
  refine ⟨129231303128580891082151069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86154202085720594054767379 129231303128580891082151069)
  ·
    refine ⟨48461738673217834155806651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129231303128580891082151069 48461738673217834155806651)
    ·
      refine ⟨72692608009826751233709977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48461738673217834155806651 72692608009826751233709977)
      ·
        refine ⟨54519456007370063425282483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72692608009826751233709977 54519456007370063425282483)
        ·
          refine ⟨81779184011055095137923725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54519456007370063425282483 81779184011055095137923725)
          ·
            refine ⟨30667194004145660676721397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81779184011055095137923725 30667194004145660676721397)
            ·
              refine ⟨2875049437888655688442631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30667194004145660676721397 2875049437888655688442631)
              ·
                refine ⟨4312574156832983532663947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2875049437888655688442631 4312574156832983532663947)
                ·
                  refine ⟨6468861235249475298995921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4312574156832983532663947 6468861235249475298995921)
                  ·
                    refine ⟨4851645926437106474246941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6468861235249475298995921 4851645926437106474246941)
                    ·
                      refine ⟨1819367222413914927842603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4851645926437106474246941 1819367222413914927842603)
                      ·
                        rfl

theorem cell23_3543205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 5, 1, 1, 2, 3].length) (baseStart_3543205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3543205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3543205 prefixEnd_3543205 := by exact prefixLift 3543205
  have htrace : WordTrace (prefixWord ++ tailWord_3543205) baseStart_3543205 baseEnd_3543205 := by
    simpa [prefixWord, tailWord_3543205, baseEnd_3543205] using wordTrace_append hprefix tailTrace_3543205
  have hstable : (prefixWord ++ tailWord_3543205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543205).length < 2 ^ (prefixWord ++ tailWord_3543205).sum := by decide
  have hdescent : baseEnd_3543205 < baseStart_3543205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543275 : List Nat := [1, 1, 1, 1, 2, 5, 3, 1, 4, 2, 2]
def baseStart_3543275 : Nat := 118140960795 + 3543275 * 2 ^ 59
def prefixEnd_3543275 : Nat := 4983230072969 + 3 ^ 40 * 3543275 * 2
def baseEnd_3543275 : Nat := 1819403166059729653967281

theorem tailTrace_3543275 : CollatzResearch.WordTrace tailWord_3543275 prefixEnd_3543275 1819403166059729653967281 := by
  unfold tailWord_3543275
  simp only [CollatzResearch.WordTrace]
  refine ⟨129233856238327293037199279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86155904158884862024799519 129233856238327293037199279)
  ·
    refine ⟨193850784357490939555798919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129233856238327293037199279 193850784357490939555798919)
    ·
      refine ⟨290776176536236409333698379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193850784357490939555798919 290776176536236409333698379)
      ·
        refine ⟨436164264804354614000547569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290776176536236409333698379 436164264804354614000547569)
        ·
          refine ⟨327123198603265960500410677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 436164264804354614000547569 327123198603265960500410677)
          ·
            refine ⟨30667799869056183796913501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 327123198603265960500410677 30667799869056183796913501)
            ·
              refine ⟨11500424950896068923842563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30667799869056183796913501 11500424950896068923842563)
              ·
                refine ⟨17250637426344103385763845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11500424950896068923842563 17250637426344103385763845)
                ·
                  refine ⟨3234494517439519384830721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17250637426344103385763845 3234494517439519384830721)
                  ·
                    refine ⟨2425870888079639538623041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3234494517439519384830721 2425870888079639538623041)
                    ·
                      refine ⟨1819403166059729653967281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2425870888079639538623041 1819403166059729653967281)
                      ·
                        rfl

theorem cell23_3543275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 4, 2, 2].length) (baseStart_3543275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3543275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3543275 prefixEnd_3543275 := by exact prefixLift 3543275
  have htrace : WordTrace (prefixWord ++ tailWord_3543275) baseStart_3543275 baseEnd_3543275 := by
    simpa [prefixWord, tailWord_3543275, baseEnd_3543275] using wordTrace_append hprefix tailTrace_3543275
  have hstable : (prefixWord ++ tailWord_3543275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543275).length < 2 ^ (prefixWord ++ tailWord_3543275).sum := by decide
  have hdescent : baseEnd_3543275 < baseStart_3543275 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543281 : List Nat := [1, 2, 2, 2, 2, 1, 3, 3, 7]
def baseStart_3543281 : Nat := 118140960795 + 3543281 * 2 ^ 59
def prefixEnd_3543281 : Nat := 4983230072969 + 3 ^ 40 * 3543281 * 2
def baseEnd_3543281 : Nat := 202156249660406292276917

theorem tailTrace_3543281 : CollatzResearch.WordTrace tailWord_3543281 prefixEnd_3543281 202156249660406292276917 := by
  unfold tailWord_3543281
  simp only [CollatzResearch.WordTrace]
  refine ⟨129234075076305556061917697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86156050050870370707945131 129234075076305556061917697)
  ·
    refine ⟨96925556307229167046438273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129234075076305556061917697 96925556307229167046438273)
    ·
      refine ⟨72694167230421875284828705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96925556307229167046438273 72694167230421875284828705)
      ·
        refine ⟨54520625422816406463621529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72694167230421875284828705 54520625422816406463621529)
        ·
          refine ⟨40890469067112304847716147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54520625422816406463621529 40890469067112304847716147)
          ·
            refine ⟨61335703600668457271574221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40890469067112304847716147 61335703600668457271574221)
            ·
              refine ⟨23000888850250671476840333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61335703600668457271574221 23000888850250671476840333)
              ·
                refine ⟨8625333318844001803815125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23000888850250671476840333 8625333318844001803815125)
                ·
                  refine ⟨202156249660406292276917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8625333318844001803815125 202156249660406292276917)
                  ·
                    rfl

theorem cell23_3543281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 3, 7].length) (baseStart_3543281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3543281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3543281 prefixEnd_3543281 := by exact prefixLift 3543281
  have htrace : WordTrace (prefixWord ++ tailWord_3543281) baseStart_3543281 baseEnd_3543281 := by
    simpa [prefixWord, tailWord_3543281, baseEnd_3543281] using wordTrace_append hprefix tailTrace_3543281
  have hstable : (prefixWord ++ tailWord_3543281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543281).length < 2 ^ (prefixWord ++ tailWord_3543281).sum := by decide
  have hdescent : baseEnd_3543281 < baseStart_3543281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543292 : List Nat := [2, 2, 2, 1, 4, 3, 1, 1, 1, 4, 2]
def baseStart_3543292 : Nat := 118140960795 + 3543292 * 2 ^ 59
def prefixEnd_3543292 : Nat := 4983230072969 + 3 ^ 40 * 3543292 * 2
def baseEnd_3543292 : Nat := 1819411895230856087454703

theorem tailTrace_3543292 : CollatzResearch.WordTrace tailWord_3543292 prefixEnd_3543292 1819411895230856087454703 := by
  unfold tailWord_3543292
  simp only [CollatzResearch.WordTrace]
  refine ⟨64617238139632852470284065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86156317519510469960378753 64617238139632852470284065)
  ·
    refine ⟨48462928604724639352713049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64617238139632852470284065 48462928604724639352713049)
    ·
      refine ⟨36347196453543479514534787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48462928604724639352713049 36347196453543479514534787)
      ·
        refine ⟨54520794680315219271802181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36347196453543479514534787 54520794680315219271802181)
        ·
          refine ⟨10222649002559103613462909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54520794680315219271802181 10222649002559103613462909)
          ·
            refine ⟨3833493375959663855048591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10222649002559103613462909 3833493375959663855048591)
            ·
              refine ⟨5750240063939495782572887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3833493375959663855048591 5750240063939495782572887)
              ·
                refine ⟨8625360095909243673859331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5750240063939495782572887 8625360095909243673859331)
                ·
                  refine ⟨12938040143863865510788997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8625360095909243673859331 12938040143863865510788997)
                  ·
                    refine ⟨2425882526974474783272937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12938040143863865510788997 2425882526974474783272937)
                    ·
                      refine ⟨1819411895230856087454703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2425882526974474783272937 1819411895230856087454703)
                      ·
                        rfl

theorem cell23_3543292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 1, 1, 4, 2].length) (baseStart_3543292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3543292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3543292 prefixEnd_3543292 := by exact prefixLift 3543292
  have htrace : WordTrace (prefixWord ++ tailWord_3543292) baseStart_3543292 baseEnd_3543292 := by
    simpa [prefixWord, tailWord_3543292, baseEnd_3543292] using wordTrace_append hprefix tailTrace_3543292
  have hstable : (prefixWord ++ tailWord_3543292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543292).length < 2 ^ (prefixWord ++ tailWord_3543292).sum := by decide
  have hdescent : baseEnd_3543292 < baseStart_3543292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543311 : List Nat := [1, 1, 2, 1, 1, 1, 3, 2, 6, 5]
def baseStart_3543311 : Nat := 118140960795 + 3543311 * 2 ^ 59
def prefixEnd_3543311 : Nat := 4983230072969 + 3 ^ 40 * 3543311 * 2
def baseEnd_3543311 : Nat := 606473883787763837705705

theorem tailTrace_3543311 : CollatzResearch.WordTrace tailWord_3543311 prefixEnd_3543311 606473883787763837705705 := by
  unfold tailWord_3543311
  simp only [CollatzResearch.WordTrace]
  refine ⟨129235169266196871185509787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86156779510797914123673191 129235169266196871185509787)
  ·
    refine ⟨193852753899295306778264681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129235169266196871185509787 193852753899295306778264681)
    ·
      refine ⟨145389565424471480083698511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193852753899295306778264681 145389565424471480083698511)
      ·
        refine ⟨218084348136707220125547767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145389565424471480083698511 218084348136707220125547767)
        ·
          refine ⟨327126522205060830188321651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218084348136707220125547767 327126522205060830188321651)
          ·
            refine ⟨490689783307591245282482477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327126522205060830188321651 490689783307591245282482477)
            ·
              refine ⟨184008668740346716980930929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 490689783307591245282482477 184008668740346716980930929)
              ·
                refine ⟨138006501555260037735698197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184008668740346716980930929 138006501555260037735698197)
                ·
                  refine ⟨6469054760402814268860853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 138006501555260037735698197 6469054760402814268860853)
                  ·
                    refine ⟨606473883787763837705705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6469054760402814268860853 606473883787763837705705)
                    ·
                      rfl

theorem cell23_3543311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 6, 5].length) (baseStart_3543311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3543311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3543311 prefixEnd_3543311 := by exact prefixLift 3543311
  have htrace : WordTrace (prefixWord ++ tailWord_3543311) baseStart_3543311 baseEnd_3543311 := by
    simpa [prefixWord, tailWord_3543311, baseEnd_3543311] using wordTrace_append hprefix tailTrace_3543311
  have hstable : (prefixWord ++ tailWord_3543311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543311).length < 2 ^ (prefixWord ++ tailWord_3543311).sum := by decide
  have hdescent : baseEnd_3543311 < baseStart_3543311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543328 : List Nat := [2, 1, 1, 5, 2, 1, 1, 1, 4, 5]
def baseStart_3543328 : Nat := 118140960795 + 3543328 * 2 ^ 59
def prefixEnd_3543328 : Nat := 4983230072969 + 3 ^ 40 * 3543328 * 2
def baseEnd_3543328 : Nat := 606476793511472648868179

theorem tailTrace_3543328 : CollatzResearch.WordTrace tailWord_3543328 prefixEnd_3543328 606476793511472648868179 := by
  unfold tailWord_3543328
  simp only [CollatzResearch.WordTrace]
  refine ⟨64617894653567641544439319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86157192871423522059252425 64617894653567641544439319)
  ·
    refine ⟨96926841980351462316658979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64617894653567641544439319 96926841980351462316658979)
    ·
      refine ⟨145390262970527193474988469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96926841980351462316658979 145390262970527193474988469)
      ·
        refine ⟨13630337153486924388280169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 145390262970527193474988469 13630337153486924388280169)
        ·
          refine ⟨10222752865115193291210127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13630337153486924388280169 10222752865115193291210127)
          ·
            refine ⟨15334129297672789936815191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10222752865115193291210127 15334129297672789936815191)
            ·
              refine ⟨23001193946509184905222787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15334129297672789936815191 23001193946509184905222787)
              ·
                refine ⟨34501790919763777357834181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23001193946509184905222787 34501790919763777357834181)
                ·
                  refine ⟨6469085797455708254593909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34501790919763777357834181 6469085797455708254593909)
                  ·
                    refine ⟨606476793511472648868179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6469085797455708254593909 606476793511472648868179)
                    ·
                      rfl

theorem cell23_3543328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 4, 5].length) (baseStart_3543328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3543328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3543328 prefixEnd_3543328 := by exact prefixLift 3543328
  have htrace : WordTrace (prefixWord ++ tailWord_3543328) baseStart_3543328 baseEnd_3543328 := by
    simpa [prefixWord, tailWord_3543328, baseEnd_3543328] using wordTrace_append hprefix tailTrace_3543328
  have hstable : (prefixWord ++ tailWord_3543328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543328).length < 2 ^ (prefixWord ++ tailWord_3543328).sum := by decide
  have hdescent : baseEnd_3543328 < baseStart_3543328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543332 : List Nat := [2, 3, 1, 3, 1, 3, 3, 2, 5]
def baseStart_3543332 : Nat := 118140960795 + 3543332 * 2 ^ 59
def prefixEnd_3543332 : Nat := 4983230072969 + 3 ^ 40 * 3543332 * 2
def baseEnd_3543332 : Nat := 202159159384115103439391

theorem tailTrace_3543332 : CollatzResearch.WordTrace tailWord_3543332 prefixEnd_3543332 202159159384115103439391 := by
  unfold tailWord_3543332
  simp only [CollatzResearch.WordTrace]
  refine ⟨64617967599560395886012125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86157290132747194514682833 64617967599560395886012125)
  ·
    refine ⟨24231737849835148457254547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64617967599560395886012125 24231737849835148457254547)
    ·
      refine ⟨36347606774752722685881821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24231737849835148457254547 36347606774752722685881821)
      ·
        refine ⟨13630352540532271007205683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36347606774752722685881821 13630352540532271007205683)
        ·
          refine ⟨20445528810798406510808525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13630352540532271007205683 20445528810798406510808525)
          ·
            refine ⟨7667073304049402441553197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20445528810798406510808525 7667073304049402441553197)
            ·
              refine ⟨2875152489018525915582449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7667073304049402441553197 2875152489018525915582449)
              ·
                refine ⟨2156364366763894436686837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2875152489018525915582449 2156364366763894436686837)
                ·
                  refine ⟨202159159384115103439391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2156364366763894436686837 202159159384115103439391)
                  ·
                    rfl

theorem cell23_3543332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 3, 2, 5].length) (baseStart_3543332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3543332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3543332 prefixEnd_3543332 := by exact prefixLift 3543332
  have htrace : WordTrace (prefixWord ++ tailWord_3543332) baseStart_3543332 baseEnd_3543332 := by
    simpa [prefixWord, tailWord_3543332, baseEnd_3543332] using wordTrace_append hprefix tailTrace_3543332
  have hstable : (prefixWord ++ tailWord_3543332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543332).length < 2 ^ (prefixWord ++ tailWord_3543332).sum := by decide
  have hdescent : baseEnd_3543332 < baseStart_3543332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543351 : List Nat := [1, 1, 3, 1, 2, 1, 1, 2, 1, 5, 5]
def baseStart_3543351 : Nat := 118140960795 + 3543351 * 2 ^ 59
def prefixEnd_3543351 : Nat := 4983230072969 + 3 ^ 40 * 3543351 * 2
def baseEnd_3543351 : Nat := 1819442190589471356616931

theorem tailTrace_3543351 : CollatzResearch.WordTrace tailWord_3543351 prefixEnd_3543351 1819442190589471356616931 := by
  unfold tailWord_3543351
  simp only [CollatzResearch.WordTrace]
  refine ⟨129236628186051958016965907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86157752124034638677977271 129236628186051958016965907)
  ·
    refine ⟨193854942279077937025448861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129236628186051958016965907 193854942279077937025448861)
    ·
      refine ⟨72695603354654226384543323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193854942279077937025448861 72695603354654226384543323)
      ·
        refine ⟨109043405031981339576814985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72695603354654226384543323 109043405031981339576814985)
        ·
          refine ⟨81782553773986004682611239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109043405031981339576814985 81782553773986004682611239)
          ·
            refine ⟨122673830660979007023916859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81782553773986004682611239 122673830660979007023916859)
            ·
              refine ⟨184010745991468510535875289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122673830660979007023916859 184010745991468510535875289)
              ·
                refine ⟨138008059493601382901906467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184010745991468510535875289 138008059493601382901906467)
                ·
                  refine ⟨207012089240402074352859701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138008059493601382901906467 207012089240402074352859701)
                  ·
                    refine ⟨19407383366287694470580597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 207012089240402074352859701 19407383366287694470580597)
                    ·
                      refine ⟨1819442190589471356616931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19407383366287694470580597 1819442190589471356616931)
                      ·
                        rfl

theorem cell23_3543351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 5, 5].length) (baseStart_3543351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3543351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3543351 prefixEnd_3543351 := by exact prefixLift 3543351
  have htrace : WordTrace (prefixWord ++ tailWord_3543351) baseStart_3543351 baseEnd_3543351 := by
    simpa [prefixWord, tailWord_3543351, baseEnd_3543351] using wordTrace_append hprefix tailTrace_3543351
  have hstable : (prefixWord ++ tailWord_3543351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543351).length < 2 ^ (prefixWord ++ tailWord_3543351).sum := by decide
  have hdescent : baseEnd_3543351 < baseStart_3543351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543368 : List Nat := [2, 1, 3, 1, 1, 2, 2, 3, 1, 4, 3]
def baseStart_3543368 : Nat := 118140960795 + 3543368 * 2 ^ 59
def prefixEnd_3543368 : Nat := 4983230072969 + 3 ^ 40 * 3543368 * 2
def baseEnd_3543368 : Nat := 1819450919760597790104353

theorem tailTrace_3543368 : CollatzResearch.WordTrace tailWord_3543368 prefixEnd_3543368 1819450919760597790104353 := by
  unfold tailWord_3543368
  simp only [CollatzResearch.WordTrace]
  refine ⟨64618624113495184960167379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86158165484660246613556505 64618624113495184960167379)
  ·
    refine ⟨96927936170242777440251069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64618624113495184960167379 96927936170242777440251069)
    ·
      refine ⟨36347976063841041540094151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96927936170242777440251069 36347976063841041540094151)
      ·
        refine ⟨54521964095761562310141227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36347976063841041540094151 54521964095761562310141227)
        ·
          refine ⟨81782946143642343465211841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54521964095761562310141227 81782946143642343465211841)
          ·
            refine ⟨61337209607731757598908881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81782946143642343465211841 61337209607731757598908881)
            ·
              refine ⟨46002907205798818199181661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61337209607731757598908881 46002907205798818199181661)
              ·
                refine ⟨17251090202174556824693123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46002907205798818199181661 17251090202174556824693123)
                ·
                  refine ⟨25876635303261835237039685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17251090202174556824693123 25876635303261835237039685)
                  ·
                    refine ⟨4851869119361594106944941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25876635303261835237039685 4851869119361594106944941)
                    ·
                      refine ⟨1819450919760597790104353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4851869119361594106944941 1819450919760597790104353)
                      ·
                        rfl

theorem cell23_3543368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 1, 4, 3].length) (baseStart_3543368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3543368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3543368 prefixEnd_3543368 := by exact prefixLift 3543368
  have htrace : WordTrace (prefixWord ++ tailWord_3543368) baseStart_3543368 baseEnd_3543368 := by
    simpa [prefixWord, tailWord_3543368, baseEnd_3543368] using wordTrace_append hprefix tailTrace_3543368
  have hstable : (prefixWord ++ tailWord_3543368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543368).length < 2 ^ (prefixWord ++ tailWord_3543368).sum := by decide
  have hdescent : baseEnd_3543368 < baseStart_3543368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543371 : List Nat := [1, 1, 1, 1, 3, 1, 1, 6, 8]
def baseStart_3543371 : Nat := 118140960795 + 3543371 * 2 ^ 59
def prefixEnd_3543371 : Nat := 4983230072969 + 3 ^ 40 * 3543371 * 2
def baseEnd_3543371 : Nat := 202161384466951253151871

theorem tailTrace_3543371 : CollatzResearch.WordTrace tailWord_3543371 prefixEnd_3543371 202161384466951253151871 := by
  unfold tailWord_3543371
  simp only [CollatzResearch.WordTrace]
  refine ⟨129237357645979501432693967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86158238430653000955129311 129237357645979501432693967)
  ·
    refine ⟨193856036468969252149040951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129237357645979501432693967 193856036468969252149040951)
    ·
      refine ⟨290784054703453878223561427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193856036468969252149040951 290784054703453878223561427)
      ·
        refine ⟨436176082055180817335342141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290784054703453878223561427 436176082055180817335342141)
        ·
          refine ⟨163566030770692806500753303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 436176082055180817335342141 163566030770692806500753303)
          ·
            refine ⟨245349046156039209751129955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163566030770692806500753303 245349046156039209751129955)
            ·
              refine ⟨368023569234058814626694933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245349046156039209751129955 368023569234058814626694933)
              ·
                refine ⟨17251104807846506935626325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 368023569234058814626694933 17251104807846506935626325)
                ·
                  refine ⟨202161384466951253151871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17251104807846506935626325 202161384466951253151871)
                  ·
                    rfl

theorem cell23_3543371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 8].length) (baseStart_3543371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3543371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3543371 prefixEnd_3543371 := by exact prefixLift 3543371
  have htrace : WordTrace (prefixWord ++ tailWord_3543371) baseStart_3543371 baseEnd_3543371 := by
    simpa [prefixWord, tailWord_3543371, baseEnd_3543371] using wordTrace_append hprefix tailTrace_3543371
  have hstable : (prefixWord ++ tailWord_3543371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543371).length < 2 ^ (prefixWord ++ tailWord_3543371).sum := by decide
  have hdescent : baseEnd_3543371 < baseStart_3543371 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543435 : List Nat := [1, 1, 1, 1, 4, 5, 1, 3, 1, 5]
def baseStart_3543435 : Nat := 118140960795 + 3543435 * 2 ^ 59
def prefixEnd_3543435 : Nat := 4983230072969 + 3 ^ 40 * 3543435 * 2
def baseEnd_3543435 : Nat := 606495107654816342655515

theorem tailTrace_3543435 : CollatzResearch.WordTrace tailWord_3543435 prefixEnd_3543435 606495107654816342655515 := by
  unfold tailWord_3543435
  simp only [CollatzResearch.WordTrace]
  refine ⟨129239691917747640363023759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86159794611831760242015839 129239691917747640363023759)
  ·
    refine ⟨193859537876621460544535639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129239691917747640363023759 193859537876621460544535639)
    ·
      refine ⟨290789306814932190816803459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193859537876621460544535639 290789306814932190816803459)
      ·
        refine ⟨436183960222398286225205189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290789306814932190816803459 436183960222398286225205189)
        ·
          refine ⟨81784492541699678667225973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 436183960222398286225205189 81784492541699678667225973)
          ·
            refine ⟨7667296175784344875052435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81784492541699678667225973 7667296175784344875052435)
            ·
              refine ⟨11500944263676517312578653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7667296175784344875052435 11500944263676517312578653)
              ·
                refine ⟨4312854098878693992216995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11500944263676517312578653 4312854098878693992216995)
                ·
                  refine ⟨6469281148318040988325493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4312854098878693992216995 6469281148318040988325493)
                  ·
                    refine ⟨606495107654816342655515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6469281148318040988325493 606495107654816342655515)
                    ·
                      rfl

theorem cell23_3543435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 3, 1, 5].length) (baseStart_3543435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3543435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3543435 prefixEnd_3543435 := by exact prefixLift 3543435
  have htrace : WordTrace (prefixWord ++ tailWord_3543435) baseStart_3543435 baseEnd_3543435 := by
    simpa [prefixWord, tailWord_3543435, baseEnd_3543435] using wordTrace_append hprefix tailTrace_3543435
  have hstable : (prefixWord ++ tailWord_3543435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543435).length < 2 ^ (prefixWord ++ tailWord_3543435).sum := by decide
  have hdescent : baseEnd_3543435 < baseStart_3543435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543465 : List Nat := [1, 2, 1, 1, 1, 1, 3, 7, 2, 4]
def baseStart_3543465 : Nat := 118140960795 + 3543465 * 2 ^ 59
def prefixEnd_3543465 : Nat := 4983230072969 + 3 ^ 40 * 3543465 * 2
def baseEnd_3543465 : Nat := 606500242461361303530469

theorem tailTrace_3543465 : CollatzResearch.WordTrace tailWord_3543465 prefixEnd_3543465 606500242461361303530469 := by
  unfold tailWord_3543465
  simp only [CollatzResearch.WordTrace]
  refine ⟨129240786107638955486615849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86160524071759303657743899 129240786107638955486615849)
  ·
    refine ⟨96930589580729216614961887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129240786107638955486615849 96930589580729216614961887)
    ·
      refine ⟨145395884371093824922442831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96930589580729216614961887 145395884371093824922442831)
      ·
        refine ⟨218093826556640737383664247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145395884371093824922442831 218093826556640737383664247)
        ·
          refine ⟨327140739834961106075496371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218093826556640737383664247 327140739834961106075496371)
          ·
            refine ⟨490711109752441659113244557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327140739834961106075496371 490711109752441659113244557)
            ·
              refine ⟨184016666157165622167466709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 490711109752441659113244557 184016666157165622167466709)
              ·
                refine ⟨4312890613058569269550001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 184016666157165622167466709 4312890613058569269550001)
                ·
                  refine ⟨3234667959793926952162501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4312890613058569269550001 3234667959793926952162501)
                  ·
                    refine ⟨606500242461361303530469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3234667959793926952162501 606500242461361303530469)
                    ·
                      rfl

theorem cell23_3543465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 7, 2, 4].length) (baseStart_3543465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3543465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3543465 prefixEnd_3543465 := by exact prefixLift 3543465
  have htrace : WordTrace (prefixWord ++ tailWord_3543465) baseStart_3543465 baseEnd_3543465 := by
    simpa [prefixWord, tailWord_3543465, baseEnd_3543465] using wordTrace_append hprefix tailTrace_3543465
  have hstable : (prefixWord ++ tailWord_3543465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543465).length < 2 ^ (prefixWord ++ tailWord_3543465).sum := by decide
  have hdescent : baseEnd_3543465 < baseStart_3543465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543469 : List Nat := [1, 5, 2, 2, 2, 1, 2, 2, 1, 5]
def baseStart_3543469 : Nat := 118140960795 + 3543469 * 2 ^ 59
def prefixEnd_3543469 : Nat := 4983230072969 + 3 ^ 40 * 3543469 * 2
def baseEnd_3543469 : Nat := 606500927102233964980463

theorem tailTrace_3543469 : CollatzResearch.WordTrace tailWord_3543469 prefixEnd_3543469 606500927102233964980463 := by
  unfold tailWord_3543469
  simp only [CollatzResearch.WordTrace]
  refine ⟨129240931999624464169761461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86160621333082976113174307 129240931999624464169761461)
  ·
    refine ⟨12116337374964793515915137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 129240931999624464169761461 12116337374964793515915137)
    ·
      refine ⟨9087253031223595136936353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12116337374964793515915137 9087253031223595136936353)
      ·
        refine ⟨6815439773417696352702265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9087253031223595136936353 6815439773417696352702265)
        ·
          refine ⟨5111579830063272264526699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6815439773417696352702265 5111579830063272264526699)
          ·
            refine ⟨7667369745094908396790049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5111579830063272264526699 7667369745094908396790049)
            ·
              refine ⟨5750527308821181297592537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7667369745094908396790049 5750527308821181297592537)
              ·
                refine ⟨4312895481615885973194403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5750527308821181297592537 4312895481615885973194403)
                ·
                  refine ⟨6469343222423828959791605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4312895481615885973194403 6469343222423828959791605)
                  ·
                    refine ⟨606500927102233964980463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6469343222423828959791605 606500927102233964980463)
                    ·
                      rfl

theorem cell23_3543469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_3543469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3543469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3543469 prefixEnd_3543469 := by exact prefixLift 3543469
  have htrace : WordTrace (prefixWord ++ tailWord_3543469) baseStart_3543469 baseEnd_3543469 := by
    simpa [prefixWord, tailWord_3543469, baseEnd_3543469] using wordTrace_append hprefix tailTrace_3543469
  have hstable : (prefixWord ++ tailWord_3543469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543469).length < 2 ^ (prefixWord ++ tailWord_3543469).sum := by decide
  have hdescent : baseEnd_3543469 < baseStart_3543469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543532 : List Nat := [2, 2, 1, 1, 2, 1, 5, 1, 3, 3, 2]
def baseStart_3543532 : Nat := 118140960795 + 3543532 * 2 ^ 59
def prefixEnd_3543532 : Nat := 4983230072969 + 3 ^ 40 * 3543532 * 2
def baseEnd_3543532 : Nat := 1819535130587935148453599

theorem tailTrace_3543532 : CollatzResearch.WordTrace tailWord_3543532 prefixEnd_3543532 1819535130587935148453599 := by
  unfold tailWord_3543532
  simp only [CollatzResearch.WordTrace]
  refine ⟨64621614899198112964652425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86162153198930817286203233 64621614899198112964652425)
  ·
    refine ⟨48466211174398584723489319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64621614899198112964652425 48466211174398584723489319)
    ·
      refine ⟨72699316761597877085233979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48466211174398584723489319 72699316761597877085233979)
      ·
        refine ⟨109048975142396815627850969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72699316761597877085233979 109048975142396815627850969)
        ·
          refine ⟨81786731356797611720888227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109048975142396815627850969 81786731356797611720888227)
          ·
            refine ⟨122680097035196417581332341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81786731356797611720888227 122680097035196417581332341)
            ·
              refine ⟨11501259097049664148249907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 122680097035196417581332341 11501259097049664148249907)
              ·
                refine ⟨17251888645574496222374861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11501259097049664148249907 17251888645574496222374861)
                ·
                  refine ⟨6469458242090436083390573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17251888645574496222374861 6469458242090436083390573)
                  ·
                    refine ⟨2426046840783913531271465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6469458242090436083390573 2426046840783913531271465)
                    ·
                      refine ⟨1819535130587935148453599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2426046840783913531271465 1819535130587935148453599)
                      ·
                        rfl

theorem cell23_3543532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 3, 2].length) (baseStart_3543532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3543532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3543532 prefixEnd_3543532 := by exact prefixLift 3543532
  have htrace : WordTrace (prefixWord ++ tailWord_3543532) baseStart_3543532 baseEnd_3543532 := by
    simpa [prefixWord, tailWord_3543532, baseEnd_3543532] using wordTrace_append hprefix tailTrace_3543532
  have hstable : (prefixWord ++ tailWord_3543532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543532).length < 2 ^ (prefixWord ++ tailWord_3543532).sum := by decide
  have hdescent : baseEnd_3543532 < baseStart_3543532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543556 : List Nat := [2, 3, 2, 3, 1, 2, 2, 2, 2, 1, 3]
def baseStart_3543556 : Nat := 118140960795 + 3543556 * 2 ^ 59
def prefixEnd_3543556 : Nat := 4983230072969 + 3 ^ 40 * 3543556 * 2
def baseEnd_3543556 : Nat := 1819547454123643054553489

theorem tailTrace_3543556 : CollatzResearch.WordTrace tailWord_3543556 prefixEnd_3543556 1819547454123643054553489 := by
  unfold tailWord_3543556
  simp only [CollatzResearch.WordTrace]
  refine ⟨64622052575154639014089261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86162736766872852018785681 64622052575154639014089261)
  ·
    refine ⟨24233269715682989630283473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64622052575154639014089261 24233269715682989630283473)
    ·
      refine ⟨18174952286762242222712605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24233269715682989630283473 18174952286762242222712605)
      ·
        refine ⟨6815607107535840833517227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18174952286762242222712605 6815607107535840833517227)
        ·
          refine ⟨10223410661303761250275841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6815607107535840833517227 10223410661303761250275841)
          ·
            refine ⟨7667557995977820937706881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10223410661303761250275841 7667557995977820937706881)
            ·
              refine ⟨5750668496983365703280161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7667557995977820937706881 5750668496983365703280161)
              ·
                refine ⟨4313001372737524277460121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5750668496983365703280161 4313001372737524277460121)
                ·
                  refine ⟨3234751029553143208095091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4313001372737524277460121 3234751029553143208095091)
                  ·
                    refine ⟨4852126544329714812142637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3234751029553143208095091 4852126544329714812142637)
                    ·
                      refine ⟨1819547454123643054553489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4852126544329714812142637 1819547454123643054553489)
                      ·
                        rfl

theorem cell23_3543556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_3543556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3543556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3543556 prefixEnd_3543556 := by exact prefixLift 3543556
  have htrace : WordTrace (prefixWord ++ tailWord_3543556) baseStart_3543556 baseEnd_3543556 := by
    simpa [prefixWord, tailWord_3543556, baseEnd_3543556] using wordTrace_append hprefix tailTrace_3543556
  have hstable : (prefixWord ++ tailWord_3543556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543556).length < 2 ^ (prefixWord ++ tailWord_3543556).sum := by decide
  have hdescent : baseEnd_3543556 < baseStart_3543556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543562 : List Nat := [3, 1, 2, 2, 2, 1, 1, 2, 3, 4, 2]
def baseStart_3543562 : Nat := 118140960795 + 3543562 * 2 ^ 59
def prefixEnd_3543562 : Nat := 4983230072969 + 3 ^ 40 * 3543562 * 2
def baseEnd_3543562 : Nat := 1819550535007570031078461

theorem tailTrace_3543562 : CollatzResearch.WordTrace tailWord_3543562 prefixEnd_3543562 1819550535007570031078461 := by
  unfold tailWord_3543562
  simp only [CollatzResearch.WordTrace]
  refine ⟨32311080997071885263224235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86162882658858360701931293 32311080997071885263224235)
  ·
    refine ⟨48466621495607827894836353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32311080997071885263224235 48466621495607827894836353)
    ·
      refine ⟨36349966121705870921127265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48466621495607827894836353 36349966121705870921127265)
      ·
        refine ⟨27262474591279403190845449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36349966121705870921127265 27262474591279403190845449)
        ·
          refine ⟨20446855943459552393134087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27262474591279403190845449 20446855943459552393134087)
          ·
            refine ⟨30670283915189328589701131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20446855943459552393134087 30670283915189328589701131)
            ·
              refine ⟨46005425872783992884551697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30670283915189328589701131 46005425872783992884551697)
              ·
                refine ⟨34504069404587994663413773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46005425872783992884551697 34504069404587994663413773)
                ·
                  refine ⟨12939026026720497998780165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34504069404587994663413773 12939026026720497998780165)
                  ·
                    refine ⟨2426067380010093374771281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12939026026720497998780165 2426067380010093374771281)
                    ·
                      refine ⟨1819550535007570031078461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2426067380010093374771281 1819550535007570031078461)
                      ·
                        rfl

theorem cell23_3543562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 3, 4, 2].length) (baseStart_3543562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3543562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3543562 prefixEnd_3543562 := by exact prefixLift 3543562
  have htrace : WordTrace (prefixWord ++ tailWord_3543562) baseStart_3543562 baseEnd_3543562 := by
    simpa [prefixWord, tailWord_3543562, baseEnd_3543562] using wordTrace_append hprefix tailTrace_3543562
  have hstable : (prefixWord ++ tailWord_3543562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543562).length < 2 ^ (prefixWord ++ tailWord_3543562).sum := by decide
  have hdescent : baseEnd_3543562 < baseStart_3543562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543572 : List Nat := [2, 4, 3, 1, 1, 1, 1, 1, 1, 8]
def baseStart_3543572 : Nat := 118140960795 + 3543572 * 2 ^ 59
def prefixEnd_3543572 : Nat := 4983230072969 + 3 ^ 40 * 3543572 * 2
def baseEnd_3543572 : Nat := 606518556604704997317805

theorem tailTrace_3543572 : CollatzResearch.WordTrace tailWord_3543572 prefixEnd_3543572 606518556604704997317805 := by
  unfold tailWord_3543572
  simp only [CollatzResearch.WordTrace]
  refine ⟨64622344359125656380380485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86163125812167541840507313 64622344359125656380380485)
  ·
    refine ⟨12116689567336060571321341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64622344359125656380380485 12116689567336060571321341)
    ·
      refine ⟨4543758587751022714245503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12116689567336060571321341 4543758587751022714245503)
      ·
        refine ⟨6815637881626534071368255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4543758587751022714245503 6815637881626534071368255)
        ·
          refine ⟨10223456822439801107052383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6815637881626534071368255 10223456822439801107052383)
          ·
            refine ⟨15335185233659701660578575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10223456822439801107052383 15335185233659701660578575)
            ·
              refine ⟨23002777850489552490867863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15335185233659701660578575 23002777850489552490867863)
              ·
                refine ⟨34504166775734328736301795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23002777850489552490867863 34504166775734328736301795)
                ·
                  refine ⟨51756250163601493104452693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34504166775734328736301795 51756250163601493104452693)
                  ·
                    refine ⟨606518556604704997317805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 51756250163601493104452693 606518556604704997317805)
                    ·
                      rfl

theorem cell23_3543572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_3543572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3543572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3543572 prefixEnd_3543572 := by exact prefixLift 3543572
  have htrace : WordTrace (prefixWord ++ tailWord_3543572) baseStart_3543572 baseEnd_3543572 := by
    simpa [prefixWord, tailWord_3543572, baseEnd_3543572] using wordTrace_append hprefix tailTrace_3543572
  have hstable : (prefixWord ++ tailWord_3543572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543572).length < 2 ^ (prefixWord ++ tailWord_3543572).sum := by decide
  have hdescent : baseEnd_3543572 < baseStart_3543572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543585 : List Nat := [1, 2, 3, 2, 2, 1, 3, 2, 7]
def baseStart_3543585 : Nat := 118140960795 + 3543585 * 2 ^ 59
def prefixEnd_3543585 : Nat := 4983230072969 + 3 ^ 40 * 3543585 * 2
def baseEnd_3543585 : Nat := 202173593895847049010095

theorem tailTrace_3543585 : CollatzResearch.WordTrace tailWord_3543585 prefixEnd_3543585 202173593895847049010095 := by
  unfold tailWord_3543585
  simp only [CollatzResearch.WordTrace]
  refine ⟨129245162867204215980984209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86163441911469477320656139 129245162867204215980984209)
  ·
    refine ⟨96933872150403161985738157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129245162867204215980984209 96933872150403161985738157)
    ·
      refine ⟨36350202056401185744651809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96933872150403161985738157 36350202056401185744651809)
      ·
        refine ⟨27262651542300889308488857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36350202056401185744651809 27262651542300889308488857)
        ·
          refine ⟨20446988656725666981366643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27262651542300889308488857 20446988656725666981366643)
          ·
            refine ⟨30670482985088500472049965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20446988656725666981366643 30670482985088500472049965)
            ·
              refine ⟨11501431119408187677018737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30670482985088500472049965 11501431119408187677018737)
              ·
                refine ⟨8626073339556140757764053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11501431119408187677018737 8626073339556140757764053)
                ·
                  refine ⟨202173593895847049010095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8626073339556140757764053 202173593895847049010095)
                  ·
                    rfl

theorem cell23_3543585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 2, 7].length) (baseStart_3543585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3543585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3543585 prefixEnd_3543585 := by exact prefixLift 3543585
  have htrace : WordTrace (prefixWord ++ tailWord_3543585) baseStart_3543585 baseEnd_3543585 := by
    simpa [prefixWord, tailWord_3543585, baseEnd_3543585] using wordTrace_append hprefix tailTrace_3543585
  have hstable : (prefixWord ++ tailWord_3543585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543585).length < 2 ^ (prefixWord ++ tailWord_3543585).sum := by decide
  have hdescent : baseEnd_3543585 < baseStart_3543585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543602 : List Nat := [3, 2, 1, 1, 2, 1, 3, 5, 5]
def baseStart_3543602 : Nat := 118140960795 + 3543602 * 2 ^ 59
def prefixEnd_3543602 : Nat := 4983230072969 + 3 ^ 40 * 3543602 * 2
def baseEnd_3543602 : Nat := 202174563803749986064253

theorem tailTrace_3543602 : CollatzResearch.WordTrace tailWord_3543602 prefixEnd_3543602 202174563803749986064253 := by
  unfold tailWord_3543602
  simp only [CollatzResearch.WordTrace]
  refine ⟨32311445727035656971088265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86163855272095085256235373 32311445727035656971088265)
  ·
    refine ⟨24233584295276742728316199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32311445727035656971088265 24233584295276742728316199)
    ·
      refine ⟨36350376442915114092474299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24233584295276742728316199 36350376442915114092474299)
      ·
        refine ⟨54525564664372671138711449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36350376442915114092474299 54525564664372671138711449)
        ·
          refine ⟨40894173498279503354033587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54525564664372671138711449 40894173498279503354033587)
          ·
            refine ⟨61341260247419255031050381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40894173498279503354033587 61341260247419255031050381)
            ·
              refine ⟨23002972592782220636643893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61341260247419255031050381 23002972592782220636643893)
              ·
                refine ⟨2156528680573333184685365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23002972592782220636643893 2156528680573333184685365)
                ·
                  refine ⟨202174563803749986064253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2156528680573333184685365 202174563803749986064253)
                  ·
                    rfl

theorem cell23_3543602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 5, 5].length) (baseStart_3543602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3543602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3543602 prefixEnd_3543602 := by exact prefixLift 3543602
  have htrace : WordTrace (prefixWord ++ tailWord_3543602) baseStart_3543602 baseEnd_3543602 := by
    simpa [prefixWord, tailWord_3543602, baseEnd_3543602] using wordTrace_append hprefix tailTrace_3543602
  have hstable : (prefixWord ++ tailWord_3543602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543602).length < 2 ^ (prefixWord ++ tailWord_3543602).sum := by decide
  have hdescent : baseEnd_3543602 < baseStart_3543602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543612 : List Nat := [2, 2, 2, 2, 3, 1, 1, 2, 2, 3, 3]
def baseStart_3543612 : Nat := 118140960795 + 3543612 * 2 ^ 59
def prefixEnd_3543612 : Nat := 4983230072969 + 3 ^ 40 * 3543612 * 2
def baseEnd_3543612 : Nat := 1819576209040294835453231

theorem tailTrace_3543612 : CollatzResearch.WordTrace tailWord_3543612 prefixEnd_3543612 1819576209040294835453231 := by
  unfold tailWord_3543612
  simp only [CollatzResearch.WordTrace]
  refine ⟨64623073819053199796108545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86164098425404266394811393 64623073819053199796108545)
  ·
    refine ⟨48467305364289899847081409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64623073819053199796108545 48467305364289899847081409)
    ·
      refine ⟨36350479023217424885311057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48467305364289899847081409 36350479023217424885311057)
      ·
        refine ⟨27262859267413068663983293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36350479023217424885311057 27262859267413068663983293)
        ·
          refine ⟨10223572225279900748993735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27262859267413068663983293 10223572225279900748993735)
          ·
            refine ⟨15335358337919851123490603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10223572225279900748993735 15335358337919851123490603)
            ·
              refine ⟨23003037506879776685235905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15335358337919851123490603 23003037506879776685235905)
              ·
                refine ⟨17252278130159832513926929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23003037506879776685235905 17252278130159832513926929)
                ·
                  refine ⟨12939208597619874385445197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17252278130159832513926929 12939208597619874385445197)
                  ·
                    refine ⟨4852203224107452894541949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12939208597619874385445197 4852203224107452894541949)
                    ·
                      refine ⟨1819576209040294835453231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4852203224107452894541949 1819576209040294835453231)
                      ·
                        rfl

theorem cell23_3543612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 2, 3, 3].length) (baseStart_3543612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3543612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3543612 prefixEnd_3543612 := by exact prefixLift 3543612
  have htrace : WordTrace (prefixWord ++ tailWord_3543612) baseStart_3543612 baseEnd_3543612 := by
    simpa [prefixWord, tailWord_3543612, baseEnd_3543612] using wordTrace_append hprefix tailTrace_3543612
  have hstable : (prefixWord ++ tailWord_3543612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543612).length < 2 ^ (prefixWord ++ tailWord_3543612).sum := by decide
  have hdescent : baseEnd_3543612 < baseStart_3543612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543613 : List Nat := [1, 4, 1, 3, 2, 3, 1, 2, 2, 2, 2]
def baseStart_3543613 : Nat := 118140960795 + 3543613 * 2 ^ 59
def prefixEnd_3543613 : Nat := 4983230072969 + 3 ^ 40 * 3543613 * 2
def baseEnd_3543613 : Nat := 1819576722520949331540727

theorem tailTrace_3543613 : CollatzResearch.WordTrace tailWord_3543613 prefixEnd_3543613 1819576722520949331540727 := by
  unfold tailWord_3543613
  simp only [CollatzResearch.WordTrace]
  refine ⟨129246184111102776763003493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86164122740735184508668995 129246184111102776763003493)
  ·
    refine ⟨24233659520831770643063155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129246184111102776763003493 24233659520831770643063155)
    ·
      refine ⟨36350489281247655964594733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24233659520831770643063155 36350489281247655964594733)
      ·
        refine ⟨13631433480467870986723025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36350489281247655964594733 13631433480467870986723025)
        ·
          refine ⟨10223575110350903240042269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13631433480467870986723025 10223575110350903240042269)
          ·
            refine ⟨3833840666381588715015851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10223575110350903240042269 3833840666381588715015851)
            ·
              refine ⟨5750760999572383072523777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3833840666381588715015851 5750760999572383072523777)
              ·
                refine ⟨4313070749679287304392833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5750760999572383072523777 4313070749679287304392833)
                ·
                  refine ⟨3234803062259465478294625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4313070749679287304392833 3234803062259465478294625)
                  ·
                    refine ⟨2426102296694599108720969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3234803062259465478294625 2426102296694599108720969)
                    ·
                      refine ⟨1819576722520949331540727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2426102296694599108720969 1819576722520949331540727)
                      ·
                        rfl

theorem cell23_3543613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 2, 2, 2, 2].length) (baseStart_3543613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3543613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3543613 prefixEnd_3543613 := by exact prefixLift 3543613
  have htrace : WordTrace (prefixWord ++ tailWord_3543613) baseStart_3543613 baseEnd_3543613 := by
    simpa [prefixWord, tailWord_3543613, baseEnd_3543613] using wordTrace_append hprefix tailTrace_3543613
  have hstable : (prefixWord ++ tailWord_3543613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543613).length < 2 ^ (prefixWord ++ tailWord_3543613).sum := by decide
  have hdescent : baseEnd_3543613 < baseStart_3543613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543615 : List Nat := [1, 1, 2, 2, 3, 2, 2, 1, 4, 5]
def baseStart_3543615 : Nat := 118140960795 + 3543615 * 2 ^ 59
def prefixEnd_3543615 : Nat := 4983230072969 + 3 ^ 40 * 3543615 * 2
def baseEnd_3543615 : Nat := 606525916494086107905239

theorem tailTrace_3543615 : CollatzResearch.WordTrace tailWord_3543615 prefixEnd_3543615 606525916494086107905239 := by
  unfold tailWord_3543615
  simp only [CollatzResearch.WordTrace]
  refine ⟨129246257057095531104576299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86164171371397020736384199 129246257057095531104576299)
  ·
    refine ⟨193869385585643296656864449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129246257057095531104576299 193869385585643296656864449)
    ·
      refine ⟨145402039189232472492648337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193869385585643296656864449 145402039189232472492648337)
      ·
        refine ⟨109051529391924354369486253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145402039189232472492648337 109051529391924354369486253)
        ·
          refine ⟨40894323521971632888557345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109051529391924354369486253 40894323521971632888557345)
          ·
            refine ⟨30670742641478724666418009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40894323521971632888557345 30670742641478724666418009)
            ·
              refine ⟨23003056981109043499813507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30670742641478724666418009 23003056981109043499813507)
              ·
                refine ⟨34504585471663565249720261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23003056981109043499813507 34504585471663565249720261)
                ·
                  refine ⟨6469609775936918484322549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34504585471663565249720261 6469609775936918484322549)
                  ·
                    refine ⟨606525916494086107905239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6469609775936918484322549 606525916494086107905239)
                    ·
                      rfl

theorem cell23_3543615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 4, 5].length) (baseStart_3543615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3543615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3543615 prefixEnd_3543615 := by exact prefixLift 3543615
  have htrace : WordTrace (prefixWord ++ tailWord_3543615) baseStart_3543615 baseEnd_3543615 := by
    simpa [prefixWord, tailWord_3543615, baseEnd_3543615] using wordTrace_append hprefix tailTrace_3543615
  have hstable : (prefixWord ++ tailWord_3543615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543615).length < 2 ^ (prefixWord ++ tailWord_3543615).sum := by decide
  have hdescent : baseEnd_3543615 < baseStart_3543615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543629 : List Nat := [1, 6, 1, 1, 2, 1, 2, 1, 2, 3, 3]
def baseStart_3543629 : Nat := 118140960795 + 3543629 * 2 ^ 59
def prefixEnd_3543629 : Nat := 4983230072969 + 3 ^ 40 * 3543629 * 2
def baseEnd_3543629 : Nat := 1819584938211421268940653

theorem tailTrace_3543629 : CollatzResearch.WordTrace tailWord_3543629 prefixEnd_3543629 1819584938211421268940653 := by
  unfold tailWord_3543629
  simp only [CollatzResearch.WordTrace]
  refine ⟨129246767679044811495585941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86164511786029874330390627 129246767679044811495585941)
  ·
    refine ⟨6058442234955225538855591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 129246767679044811495585941 6058442234955225538855591)
    ·
      refine ⟨9087663352432838308283387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6058442234955225538855591 9087663352432838308283387)
      ·
        refine ⟨13631495028649257462425081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9087663352432838308283387 13631495028649257462425081)
        ·
          refine ⟨10223621271486943096818811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13631495028649257462425081 10223621271486943096818811)
          ·
            refine ⟨15335431907230414645228217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10223621271486943096818811 15335431907230414645228217)
            ·
              refine ⟨11501573930422810983921163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15335431907230414645228217 11501573930422810983921163)
              ·
                refine ⟨17252360895634216475881745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11501573930422810983921163 17252360895634216475881745)
                ·
                  refine ⟨12939270671725662356911309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17252360895634216475881745 12939270671725662356911309)
                  ·
                    refine ⟨4852226501897123383841741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12939270671725662356911309 4852226501897123383841741)
                    ·
                      refine ⟨1819584938211421268940653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4852226501897123383841741 1819584938211421268940653)
                      ·
                        rfl

theorem cell23_3543629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_3543629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3543629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3543629 prefixEnd_3543629 := by exact prefixLift 3543629
  have htrace : WordTrace (prefixWord ++ tailWord_3543629) baseStart_3543629 baseEnd_3543629 := by
    simpa [prefixWord, tailWord_3543629, baseEnd_3543629] using wordTrace_append hprefix tailTrace_3543629
  have hstable : (prefixWord ++ tailWord_3543629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543629).length < 2 ^ (prefixWord ++ tailWord_3543629).sum := by decide
  have hdescent : baseEnd_3543629 < baseStart_3543629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543652 : List Nat := [2, 3, 1, 1, 2, 2, 2, 3, 2, 1, 4]
def baseStart_3543652 : Nat := 118140960795 + 3543652 * 2 ^ 59
def prefixEnd_3543652 : Nat := 4983230072969 + 3 ^ 40 * 3543652 * 2
def baseEnd_3543652 : Nat := 1819596748266474678953047

theorem tailTrace_3543652 : CollatzResearch.WordTrace tailWord_3543652 prefixEnd_3543652 1819596748266474678953047 := by
  unfold tailWord_3543652
  simp only [CollatzResearch.WordTrace]
  refine ⟨64623803278980743211836605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86165071038640990949115473 64623803278980743211836605)
  ·
    refine ⟨24233926229617778704438727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64623803278980743211836605 24233926229617778704438727)
    ·
      refine ⟨36350889344426668056658091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24233926229617778704438727 36350889344426668056658091)
      ·
        refine ⟨54526334016640002084987137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36350889344426668056658091 54526334016640002084987137)
        ·
          refine ⟨40894750512480001563740353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54526334016640002084987137 40894750512480001563740353)
          ·
            refine ⟨30671062884360001172805265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40894750512480001563740353 30671062884360001172805265)
            ·
              refine ⟨23003297163270000879603949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30671062884360001172805265 23003297163270000879603949)
              ·
                refine ⟨8626236436226250329851481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23003297163270000879603949 8626236436226250329851481)
                ·
                  refine ⟨6469677327169687747388611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8626236436226250329851481 6469677327169687747388611)
                  ·
                    refine ⟨9704515990754531621082917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6469677327169687747388611 9704515990754531621082917)
                    ·
                      refine ⟨1819596748266474678953047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9704515990754531621082917 1819596748266474678953047)
                      ·
                        rfl

theorem cell23_3543652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 3, 2, 1, 4].length) (baseStart_3543652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3543652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3543652 prefixEnd_3543652 := by exact prefixLift 3543652
  have htrace : WordTrace (prefixWord ++ tailWord_3543652) baseStart_3543652 baseEnd_3543652 := by
    simpa [prefixWord, tailWord_3543652, baseEnd_3543652] using wordTrace_append hprefix tailTrace_3543652
  have hstable : (prefixWord ++ tailWord_3543652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543652).length < 2 ^ (prefixWord ++ tailWord_3543652).sum := by decide
  have hdescent : baseEnd_3543652 < baseStart_3543652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543655 : List Nat := [1, 1, 5, 1, 1, 1, 1, 2, 2, 3, 5]
def baseStart_3543655 : Nat := 118140960795 + 3543655 * 2 ^ 59
def prefixEnd_3543655 : Nat := 4983230072969 + 3 ^ 40 * 3543655 * 2
def baseEnd_3543655 : Nat := 1819598288708438167215533

theorem tailTrace_3543655 : CollatzResearch.WordTrace tailWord_3543655 prefixEnd_3543655 1819598288708438167215533 := by
  unfold tailWord_3543655
  simp only [CollatzResearch.WordTrace]
  refine ⟨129247715976950617936032419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86165143984633745290688279 129247715976950617936032419)
  ·
    refine ⟨193871573965425926904048629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129247715976950617936032419 193871573965425926904048629)
    ·
      refine ⟨18175460059258680647254559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 193871573965425926904048629 18175460059258680647254559)
      ·
        refine ⟨27263190088888020970881839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18175460059258680647254559 27263190088888020970881839)
        ·
          refine ⟨40894785133332031456322759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27263190088888020970881839 40894785133332031456322759)
          ·
            refine ⟨61342177699998047184484139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40894785133332031456322759 61342177699998047184484139)
            ·
              refine ⟨92013266549997070776726209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61342177699998047184484139 92013266549997070776726209)
              ·
                refine ⟨69009949912497803082544657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92013266549997070776726209 69009949912497803082544657)
                ·
                  refine ⟨51757462434373352311908493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69009949912497803082544657 51757462434373352311908493)
                  ·
                    refine ⟨19409048412890007116965685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51757462434373352311908493 19409048412890007116965685)
                    ·
                      refine ⟨1819598288708438167215533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19409048412890007116965685 1819598288708438167215533)
                      ·
                        rfl

theorem cell23_3543655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_3543655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3543655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3543655 prefixEnd_3543655 := by exact prefixLift 3543655
  have htrace : WordTrace (prefixWord ++ tailWord_3543655) baseStart_3543655 baseEnd_3543655 := by
    simpa [prefixWord, tailWord_3543655, baseEnd_3543655] using wordTrace_append hprefix tailTrace_3543655
  have hstable : (prefixWord ++ tailWord_3543655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543655).length < 2 ^ (prefixWord ++ tailWord_3543655).sum := by decide
  have hdescent : baseEnd_3543655 < baseStart_3543655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543672 : List Nat := [2, 1, 2, 1, 1, 1, 2, 6, 2, 2, 3]
def baseStart_3543672 : Nat := 118140960795 + 3543672 * 2 ^ 59
def prefixEnd_3543672 : Nat := 4983230072969 + 3 ^ 40 * 3543672 * 2
def baseEnd_3543672 : Nat := 1819607017879564600702955

theorem tailTrace_3543672 : CollatzResearch.WordTrace tailWord_3543672 prefixEnd_3543672 1819607017879564600702955 := by
  unfold tailWord_3543672
  simp only [CollatzResearch.WordTrace]
  refine ⟨64624168008944514919700635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86165557345259353226267513 64624168008944514919700635)
  ·
    refine ⟨96936252013416772379550953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64624168008944514919700635 96936252013416772379550953)
    ·
      refine ⟨72702189010062579284663215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96936252013416772379550953 72702189010062579284663215)
      ·
        refine ⟨109053283515093868926994823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72702189010062579284663215 109053283515093868926994823)
        ·
          refine ⟨163579925272640803390492235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109053283515093868926994823 163579925272640803390492235)
          ·
            refine ⟨245369887908961205085738353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163579925272640803390492235 245369887908961205085738353)
            ·
              refine ⟨184027415931720903814303765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 245369887908961205085738353 184027415931720903814303765)
              ·
                refine ⟨8626285121799417366295489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 184027415931720903814303765 8626285121799417366295489)
                ·
                  refine ⟨6469713841349563024721617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8626285121799417366295489 6469713841349563024721617)
                  ·
                    refine ⟨4852285381012172268541213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6469713841349563024721617 4852285381012172268541213)
                    ·
                      refine ⟨1819607017879564600702955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4852285381012172268541213 1819607017879564600702955)
                      ·
                        rfl

theorem cell23_3543672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 6, 2, 2, 3].length) (baseStart_3543672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3543672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3543672 prefixEnd_3543672 := by exact prefixLift 3543672
  have htrace : WordTrace (prefixWord ++ tailWord_3543672) baseStart_3543672 baseEnd_3543672 := by
    simpa [prefixWord, tailWord_3543672, baseEnd_3543672] using wordTrace_append hprefix tailTrace_3543672
  have hstable : (prefixWord ++ tailWord_3543672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543672).length < 2 ^ (prefixWord ++ tailWord_3543672).sum := by decide
  have hdescent : baseEnd_3543672 < baseStart_3543672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543715 : List Nat := [1, 1, 1, 4, 1, 1, 2, 1, 2, 4, 5]
def baseStart_3543715 : Nat := 118140960795 + 3543715 * 2 ^ 59
def prefixEnd_3543715 : Nat := 4983230072969 + 3 ^ 40 * 3543715 * 2
def baseEnd_3543715 : Nat := 1819629097547707932465257

theorem tailTrace_3543715 : CollatzResearch.WordTrace tailWord_3543715 prefixEnd_3543715 1819629097547707932465257 := by
  unfold tailWord_3543715
  simp only [CollatzResearch.WordTrace]
  refine ⟨129249904356733248183216599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86166602904488832122144399 129249904356733248183216599)
  ·
    refine ⟨193874856535099872274824899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129249904356733248183216599 193874856535099872274824899)
    ·
      refine ⟨290812284802649808412237349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193874856535099872274824899 290812284802649808412237349)
      ·
        refine ⟨54527303400496839077294503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 290812284802649808412237349 54527303400496839077294503)
        ·
          refine ⟨81790955100745258615941755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54527303400496839077294503 81790955100745258615941755)
          ·
            refine ⟨122686432651117887923912633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81790955100745258615941755 122686432651117887923912633)
            ·
              refine ⟨92014824488338415942934475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122686432651117887923912633 92014824488338415942934475)
              ·
                refine ⟨138022236732507623914401713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92014824488338415942934475 138022236732507623914401713)
                ·
                  refine ⟨103516677549380717935801285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 138022236732507623914401713 103516677549380717935801285)
                  ·
                    refine ⟨19409377040508884612962741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 103516677549380717935801285 19409377040508884612962741)
                    ·
                      refine ⟨1819629097547707932465257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19409377040508884612962741 1819629097547707932465257)
                      ·
                        rfl

theorem cell23_3543715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_3543715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3543715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3543715 prefixEnd_3543715 := by exact prefixLift 3543715
  have htrace : WordTrace (prefixWord ++ tailWord_3543715) baseStart_3543715 baseEnd_3543715 := by
    simpa [prefixWord, tailWord_3543715, baseEnd_3543715] using wordTrace_append hprefix tailTrace_3543715
  have hstable : (prefixWord ++ tailWord_3543715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543715).length < 2 ^ (prefixWord ++ tailWord_3543715).sum := by decide
  have hdescent : baseEnd_3543715 < baseStart_3543715 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543726 : List Nat := [4, 1, 4, 1, 1, 2, 2, 2, 6]
def baseStart_3543726 : Nat := 118140960795 + 3543726 * 2 ^ 59
def prefixEnd_3543726 : Nat := 4983230072969 + 3 ^ 40 * 3543726 * 2
def baseEnd_3543726 : Nat := 202181638426100821047523

theorem tailTrace_3543726 : CollatzResearch.WordTrace tailWord_3543726 prefixEnd_3543726 202181638426100821047523 := by
  unfold tailWord_3543726
  simp only [CollatzResearch.WordTrace]
  refine ⟨16156288194961674632733379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86166870373128931374578021 16156288194961674632733379)
  ·
    refine ⟨24234432292442511949100069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16156288194961674632733379 24234432292442511949100069)
    ·
      refine ⟨4543956054832970990456263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24234432292442511949100069 4543956054832970990456263)
      ·
        refine ⟨6815934082249456485684395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4543956054832970990456263 6815934082249456485684395)
        ·
          refine ⟨10223901123374184728526593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6815934082249456485684395 10223901123374184728526593)
          ·
            refine ⟨7667925842530638546394945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10223901123374184728526593 7667925842530638546394945)
            ·
              refine ⟨5750944381897978909796209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7667925842530638546394945 5750944381897978909796209)
              ·
                refine ⟨4313208286423484182347157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5750944381897978909796209 4313208286423484182347157)
                ·
                  refine ⟨202181638426100821047523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4313208286423484182347157 202181638426100821047523)
                  ·
                    rfl

theorem cell23_3543726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 2, 6].length) (baseStart_3543726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3543726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3543726 prefixEnd_3543726 := by exact prefixLift 3543726
  have htrace : WordTrace (prefixWord ++ tailWord_3543726) baseStart_3543726 baseEnd_3543726 := by
    simpa [prefixWord, tailWord_3543726, baseEnd_3543726] using wordTrace_append hprefix tailTrace_3543726
  have hstable : (prefixWord ++ tailWord_3543726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543726).length < 2 ^ (prefixWord ++ tailWord_3543726).sum := by decide
  have hdescent : baseEnd_3543726 < baseStart_3543726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543752 : List Nat := [2, 1, 3, 1, 2, 3, 1, 3, 1, 6]
def baseStart_3543752 : Nat := 118140960795 + 3543752 * 2 ^ 59
def prefixEnd_3543752 : Nat := 4983230072969 + 3 ^ 40 * 3543752 * 2
def baseEnd_3543752 : Nat := 606549365443974762567529

theorem tailTrace_3543752 : CollatzResearch.WordTrace tailWord_3543752 prefixEnd_3543752 606549365443974762567529 := by
  unfold tailWord_3543752
  simp only [CollatzResearch.WordTrace]
  refine ⟨64625626928799601751156755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86167502571732802334875673 64625626928799601751156755)
  ·
    refine ⟨96938440393199402626735133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64625626928799601751156755 96938440393199402626735133)
    ·
      refine ⟨36351915147449775985025675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96938440393199402626735133 36351915147449775985025675)
      ·
        refine ⟨54527872721174663977538513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36351915147449775985025675 54527872721174663977538513)
        ·
          refine ⟨40895904540880997983153885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54527872721174663977538513 40895904540880997983153885)
          ·
            refine ⟨15335964202830374243682707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40895904540880997983153885 15335964202830374243682707)
            ·
              refine ⟨23003946304245561365524061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15335964202830374243682707 23003946304245561365524061)
              ·
                refine ⟨8626479864092085512071523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23003946304245561365524061 8626479864092085512071523)
                ·
                  refine ⟨12939719796138128268107285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8626479864092085512071523 12939719796138128268107285)
                  ·
                    refine ⟨606549365443974762567529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12939719796138128268107285 606549365443974762567529)
                    ·
                      rfl

theorem cell23_3543752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 3, 1, 6].length) (baseStart_3543752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3543752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3543752 prefixEnd_3543752 := by exact prefixLift 3543752
  have htrace : WordTrace (prefixWord ++ tailWord_3543752) baseStart_3543752 baseEnd_3543752 := by
    simpa [prefixWord, tailWord_3543752, baseEnd_3543752] using wordTrace_append hprefix tailTrace_3543752
  have hstable : (prefixWord ++ tailWord_3543752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543752).length < 2 ^ (prefixWord ++ tailWord_3543752).sum := by decide
  have hdescent : baseEnd_3543752 < baseStart_3543752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543793 : List Nat := [1, 2, 2, 2, 2, 2, 1, 6, 1, 2, 2]
def baseStart_3543793 : Nat := 118140960795 + 3543793 * 2 ^ 59
def prefixEnd_3543793 : Nat := 4983230072969 + 3 ^ 40 * 3543793 * 2
def baseEnd_3543793 : Nat := 1819669149038758627289899

theorem tailTrace_3543793 : CollatzResearch.WordTrace tailWord_3543793 prefixEnd_3543793 1819669149038758627289899 := by
  unfold tailWord_3543793
  simp only [CollatzResearch.WordTrace]
  refine ⟨129252749250450667504556033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86168499500300445003037355 129252749250450667504556033)
  ·
    refine ⟨96939561937838000628417025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129252749250450667504556033 96939561937838000628417025)
    ·
      refine ⟨72704671453378500471312769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96939561937838000628417025 72704671453378500471312769)
      ·
        refine ⟨54528503590033875353484577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72704671453378500471312769 54528503590033875353484577)
        ·
          refine ⟨40896377692525406515113433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54528503590033875353484577 40896377692525406515113433)
          ·
            refine ⟨30672283269394054886335075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40896377692525406515113433 30672283269394054886335075)
            ·
              refine ⟨46008424904091082329502613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30672283269394054886335075 46008424904091082329502613)
              ·
                refine ⟨2156644917379269484195435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 46008424904091082329502613 2156644917379269484195435)
                ·
                  refine ⟨3234967376068904226293153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2156644917379269484195435 3234967376068904226293153)
                  ·
                    refine ⟨2426225532051678169719865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3234967376068904226293153 2426225532051678169719865)
                    ·
                      refine ⟨1819669149038758627289899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2426225532051678169719865 1819669149038758627289899)
                      ·
                        rfl

theorem cell23_3543793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 6, 1, 2, 2].length) (baseStart_3543793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3543793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3543793 prefixEnd_3543793 := by exact prefixLift 3543793
  have htrace : WordTrace (prefixWord ++ tailWord_3543793) baseStart_3543793 baseEnd_3543793 := by
    simpa [prefixWord, tailWord_3543793, baseEnd_3543793] using wordTrace_append hprefix tailTrace_3543793
  have hstable : (prefixWord ++ tailWord_3543793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543793).length < 2 ^ (prefixWord ++ tailWord_3543793).sum := by decide
  have hdescent : baseEnd_3543793 < baseStart_3543793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543806 : List Nat := [4, 2, 2, 1, 2, 1, 3, 1, 1, 2, 4]
def baseStart_3543806 : Nat := 118140960795 + 3543806 * 2 ^ 59
def prefixEnd_3543806 : Nat := 4983230072969 + 3 ^ 40 * 3543806 * 2
def baseEnd_3543806 : Nat := 1819675824287267076427339

theorem tailTrace_3543806 : CollatzResearch.WordTrace tailWord_3543806 prefixEnd_3543806 1819675824287267076427339 := by
  unfold tailWord_3543806
  simp only [CollatzResearch.WordTrace]
  refine ⟨16156652924925446340597409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86168815599602380483186181 16156652924925446340597409)
  ·
    refine ⟨12117489693694084755448057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16156652924925446340597409 12117489693694084755448057)
    ·
      refine ⟨9088117270270563566586043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12117489693694084755448057 9088117270270563566586043)
      ·
        refine ⟨13632175905405845349879065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9088117270270563566586043 13632175905405845349879065)
        ·
          refine ⟨10224131929054384012409299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13632175905405845349879065 10224131929054384012409299)
          ·
            refine ⟨15336197893581576018613949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10224131929054384012409299 15336197893581576018613949)
            ·
              refine ⟨5751074210093091006980231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15336197893581576018613949 5751074210093091006980231)
              ·
                refine ⟨8626611315139636510470347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5751074210093091006980231 8626611315139636510470347)
                ·
                  refine ⟨12939916972709454765705521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8626611315139636510470347 12939916972709454765705521)
                  ·
                    refine ⟨9704937729532091074279141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12939916972709454765705521 9704937729532091074279141)
                    ·
                      refine ⟨1819675824287267076427339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9704937729532091074279141 1819675824287267076427339)
                      ·
                        rfl

theorem cell23_3543806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_3543806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3543806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3543806 prefixEnd_3543806 := by exact prefixLift 3543806
  have htrace : WordTrace (prefixWord ++ tailWord_3543806) baseStart_3543806 baseEnd_3543806 := by
    simpa [prefixWord, tailWord_3543806, baseEnd_3543806] using wordTrace_append hprefix tailTrace_3543806
  have hstable : (prefixWord ++ tailWord_3543806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543806).length < 2 ^ (prefixWord ++ tailWord_3543806).sum := by decide
  have hdescent : baseEnd_3543806 < baseStart_3543806 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543832 : List Nat := [2, 1, 2, 3, 1, 1, 1, 2, 1, 5, 4]
def baseStart_3543832 : Nat := 118140960795 + 3543832 * 2 ^ 59
def prefixEnd_3543832 : Nat := 4983230072969 + 3 ^ 40 * 3543832 * 2
def baseEnd_3543832 : Nat := 1819689174784283974702219

theorem tailTrace_3543832 : CollatzResearch.WordTrace tailWord_3543832 prefixEnd_3543832 1819689174784283974702219 := by
  unfold tailWord_3543832
  simp only [CollatzResearch.WordTrace]
  refine ⟨64627085848654688582612875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86169447798206251443483833 64627085848654688582612875)
  ·
    refine ⟨96940628772982032873919313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64627085848654688582612875 96940628772982032873919313)
    ·
      refine ⟨72705471579736524655439485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96940628772982032873919313 72705471579736524655439485)
      ·
        refine ⟨27264551842401196745789807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72705471579736524655439485 27264551842401196745789807)
        ·
          refine ⟨40896827763601795118684711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27264551842401196745789807 40896827763601795118684711)
          ·
            refine ⟨61345241645402692678027067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40896827763601795118684711 61345241645402692678027067)
            ·
              refine ⟨92017862468104039017040601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61345241645402692678027067 92017862468104039017040601)
              ·
                refine ⟨69013396851078029262780451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92017862468104039017040601 69013396851078029262780451)
                ·
                  refine ⟨103520095276617043894170677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69013396851078029262780451 103520095276617043894170677)
                  ·
                    refine ⟨9705008932182847865078501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 103520095276617043894170677 9705008932182847865078501)
                    ·
                      refine ⟨1819689174784283974702219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9705008932182847865078501 1819689174784283974702219)
                      ·
                        rfl

theorem cell23_3543832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_3543832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3543832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3543832 prefixEnd_3543832 := by exact prefixLift 3543832
  have htrace : WordTrace (prefixWord ++ tailWord_3543832) baseStart_3543832 baseEnd_3543832 := by
    simpa [prefixWord, tailWord_3543832, baseEnd_3543832] using wordTrace_append hprefix tailTrace_3543832
  have hstable : (prefixWord ++ tailWord_3543832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543832).length < 2 ^ (prefixWord ++ tailWord_3543832).sum := by decide
  have hdescent : baseEnd_3543832 < baseStart_3543832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543849 : List Nat := [1, 2, 1, 1, 1, 1, 1, 6, 3, 4, 2]
def baseStart_3543849 : Nat := 118140960795 + 3543849 * 2 ^ 59
def prefixEnd_3543849 : Nat := 4983230072969 + 3 ^ 40 * 3543849 * 2
def baseEnd_3543849 : Nat := 1819697903955410408189641

theorem tailTrace_3543849 : CollatzResearch.WordTrace tailWord_3543849 prefixEnd_3543849 1819697903955410408189641 := by
  unfold tailWord_3543849
  simp only [CollatzResearch.WordTrace]
  refine ⟨129254791738247789068594601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86169861158831859379063067 129254791738247789068594601)
  ·
    refine ⟨96941093803685841801445951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129254791738247789068594601 96941093803685841801445951)
    ·
      refine ⟨145411640705528762702168927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96941093803685841801445951 145411640705528762702168927)
      ·
        refine ⟨218117461058293144053253391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145411640705528762702168927 218117461058293144053253391)
        ·
          refine ⟨327176191587439716079880087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218117461058293144053253391 327176191587439716079880087)
          ·
            refine ⟨490764287381159574119820131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327176191587439716079880087 490764287381159574119820131)
            ·
              refine ⟨736146431071739361179730197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 490764287381159574119820131 736146431071739361179730197)
              ·
                refine ⟨34506863956487782555299853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 736146431071739361179730197 34506863956487782555299853)
                ·
                  refine ⟨12940073983682918458237445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34506863956487782555299853 12940073983682918458237445)
                  ·
                    refine ⟨2426263871940547210919521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12940073983682918458237445 2426263871940547210919521)
                    ·
                      refine ⟨1819697903955410408189641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2426263871940547210919521 1819697903955410408189641)
                      ·
                        rfl

theorem cell23_3543849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 3, 4, 2].length) (baseStart_3543849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3543849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3543849 prefixEnd_3543849 := by exact prefixLift 3543849
  have htrace : WordTrace (prefixWord ++ tailWord_3543849) baseStart_3543849 baseEnd_3543849 := by
    simpa [prefixWord, tailWord_3543849, baseEnd_3543849] using wordTrace_append hprefix tailTrace_3543849
  have hstable : (prefixWord ++ tailWord_3543849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543849).length < 2 ^ (prefixWord ++ tailWord_3543849).sum := by decide
  have hdescent : baseEnd_3543849 < baseStart_3543849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543852 : List Nat := [2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 5]
def baseStart_3543852 : Nat := 118140960795 + 3543852 * 2 ^ 59
def prefixEnd_3543852 : Nat := 4983230072969 + 3 ^ 40 * 3543852 * 2
def baseEnd_3543852 : Nat := 1819699444397373896452127

theorem tailTrace_3543852 : CollatzResearch.WordTrace tailWord_3543852 prefixEnd_3543852 1819699444397373896452127 := by
  unfold tailWord_3543852
  simp only [CollatzResearch.WordTrace]
  refine ⟨64627450578618460290476905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86169934104824613720635873 64627450578618460290476905)
  ·
    refine ⟨48470587933963845217857679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64627450578618460290476905 48470587933963845217857679)
    ·
      refine ⟨72705881900945767826786519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48470587933963845217857679 72705881900945767826786519)
      ·
        refine ⟨109058822851418651740179779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72705881900945767826786519 109058822851418651740179779)
        ·
          refine ⟨163588234277127977610269669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109058822851418651740179779 163588234277127977610269669)
          ·
            refine ⟨30672793926961495801925563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 163588234277127977610269669 30672793926961495801925563)
            ·
              refine ⟨46009190890442243702888345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30672793926961495801925563 46009190890442243702888345)
              ·
                refine ⟨34506893167831682777166259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46009190890442243702888345 34506893167831682777166259)
                ·
                  refine ⟨51760339751747524165749389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34506893167831682777166259 51760339751747524165749389)
                  ·
                    refine ⟨19410127406905321562156021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51760339751747524165749389 19410127406905321562156021)
                    ·
                      refine ⟨1819699444397373896452127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19410127406905321562156021 1819699444397373896452127)
                      ·
                        rfl

theorem cell23_3543852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 5].length) (baseStart_3543852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3543852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3543852 prefixEnd_3543852 := by exact prefixLift 3543852
  have htrace : WordTrace (prefixWord ++ tailWord_3543852) baseStart_3543852 baseEnd_3543852 := by
    simpa [prefixWord, tailWord_3543852, baseEnd_3543852] using wordTrace_append hprefix tailTrace_3543852
  have hstable : (prefixWord ++ tailWord_3543852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543852).length < 2 ^ (prefixWord ++ tailWord_3543852).sum := by decide
  have hdescent : baseEnd_3543852 < baseStart_3543852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543860 : List Nat := [2, 5, 1, 1, 3, 1, 1, 3, 2, 1, 3]
def baseStart_3543860 : Nat := 118140960795 + 3543860 * 2 ^ 59
def prefixEnd_3543860 : Nat := 4983230072969 + 3 ^ 40 * 3543860 * 2
def baseEnd_3543860 : Nat := 1819703552242609865152091

theorem tailTrace_3543860 : CollatzResearch.WordTrace tailWord_3543860 prefixEnd_3543860 1819703552242609865152091 := by
  unfold tailWord_3543860
  simp only [CollatzResearch.WordTrace]
  refine ⟨64627596470603968973622517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86170128627471958631496689 64627596470603968973622517)
  ·
    refine ⟨6058837169119122091277111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64627596470603968973622517 6058837169119122091277111)
    ·
      refine ⟨9088255753678683136915667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6058837169119122091277111 9088255753678683136915667)
      ·
        refine ⟨13632383630518024705373501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9088255753678683136915667 13632383630518024705373501)
        ·
          refine ⟨5112143861444259264515063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13632383630518024705373501 5112143861444259264515063)
          ·
            refine ⟨7668215792166388896772595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5112143861444259264515063 7668215792166388896772595)
            ·
              refine ⟨11502323688249583345158893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7668215792166388896772595 11502323688249583345158893)
              ·
                refine ⟨4313371383093593754434585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11502323688249583345158893 4313371383093593754434585)
                ·
                  refine ⟨3235028537320195315825939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4313371383093593754434585 3235028537320195315825939)
                  ·
                    refine ⟨4852542805980292973738909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3235028537320195315825939 4852542805980292973738909)
                    ·
                      refine ⟨1819703552242609865152091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4852542805980292973738909 1819703552242609865152091)
                      ·
                        rfl

theorem cell23_3543860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_3543860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3543860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3543860 prefixEnd_3543860 := by exact prefixLift 3543860
  have htrace : WordTrace (prefixWord ++ tailWord_3543860) baseStart_3543860 baseEnd_3543860 := by
    simpa [prefixWord, tailWord_3543860, baseEnd_3543860] using wordTrace_append hprefix tailTrace_3543860
  have hstable : (prefixWord ++ tailWord_3543860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543860).length < 2 ^ (prefixWord ++ tailWord_3543860).sum := by decide
  have hdescent : baseEnd_3543860 < baseStart_3543860 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543872 : List Nat := [2, 1, 1, 2, 2, 1, 1, 6, 7]
def baseStart_3543872 : Nat := 118140960795 + 3543872 * 2 ^ 59
def prefixEnd_3543872 : Nat := 4983230072969 + 3 ^ 40 * 3543872 * 2
def baseEnd_3543872 : Nat := 202189968223384868689115

theorem tailTrace_3543872 : CollatzResearch.WordTrace tailWord_3543872 prefixEnd_3543872 202189968223384868689115 := by
  unfold tailWord_3543872
  simp only [CollatzResearch.WordTrace]
  refine ⟨64627815308582231998340935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86170420411442975997787913 64627815308582231998340935)
  ·
    refine ⟨96941722962873347997511403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64627815308582231998340935 96941722962873347997511403)
    ·
      refine ⟨145412584444310021996267105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96941722962873347997511403 145412584444310021996267105)
      ·
        refine ⟨109059438333232516497200329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145412584444310021996267105 109059438333232516497200329)
        ·
          refine ⟨81794578749924387372900247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109059438333232516497200329 81794578749924387372900247)
          ·
            refine ⟨122691868124886581059350371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81794578749924387372900247 122691868124886581059350371)
            ·
              refine ⟨184037802187329871589025557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122691868124886581059350371 184037802187329871589025557)
              ·
                refine ⟨8626771977531087730735573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 184037802187329871589025557 8626771977531087730735573)
                ·
                  refine ⟨202189968223384868689115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8626771977531087730735573 202189968223384868689115)
                  ·
                    rfl

theorem cell23_3543872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 6, 7].length) (baseStart_3543872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3543872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3543872 prefixEnd_3543872 := by exact prefixLift 3543872
  have htrace : WordTrace (prefixWord ++ tailWord_3543872) baseStart_3543872 baseEnd_3543872 := by
    simpa [prefixWord, tailWord_3543872, baseEnd_3543872] using wordTrace_append hprefix tailTrace_3543872
  have hstable : (prefixWord ++ tailWord_3543872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543872).length < 2 ^ (prefixWord ++ tailWord_3543872).sum := by decide
  have hdescent : baseEnd_3543872 < baseStart_3543872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543882 : List Nat := [3, 1, 2, 1, 1, 1, 2, 2, 1, 2, 7]
def baseStart_3543882 : Nat := 118140960795 + 3543882 * 2 ^ 59
def prefixEnd_3543882 : Nat := 4983230072969 + 3 ^ 40 * 3543882 * 2
def baseEnd_3543882 : Nat := 1819714848817008779076989

theorem tailTrace_3543882 : CollatzResearch.WordTrace tailWord_3543882 prefixEnd_3543882 1819714848817008779076989 := by
  unfold tailWord_3543882
  simp only [CollatzResearch.WordTrace]
  refine ⟨32313998836782058926136475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86170663564752157136363933 32313998836782058926136475)
  ·
    refine ⟨48470998255173088389204713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32313998836782058926136475 48470998255173088389204713)
    ·
      refine ⟨36353248691379816291903535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48470998255173088389204713 36353248691379816291903535)
      ·
        refine ⟨54529873037069724437855303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36353248691379816291903535 54529873037069724437855303)
        ·
          refine ⟨81794809555604586656782955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54529873037069724437855303 81794809555604586656782955)
          ·
            refine ⟨122692214333406879985174433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81794809555604586656782955 122692214333406879985174433)
            ·
              refine ⟨92019160750055159988880825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122692214333406879985174433 92019160750055159988880825)
              ·
                refine ⟨69014370562541369991660619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92019160750055159988880825 69014370562541369991660619)
                ·
                  refine ⟨103521555843812054987490929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69014370562541369991660619 103521555843812054987490929)
                  ·
                    refine ⟨77641166882859041240618197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 103521555843812054987490929 77641166882859041240618197)
                    ·
                      refine ⟨1819714848817008779076989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 77641166882859041240618197 1819714848817008779076989)
                      ·
                        rfl

theorem cell23_3543882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_3543882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3543882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3543882 prefixEnd_3543882 := by exact prefixLift 3543882
  have htrace : WordTrace (prefixWord ++ tailWord_3543882) baseStart_3543882 baseEnd_3543882 := by
    simpa [prefixWord, tailWord_3543882, baseEnd_3543882] using wordTrace_append hprefix tailTrace_3543882
  have hstable : (prefixWord ++ tailWord_3543882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543882).length < 2 ^ (prefixWord ++ tailWord_3543882).sum := by decide
  have hdescent : baseEnd_3543882 < baseStart_3543882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543900 : List Nat := [2, 2, 4, 2, 1, 1, 1, 4, 2, 2, 2]
def baseStart_3543900 : Nat := 118140960795 + 3543900 * 2 ^ 59
def prefixEnd_3543900 : Nat := 4983230072969 + 3 ^ 40 * 3543900 * 2
def baseEnd_3543900 : Nat := 1819724091468789708651907

theorem tailTrace_3543900 : CollatzResearch.WordTrace tailWord_3543900 prefixEnd_3543900 1819724091468789708651907 := by
  unfold tailWord_3543900
  simp only [CollatzResearch.WordTrace]
  refine ⟨64628325930531512389350577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86171101240708683185800769 64628325930531512389350577)
  ·
    refine ⟨48471244447898634292012933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64628325930531512389350577 48471244447898634292012933)
    ·
      refine ⟨9088358333980993929752425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48471244447898634292012933 9088358333980993929752425)
      ·
        refine ⟨6816268750485745447314319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9088358333980993929752425 6816268750485745447314319)
        ·
          refine ⟨10224403125728618170971479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6816268750485745447314319 10224403125728618170971479)
          ·
            refine ⟨15336604688592927256457219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10224403125728618170971479 15336604688592927256457219)
            ·
              refine ⟨23004907032889390884685829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15336604688592927256457219 23004907032889390884685829)
              ·
                refine ⟨4313420068666760790878593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23004907032889390884685829 4313420068666760790878593)
                ·
                  refine ⟨3235065051500070593158945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4313420068666760790878593 3235065051500070593158945)
                  ·
                    refine ⟨2426298788625052944869209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3235065051500070593158945 2426298788625052944869209)
                    ·
                      refine ⟨1819724091468789708651907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2426298788625052944869209 1819724091468789708651907)
                      ·
                        rfl

theorem cell23_3543900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_3543900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3543900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3543900 prefixEnd_3543900 := by exact prefixLift 3543900
  have htrace : WordTrace (prefixWord ++ tailWord_3543900) baseStart_3543900 baseEnd_3543900 := by
    simpa [prefixWord, tailWord_3543900, baseEnd_3543900] using wordTrace_append hprefix tailTrace_3543900
  have hstable : (prefixWord ++ tailWord_3543900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543900).length < 2 ^ (prefixWord ++ tailWord_3543900).sum := by decide
  have hdescent : baseEnd_3543900 < baseStart_3543900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543939 : List Nat := [1, 1, 1, 3, 4, 1, 3, 1, 1, 3, 4]
def baseStart_3543939 : Nat := 118140960795 + 3543939 * 2 ^ 59
def prefixEnd_3543939 : Nat := 4983230072969 + 3 ^ 40 * 3543939 * 2
def baseEnd_3543939 : Nat := 1819744117214315056064227

theorem tailTrace_3543939 : CollatzResearch.WordTrace tailWord_3543939 prefixEnd_3543939 1819744117214315056064227 := by
  unfold tailWord_3543939
  simp only [CollatzResearch.WordTrace]
  refine ⟨129258074307921734439370871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86172049538614489626247247 129258074307921734439370871)
  ·
    refine ⟨193887111461882601659056307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129258074307921734439370871 193887111461882601659056307)
    ·
      refine ⟨290830667192823902488584461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193887111461882601659056307 290830667192823902488584461)
      ·
        refine ⟨109061500197308963433219173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 290830667192823902488584461 109061500197308963433219173)
        ·
          refine ⟨20449031286995430643728595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109061500197308963433219173 20449031286995430643728595)
          ·
            refine ⟨30673546930493145965592893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20449031286995430643728595 30673546930493145965592893)
            ·
              refine ⟨11502580098934929737097335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30673546930493145965592893 11502580098934929737097335)
              ·
                refine ⟨17253870148402394605646003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11502580098934929737097335 17253870148402394605646003)
                ·
                  refine ⟨25880805222603591908469005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17253870148402394605646003 25880805222603591908469005)
                  ·
                    refine ⟨9705301958476346965675877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25880805222603591908469005 9705301958476346965675877)
                    ·
                      refine ⟨1819744117214315056064227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9705301958476346965675877 1819744117214315056064227)
                      ·
                        rfl

theorem cell23_3543939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 3, 4].length) (baseStart_3543939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3543939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3543939 prefixEnd_3543939 := by exact prefixLift 3543939
  have htrace : WordTrace (prefixWord ++ tailWord_3543939) baseStart_3543939 baseEnd_3543939 := by
    simpa [prefixWord, tailWord_3543939, baseEnd_3543939] using wordTrace_append hprefix tailTrace_3543939
  have hstable : (prefixWord ++ tailWord_3543939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543939).length < 2 ^ (prefixWord ++ tailWord_3543939).sum := by decide
  have hdescent : baseEnd_3543939 < baseStart_3543939 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543956 : List Nat := [2, 4, 2, 1, 1, 1, 2, 1, 4, 1, 4]
def baseStart_3543956 : Nat := 118140960795 + 3543956 * 2 ^ 59
def prefixEnd_3543956 : Nat := 4983230072969 + 3 ^ 40 * 3543956 * 2
def baseEnd_3543956 : Nat := 1819752846385441489551649

theorem tailTrace_3543956 : CollatzResearch.WordTrace tailWord_3543956 prefixEnd_3543956 1819752846385441489551649 := by
  unfold tailWord_3543956
  simp only [CollatzResearch.WordTrace]
  refine ⟨64629347174430073171369861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86172462899240097561826481 64629347174430073171369861)
  ·
    refine ⟨12118002595205638719631849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64629347174430073171369861 12118002595205638719631849)
    ·
      refine ⟨9088501946404229039723887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12118002595205638719631849 9088501946404229039723887)
      ·
        refine ⟨13632752919606343559585831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9088501946404229039723887 13632752919606343559585831)
        ·
          refine ⟨20449129379409515339378747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13632752919606343559585831 20449129379409515339378747)
          ·
            refine ⟨30673694069114273009068121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20449129379409515339378747 30673694069114273009068121)
            ·
              refine ⟨23005270551835704756801091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30673694069114273009068121 23005270551835704756801091)
              ·
                refine ⟨34507905827753557135201637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23005270551835704756801091 34507905827753557135201637)
                ·
                  refine ⟨6470232342703791962850307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34507905827753557135201637 6470232342703791962850307)
                  ·
                    refine ⟨9705348514055687944275461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6470232342703791962850307 9705348514055687944275461)
                    ·
                      refine ⟨1819752846385441489551649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9705348514055687944275461 1819752846385441489551649)
                      ·
                        rfl

theorem cell23_3543956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_3543956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3543956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3543956 prefixEnd_3543956 := by exact prefixLift 3543956
  have htrace : WordTrace (prefixWord ++ tailWord_3543956) baseStart_3543956 baseEnd_3543956 := by
    simpa [prefixWord, tailWord_3543956, baseEnd_3543956] using wordTrace_append hprefix tailTrace_3543956
  have hstable : (prefixWord ++ tailWord_3543956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543956).length < 2 ^ (prefixWord ++ tailWord_3543956).sum := by decide
  have hdescent : baseEnd_3543956 < baseStart_3543956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544000 : List Nat := [2, 1, 1, 2, 3, 5, 1, 3, 1, 4]
def baseStart_3544000 : Nat := 118140960795 + 3544000 * 2 ^ 59
def prefixEnd_3544000 : Nat := 4983230072969 + 3 ^ 40 * 3544000 * 2
def baseEnd_3544000 : Nat := 606591813178079772467149

theorem tailTrace_3544000 : CollatzResearch.WordTrace tailWord_3544000 prefixEnd_3544000 606591813178079772467149 := by
  unfold tailWord_3544000
  simp only [CollatzResearch.WordTrace]
  refine ⟨64630149580350370928670727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86173532773800494571560969 64630149580350370928670727)
  ·
    refine ⟨96945224370525556393006091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64630149580350370928670727 96945224370525556393006091)
    ·
      refine ⟨145417836555788334589509137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96945224370525556393006091 145417836555788334589509137)
      ·
        refine ⟨109063377416841250942131853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145417836555788334589509137 109063377416841250942131853)
        ·
          refine ⟨40898766531315469103299445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109063377416841250942131853 40898766531315469103299445)
          ·
            refine ⟨3834259362310825228434323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40898766531315469103299445 3834259362310825228434323)
            ·
              refine ⟨5751389043466237842651485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3834259362310825228434323 5751389043466237842651485)
              ·
                refine ⟨2156770891299839190994307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5751389043466237842651485 2156770891299839190994307)
                ·
                  refine ⟨3235156336949758786491461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2156770891299839190994307 3235156336949758786491461)
                  ·
                    refine ⟨606591813178079772467149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3235156336949758786491461 606591813178079772467149)
                    ·
                      rfl

theorem cell23_3544000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 3, 1, 4].length) (baseStart_3544000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3544000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3544000 prefixEnd_3544000 := by exact prefixLift 3544000
  have htrace : WordTrace (prefixWord ++ tailWord_3544000) baseStart_3544000 baseEnd_3544000 := by
    simpa [prefixWord, tailWord_3544000, baseEnd_3544000] using wordTrace_append hprefix tailTrace_3544000
  have hstable : (prefixWord ++ tailWord_3544000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544000).length < 2 ^ (prefixWord ++ tailWord_3544000).sum := by decide
  have hdescent : baseEnd_3544000 < baseStart_3544000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544074 : List Nat := [3, 1, 2, 2, 3, 3, 2, 2, 1, 1, 3]
def baseStart_3544074 : Nat := 118140960795 + 3544074 * 2 ^ 59
def prefixEnd_3544074 : Nat := 4983230072969 + 3 ^ 40 * 3544074 * 2
def baseEnd_3544074 : Nat := 1819813437102672027876107

theorem tailTrace_3544074 : CollatzResearch.WordTrace tailWord_3544074 prefixEnd_3544074 1819813437102672027876107 := by
  unfold tailWord_3544074
  simp only [CollatzResearch.WordTrace]
  refine ⟨32315749540608163123883819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86175332108288434997023517 32315749540608163123883819)
  ·
    refine ⟨48473624310912244685825729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32315749540608163123883819 48473624310912244685825729)
    ·
      refine ⟨36355218233184183514369297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48473624310912244685825729 36355218233184183514369297)
      ·
        refine ⟨27266413674888137635776973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36355218233184183514369297 27266413674888137635776973)
        ·
          refine ⟨10224905128083051613416365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27266413674888137635776973 10224905128083051613416365)
          ·
            refine ⟨3834339423031144355031137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10224905128083051613416365 3834339423031144355031137)
            ·
              refine ⟨2875754567273358266273353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3834339423031144355031137 2875754567273358266273353)
              ·
                refine ⟨2156815925455018699705015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2875754567273358266273353 2156815925455018699705015)
                ·
                  refine ⟨3235223888182528049557523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2156815925455018699705015 3235223888182528049557523)
                  ·
                    refine ⟨4852835832273792074336285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3235223888182528049557523 4852835832273792074336285)
                    ·
                      refine ⟨1819813437102672027876107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4852835832273792074336285 1819813437102672027876107)
                      ·
                        rfl

theorem cell23_3544074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 2, 2, 1, 1, 3].length) (baseStart_3544074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3544074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3544074 prefixEnd_3544074 := by exact prefixLift 3544074
  have htrace : WordTrace (prefixWord ++ tailWord_3544074) baseStart_3544074 baseEnd_3544074 := by
    simpa [prefixWord, tailWord_3544074, baseEnd_3544074] using wordTrace_append hprefix tailTrace_3544074
  have hstable : (prefixWord ++ tailWord_3544074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544074).length < 2 ^ (prefixWord ++ tailWord_3544074).sum := by decide
  have hdescent : baseEnd_3544074 < baseStart_3544074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544089 : List Nat := [1, 2, 1, 2, 1, 1, 4, 1, 2, 2, 6]
def baseStart_3544089 : Nat := 118140960795 + 3544089 * 2 ^ 59
def prefixEnd_3544089 : Nat := 4983230072969 + 3 ^ 40 * 3544089 * 2
def baseEnd_3544089 : Nat := 1819821139312489469188537

theorem tailTrace_3544089 : CollatzResearch.WordTrace tailWord_3544089 prefixEnd_3544089 1819821139312489469188537 := by
  unfold tailWord_3544089
  simp only [CollatzResearch.WordTrace]
  refine ⟨129263545257378310057331321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86175696838252206704887547 129263545257378310057331321)
  ·
    refine ⟨96947658943033732542998491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129263545257378310057331321 96947658943033732542998491)
    ·
      refine ⟨145421488414550598814497737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96947658943033732542998491 145421488414550598814497737)
      ·
        refine ⟨109066116310912949110873303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145421488414550598814497737 109066116310912949110873303)
        ·
          refine ⟨163599174466369423666309955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109066116310912949110873303 163599174466369423666309955)
          ·
            refine ⟨245398761699554135499464933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163599174466369423666309955 245398761699554135499464933)
            ·
              refine ⟨46012267818666400406149675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 245398761699554135499464933 46012267818666400406149675)
              ·
                refine ⟨69018401727999600609224513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46012267818666400406149675 69018401727999600609224513)
                ·
                  refine ⟨51763801295999700456918385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69018401727999600609224513 51763801295999700456918385)
                  ·
                    refine ⟨38822850971999775342688789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51763801295999700456918385 38822850971999775342688789)
                    ·
                      refine ⟨1819821139312489469188537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38822850971999775342688789 1819821139312489469188537)
                      ·
                        rfl

theorem cell23_3544089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 2, 6].length) (baseStart_3544089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3544089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3544089 prefixEnd_3544089 := by exact prefixLift 3544089
  have htrace : WordTrace (prefixWord ++ tailWord_3544089) baseStart_3544089 baseEnd_3544089 := by
    simpa [prefixWord, tailWord_3544089, baseEnd_3544089] using wordTrace_append hprefix tailTrace_3544089
  have hstable : (prefixWord ++ tailWord_3544089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544089).length < 2 ^ (prefixWord ++ tailWord_3544089).sum := by decide
  have hdescent : baseEnd_3544089 < baseStart_3544089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544113 : List Nat := [1, 2, 2, 3, 1, 2, 2, 2, 4, 1, 3]
def baseStart_3544113 : Nat := 118140960795 + 3544113 * 2 ^ 59
def prefixEnd_3544113 : Nat := 4983230072969 + 3 ^ 40 * 3544113 * 2
def baseEnd_3544113 : Nat := 1819833462848197375288427

theorem tailTrace_3544113 : CollatzResearch.WordTrace tailWord_3544113 prefixEnd_3544113 1819833462848197375288427 := by
  unfold tailWord_3544113
  simp only [CollatzResearch.WordTrace]
  refine ⟨129264420609291362156204993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86176280406194241437469995 129264420609291362156204993)
  ·
    refine ⟨96948315456968521617153745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129264420609291362156204993 96948315456968521617153745)
    ·
      refine ⟨72711236592726391212865309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96948315456968521617153745 72711236592726391212865309)
      ·
        refine ⟨27266713722272396704824491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72711236592726391212865309 27266713722272396704824491)
        ·
          refine ⟨40900070583408595057236737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27266713722272396704824491 40900070583408595057236737)
          ·
            refine ⟨30675052937556446292927553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40900070583408595057236737 30675052937556446292927553)
            ·
              refine ⟨23006289703167334719695665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30675052937556446292927553 23006289703167334719695665)
              ·
                refine ⟨17254717277375501039771749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23006289703167334719695665 17254717277375501039771749)
                ·
                  refine ⟨3235259489507906444957203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17254717277375501039771749 3235259489507906444957203)
                  ·
                    refine ⟨4852889234261859667435805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3235259489507906444957203 4852889234261859667435805)
                    ·
                      refine ⟨1819833462848197375288427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4852889234261859667435805 1819833462848197375288427)
                      ·
                        rfl

theorem cell23_3544113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 4, 1, 3].length) (baseStart_3544113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3544113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3544113 prefixEnd_3544113 := by exact prefixLift 3544113
  have htrace : WordTrace (prefixWord ++ tailWord_3544113) baseStart_3544113 baseEnd_3544113 := by
    simpa [prefixWord, tailWord_3544113, baseEnd_3544113] using wordTrace_append hprefix tailTrace_3544113
  have hstable : (prefixWord ++ tailWord_3544113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544113).length < 2 ^ (prefixWord ++ tailWord_3544113).sum := by decide
  have hdescent : baseEnd_3544113 < baseStart_3544113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544153 : List Nat := [1, 2, 1, 2, 2, 1, 2, 5, 1, 4, 2]
def baseStart_3544153 : Nat := 118140960795 + 3544153 * 2 ^ 59
def prefixEnd_3544153 : Nat := 4983230072969 + 3 ^ 40 * 3544153 * 2
def baseEnd_3544153 : Nat := 1819854002074377218788243

theorem tailTrace_3544153 : CollatzResearch.WordTrace tailWord_3544153 prefixEnd_3544153 1819854002074377218788243 := by
  unfold tailWord_3544153
  simp only [CollatzResearch.WordTrace]
  refine ⟨129265879529146448987661113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86177253019430965991774075 129265879529146448987661113)
  ·
    refine ⟨96949409646859836740745835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129265879529146448987661113 96949409646859836740745835)
    ·
      refine ⟨145424114470289755111118753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96949409646859836740745835 145424114470289755111118753)
      ·
        refine ⟨109068085852717316333339065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145424114470289755111118753 109068085852717316333339065)
        ·
          refine ⟨81801064389537987250004299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109068085852717316333339065 81801064389537987250004299)
          ·
            refine ⟨122701596584306980875006449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81801064389537987250004299 122701596584306980875006449)
            ·
              refine ⟨92026197438230235656254837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122701596584306980875006449 92026197438230235656254837)
              ·
                refine ⟨8627456009834084592773891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92026197438230235656254837 8627456009834084592773891)
                ·
                  refine ⟨12941184014751126889160837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8627456009834084592773891 12941184014751126889160837)
                  ·
                    refine ⟨2426472002765836291717657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12941184014751126889160837 2426472002765836291717657)
                    ·
                      refine ⟨1819854002074377218788243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2426472002765836291717657 1819854002074377218788243)
                      ·
                        rfl

theorem cell23_3544153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 5, 1, 4, 2].length) (baseStart_3544153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3544153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3544153 prefixEnd_3544153 := by exact prefixLift 3544153
  have htrace : WordTrace (prefixWord ++ tailWord_3544153) baseStart_3544153 baseEnd_3544153 := by
    simpa [prefixWord, tailWord_3544153, baseEnd_3544153] using wordTrace_append hprefix tailTrace_3544153
  have hstable : (prefixWord ++ tailWord_3544153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544153).length < 2 ^ (prefixWord ++ tailWord_3544153).sum := by decide
  have hdescent : baseEnd_3544153 < baseStart_3544153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544173 : List Nat := [1, 5, 1, 1, 2, 3, 1, 1, 2, 1, 5]
def baseStart_3544173 : Nat := 118140960795 + 3544173 * 2 ^ 59
def prefixEnd_3544173 : Nat := 4983230072969 + 3 ^ 40 * 3544173 * 2
def baseEnd_3544173 : Nat := 1819864271687467140538151

theorem tailTrace_3544173 : CollatzResearch.WordTrace tailWord_3544173 prefixEnd_3544173 1819864271687467140538151 := by
  unfold tailWord_3544173
  simp only [CollatzResearch.WordTrace]
  refine ⟨129266608989073992403389173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86177739326049328268926115 129266608989073992403389173)
  ·
    refine ⟨12118744592725686787817735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 129266608989073992403389173 12118744592725686787817735)
    ·
      refine ⟨18178116889088530181726603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12118744592725686787817735 18178116889088530181726603)
      ·
        refine ⟨27267175333632795272589905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18178116889088530181726603 27267175333632795272589905)
        ·
          refine ⟨20450381500224596454442429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27267175333632795272589905 20450381500224596454442429)
          ·
            refine ⟨7668893062584223670415911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20450381500224596454442429 7668893062584223670415911)
            ·
              refine ⟨11503339593876335505623867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7668893062584223670415911 11503339593876335505623867)
              ·
                refine ⟨17255009390814503258435801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11503339593876335505623867 17255009390814503258435801)
                ·
                  refine ⟨12941257043110877443826851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17255009390814503258435801 12941257043110877443826851)
                  ·
                    refine ⟨19411885564666316165740277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12941257043110877443826851 19411885564666316165740277)
                    ·
                      refine ⟨1819864271687467140538151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19411885564666316165740277 1819864271687467140538151)
                      ·
                        rfl

theorem cell23_3544173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_3544173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3544173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3544173 prefixEnd_3544173 := by exact prefixLift 3544173
  have htrace : WordTrace (prefixWord ++ tailWord_3544173) baseStart_3544173 baseEnd_3544173 := by
    simpa [prefixWord, tailWord_3544173, baseEnd_3544173] using wordTrace_append hprefix tailTrace_3544173
  have hstable : (prefixWord ++ tailWord_3544173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544173).length < 2 ^ (prefixWord ++ tailWord_3544173).sum := by decide
  have hdescent : baseEnd_3544173 < baseStart_3544173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544193 : List Nat := [1, 2, 4, 2, 2, 1, 3, 1, 7]
def baseStart_3544193 : Nat := 118140960795 + 3544193 * 2 ^ 59
def prefixEnd_3544193 : Nat := 4983230072969 + 3 ^ 40 * 3544193 * 2
def baseEnd_3544193 : Nat := 202208282366728562476451

theorem tailTrace_3544193 : CollatzResearch.WordTrace tailWord_3544193 prefixEnd_3544193 202208282366728562476451 := by
  unfold tailWord_3544193
  simp only [CollatzResearch.WordTrace]
  refine ⟨129267338449001535819117233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86178225632667690546078155 129267338449001535819117233)
  ·
    refine ⟨96950503836751151864337925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129267338449001535819117233 96950503836751151864337925)
    ·
      refine ⟨18178219469390840974563361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96950503836751151864337925 18178219469390840974563361)
      ·
        refine ⟨13633664602043130730922521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18178219469390840974563361 13633664602043130730922521)
        ·
          refine ⟨10225248451532348048191891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13633664602043130730922521 10225248451532348048191891)
          ·
            refine ⟨15337872677298522072287837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10225248451532348048191891 15337872677298522072287837)
            ·
              refine ⟨5751702253986945777107939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15337872677298522072287837 5751702253986945777107939)
              ·
                refine ⟨8627553380980418665661909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5751702253986945777107939 8627553380980418665661909)
                ·
                  refine ⟨202208282366728562476451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8627553380980418665661909 202208282366728562476451)
                  ·
                    rfl

theorem cell23_3544193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 1, 7].length) (baseStart_3544193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3544193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3544193 prefixEnd_3544193 := by exact prefixLift 3544193
  have htrace : WordTrace (prefixWord ++ tailWord_3544193) baseStart_3544193 baseEnd_3544193 := by
    simpa [prefixWord, tailWord_3544193, baseEnd_3544193] using wordTrace_append hprefix tailTrace_3544193
  have hstable : (prefixWord ++ tailWord_3544193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544193).length < 2 ^ (prefixWord ++ tailWord_3544193).sum := by decide
  have hdescent : baseEnd_3544193 < baseStart_3544193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544213 : List Nat := [1, 3, 2, 1, 1, 1, 2, 1, 4, 5, 2]
def baseStart_3544213 : Nat := 118140960795 + 3544213 * 2 ^ 59
def prefixEnd_3544213 : Nat := 4983230072969 + 3 ^ 40 * 3544213 * 2
def baseEnd_3544213 : Nat := 1819884810913646984037967

theorem tailTrace_3544213 : CollatzResearch.WordTrace tailWord_3544213 prefixEnd_3544213 1819884810913646984037967 := by
  unfold tailWord_3544213
  simp only [CollatzResearch.WordTrace]
  refine ⟨129268067908929079234845293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86178711939286052823230195 129268067908929079234845293)
  ·
    refine ⟨48475525465848404713066985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129268067908929079234845293 48475525465848404713066985)
    ·
      refine ⟨36356644099386303534800239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48475525465848404713066985 36356644099386303534800239)
      ·
        refine ⟨54534966149079455302200359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36356644099386303534800239 54534966149079455302200359)
        ·
          refine ⟨81802449223619182953300539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54534966149079455302200359 81802449223619182953300539)
          ·
            refine ⟨122703673835428774429950809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81802449223619182953300539 122703673835428774429950809)
            ·
              refine ⟨92027755376571580822463107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122703673835428774429950809 92027755376571580822463107)
              ·
                refine ⟨138041633064857371233694661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92027755376571580822463107 138041633064857371233694661)
                ·
                  refine ⟨25882806199660757106317749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 138041633064857371233694661 25882806199660757106317749)
                  ·
                    refine ⟨2426513081218195978717289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25882806199660757106317749 2426513081218195978717289)
                    ·
                      refine ⟨1819884810913646984037967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2426513081218195978717289 1819884810913646984037967)
                      ·
                        rfl

theorem cell23_3544213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 5, 2].length) (baseStart_3544213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3544213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3544213 prefixEnd_3544213 := by exact prefixLift 3544213
  have htrace : WordTrace (prefixWord ++ tailWord_3544213) baseStart_3544213 baseEnd_3544213 := by
    simpa [prefixWord, tailWord_3544213, baseEnd_3544213] using wordTrace_append hprefix tailTrace_3544213
  have hstable : (prefixWord ++ tailWord_3544213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544213).length < 2 ^ (prefixWord ++ tailWord_3544213).sum := by decide
  have hdescent : baseEnd_3544213 < baseStart_3544213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544243 : List Nat := [1, 1, 1, 2, 3, 2, 4, 2, 2, 1, 4]
def baseStart_3544243 : Nat := 118140960795 + 3544243 * 2 ^ 59
def prefixEnd_3544243 : Nat := 4983230072969 + 3 ^ 40 * 3544243 * 2
def baseEnd_3544243 : Nat := 1819900215333281866662829

theorem tailTrace_3544243 : CollatzResearch.WordTrace tailWord_3544243 prefixEnd_3544243 1819900215333281866662829 := by
  unfold tailWord_3544243
  simp only [CollatzResearch.WordTrace]
  refine ⟨129269162098820394358437383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86179441399213596238958255 129269162098820394358437383)
  ·
    refine ⟨193903743148230591537656075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129269162098820394358437383 193903743148230591537656075)
    ·
      refine ⟨290855614722345887306484113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193903743148230591537656075 290855614722345887306484113)
      ·
        refine ⟨218141711041759415479863085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290855614722345887306484113 218141711041759415479863085)
        ·
          refine ⟨81803141640659780804948657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218141711041759415479863085 81803141640659780804948657)
          ·
            refine ⟨61352356230494835603711493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81803141640659780804948657 61352356230494835603711493)
            ·
              refine ⟨11503566793217781675695905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61352356230494835603711493 11503566793217781675695905)
              ·
                refine ⟨8627675094913336256771929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11503566793217781675695905 8627675094913336256771929)
                ·
                  refine ⟨6470756321185002192578947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8627675094913336256771929 6470756321185002192578947)
                  ·
                    refine ⟨9706134481777503288868421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6470756321185002192578947 9706134481777503288868421)
                    ·
                      refine ⟨1819900215333281866662829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9706134481777503288868421 1819900215333281866662829)
                      ·
                        rfl

theorem cell23_3544243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 2, 2, 1, 4].length) (baseStart_3544243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3544243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3544243 prefixEnd_3544243 := by exact prefixLift 3544243
  have htrace : WordTrace (prefixWord ++ tailWord_3544243) baseStart_3544243 baseEnd_3544243 := by
    simpa [prefixWord, tailWord_3544243, baseEnd_3544243] using wordTrace_append hprefix tailTrace_3544243
  have hstable : (prefixWord ++ tailWord_3544243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544243).length < 2 ^ (prefixWord ++ tailWord_3544243).sum := by decide
  have hdescent : baseEnd_3544243 < baseStart_3544243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544263 : List Nat := [1, 1, 4, 1, 1, 1, 1, 4, 4, 2, 3]
def baseStart_3544263 : Nat := 118140960795 + 3544263 * 2 ^ 59
def prefixEnd_3544263 : Nat := 4983230072969 + 3 ^ 40 * 3544263 * 2
def baseEnd_3544263 : Nat := 1819910484946371788412737

theorem tailTrace_3544263 : CollatzResearch.WordTrace tailWord_3544263 prefixEnd_3544263 1819910484946371788412737 := by
  unfold tailWord_3544263
  simp only [CollatzResearch.WordTrace]
  refine ⟨129269891558747937774165443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86179927705831958516110295 129269891558747937774165443)
  ·
    refine ⟨193904837338121906661248165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129269891558747937774165443 193904837338121906661248165)
    ·
      refine ⟨36357157000897857498984031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 193904837338121906661248165 36357157000897857498984031)
      ·
        refine ⟨54535735501346786248476047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36357157000897857498984031 54535735501346786248476047)
        ·
          refine ⟨81803603252020179372714071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54535735501346786248476047 81803603252020179372714071)
          ·
            refine ⟨122705404878030269059071107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81803603252020179372714071 122705404878030269059071107)
            ·
              refine ⟨184058107317045403588606661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122705404878030269059071107 184058107317045403588606661)
              ·
                refine ⟨34510895121946013172863749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 184058107317045403588606661 34510895121946013172863749)
                ·
                  refine ⟨6470792835364877469911953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34510895121946013172863749 6470792835364877469911953)
                  ·
                    refine ⟨4853094626523658102433965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6470792835364877469911953 4853094626523658102433965)
                    ·
                      refine ⟨1819910484946371788412737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4853094626523658102433965 1819910484946371788412737)
                      ·
                        rfl

theorem cell23_3544263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 4, 2, 3].length) (baseStart_3544263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3544263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3544263 prefixEnd_3544263 := by exact prefixLift 3544263
  have htrace : WordTrace (prefixWord ++ tailWord_3544263) baseStart_3544263 baseEnd_3544263 := by
    simpa [prefixWord, tailWord_3544263, baseEnd_3544263] using wordTrace_append hprefix tailTrace_3544263
  have hstable : (prefixWord ++ tailWord_3544263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544263).length < 2 ^ (prefixWord ++ tailWord_3544263).sum := by decide
  have hdescent : baseEnd_3544263 < baseStart_3544263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544277 : List Nat := [1, 3, 2, 4, 1, 3, 1, 1, 2, 1, 4]
def baseStart_3544277 : Nat := 118140960795 + 3544277 * 2 ^ 59
def prefixEnd_3544277 : Nat := 4983230072969 + 3 ^ 40 * 3544277 * 2
def baseEnd_3544277 : Nat := 1819917673675534733637673

theorem tailTrace_3544277 : CollatzResearch.WordTrace tailWord_3544277 prefixEnd_3544277 1819917673675534733637673 := by
  unfold tailWord_3544277
  simp only [CollatzResearch.WordTrace]
  refine ⟨129270402180697218165175085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86180268120464812110116723 129270402180697218165175085)
  ·
    refine ⟨48476400817761456811940657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129270402180697218165175085 48476400817761456811940657)
    ·
      refine ⟨36357300613321092608955493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48476400817761456811940657 36357300613321092608955493)
      ·
        refine ⟨6816993864997704864179155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36357300613321092608955493 6816993864997704864179155)
        ·
          refine ⟨10225490797496557296268733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6816993864997704864179155 10225490797496557296268733)
          ·
            refine ⟨3834559049061208986100775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10225490797496557296268733 3834559049061208986100775)
            ·
              refine ⟨5751838573591813479151163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3834559049061208986100775 5751838573591813479151163)
              ·
                refine ⟨8627757860387720218726745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5751838573591813479151163 8627757860387720218726745)
                ·
                  refine ⟨6470818395290790164045059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8627757860387720218726745 6470818395290790164045059)
                  ·
                    refine ⟨9706227592936185246067589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6470818395290790164045059 9706227592936185246067589)
                    ·
                      refine ⟨1819917673675534733637673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9706227592936185246067589 1819917673675534733637673)
                      ·
                        rfl

theorem cell23_3544277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_3544277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3544277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3544277 prefixEnd_3544277 := by exact prefixLift 3544277
  have htrace : WordTrace (prefixWord ++ tailWord_3544277) baseStart_3544277 baseEnd_3544277 := by
    simpa [prefixWord, tailWord_3544277, baseEnd_3544277] using wordTrace_append hprefix tailTrace_3544277
  have hstable : (prefixWord ++ tailWord_3544277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544277).length < 2 ^ (prefixWord ++ tailWord_3544277).sum := by decide
  have hdescent : baseEnd_3544277 < baseStart_3544277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544280 : List Nat := [2, 1, 2, 2, 5, 1, 1, 1, 1, 4, 3]
def baseStart_3544280 : Nat := 118140960795 + 3544280 * 2 ^ 59
def prefixEnd_3544280 : Nat := 4983230072969 + 3 ^ 40 * 3544280 * 2
def baseEnd_3544280 : Nat := 1819919214117498221900159

theorem tailTrace_3544280 : CollatzResearch.WordTrace tailWord_3544280 prefixEnd_3544280 1819919214117498221900159 := by
  unfold tailWord_3544280
  simp only [CollatzResearch.WordTrace]
  refine ⟨64635255799843174838767147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86180341066457566451689529 64635255799843174838767147)
  ·
    refine ⟨96952883699764762258150721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64635255799843174838767147 96952883699764762258150721)
    ·
      refine ⟨72714662774823571693613041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96952883699764762258150721 72714662774823571693613041)
      ·
        refine ⟨54535997081117678770209781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72714662774823571693613041 54535997081117678770209781)
        ·
          refine ⟨5112749726354782384707167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54535997081117678770209781 5112749726354782384707167)
          ·
            refine ⟨7669124589532173577060751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5112749726354782384707167 7669124589532173577060751)
            ·
              refine ⟨11503686884298260365591127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7669124589532173577060751 11503686884298260365591127)
              ·
                refine ⟨17255530326447390548386691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11503686884298260365591127 17255530326447390548386691)
                ·
                  refine ⟨25883295489671085822580037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17255530326447390548386691 25883295489671085822580037)
                  ·
                    refine ⟨4853117904313328591733757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25883295489671085822580037 4853117904313328591733757)
                    ·
                      refine ⟨1819919214117498221900159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4853117904313328591733757 1819919214117498221900159)
                      ·
                        rfl

theorem cell23_3544280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 1, 4, 3].length) (baseStart_3544280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3544280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3544280 prefixEnd_3544280 := by exact prefixLift 3544280
  have htrace : WordTrace (prefixWord ++ tailWord_3544280) baseStart_3544280 baseEnd_3544280 := by
    simpa [prefixWord, tailWord_3544280, baseEnd_3544280] using wordTrace_append hprefix tailTrace_3544280
  have hstable : (prefixWord ++ tailWord_3544280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544280).length < 2 ^ (prefixWord ++ tailWord_3544280).sum := by decide
  have hdescent : baseEnd_3544280 < baseStart_3544280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544300 : List Nat := [2, 2, 1, 1, 2, 6, 1, 2, 6]
def baseStart_3544300 : Nat := 118140960795 + 3544300 * 2 ^ 59
def prefixEnd_3544300 : Nat := 4983230072969 + 3 ^ 40 * 3544300 * 2
def baseEnd_3544300 : Nat := 202214387081176460405563

theorem tailTrace_3544300 : CollatzResearch.WordTrace tailWord_3544300 prefixEnd_3544300 202214387081176460405563 := by
  unfold tailWord_3544300
  simp only [CollatzResearch.WordTrace]
  refine ⟨64635620529806946546631177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86180827373075928728841569 64635620529806946546631177)
  ·
    refine ⟨48476715397355209909973383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64635620529806946546631177 48476715397355209909973383)
    ·
      refine ⟨72715073096032814864960075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48476715397355209909973383 72715073096032814864960075)
      ·
        refine ⟨109072609644049222297440113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72715073096032814864960075 109072609644049222297440113)
        ·
          refine ⟨81804457233036916723080085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109072609644049222297440113 81804457233036916723080085)
          ·
            refine ⟨3834583932798605471394379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 81804457233036916723080085 3834583932798605471394379)
            ·
              refine ⟨5751875899197908207091569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3834583932798605471394379 5751875899197908207091569)
              ·
                refine ⟨4313906924398431155318677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5751875899197908207091569 4313906924398431155318677)
                ·
                  refine ⟨202214387081176460405563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4313906924398431155318677 202214387081176460405563)
                  ·
                    rfl

theorem cell23_3544300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 6].length) (baseStart_3544300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3544300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3544300 prefixEnd_3544300 := by exact prefixLift 3544300
  have htrace : WordTrace (prefixWord ++ tailWord_3544300) baseStart_3544300 baseEnd_3544300 := by
    simpa [prefixWord, tailWord_3544300, baseEnd_3544300] using wordTrace_append hprefix tailTrace_3544300
  have hstable : (prefixWord ++ tailWord_3544300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544300).length < 2 ^ (prefixWord ++ tailWord_3544300).sum := by decide
  have hdescent : baseEnd_3544300 < baseStart_3544300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544338 : List Nat := [3, 2, 4, 2, 1, 2, 1, 3, 1, 4]
def baseStart_3544338 : Nat := 118140960795 + 3544338 * 2 ^ 59
def prefixEnd_3544338 : Nat := 4983230072969 + 3 ^ 40 * 3544338 * 2
def baseEnd_3544338 : Nat := 606649665331819664991631

theorem tailTrace_3544338 : CollatzResearch.WordTrace tailWord_3544338 prefixEnd_3544338 606649665331819664991631 := by
  unfold tailWord_3544338
  simp only [CollatzResearch.WordTrace]
  refine ⟨32318156758369056395786417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86181751355650817055430445 32318156758369056395786417)
  ·
    refine ⟨24238617568776792296839813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32318156758369056395786417 24238617568776792296839813)
    ·
      refine ⟨4544740794145648555657465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24238617568776792296839813 4544740794145648555657465)
      ·
        refine ⟨3408555595609236416743099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4544740794145648555657465 3408555595609236416743099)
        ·
          refine ⟨5112833393413854625114649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3408555595609236416743099 5112833393413854625114649)
          ·
            refine ⟨3834625045060390968835987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5112833393413854625114649 3834625045060390968835987)
            ·
              refine ⟨5751937567590586453253981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3834625045060390968835987 5751937567590586453253981)
              ·
                refine ⟨2156976587846469919970243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5751937567590586453253981 2156976587846469919970243)
                ·
                  refine ⟨3235464881769704879955365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2156976587846469919970243 3235464881769704879955365)
                  ·
                    refine ⟨606649665331819664991631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3235464881769704879955365 606649665331819664991631)
                    ·
                      rfl

theorem cell23_3544338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_3544338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3544338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3544338 prefixEnd_3544338 := by exact prefixLift 3544338
  have htrace : WordTrace (prefixWord ++ tailWord_3544338) baseStart_3544338 baseEnd_3544338 := by
    simpa [prefixWord, tailWord_3544338, baseEnd_3544338] using wordTrace_append hprefix tailTrace_3544338
  have hstable : (prefixWord ++ tailWord_3544338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544338).length < 2 ^ (prefixWord ++ tailWord_3544338).sum := by decide
  have hdescent : baseEnd_3544338 < baseStart_3544338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544343 : List Nat := [1, 1, 3, 4, 1, 1, 2, 1, 3, 6]
def baseStart_3544343 : Nat := 118140960795 + 3544343 * 2 ^ 59
def prefixEnd_3544343 : Nat := 4983230072969 + 3 ^ 40 * 3544343 * 2
def baseEnd_3544343 : Nat := 606650521132910491804123

theorem tailTrace_3544343 : CollatzResearch.WordTrace tailWord_3544343 prefixEnd_3544343 606650521132910491804123 := by
  unfold tailWord_3544343
  simp only [CollatzResearch.WordTrace]
  refine ⟨129272809398458111437077683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86181872932305407624718455 129272809398458111437077683)
  ·
    refine ⟨193909214097687167155616525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129272809398458111437077683 193909214097687167155616525)
    ·
      refine ⟨72715955286632687683356197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193909214097687167155616525 72715955286632687683356197)
      ·
        refine ⟨13634241616243628940629287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72715955286632687683356197 13634241616243628940629287)
        ·
          refine ⟨20451362424365443410943931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13634241616243628940629287 20451362424365443410943931)
          ·
            refine ⟨30677043636548165116415897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20451362424365443410943931 30677043636548165116415897)
            ·
              refine ⟨23007782727411123837311923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30677043636548165116415897 23007782727411123837311923)
              ·
                refine ⟨34511674091116685755967885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23007782727411123837311923 34511674091116685755967885)
                ·
                  refine ⟨12941877784168757158487957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34511674091116685755967885 12941877784168757158487957)
                  ·
                    refine ⟨606650521132910491804123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12941877784168757158487957 606650521132910491804123)
                    ·
                      rfl

theorem cell23_3544343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 3, 6].length) (baseStart_3544343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3544343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3544343 prefixEnd_3544343 := by exact prefixLift 3544343
  have htrace : WordTrace (prefixWord ++ tailWord_3544343) baseStart_3544343 baseEnd_3544343 := by
    simpa [prefixWord, tailWord_3544343, baseEnd_3544343] using wordTrace_append hprefix tailTrace_3544343
  have hstable : (prefixWord ++ tailWord_3544343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544343).length < 2 ^ (prefixWord ++ tailWord_3544343).sum := by decide
  have hdescent : baseEnd_3544343 < baseStart_3544343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544344 : List Nat := [2, 1, 2, 3, 1, 3, 3, 3, 1, 1, 3]
def baseStart_3544344 : Nat := 118140960795 + 3544344 * 2 ^ 59
def prefixEnd_3544344 : Nat := 4983230072969 + 3 ^ 40 * 3544344 * 2
def baseEnd_3544344 : Nat := 1819952076879385971499865

theorem tailTrace_3544344 : CollatzResearch.WordTrace tailWord_3544344 prefixEnd_3544344 1819952076879385971499865 := by
  unfold tailWord_3544344
  simp only [CollatzResearch.WordTrace]
  refine ⟨64636422935727244303932043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86181897247636325738576057 64636422935727244303932043)
  ·
    refine ⟨96954634403590866455898065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64636422935727244303932043 96954634403590866455898065)
    ·
      refine ⟨72715975802693149841923549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96954634403590866455898065 72715975802693149841923549)
      ·
        refine ⟨27268490926009931190721331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72715975802693149841923549 27268490926009931190721331)
        ·
          refine ⟨40902736389014896786081997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27268490926009931190721331 40902736389014896786081997)
          ·
            refine ⟨15338526145880586294780749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40902736389014896786081997 15338526145880586294780749)
            ·
              refine ⟨5751947304705219860542781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15338526145880586294780749 5751947304705219860542781)
              ·
                refine ⟨2156980239264457447703543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5751947304705219860542781 2156980239264457447703543)
                ·
                  refine ⟨3235470358896686171555315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2156980239264457447703543 3235470358896686171555315)
                  ·
                    refine ⟨4853205538345029257332973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3235470358896686171555315 4853205538345029257332973)
                    ·
                      refine ⟨1819952076879385971499865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4853205538345029257332973 1819952076879385971499865)
                      ·
                        rfl

theorem cell23_3544344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 3, 1, 1, 3].length) (baseStart_3544344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3544344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3544344 prefixEnd_3544344 := by exact prefixLift 3544344
  have htrace : WordTrace (prefixWord ++ tailWord_3544344) baseStart_3544344 baseEnd_3544344 := by
    simpa [prefixWord, tailWord_3544344, baseEnd_3544344] using wordTrace_append hprefix tailTrace_3544344
  have hstable : (prefixWord ++ tailWord_3544344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544344).length < 2 ^ (prefixWord ++ tailWord_3544344).sum := by decide
  have hdescent : baseEnd_3544344 < baseStart_3544344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544354 : List Nat := [3, 3, 1, 1, 4, 1, 1, 2, 2, 3, 2]
def baseStart_3544354 : Nat := 118140960795 + 3544354 * 2 ^ 59
def prefixEnd_3544354 : Nat := 4983230072969 + 3 ^ 40 * 3544354 * 2
def baseEnd_3544354 : Nat := 1819957211685930932374819

theorem tailTrace_3544354 : CollatzResearch.WordTrace tailWord_3544354 prefixEnd_3544354 1819957211685930932374819 := by
  unfold tailWord_3544354
  simp only [CollatzResearch.WordTrace]
  refine ⟨32318302650354565078932029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86182140400945506877152077 32318302650354565078932029)
  ·
    refine ⟨12119363493882961904599511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32318302650354565078932029 12119363493882961904599511)
    ·
      refine ⟨18179045240824442856899267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12119363493882961904599511 18179045240824442856899267)
      ·
        refine ⟨27268567861236664285348901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18179045240824442856899267 27268567861236664285348901)
        ·
          refine ⟨5112856473981874553502919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27268567861236664285348901 5112856473981874553502919)
          ·
            refine ⟨7669284710972811830254379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5112856473981874553502919 7669284710972811830254379)
            ·
              refine ⟨11503927066459217745381569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7669284710972811830254379 11503927066459217745381569)
              ·
                refine ⟨8627945299844413309036177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11503927066459217745381569 8627945299844413309036177)
                ·
                  refine ⟨6470958974883309981777133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8627945299844413309036177 6470958974883309981777133)
                  ·
                    refine ⟨2426609615581241243166425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6470958974883309981777133 2426609615581241243166425)
                    ·
                      refine ⟨1819957211685930932374819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2426609615581241243166425 1819957211685930932374819)
                      ·
                        rfl

theorem cell23_3544354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 2, 2, 3, 2].length) (baseStart_3544354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3544354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3544354 prefixEnd_3544354 := by exact prefixLift 3544354
  have htrace : WordTrace (prefixWord ++ tailWord_3544354) baseStart_3544354 baseEnd_3544354 := by
    simpa [prefixWord, tailWord_3544354, baseEnd_3544354] using wordTrace_append hprefix tailTrace_3544354
  have hstable : (prefixWord ++ tailWord_3544354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544354).length < 2 ^ (prefixWord ++ tailWord_3544354).sum := by decide
  have hdescent : baseEnd_3544354 < baseStart_3544354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544370 : List Nat := [3, 2, 1, 1, 4, 1, 2, 2, 1, 1, 5]
def baseStart_3544370 : Nat := 118140960795 + 3544370 * 2 ^ 59
def prefixEnd_3544370 : Nat := 4983230072969 + 3 ^ 40 * 3544370 * 2
def baseEnd_3544370 : Nat := 1819965427376402869774745

theorem tailTrace_3544370 : CollatzResearch.WordTrace tailWord_3544370 prefixEnd_3544370 1819965427376402869774745 := by
  unfold tailWord_3544370
  simp only [CollatzResearch.WordTrace]
  refine ⟨32318448542340073762077641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86182529446240196698873709 32318448542340073762077641)
  ·
    refine ⟨24238836406755055321558231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32318448542340073762077641 24238836406755055321558231)
    ·
      refine ⟨36358254610132582982337347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24238836406755055321558231 36358254610132582982337347)
      ·
        refine ⟨54537381915198874473506021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36358254610132582982337347 54537381915198874473506021)
        ·
          refine ⟨10225759109099788963782379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54537381915198874473506021 10225759109099788963782379)
          ·
            refine ⟨15338638663649683445673569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10225759109099788963782379 15338638663649683445673569)
            ·
              refine ⟨11503978997737262584255177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15338638663649683445673569 11503978997737262584255177)
              ·
                refine ⟨8627984248302946938191383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11503978997737262584255177 8627984248302946938191383)
                ·
                  refine ⟨12941976372454420407287075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8627984248302946938191383 12941976372454420407287075)
                  ·
                    refine ⟨19412964558681630610930613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12941976372454420407287075 19412964558681630610930613)
                    ·
                      refine ⟨1819965427376402869774745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19412964558681630610930613 1819965427376402869774745)
                      ·
                        rfl

theorem cell23_3544370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 2, 1, 1, 5].length) (baseStart_3544370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3544370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3544370 prefixEnd_3544370 := by exact prefixLift 3544370
  have htrace : WordTrace (prefixWord ++ tailWord_3544370) baseStart_3544370 baseEnd_3544370 := by
    simpa [prefixWord, tailWord_3544370, baseEnd_3544370] using wordTrace_append hprefix tailTrace_3544370
  have hstable : (prefixWord ++ tailWord_3544370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544370).length < 2 ^ (prefixWord ++ tailWord_3544370).sum := by decide
  have hdescent : baseEnd_3544370 < baseStart_3544370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544373 : List Nat := [1, 3, 3, 1, 2, 2, 1, 10]
def baseStart_3544373 : Nat := 118140960795 + 3544373 * 2 ^ 59
def prefixEnd_3544373 : Nat := 4983230072969 + 3 ^ 40 * 3544373 * 2
def baseEnd_3544373 : Nat := 67406183993272828075453

theorem tailTrace_3544373 : CollatzResearch.WordTrace tailWord_3544373 prefixEnd_3544373 67406183993272828075453 := by
  unfold tailWord_3544373
  simp only [CollatzResearch.WordTrace]
  refine ⟨129273903588349426560669773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86182602392232951040446515 129273903588349426560669773)
  ·
    refine ⟨48477713845631034960251165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129273903588349426560669773 48477713845631034960251165)
    ·
      refine ⟨18179142692111638110094187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48477713845631034960251165 18179142692111638110094187)
      ·
        refine ⟨27268714038167457165141281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18179142692111638110094187 27268714038167457165141281)
        ·
          refine ⟨20451535528625592873855961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27268714038167457165141281 20451535528625592873855961)
          ·
            refine ⟨15338651646469194655391971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20451535528625592873855961 15338651646469194655391971)
            ·
              refine ⟨23007977469703791983087957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15338651646469194655391971 23007977469703791983087957)
              ·
                refine ⟨67406183993272828075453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 23007977469703791983087957 67406183993272828075453)
                ·
                  rfl

theorem cell23_3544373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 10].length) (baseStart_3544373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3544373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3544373 prefixEnd_3544373 := by exact prefixLift 3544373
  have htrace : WordTrace (prefixWord ++ tailWord_3544373) baseStart_3544373 baseEnd_3544373 := by
    simpa [prefixWord, tailWord_3544373, baseEnd_3544373] using wordTrace_append hprefix tailTrace_3544373
  have hstable : (prefixWord ++ tailWord_3544373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544373).length < 2 ^ (prefixWord ++ tailWord_3544373).sum := by decide
  have hdescent : baseEnd_3544373 < baseStart_3544373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544381 : List Nat := [1, 4, 1, 5, 2, 1, 1, 2, 1, 5]
def baseStart_3544381 : Nat := 118140960795 + 3544381 * 2 ^ 59
def prefixEnd_3544381 : Nat := 4983230072969 + 3 ^ 40 * 3544381 * 2
def baseEnd_3544381 : Nat := 606657025221200775579065

theorem tailTrace_3544381 : CollatzResearch.WordTrace tailWord_3544381 prefixEnd_3544381 606657025221200775579065 := by
  unfold tailWord_3544381
  simp only [CollatzResearch.WordTrace]
  refine ⟨129274195372320443926960997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86182796914880295951307331 129274195372320443926960997)
  ·
    refine ⟨24238911632310083236305187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129274195372320443926960997 24238911632310083236305187)
    ·
      refine ⟨36358367448465124854457781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24238911632310083236305187 36358367448465124854457781)
      ·
        refine ⟨3408596948293605455105417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36358367448465124854457781 3408596948293605455105417)
        ·
          refine ⟨2556447711220204091329063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3408596948293605455105417 2556447711220204091329063)
          ·
            refine ⟨3834671566830306136993595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2556447711220204091329063 3834671566830306136993595)
            ·
              refine ⟨5752007350245459205490393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3834671566830306136993595 5752007350245459205490393)
              ·
                refine ⟨4314005512684094404117795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5752007350245459205490393 4314005512684094404117795)
                ·
                  refine ⟨6471008269026141606176693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4314005512684094404117795 6471008269026141606176693)
                  ·
                    refine ⟨606657025221200775579065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6471008269026141606176693 606657025221200775579065)
                    ·
                      rfl

theorem cell23_3544381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 2, 1, 5].length) (baseStart_3544381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3544381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3544381 prefixEnd_3544381 := by exact prefixLift 3544381
  have htrace : WordTrace (prefixWord ++ tailWord_3544381) baseStart_3544381 baseEnd_3544381 := by
    simpa [prefixWord, tailWord_3544381, baseEnd_3544381] using wordTrace_append hprefix tailTrace_3544381
  have hstable : (prefixWord ++ tailWord_3544381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544381).length < 2 ^ (prefixWord ++ tailWord_3544381).sum := by decide
  have hdescent : baseEnd_3544381 < baseStart_3544381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544400 : List Nat := [2, 1, 1, 1, 1, 5, 3, 2, 1, 3, 3]
def baseStart_3544400 : Nat := 118140960795 + 3544400 * 2 ^ 59
def prefixEnd_3544400 : Nat := 4983230072969 + 3 ^ 40 * 3544400 * 2
def baseEnd_3544400 : Nat := 1819980831796037752399607

theorem tailTrace_3544400 : CollatzResearch.WordTrace tailWord_3544400 prefixEnd_3544400 1819980831796037752399607 := by
  unfold tailWord_3544400
  simp only [CollatzResearch.WordTrace]
  refine ⟨64637444179625805085951327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86183258906167740114601769 64637444179625805085951327)
  ·
    refine ⟨96956166269438707628926991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64637444179625805085951327 96956166269438707628926991)
    ·
      refine ⟨145434249404158061443390487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96956166269438707628926991 145434249404158061443390487)
      ·
        refine ⟨218151374106237092165085731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145434249404158061443390487 218151374106237092165085731)
        ·
          refine ⟨327227061159355638247628597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218151374106237092165085731 327227061159355638247628597)
          ·
            refine ⟨30677536983689591085715181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 327227061159355638247628597 30677536983689591085715181)
            ·
              refine ⟨11504076368883596657143193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30677536983689591085715181 11504076368883596657143193)
              ·
                refine ⟨8628057276662697492857395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11504076368883596657143193 8628057276662697492857395)
                ·
                  refine ⟨12942085914994046239286093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8628057276662697492857395 12942085914994046239286093)
                  ·
                    refine ⟨4853282218122767339732285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12942085914994046239286093 4853282218122767339732285)
                    ·
                      refine ⟨1819980831796037752399607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4853282218122767339732285 1819980831796037752399607)
                      ·
                        rfl

theorem cell23_3544400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 2, 1, 3, 3].length) (baseStart_3544400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3544400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3544400 prefixEnd_3544400 := by exact prefixLift 3544400
  have htrace : WordTrace (prefixWord ++ tailWord_3544400) baseStart_3544400 baseEnd_3544400 := by
    simpa [prefixWord, tailWord_3544400, baseEnd_3544400] using wordTrace_append hprefix tailTrace_3544400
  have hstable : (prefixWord ++ tailWord_3544400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544400).length < 2 ^ (prefixWord ++ tailWord_3544400).sum := by decide
  have hdescent : baseEnd_3544400 < baseStart_3544400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544404 : List Nat := [2, 4, 1, 1, 2, 1, 5, 1, 1, 2, 3]
def baseStart_3544404 : Nat := 118140960795 + 3544404 * 2 ^ 59
def prefixEnd_3544404 : Nat := 4983230072969 + 3 ^ 40 * 3544404 * 2
def baseEnd_3544404 : Nat := 1819982885718655736749589

theorem tailTrace_3544404 : CollatzResearch.WordTrace tailWord_3544404 prefixEnd_3544404 1819982885718655736749589 := by
  unfold tailWord_3544404
  simp only [CollatzResearch.WordTrace]
  refine ⟨64637517125618559427524133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86183356167491412570032177 64637517125618559427524133)
  ·
    refine ⟨12119534461053479892660775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64637517125618559427524133 12119534461053479892660775)
    ·
      refine ⟨18179301691580219838991163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12119534461053479892660775 18179301691580219838991163)
      ·
        refine ⟨27268952537370329758486745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18179301691580219838991163 27268952537370329758486745)
        ·
          refine ⟨20451714403027747318865059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27268952537370329758486745 20451714403027747318865059)
          ·
            refine ⟨30677571604541620978297589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20451714403027747318865059 30677571604541620978297589)
            ·
              refine ⟨2876022337925776966715399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30677571604541620978297589 2876022337925776966715399)
              ·
                refine ⟨4314033506888665450073099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2876022337925776966715399 4314033506888665450073099)
                ·
                  refine ⟨6471050260332998175109649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4314033506888665450073099 6471050260332998175109649)
                  ·
                    refine ⟨4853287695249748631332237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6471050260332998175109649 4853287695249748631332237)
                    ·
                      refine ⟨1819982885718655736749589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4853287695249748631332237 1819982885718655736749589)
                      ·
                        rfl

theorem cell23_3544404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 5, 1, 1, 2, 3].length) (baseStart_3544404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3544404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3544404 prefixEnd_3544404 := by exact prefixLift 3544404
  have htrace : WordTrace (prefixWord ++ tailWord_3544404) baseStart_3544404 baseEnd_3544404 := by
    simpa [prefixWord, tailWord_3544404, baseEnd_3544404] using wordTrace_append hprefix tailTrace_3544404
  have hstable : (prefixWord ++ tailWord_3544404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544404).length < 2 ^ (prefixWord ++ tailWord_3544404).sum := by decide
  have hdescent : baseEnd_3544404 < baseStart_3544404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544433 : List Nat := [1, 2, 2, 2, 1, 2, 3, 1, 1, 8]
def baseStart_3544433 : Nat := 118140960795 + 3544433 * 2 ^ 59
def prefixEnd_3544433 : Nat := 4983230072969 + 3 ^ 40 * 3544433 * 2
def baseEnd_3544433 : Nat := 606665925552545374428985

theorem tailTrace_3544433 : CollatzResearch.WordTrace tailWord_3544433 prefixEnd_3544433 606665925552545374428985 := by
  unfold tailWord_3544433
  simp only [CollatzResearch.WordTrace]
  refine ⟨129276091968132056807853953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86184061312088037871902635 129276091968132056807853953)
  ·
    refine ⟨96957068976099042605890465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129276091968132056807853953 96957068976099042605890465)
    ·
      refine ⟨72717801732074281954417849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96957068976099042605890465 72717801732074281954417849)
      ·
        refine ⟨54538351299055711465813387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72717801732074281954417849 54538351299055711465813387)
        ·
          refine ⟨81807526948583567198720081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54538351299055711465813387 81807526948583567198720081)
          ·
            refine ⟨61355645211437675399040061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81807526948583567198720081 61355645211437675399040061)
            ·
              refine ⟨23008366954289128274640023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61355645211437675399040061 23008366954289128274640023)
              ·
                refine ⟨34512550431433692411960035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23008366954289128274640023 34512550431433692411960035)
                ·
                  refine ⟨51768825647150538617940053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34512550431433692411960035 51768825647150538617940053)
                  ·
                    refine ⟨606665925552545374428985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 51768825647150538617940053 606665925552545374428985)
                    ·
                      rfl

theorem cell23_3544433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 8].length) (baseStart_3544433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3544433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3544433 prefixEnd_3544433 := by exact prefixLift 3544433
  have htrace : WordTrace (prefixWord ++ tailWord_3544433) baseStart_3544433 baseEnd_3544433 := by
    simpa [prefixWord, tailWord_3544433, baseEnd_3544433] using wordTrace_append hprefix tailTrace_3544433
  have hstable : (prefixWord ++ tailWord_3544433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544433).length < 2 ^ (prefixWord ++ tailWord_3544433).sum := by decide
  have hdescent : baseEnd_3544433 < baseStart_3544433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544474 : List Nat := [3, 1, 1, 4, 1, 1, 3, 1, 4, 2, 2]
def baseStart_3544474 : Nat := 118140960795 + 3544474 * 2 ^ 59
def prefixEnd_3544474 : Nat := 4983230072969 + 3 ^ 40 * 3544474 * 2
def baseEnd_3544474 : Nat := 1820018829364470462874267

theorem tailTrace_3544474 : CollatzResearch.WordTrace tailWord_3544474 prefixEnd_3544474 1820018829364470462874267 := by
  unfold tailWord_3544474
  simp only [CollatzResearch.WordTrace]
  refine ⟨32319396840245880202524119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86185058240655680540064317 32319396840245880202524119)
  ·
    refine ⟨48479095260368820303786179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32319396840245880202524119 48479095260368820303786179)
    ·
      refine ⟨72718642890553230455679269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48479095260368820303786179 72718642890553230455679269)
      ·
        refine ⟨13634745541978730710439863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72718642890553230455679269 13634745541978730710439863)
        ·
          refine ⟨20452118312968096065659795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13634745541978730710439863 20452118312968096065659795)
          ·
            refine ⟨30678177469452144098489693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20452118312968096065659795 30678177469452144098489693)
            ·
              refine ⟨11504316551044554036933635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30678177469452144098489693 11504316551044554036933635)
              ·
                refine ⟨17256474826566831055400453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11504316551044554036933635 17256474826566831055400453)
                ·
                  refine ⟨3235589029981280822887585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17256474826566831055400453 3235589029981280822887585)
                  ·
                    refine ⟨2426691772485960617165689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3235589029981280822887585 2426691772485960617165689)
                    ·
                      refine ⟨1820018829364470462874267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2426691772485960617165689 1820018829364470462874267)
                      ·
                        rfl

theorem cell23_3544474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 4, 2, 2].length) (baseStart_3544474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3544474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3544474 prefixEnd_3544474 := by exact prefixLift 3544474
  have htrace : WordTrace (prefixWord ++ tailWord_3544474) baseStart_3544474 baseEnd_3544474 := by
    simpa [prefixWord, tailWord_3544474, baseEnd_3544474] using wordTrace_append hprefix tailTrace_3544474
  have hstable : (prefixWord ++ tailWord_3544474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544474).length < 2 ^ (prefixWord ++ tailWord_3544474).sum := by decide
  have hdescent : baseEnd_3544474 < baseStart_3544474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544480 : List Nat := [2, 1, 1, 4, 1, 2, 4, 1, 7]
def baseStart_3544480 : Nat := 118140960795 + 3544480 * 2 ^ 59
def prefixEnd_3544480 : Nat := 4983230072969 + 3 ^ 40 * 3544480 * 2
def baseEnd_3544480 : Nat := 202224656694266382155471

theorem tailTrace_3544480 : CollatzResearch.WordTrace tailWord_3544480 prefixEnd_3544480 202224656694266382155471 := by
  unfold tailWord_3544480
  simp only [CollatzResearch.WordTrace]
  refine ⟨64638903099480891917407447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86185204132641189223209929 64638903099480891917407447)
  ·
    refine ⟨96958354649221337876111171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64638903099480891917407447 96958354649221337876111171)
    ·
      refine ⟨145437531973832006814166757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96958354649221337876111171 145437531973832006814166757)
      ·
        refine ⟨27269537245093501277656267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145437531973832006814166757 27269537245093501277656267)
        ·
          refine ⟨40904305867640251916484401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27269537245093501277656267 40904305867640251916484401)
          ·
            refine ⟨30678229400730188937363301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40904305867640251916484401 30678229400730188937363301)
            ·
              refine ⟨5752168012636910425755619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30678229400730188937363301 5752168012636910425755619)
              ·
                refine ⟨8628252018955365638633429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5752168012636910425755619 8628252018955365638633429)
                ·
                  refine ⟨202224656694266382155471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8628252018955365638633429 202224656694266382155471)
                  ·
                    rfl

theorem cell23_3544480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 1, 7].length) (baseStart_3544480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3544480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3544480 prefixEnd_3544480 := by exact prefixLift 3544480
  have htrace : WordTrace (prefixWord ++ tailWord_3544480) baseStart_3544480 baseEnd_3544480 := by
    simpa [prefixWord, tailWord_3544480, baseEnd_3544480] using wordTrace_append hprefix tailTrace_3544480
  have hstable : (prefixWord ++ tailWord_3544480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544480).length < 2 ^ (prefixWord ++ tailWord_3544480).sum := by decide
  have hdescent : baseEnd_3544480 < baseStart_3544480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544520 : List Nat := [2, 1, 3, 1, 3, 1, 2, 2, 1, 2, 5]
def baseStart_3544520 : Nat := 118140960795 + 3544520 * 2 ^ 59
def prefixEnd_3544520 : Nat := 4983230072969 + 3 ^ 40 * 3544520 * 2
def baseEnd_3544520 : Nat := 1820042449474577282899055

theorem tailTrace_3544520 : CollatzResearch.WordTrace tailWord_3544520 prefixEnd_3544520 1820042449474577282899055 := by
  unfold tailWord_3544520
  simp only [CollatzResearch.WordTrace]
  refine ⟨64639632559408435333135507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86186176745877913777514009 64639632559408435333135507)
  ·
    refine ⟨96959448839112652999703261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64639632559408435333135507 96959448839112652999703261)
    ·
      refine ⟨36359793314667244874888723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96959448839112652999703261 36359793314667244874888723)
      ·
        refine ⟨54539689972000867312333085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36359793314667244874888723 54539689972000867312333085)
        ·
          refine ⟨20452383739500325242124907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54539689972000867312333085 20452383739500325242124907)
          ·
            refine ⟨30678575609250487863187361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20452383739500325242124907 30678575609250487863187361)
            ·
              refine ⟨23008931706937865897390521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30678575609250487863187361 23008931706937865897390521)
              ·
                refine ⟨17256698780203399423042891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23008931706937865897390521 17256698780203399423042891)
                ·
                  refine ⟨25885048170305099134564337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17256698780203399423042891 25885048170305099134564337)
                  ·
                    refine ⟨19413786127728824350923253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25885048170305099134564337 19413786127728824350923253)
                    ·
                      refine ⟨1820042449474577282899055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19413786127728824350923253 1820042449474577282899055)
                      ·
                        rfl

theorem cell23_3544520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 1, 2, 5].length) (baseStart_3544520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3544520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3544520 prefixEnd_3544520 := by exact prefixLift 3544520
  have htrace : WordTrace (prefixWord ++ tailWord_3544520) baseStart_3544520 baseEnd_3544520 := by
    simpa [prefixWord, tailWord_3544520, baseEnd_3544520] using wordTrace_append hprefix tailTrace_3544520
  have hstable : (prefixWord ++ tailWord_3544520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544520).length < 2 ^ (prefixWord ++ tailWord_3544520).sum := by decide
  have hdescent : baseEnd_3544520 < baseStart_3544520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544582 : List Nat := [6, 2, 1, 1, 2, 2, 2, 2, 5]
def baseStart_3544582 : Nat := 118140960795 + 3544582 * 2 ^ 59
def prefixEnd_3544582 : Nat := 4983230072969 + 3 ^ 40 * 3544582 * 2
def baseEnd_3544582 : Nat := 202230476141684004480419

theorem tailTrace_3544582 : CollatzResearch.WordTrace tailWord_3544582 prefixEnd_3544582 202230476141684004480419 := by
  unfold tailWord_3544582
  simp only [CollatzResearch.WordTrace]
  refine ⟨4040047701393507976719625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 86187684296394836836685333 4040047701393507976719625)
  ·
    refine ⟨3030035776045130982539719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4040047701393507976719625 3030035776045130982539719)
    ·
      refine ⟨4545053664067696473809579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3030035776045130982539719 4545053664067696473809579)
      ·
        refine ⟨6817580496101544710714369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4545053664067696473809579 6817580496101544710714369)
        ·
          refine ⟨5113185372076158533035777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6817580496101544710714369 5113185372076158533035777)
          ·
            refine ⟨3834889029057118899776833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5113185372076158533035777 3834889029057118899776833)
            ·
              refine ⟨2876166771792839174832625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3834889029057118899776833 2876166771792839174832625)
              ·
                refine ⟨2157125078844629381124469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2876166771792839174832625 2157125078844629381124469)
                ·
                  refine ⟨202230476141684004480419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2157125078844629381124469 202230476141684004480419)
                  ·
                    rfl

theorem cell23_3544582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_3544582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3544582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3544582 prefixEnd_3544582 := by exact prefixLift 3544582
  have htrace : WordTrace (prefixWord ++ tailWord_3544582) baseStart_3544582 baseEnd_3544582 := by
    simpa [prefixWord, tailWord_3544582, baseEnd_3544582] using wordTrace_append hprefix tailTrace_3544582
  have hstable : (prefixWord ++ tailWord_3544582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544582).length < 2 ^ (prefixWord ++ tailWord_3544582).sum := by decide
  have hdescent : baseEnd_3544582 < baseStart_3544582 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544631 : List Nat := [1, 1, 3, 1, 2, 4, 1, 5, 1, 1, 3]
def baseStart_3544631 : Nat := 118140960795 + 3544631 * 2 ^ 59
def prefixEnd_3544631 : Nat := 4983230072969 + 3 ^ 40 * 3544631 * 2
def baseEnd_3544631 : Nat := 1820099445827226348611045

theorem tailTrace_3544631 : CollatzResearch.WordTrace tailWord_3544631 prefixEnd_3544631 1820099445827226348611045 := by
  unfold tailWord_3544631
  simp only [CollatzResearch.WordTrace]
  refine ⟨129283313621414736623561747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86188875747609824415707831 129283313621414736623561747)
  ·
    refine ⟨193924970432122104935342621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129283313621414736623561747 193924970432122104935342621)
    ·
      refine ⟨72721863912045789350753483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193924970432122104935342621 72721863912045789350753483)
      ·
        refine ⟨109082795868068684026130225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72721863912045789350753483 109082795868068684026130225)
        ·
          refine ⟨81812096901051513019597669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109082795868068684026130225 81812096901051513019597669)
          ·
            refine ⟨15339768168947158691174563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81812096901051513019597669 15339768168947158691174563)
            ·
              refine ⟨23009652253420738036761845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15339768168947158691174563 23009652253420738036761845)
              ·
                refine ⟨2157154898758194190946423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23009652253420738036761845 2157154898758194190946423)
                ·
                  refine ⟨3235732348137291286419635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2157154898758194190946423 3235732348137291286419635)
                  ·
                    refine ⟨4853598522205936929629453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3235732348137291286419635 4853598522205936929629453)
                    ·
                      refine ⟨1820099445827226348611045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4853598522205936929629453 1820099445827226348611045)
                      ·
                        rfl

theorem cell23_3544631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 5, 1, 1, 3].length) (baseStart_3544631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3544631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3544631 prefixEnd_3544631 := by exact prefixLift 3544631
  have htrace : WordTrace (prefixWord ++ tailWord_3544631) baseStart_3544631 baseEnd_3544631 := by
    simpa [prefixWord, tailWord_3544631, baseEnd_3544631] using wordTrace_append hprefix tailTrace_3544631
  have hstable : (prefixWord ++ tailWord_3544631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544631).length < 2 ^ (prefixWord ++ tailWord_3544631).sum := by decide
  have hdescent : baseEnd_3544631 < baseStart_3544631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544657 : List Nat := [1, 2, 2, 1, 3, 2, 3, 2, 1, 1, 5]
def baseStart_3544657 : Nat := 118140960795 + 3544657 * 2 ^ 59
def prefixEnd_3544657 : Nat := 4983230072969 + 3 ^ 40 * 3544657 * 2
def baseEnd_3544657 : Nat := 1820112796324243246885925

theorem tailTrace_3544657 : CollatzResearch.WordTrace tailWord_3544657 prefixEnd_3544657 1820112796324243246885925 := by
  unfold tailWord_3544657
  simp only [CollatzResearch.WordTrace]
  refine ⟨129284261919320543064008225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86189507946213695376005483 129284261919320543064008225)
  ·
    refine ⟨96963196439490407298006169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129284261919320543064008225 96963196439490407298006169)
    ·
      refine ⟨72722397329617805473504627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96963196439490407298006169 72722397329617805473504627)
      ·
        refine ⟨109083595994426708210256941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72722397329617805473504627 109083595994426708210256941)
        ·
          refine ⟨40906348497910015578846353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109083595994426708210256941 40906348497910015578846353)
          ·
            refine ⟨30679761373432511684134765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40906348497910015578846353 30679761373432511684134765)
            ·
              refine ⟨11504910515037191881550537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30679761373432511684134765 11504910515037191881550537)
              ·
                refine ⟨8628682886277893911162903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11504910515037191881550537 8628682886277893911162903)
                ·
                  refine ⟨12943024329416840866744355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8628682886277893911162903 12943024329416840866744355)
                  ·
                    refine ⟨19414536494125261300116533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12943024329416840866744355 19414536494125261300116533)
                    ·
                      refine ⟨1820112796324243246885925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19414536494125261300116533 1820112796324243246885925)
                      ·
                        rfl

theorem cell23_3544657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 2, 1, 1, 5].length) (baseStart_3544657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3544657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3544657 prefixEnd_3544657 := by exact prefixLift 3544657
  have htrace : WordTrace (prefixWord ++ tailWord_3544657) baseStart_3544657 baseEnd_3544657 := by
    simpa [prefixWord, tailWord_3544657, baseEnd_3544657] using wordTrace_append hprefix tailTrace_3544657
  have hstable : (prefixWord ++ tailWord_3544657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544657).length < 2 ^ (prefixWord ++ tailWord_3544657).sum := by decide
  have hdescent : baseEnd_3544657 < baseStart_3544657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544677 : List Nat := [1, 3, 1, 3, 3, 2, 1, 9]
def baseStart_3544677 : Nat := 118140960795 + 3544677 * 2 ^ 59
def prefixEnd_3544677 : Nat := 4983230072969 + 3 ^ 40 * 3544677 * 2
def baseEnd_3544677 : Nat := 67411965405086413653179

theorem tailTrace_3544677 : CollatzResearch.WordTrace tailWord_3544677 prefixEnd_3544677 67411965405086413653179 := by
  unfold tailWord_3544677
  simp only [CollatzResearch.WordTrace]
  refine ⟨129284991379248086479736285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86189994252832057653157523 129284991379248086479736285)
  ·
    refine ⟨48481871767218032429901107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129284991379248086479736285 48481871767218032429901107)
    ·
      refine ⟨72722807650827048644851661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48481871767218032429901107 72722807650827048644851661)
      ·
        refine ⟨27271052869060143241819373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72722807650827048644851661 27271052869060143241819373)
        ·
          refine ⟨10226644825897553715682265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27271052869060143241819373 10226644825897553715682265)
          ·
            refine ⟨7669983619423165286761699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10226644825897553715682265 7669983619423165286761699)
            ·
              refine ⟨11504975429134747930142549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7669983619423165286761699 11504975429134747930142549)
              ·
                refine ⟨67411965405086413653179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11504975429134747930142549 67411965405086413653179)
                ·
                  rfl

theorem cell23_3544677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 9].length) (baseStart_3544677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3544677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3544677 prefixEnd_3544677 := by exact prefixLift 3544677
  have htrace : WordTrace (prefixWord ++ tailWord_3544677) baseStart_3544677 baseEnd_3544677 := by
    simpa [prefixWord, tailWord_3544677, baseEnd_3544677] using wordTrace_append hprefix tailTrace_3544677
  have hstable : (prefixWord ++ tailWord_3544677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544677).length < 2 ^ (prefixWord ++ tailWord_3544677).sum := by decide
  have hdescent : baseEnd_3544677 < baseStart_3544677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544687 : List Nat := [1, 1, 2, 1, 3, 2, 1, 3, 3, 3, 3]
def baseStart_3544687 : Nat := 118140960795 + 3544687 * 2 ^ 59
def prefixEnd_3544687 : Nat := 4983230072969 + 3 ^ 40 * 3544687 * 2
def baseEnd_3544687 : Nat := 1820128200743878129510787

theorem tailTrace_3544687 : CollatzResearch.WordTrace tailWord_3544687 prefixEnd_3544687 1820128200743878129510787 := by
  unfold tailWord_3544687
  simp only [CollatzResearch.WordTrace]
  refine ⟨129285356109211858187600315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86190237406141238791733543 129285356109211858187600315)
  ·
    refine ⟨193928034163817787281400473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129285356109211858187600315 193928034163817787281400473)
    ·
      refine ⟨145446025622863340461050355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193928034163817787281400473 145446025622863340461050355)
      ·
        refine ⟨218169038434295010691575533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145446025622863340461050355 218169038434295010691575533)
        ·
          refine ⟨81813389412860629009340825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218169038434295010691575533 81813389412860629009340825)
          ·
            refine ⟨61360042059645471757005619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81813389412860629009340825 61360042059645471757005619)
            ·
              refine ⟨92040063089468207635508429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61360042059645471757005619 92040063089468207635508429)
              ·
                refine ⟨34515023658550577863315661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92040063089468207635508429 34515023658550577863315661)
                ·
                  refine ⟨12943133871956466698743373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34515023658550577863315661 12943133871956466698743373)
                  ·
                    refine ⟨4853675201983675012028765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12943133871956466698743373 4853675201983675012028765)
                    ·
                      refine ⟨1820128200743878129510787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4853675201983675012028765 1820128200743878129510787)
                      ·
                        rfl

theorem cell23_3544687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 3, 3, 3].length) (baseStart_3544687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3544687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3544687 prefixEnd_3544687 := by exact prefixLift 3544687
  have htrace : WordTrace (prefixWord ++ tailWord_3544687) baseStart_3544687 baseEnd_3544687 := by
    simpa [prefixWord, tailWord_3544687, baseEnd_3544687] using wordTrace_append hprefix tailTrace_3544687
  have hstable : (prefixWord ++ tailWord_3544687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544687).length < 2 ^ (prefixWord ++ tailWord_3544687).sum := by decide
  have hdescent : baseEnd_3544687 < baseStart_3544687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544694 : List Nat := [5, 1, 1, 2, 2, 3, 9]
def baseStart_3544694 : Nat := 118140960795 + 3544694 * 2 ^ 59
def prefixEnd_3544694 : Nat := 4983230072969 + 3 ^ 40 * 3544694 * 2
def baseEnd_3544694 : Nat := 22470762902573575334855

theorem tailTrace_3544694 : CollatzResearch.WordTrace tailWord_3544694 prefixEnd_3544694 22470762902573575334855 := by
  unfold tailWord_3544694
  simp only [CollatzResearch.WordTrace]
  refine ⟨8080350713761656148944071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86190407613457665588736757 8080350713761656148944071)
  ·
    refine ⟨12120526070642484223416107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8080350713761656148944071 12120526070642484223416107)
    ·
      refine ⟨18180789105963726335124161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12120526070642484223416107 18180789105963726335124161)
      ·
        refine ⟨13635591829472794751343121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18180789105963726335124161 13635591829472794751343121)
        ·
          refine ⟨10226693872104596063507341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13635591829472794751343121 10226693872104596063507341)
          ·
            refine ⟨3835010202039223523815253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10226693872104596063507341 3835010202039223523815253)
            ·
              refine ⟨22470762902573575334855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3835010202039223523815253 22470762902573575334855)
              ·
                rfl

theorem cell23_3544694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 9].length) (baseStart_3544694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3544694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3544694 prefixEnd_3544694 := by exact prefixLift 3544694
  have htrace : WordTrace (prefixWord ++ tailWord_3544694) baseStart_3544694 baseEnd_3544694 := by
    simpa [prefixWord, tailWord_3544694, baseEnd_3544694] using wordTrace_append hprefix tailTrace_3544694
  have hstable : (prefixWord ++ tailWord_3544694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544694).length < 2 ^ (prefixWord ++ tailWord_3544694).sum := by decide
  have hdescent : baseEnd_3544694 < baseStart_3544694 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544704 : List Nat := [2, 1, 1, 2, 1, 4, 1, 3, 4, 1, 3]
def baseStart_3544704 : Nat := 118140960795 + 3544704 * 2 ^ 59
def prefixEnd_3544704 : Nat := 4983230072969 + 3 ^ 40 * 3544704 * 2
def baseEnd_3544704 : Nat := 1820136929915004562998209

theorem tailTrace_3544704 : CollatzResearch.WordTrace tailWord_3544704 prefixEnd_3544704 1820136929915004562998209 := by
  unfold tailWord_3544704
  simp only [CollatzResearch.WordTrace]
  refine ⟨64642988075075135045484583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86190650766766846727312777 64642988075075135045484583)
  ·
    refine ⟨96964482112612702568226875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64642988075075135045484583 96964482112612702568226875)
    ·
      refine ⟨145446723168919053852340313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96964482112612702568226875 145446723168919053852340313)
      ·
        refine ⟨109085042376689290389255235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145446723168919053852340313 109085042376689290389255235)
        ·
          refine ⟨163627563565033935583882853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109085042376689290389255235 163627563565033935583882853)
          ·
            refine ⟨30680168168443862921978035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 163627563565033935583882853 30680168168443862921978035)
            ·
              refine ⟨46020252252665794382967053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30680168168443862921978035 46020252252665794382967053)
              ·
                refine ⟨17257594594749672893612645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46020252252665794382967053 17257594594749672893612645)
                ·
                  refine ⟨3235798986515563667552371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17257594594749672893612645 3235798986515563667552371)
                  ·
                    refine ⟨4853698479773345501328557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3235798986515563667552371 4853698479773345501328557)
                    ·
                      refine ⟨1820136929915004562998209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4853698479773345501328557 1820136929915004562998209)
                      ·
                        rfl

theorem cell23_3544704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 4, 1, 3].length) (baseStart_3544704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3544704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3544704 prefixEnd_3544704 := by exact prefixLift 3544704
  have htrace : WordTrace (prefixWord ++ tailWord_3544704) baseStart_3544704 baseEnd_3544704 := by
    simpa [prefixWord, tailWord_3544704, baseEnd_3544704] using wordTrace_append hprefix tailTrace_3544704
  have hstable : (prefixWord ++ tailWord_3544704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544704).length < 2 ^ (prefixWord ++ tailWord_3544704).sum := by decide
  have hdescent : baseEnd_3544704 < baseStart_3544704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544738 : List Nat := [3, 3, 1, 4, 1, 1, 1, 2, 1, 3, 3]
def baseStart_3544738 : Nat := 118140960795 + 3544738 * 2 ^ 59
def prefixEnd_3544738 : Nat := 4983230072969 + 3 ^ 40 * 3544738 * 2
def baseEnd_3544738 : Nat := 1820154388257257429973053

theorem tailTrace_3544738 : CollatzResearch.WordTrace tailWord_3544738 prefixEnd_3544738 1820154388257257429973053 := by
  unfold tailWord_3544738
  simp only [CollatzResearch.WordTrace]
  refine ⟨32321804058006773474426717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86191477488018062598471245 32321804058006773474426717)
  ·
    refine ⟨12120676521752540052910019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32321804058006773474426717 12120676521752540052910019)
    ·
      refine ⟨18181014782628810079365029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12120676521752540052910019 18181014782628810079365029)
      ·
        refine ⟨3408940271742901889880943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18181014782628810079365029 3408940271742901889880943)
        ·
          refine ⟨5113410407614352834821415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3408940271742901889880943 5113410407614352834821415)
          ·
            refine ⟨7670115611421529252232123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5113410407614352834821415 7670115611421529252232123)
            ·
              refine ⟨11505173417132293878348185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7670115611421529252232123 11505173417132293878348185)
              ·
                refine ⟨8628880062849220408761139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11505173417132293878348185 8628880062849220408761139)
                ·
                  refine ⟨12943320094273830613141709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8628880062849220408761139 12943320094273830613141709)
                  ·
                    refine ⟨4853745035352686479928141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12943320094273830613141709 4853745035352686479928141)
                    ·
                      refine ⟨1820154388257257429973053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4853745035352686479928141 1820154388257257429973053)
                      ·
                        rfl

theorem cell23_3544738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_3544738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3544738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3544738 prefixEnd_3544738 := by exact prefixLift 3544738
  have htrace : WordTrace (prefixWord ++ tailWord_3544738) baseStart_3544738 baseEnd_3544738 := by
    simpa [prefixWord, tailWord_3544738, baseEnd_3544738] using wordTrace_append hprefix tailTrace_3544738
  have hstable : (prefixWord ++ tailWord_3544738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544738).length < 2 ^ (prefixWord ++ tailWord_3544738).sum := by decide
  have hdescent : baseEnd_3544738 < baseStart_3544738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544761 : List Nat := [1, 2, 1, 4, 1, 1, 2, 3, 4, 2, 2]
def baseStart_3544761 : Nat := 118140960795 + 3544761 * 2 ^ 59
def prefixEnd_3544761 : Nat := 4983230072969 + 3 ^ 40 * 3544761 * 2
def baseEnd_3544761 : Nat := 1820166198312310839985447

theorem tailTrace_3544761 : CollatzResearch.WordTrace tailWord_3544761 prefixEnd_3544761 1820166198312310839985447 := by
  unfold tailWord_3544761
  simp only [CollatzResearch.WordTrace]
  refine ⟨129288055110943768825794137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86192036740629179217196091 129288055110943768825794137)
  ·
    refine ⟨96966041333207826619345603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129288055110943768825794137 96966041333207826619345603)
    ·
      refine ⟨145449061999811739929018405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96966041333207826619345603 145449061999811739929018405)
      ·
        refine ⟨27271699124964701236690951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145449061999811739929018405 27271699124964701236690951)
        ·
          refine ⟨40907548687447051855036427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27271699124964701236690951 40907548687447051855036427)
          ·
            refine ⟨61361323031170577782554641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40907548687447051855036427 61361323031170577782554641)
            ·
              refine ⟨46020992273377933336915981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61361323031170577782554641 46020992273377933336915981)
              ·
                refine ⟨17257872102516725001343493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46020992273377933336915981 17257872102516725001343493)
                ·
                  refine ⟨3235851019221885937751905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17257872102516725001343493 3235851019221885937751905)
                  ·
                    refine ⟨2426888264416414453313929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3235851019221885937751905 2426888264416414453313929)
                    ·
                      refine ⟨1820166198312310839985447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2426888264416414453313929 1820166198312310839985447)
                      ·
                        rfl

theorem cell23_3544761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 4, 2, 2].length) (baseStart_3544761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3544761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3544761 prefixEnd_3544761 := by exact prefixLift 3544761
  have htrace : WordTrace (prefixWord ++ tailWord_3544761) baseStart_3544761 baseEnd_3544761 := by
    simpa [prefixWord, tailWord_3544761, baseEnd_3544761] using wordTrace_append hprefix tailTrace_3544761
  have hstable : (prefixWord ++ tailWord_3544761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544761).length < 2 ^ (prefixWord ++ tailWord_3544761).sum := by decide
  have hdescent : baseEnd_3544761 < baseStart_3544761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544764 : List Nat := [2, 2, 2, 3, 1, 2, 1, 1, 2, 4, 3]
def baseStart_3544764 : Nat := 118140960795 + 3544764 * 2 ^ 59
def prefixEnd_3544764 : Nat := 4983230072969 + 3 ^ 40 * 3544764 * 2
def baseEnd_3544764 : Nat := 1820167738754274328247933

theorem tailTrace_3544764 : CollatzResearch.WordTrace tailWord_3544764 prefixEnd_3544764 1820167738754274328247933 := by
  unfold tailWord_3544764
  simp only [CollatzResearch.WordTrace]
  refine ⟨64644082264966450169076673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86192109686621933558768897 64644082264966450169076673)
  ·
    refine ⟨48483061698724837626807505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64644082264966450169076673 48483061698724837626807505)
    ·
      refine ⟨36362296274043628220105629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48483061698724837626807505 36362296274043628220105629)
      ·
        refine ⟨13635861102766360582539611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36362296274043628220105629 13635861102766360582539611)
        ·
          refine ⟨20453791654149540873809417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13635861102766360582539611 20453791654149540873809417)
          ·
            refine ⟨15340343740612155655357063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20453791654149540873809417 15340343740612155655357063)
            ·
              refine ⟨23010515610918233483035595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15340343740612155655357063 23010515610918233483035595)
              ·
                refine ⟨34515773416377350224553393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23010515610918233483035595 34515773416377350224553393)
                ·
                  refine ⟨25886830062283012668415045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34515773416377350224553393 25886830062283012668415045)
                  ·
                    refine ⟨4853780636678064875327821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25886830062283012668415045 4853780636678064875327821)
                    ·
                      refine ⟨1820167738754274328247933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4853780636678064875327821 1820167738754274328247933)
                      ·
                        rfl

theorem cell23_3544764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_3544764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3544764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3544764 prefixEnd_3544764 := by exact prefixLift 3544764
  have htrace : WordTrace (prefixWord ++ tailWord_3544764) baseStart_3544764 baseEnd_3544764 := by
    simpa [prefixWord, tailWord_3544764, baseEnd_3544764] using wordTrace_append hprefix tailTrace_3544764
  have hstable : (prefixWord ++ tailWord_3544764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544764).length < 2 ^ (prefixWord ++ tailWord_3544764).sum := by decide
  have hdescent : baseEnd_3544764 < baseStart_3544764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544767 : List Nat := [1, 1, 2, 2, 2, 3, 2, 3, 7]
def baseStart_3544767 : Nat := 118140960795 + 3544767 * 2 ^ 59
def prefixEnd_3544767 : Nat := 4983230072969 + 3 ^ 40 * 3544767 * 2
def baseEnd_3544767 : Nat := 202241031021804201834491

theorem tailTrace_3544767 : CollatzResearch.WordTrace tailWord_3544767 prefixEnd_3544767 202241031021804201834491 := by
  unfold tailWord_3544767
  simp only [CollatzResearch.WordTrace]
  refine ⟨129288273948922031850512555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86192182632614687900341703 129288273948922031850512555)
  ·
    refine ⟨193932410923383047775768833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129288273948922031850512555 193932410923383047775768833)
    ·
      refine ⟨145449308192537285831826625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193932410923383047775768833 145449308192537285831826625)
      ·
        refine ⟨109086981144402964373869969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145449308192537285831826625 109086981144402964373869969)
        ·
          refine ⟨81815235858302223280402477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109086981144402964373869969 81815235858302223280402477)
          ·
            refine ⟨30680713446863333730150929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81815235858302223280402477 30680713446863333730150929)
            ·
              refine ⟨23010535085147500297613197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30680713446863333730150929 23010535085147500297613197)
              ·
                refine ⟨8628950656930312611604949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23010535085147500297613197 8628950656930312611604949)
                ·
                  refine ⟨202241031021804201834491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8628950656930312611604949 202241031021804201834491)
                  ·
                    rfl

theorem cell23_3544767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 3, 7].length) (baseStart_3544767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3544767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3544767 prefixEnd_3544767 := by exact prefixLift 3544767
  have htrace : WordTrace (prefixWord ++ tailWord_3544767) baseStart_3544767 baseEnd_3544767 := by
    simpa [prefixWord, tailWord_3544767, baseEnd_3544767] using wordTrace_append hprefix tailTrace_3544767
  have hstable : (prefixWord ++ tailWord_3544767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544767).length < 2 ^ (prefixWord ++ tailWord_3544767).sum := by decide
  have hdescent : baseEnd_3544767 < baseStart_3544767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544778 : List Nat := [3, 1, 2, 1, 5, 1, 2, 1, 1, 4, 2]
def baseStart_3544778 : Nat := 118140960795 + 3544778 * 2 ^ 59
def prefixEnd_3544778 : Nat := 4983230072969 + 3 ^ 40 * 3544778 * 2
def baseEnd_3544778 : Nat := 1820174927483437273472869

theorem tailTrace_3544778 : CollatzResearch.WordTrace tailWord_3544778 prefixEnd_3544778 1820174927483437273472869 := by
  unfold tailWord_3544778
  simp only [CollatzResearch.WordTrace]
  refine ⟨32322168787970545182290747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86192450101254787152775325 32322168787970545182290747)
  ·
    refine ⟨48483253181955817773436121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32322168787970545182290747 48483253181955817773436121)
    ·
      refine ⟨36362439886466863330077091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48483253181955817773436121 36362439886466863330077091)
      ·
        refine ⟨54543659829700294995115637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36362439886466863330077091 54543659829700294995115637)
        ·
          refine ⟨5113468109034402655792091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54543659829700294995115637 5113468109034402655792091)
          ·
            refine ⟨7670202163551603983688137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5113468109034402655792091 7670202163551603983688137)
            ·
              refine ⟨5752651622663702987766103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7670202163551603983688137 5752651622663702987766103)
              ·
                refine ⟨8628977433995554481649155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5752651622663702987766103 8628977433995554481649155)
                ·
                  refine ⟨12943466150993331722473733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8628977433995554481649155 12943466150993331722473733)
                  ·
                    refine ⟨2426899903311249697963825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12943466150993331722473733 2426899903311249697963825)
                    ·
                      refine ⟨1820174927483437273472869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2426899903311249697963825 1820174927483437273472869)
                      ·
                        rfl

theorem cell23_3544778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 1, 1, 4, 2].length) (baseStart_3544778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3544778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3544778 prefixEnd_3544778 := by exact prefixLift 3544778
  have htrace : WordTrace (prefixWord ++ tailWord_3544778) baseStart_3544778 baseEnd_3544778 := by
    simpa [prefixWord, tailWord_3544778, baseEnd_3544778] using wordTrace_append hprefix tailTrace_3544778
  have hstable : (prefixWord ++ tailWord_3544778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544778).length < 2 ^ (prefixWord ++ tailWord_3544778).sum := by decide
  have hdescent : baseEnd_3544778 < baseStart_3544778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544814 : List Nat := [4, 1, 2, 1, 1, 2, 2, 1, 4, 5]
def baseStart_3544814 : Nat := 118140960795 + 3544814 * 2 ^ 59
def prefixEnd_3544814 : Nat := 4983230072969 + 3 ^ 40 * 3544814 * 2
def baseEnd_3544814 : Nat := 606731137595666377540901

theorem tailTrace_3544814 : CollatzResearch.WordTrace tailWord_3544814 prefixEnd_3544814 606731137595666377540901 := by
  unfold tailWord_3544814
  simp only [CollatzResearch.WordTrace]
  refine ⟨16161248522468969859684187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86193325453167839251648997 16161248522468969859684187)
  ·
    refine ⟨24241872783703454789526281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16161248522468969859684187 24241872783703454789526281)
    ·
      refine ⟨18181404587777591092144711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24241872783703454789526281 18181404587777591092144711)
      ·
        refine ⟨27272106881666386638217067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18181404587777591092144711 27272106881666386638217067)
        ·
          refine ⟨40908160322499579957325601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27272106881666386638217067 40908160322499579957325601)
          ·
            refine ⟨30681120241874684967994201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40908160322499579957325601 30681120241874684967994201)
            ·
              refine ⟨23010840181406013725995651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30681120241874684967994201 23010840181406013725995651)
              ·
                refine ⟨34516260272109020588993477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23010840181406013725995651 34516260272109020588993477)
                ·
                  refine ⟨6471798801020441360436277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34516260272109020588993477 6471798801020441360436277)
                  ·
                    refine ⟨606731137595666377540901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6471798801020441360436277 606731137595666377540901)
                    ·
                      rfl

theorem cell23_3544814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_3544814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3544814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3544814 prefixEnd_3544814 := by exact prefixLift 3544814
  have htrace : WordTrace (prefixWord ++ tailWord_3544814) baseStart_3544814 baseEnd_3544814 := by
    simpa [prefixWord, tailWord_3544814, baseEnd_3544814] using wordTrace_append hprefix tailTrace_3544814
  have hstable : (prefixWord ++ tailWord_3544814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544814).length < 2 ^ (prefixWord ++ tailWord_3544814).sum := by decide
  have hdescent : baseEnd_3544814 < baseStart_3544814 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544847 : List Nat := [1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 6]
def baseStart_3544847 : Nat := 118140960795 + 3544847 * 2 ^ 59
def prefixEnd_3544847 : Nat := 4983230072969 + 3 ^ 40 * 3544847 * 2
def baseEnd_3544847 : Nat := 1820210357648597503510051

theorem tailTrace_3544847 : CollatzResearch.WordTrace tailWord_3544847 prefixEnd_3544847 1820210357648597503510051 := by
  unfold tailWord_3544847
  simp only [CollatzResearch.WordTrace]
  refine ⟨129291191788632205513424795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86194127859088137008949863 129291191788632205513424795)
  ·
    refine ⟨193936787682948308270137193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129291191788632205513424795 193936787682948308270137193)
    ·
      refine ⟨145452590762211231202602895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193936787682948308270137193 145452590762211231202602895)
      ·
        refine ⟨218178886143316846803904343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145452590762211231202602895 218178886143316846803904343)
        ·
          refine ⟨327268329214975270205856515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218178886143316846803904343 327268329214975270205856515)
          ·
            refine ⟨490902493822462905308784773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327268329214975270205856515 490902493822462905308784773)
            ·
              refine ⟨92044217591711794745397145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 490902493822462905308784773 92044217591711794745397145)
              ·
                refine ⟨69033163193783846059047859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92044217591711794745397145 69033163193783846059047859)
                ·
                  refine ⟨103549744790675769088571789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69033163193783846059047859 103549744790675769088571789)
                  ·
                    refine ⟨38831154296503413408214421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 103549744790675769088571789 38831154296503413408214421)
                    ·
                      refine ⟨1820210357648597503510051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38831154296503413408214421 1820210357648597503510051)
                      ·
                        rfl

theorem cell23_3544847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 6].length) (baseStart_3544847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3544847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3544847 prefixEnd_3544847 := by exact prefixLift 3544847
  have htrace : WordTrace (prefixWord ++ tailWord_3544847) baseStart_3544847 baseEnd_3544847 := by
    simpa [prefixWord, tailWord_3544847, baseEnd_3544847] using wordTrace_append hprefix tailTrace_3544847
  have hstable : (prefixWord ++ tailWord_3544847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544847).length < 2 ^ (prefixWord ++ tailWord_3544847).sum := by decide
  have hdescent : baseEnd_3544847 < baseStart_3544847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544901 : List Nat := [1, 3, 1, 1, 1, 2, 4, 1, 5, 1, 3]
def baseStart_3544901 : Nat := 118140960795 + 3544901 * 2 ^ 59
def prefixEnd_3544901 : Nat := 4983230072969 + 3 ^ 40 * 3544901 * 2
def baseEnd_3544901 : Nat := 1820238085603940292234803

theorem tailTrace_3544901 : CollatzResearch.WordTrace tailWord_3544901 prefixEnd_3544901 1820238085603940292234803 := by
  unfold tailWord_3544901
  simp only [CollatzResearch.WordTrace]
  refine ⟨129293161330436572735890557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86195440886957715157260371 129293161330436572735890557)
  ·
    refine ⟨48484935498913714775958959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129293161330436572735890557 48484935498913714775958959)
    ·
      refine ⟨72727403248370572163938439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48484935498913714775958959 72727403248370572163938439)
      ·
        refine ⟨109091104872555858245907659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72727403248370572163938439 109091104872555858245907659)
        ·
          refine ⟨163636657308833787368861489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109091104872555858245907659 163636657308833787368861489)
          ·
            refine ⟨122727492981625340526646117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163636657308833787368861489 122727492981625340526646117)
            ·
              refine ⟨23011404934054751348746147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122727492981625340526646117 23011404934054751348746147)
              ·
                refine ⟨34517107401082127023119221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23011404934054751348746147 34517107401082127023119221)
                ·
                  refine ⟨3235978818851449408417427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34517107401082127023119221 3235978818851449408417427)
                  ·
                    refine ⟨4853968228277174112626141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3235978818851449408417427 4853968228277174112626141)
                    ·
                      refine ⟨1820238085603940292234803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4853968228277174112626141 1820238085603940292234803)
                      ·
                        rfl

theorem cell23_3544901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 5, 1, 3].length) (baseStart_3544901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3544901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3544901 prefixEnd_3544901 := by exact prefixLift 3544901
  have htrace : WordTrace (prefixWord ++ tailWord_3544901) baseStart_3544901 baseEnd_3544901 := by
    simpa [prefixWord, tailWord_3544901, baseEnd_3544901] using wordTrace_append hprefix tailTrace_3544901
  have hstable : (prefixWord ++ tailWord_3544901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544901).length < 2 ^ (prefixWord ++ tailWord_3544901).sum := by decide
  have hdescent : baseEnd_3544901 < baseStart_3544901 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544928 : List Nat := [2, 1, 1, 3, 3, 2, 2, 2, 2, 3, 2]
def baseStart_3544928 : Nat := 118140960795 + 3544928 * 2 ^ 59
def prefixEnd_3544928 : Nat := 4983230072969 + 3 ^ 40 * 3544928 * 2
def baseEnd_3544928 : Nat := 1820251949581611686597179

theorem tailTrace_3544928 : CollatzResearch.WordTrace tailWord_3544928 prefixEnd_3544928 1820251949581611686597179 := by
  unfold tailWord_3544928
  simp only [CollatzResearch.WordTrace]
  refine ⟨64647073050669378173561719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86196097400892504231415625 64647073050669378173561719)
  ·
    refine ⟨96970609576004067260342579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64647073050669378173561719 96970609576004067260342579)
    ·
      refine ⟨145455914364006100890513869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96970609576004067260342579 145455914364006100890513869)
      ·
        refine ⟨54545967886502287833942701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145455914364006100890513869 54545967886502287833942701)
        ·
          refine ⟨20454737957438357937728513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54545967886502287833942701 20454737957438357937728513)
          ·
            refine ⟨15341053468078768453296385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20454737957438357937728513 15341053468078768453296385)
            ·
              refine ⟨11505790101059076339972289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15341053468078768453296385 11505790101059076339972289)
              ·
                refine ⟨8629342575794307254979217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11505790101059076339972289 8629342575794307254979217)
                ·
                  refine ⟨6472006931845730441234413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8629342575794307254979217 6472006931845730441234413)
                  ·
                    refine ⟨2427002599442148915462905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6472006931845730441234413 2427002599442148915462905)
                    ·
                      refine ⟨1820251949581611686597179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2427002599442148915462905 1820251949581611686597179)
                      ·
                        rfl

theorem cell23_3544928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 2, 2, 3, 2].length) (baseStart_3544928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3544928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3544928 prefixEnd_3544928 := by exact prefixLift 3544928
  have htrace : WordTrace (prefixWord ++ tailWord_3544928) baseStart_3544928 baseEnd_3544928 := by
    simpa [prefixWord, tailWord_3544928, baseEnd_3544928] using wordTrace_append hprefix tailTrace_3544928
  have hstable : (prefixWord ++ tailWord_3544928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544928).length < 2 ^ (prefixWord ++ tailWord_3544928).sum := by decide
  have hdescent : baseEnd_3544928 < baseStart_3544928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544935 : List Nat := [1, 1, 5, 1, 2, 1, 3, 4, 1, 1, 3]
def baseStart_3544935 : Nat := 118140960795 + 3544935 * 2 ^ 59
def prefixEnd_3544935 : Nat := 4983230072969 + 3 ^ 40 * 3544935 * 2
def baseEnd_3544935 : Nat := 1820255543946193159209647

theorem tailTrace_3544935 : CollatzResearch.WordTrace tailWord_3544935 prefixEnd_3544935 1820255543946193159209647 := by
  unfold tailWord_3544935
  simp only [CollatzResearch.WordTrace]
  refine ⟨129294401412313396542628259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86196267608208931028418839 129294401412313396542628259)
  ·
    refine ⟨193941602118470094813942389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129294401412313396542628259 193941602118470094813942389)
    ·
      refine ⟨18182025198606571388807099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 193941602118470094813942389 18182025198606571388807099)
      ·
        refine ⟨27273037797909857083210649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18182025198606571388807099 27273037797909857083210649)
        ·
          refine ⟨20454778348432392812407987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27273037797909857083210649 20454778348432392812407987)
          ·
            refine ⟨30682167522648589218611981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20454778348432392812407987 30682167522648589218611981)
            ·
              refine ⟨11505812820993220956979493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30682167522648589218611981 11505812820993220956979493)
              ·
                refine ⟨2157339903936228929433655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11505812820993220956979493 2157339903936228929433655)
                ·
                  refine ⟨3236009855904343394150483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2157339903936228929433655 3236009855904343394150483)
                  ·
                    refine ⟨4854014783856515091225725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3236009855904343394150483 4854014783856515091225725)
                    ·
                      refine ⟨1820255543946193159209647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4854014783856515091225725 1820255543946193159209647)
                      ·
                        rfl

theorem cell23_3544935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 4, 1, 1, 3].length) (baseStart_3544935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3544935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3544935 prefixEnd_3544935 := by exact prefixLift 3544935
  have htrace : WordTrace (prefixWord ++ tailWord_3544935) baseStart_3544935 baseEnd_3544935 := by
    simpa [prefixWord, tailWord_3544935, baseEnd_3544935] using wordTrace_append hprefix tailTrace_3544935
  have hstable : (prefixWord ++ tailWord_3544935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544935).length < 2 ^ (prefixWord ++ tailWord_3544935).sum := by decide
  have hdescent : baseEnd_3544935 < baseStart_3544935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544941 : List Nat := [1, 5, 1, 1, 1, 1, 3, 2, 3, 1, 4]
def baseStart_3544941 : Nat := 118140960795 + 3544941 * 2 ^ 59
def prefixEnd_3544941 : Nat := 4983230072969 + 3 ^ 40 * 3544941 * 2
def baseEnd_3544941 : Nat := 1820258624830120135734619

theorem tailTrace_3544941 : CollatzResearch.WordTrace tailWord_3544941 prefixEnd_3544941 1820258624830120135734619 := by
  unfold tailWord_3544941
  simp only [CollatzResearch.WordTrace]
  refine ⟨129294620250291659567346677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86196413500194439711564451 129294620250291659567346677)
  ·
    refine ⟨12121370648464843084438751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 129294620250291659567346677 12121370648464843084438751)
    ·
      refine ⟨18182055972697264626658127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12121370648464843084438751 18182055972697264626658127)
      ·
        refine ⟨27273083959045896939987191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18182055972697264626658127 27273083959045896939987191)
        ·
          refine ⟨40909625938568845409980787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27273083959045896939987191 40909625938568845409980787)
          ·
            refine ⟨61364438907853268114971181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40909625938568845409980787 61364438907853268114971181)
            ·
              refine ⟨23011664590444975543114193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61364438907853268114971181 23011664590444975543114193)
              ·
                refine ⟨17258748442833731657335645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23011664590444975543114193 17258748442833731657335645)
                ·
                  refine ⟨6472030666062649371500867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17258748442833731657335645 6472030666062649371500867)
                  ·
                    refine ⟨9708045999093974057251301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6472030666062649371500867 9708045999093974057251301)
                    ·
                      refine ⟨1820258624830120135734619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9708045999093974057251301 1820258624830120135734619)
                      ·
                        rfl

theorem cell23_3544941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_3544941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3544941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3544941 prefixEnd_3544941 := by exact prefixLift 3544941
  have htrace : WordTrace (prefixWord ++ tailWord_3544941) baseStart_3544941 baseEnd_3544941 := by
    simpa [prefixWord, tailWord_3544941, baseEnd_3544941] using wordTrace_append hprefix tailTrace_3544941
  have hstable : (prefixWord ++ tailWord_3544941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544941).length < 2 ^ (prefixWord ++ tailWord_3544941).sum := by decide
  have hdescent : baseEnd_3544941 < baseStart_3544941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544944 : List Nat := [2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 5]
def baseStart_3544944 : Nat := 118140960795 + 3544944 * 2 ^ 59
def prefixEnd_3544944 : Nat := 4983230072969 + 3 ^ 40 * 3544944 * 2
def baseEnd_3544944 : Nat := 1820260165272083623997105

theorem tailTrace_3544944 : CollatzResearch.WordTrace tailWord_3544944 prefixEnd_3544944 1820260165272083623997105 := by
  unfold tailWord_3544944
  simp only [CollatzResearch.WordTrace]
  refine ⟨64647364834640395539852943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86196486446187194053137257 64647364834640395539852943)
  ·
    refine ⟨96971047251960593309779415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64647364834640395539852943 96971047251960593309779415)
    ·
      refine ⟨145456570877940889964669123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96971047251960593309779415 145456570877940889964669123)
      ·
        refine ⟨218184856316911334947003685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145456570877940889964669123 218184856316911334947003685)
        ·
          refine ⟨40909660559420875302563191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 218184856316911334947003685 40909660559420875302563191)
          ·
            refine ⟨61364490839131312953844787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40909660559420875302563191 61364490839131312953844787)
            ·
              refine ⟨92046736258696969430767181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61364490839131312953844787 92046736258696969430767181)
              ·
                refine ⟨34517526097011363536537693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92046736258696969430767181 34517526097011363536537693)
                ·
                  refine ⟨12944072286379261326201635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34517526097011363536537693 12944072286379261326201635)
                  ·
                    refine ⟨19416108429568891989302453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12944072286379261326201635 19416108429568891989302453)
                    ·
                      refine ⟨1820260165272083623997105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19416108429568891989302453 1820260165272083623997105)
                      ·
                        rfl

theorem cell23_3544944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 5].length) (baseStart_3544944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3544944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3544944 prefixEnd_3544944 := by exact prefixLift 3544944
  have htrace : WordTrace (prefixWord ++ tailWord_3544944) baseStart_3544944 baseEnd_3544944 := by
    simpa [prefixWord, tailWord_3544944, baseEnd_3544944] using wordTrace_append hprefix tailTrace_3544944
  have hstable : (prefixWord ++ tailWord_3544944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544944).length < 2 ^ (prefixWord ++ tailWord_3544944).sum := by decide
  have hdescent : baseEnd_3544944 < baseStart_3544944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544954 : List Nat := [3, 1, 1, 1, 1, 1, 4, 3, 1, 1, 6]
def baseStart_3544954 : Nat := 118140960795 + 3544954 * 2 ^ 59
def prefixEnd_3544954 : Nat := 4983230072969 + 3 ^ 40 * 3544954 * 2
def baseEnd_3544954 : Nat := 1820265300078628584872059

theorem tailTrace_3544954 : CollatzResearch.WordTrace tailWord_3544954 prefixEnd_3544954 1820265300078628584872059 := by
  unfold tailWord_3544954
  simp only [CollatzResearch.WordTrace]
  refine ⟨32323773599811140696892479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86196729599496375191713277 32323773599811140696892479)
  ·
    refine ⟨48485660399716711045338719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32323773599811140696892479 48485660399716711045338719)
    ·
      refine ⟨72728490599575066568008079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48485660399716711045338719 72728490599575066568008079)
      ·
        refine ⟨109092735899362599852012119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72728490599575066568008079 109092735899362599852012119)
        ·
          refine ⟨163639103849043899778018179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109092735899362599852012119 163639103849043899778018179)
          ·
            refine ⟨245458655773565849667027269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163639103849043899778018179 245458655773565849667027269)
            ·
              refine ⟨46023497957543596812567613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 245458655773565849667027269 46023497957543596812567613)
              ·
                refine ⟨17258811734078848804712855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46023497957543596812567613 17258811734078848804712855)
                ·
                  refine ⟨25888217601118273207069283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17258811734078848804712855 25888217601118273207069283)
                  ·
                    refine ⟨38832326401677409810603925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25888217601118273207069283 38832326401677409810603925)
                    ·
                      refine ⟨1820265300078628584872059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38832326401677409810603925 1820265300078628584872059)
                      ·
                        rfl

theorem cell23_3544954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 1, 1, 6].length) (baseStart_3544954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3544954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3544954 prefixEnd_3544954 := by exact prefixLift 3544954
  have htrace : WordTrace (prefixWord ++ tailWord_3544954) baseStart_3544954 baseEnd_3544954 := by
    simpa [prefixWord, tailWord_3544954, baseEnd_3544954] using wordTrace_append hprefix tailTrace_3544954
  have hstable : (prefixWord ++ tailWord_3544954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544954).length < 2 ^ (prefixWord ++ tailWord_3544954).sum := by decide
  have hdescent : baseEnd_3544954 < baseStart_3544954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544964 : List Nat := [2, 3, 2, 1, 1, 1, 2, 11]
def baseStart_3544964 : Nat := 118140960795 + 3544964 * 2 ^ 59
def prefixEnd_3544964 : Nat := 4983230072969 + 3 ^ 40 * 3544964 * 2
def baseEnd_3544964 : Nat := 67417423514265686879519

theorem tailTrace_3544964 : CollatzResearch.WordTrace tailWord_3544964 prefixEnd_3544964 67417423514265686879519 := by
  unfold tailWord_3544964
  simp only [CollatzResearch.WordTrace]
  refine ⟨64647729564604167247716973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86196972752805556330289297 64647729564604167247716973)
  ·
    refine ⟨24242898586726562717893865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64647729564604167247716973 24242898586726562717893865)
    ·
      refine ⟨18182173940044922038420399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24242898586726562717893865 18182173940044922038420399)
      ·
        refine ⟨27273260910067383057630599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18182173940044922038420399 27273260910067383057630599)
        ·
          refine ⟨40909891365101074586445899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27273260910067383057630599 40909891365101074586445899)
          ·
            refine ⟨61364837047651611879668849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40909891365101074586445899 61364837047651611879668849)
            ·
              refine ⟨46023627785738708909751637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61364837047651611879668849 46023627785738708909751637)
              ·
                refine ⟨67417423514265686879519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 46023627785738708909751637 67417423514265686879519)
                ·
                  rfl

theorem cell23_3544964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 11].length) (baseStart_3544964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3544964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3544964 prefixEnd_3544964 := by exact prefixLift 3544964
  have htrace : WordTrace (prefixWord ++ tailWord_3544964) baseStart_3544964 baseEnd_3544964 := by
    simpa [prefixWord, tailWord_3544964, baseEnd_3544964] using wordTrace_append hprefix tailTrace_3544964
  have hstable : (prefixWord ++ tailWord_3544964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544964).length < 2 ^ (prefixWord ++ tailWord_3544964).sum := by decide
  have hdescent : baseEnd_3544964 < baseStart_3544964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545001 : List Nat := [1, 2, 1, 1, 1, 1, 4, 1, 2, 7, 2]
def baseStart_3545001 : Nat := 118140960795 + 3545001 * 2 ^ 59
def prefixEnd_3545001 : Nat := 4983230072969 + 3 ^ 40 * 3545001 * 2
def baseEnd_3545001 : Nat := 1820289433669389900984343

theorem tailTrace_3545001 : CollatzResearch.WordTrace tailWord_3545001 prefixEnd_3545001 1820289433669389900984343 := by
  unfold tailWord_3545001
  simp only [CollatzResearch.WordTrace]
  refine ⟨129296808630074289814530857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86197872420049526543020571 129296808630074289814530857)
  ·
    refine ⟨96972606472555717360898143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129296808630074289814530857 96972606472555717360898143)
    ·
      refine ⟨145458909708833576041347215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96972606472555717360898143 145458909708833576041347215)
      ·
        refine ⟨218188364563250364062020823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145458909708833576041347215 218188364563250364062020823)
        ·
          refine ⟨327282546844875546093031235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218188364563250364062020823 327282546844875546093031235)
          ·
            refine ⟨490923820267313319139546853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327282546844875546093031235 490923820267313319139546853)
            ·
              refine ⟨92048216300121247338665035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 490923820267313319139546853 92048216300121247338665035)
              ·
                refine ⟨138072324450181871007997553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92048216300121247338665035 138072324450181871007997553)
                ·
                  refine ⟨103554243337636403255998165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 138072324450181871007997553 103554243337636403255998165)
                  ·
                    refine ⟨2427052578225853201312457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 103554243337636403255998165 2427052578225853201312457)
                    ·
                      refine ⟨1820289433669389900984343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2427052578225853201312457 1820289433669389900984343)
                      ·
                        rfl

theorem cell23_3545001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 7, 2].length) (baseStart_3545001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3545001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3545001 prefixEnd_3545001 := by exact prefixLift 3545001
  have htrace : WordTrace (prefixWord ++ tailWord_3545001) baseStart_3545001 baseEnd_3545001 := by
    simpa [prefixWord, tailWord_3545001, baseEnd_3545001] using wordTrace_append hprefix tailTrace_3545001
  have hstable : (prefixWord ++ tailWord_3545001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545001).length < 2 ^ (prefixWord ++ tailWord_3545001).sum := by decide
  have hdescent : baseEnd_3545001 < baseStart_3545001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545004 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 5]
def baseStart_3545004 : Nat := 118140960795 + 3545004 * 2 ^ 59
def prefixEnd_3545004 : Nat := 4983230072969 + 3 ^ 40 * 3545004 * 2
def baseEnd_3545004 : Nat := 1820290974111353389246829

theorem tailTrace_3545004 : CollatzResearch.WordTrace tailWord_3545004 prefixEnd_3545004 1820290974111353389246829 := by
  unfold tailWord_3545004
  simp only [CollatzResearch.WordTrace]
  refine ⟨64648459024531710663445033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86197945366042280884593377 64648459024531710663445033)
  ·
    refine ⟨48486344268398782997583775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64648459024531710663445033 48486344268398782997583775)
    ·
      refine ⟨72729516402598174496375663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48486344268398782997583775 72729516402598174496375663)
      ·
        refine ⟨109094274603897261744563495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72729516402598174496375663 109094274603897261744563495)
        ·
          refine ⟨163641411905845892616845243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109094274603897261744563495 163641411905845892616845243)
          ·
            refine ⟨245462117858768838925267865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163641411905845892616845243 245462117858768838925267865)
            ·
              refine ⟨184096588394076629193950899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 245462117858768838925267865 184096588394076629193950899)
              ·
                refine ⟨276144882591114943790926349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184096588394076629193950899 276144882591114943790926349)
                ·
                  refine ⟨103554330971668103921597381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 276144882591114943790926349 103554330971668103921597381)
                  ·
                    refine ⟨19416437057187769485299509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 103554330971668103921597381 19416437057187769485299509)
                    ·
                      refine ⟨1820290974111353389246829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19416437057187769485299509 1820290974111353389246829)
                      ·
                        rfl

theorem cell23_3545004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 5].length) (baseStart_3545004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3545004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3545004 prefixEnd_3545004 := by exact prefixLift 3545004
  have htrace : WordTrace (prefixWord ++ tailWord_3545004) baseStart_3545004 baseEnd_3545004 := by
    simpa [prefixWord, tailWord_3545004, baseEnd_3545004] using wordTrace_append hprefix tailTrace_3545004
  have hstable : (prefixWord ++ tailWord_3545004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545004).length < 2 ^ (prefixWord ++ tailWord_3545004).sum := by decide
  have hdescent : baseEnd_3545004 < baseStart_3545004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545021 : List Nat := [1, 4, 1, 2, 3, 1, 1, 1, 2, 2, 5]
def baseStart_3545021 : Nat := 118140960795 + 3545021 * 2 ^ 59
def prefixEnd_3545021 : Nat := 4983230072969 + 3 ^ 40 * 3545021 * 2
def baseEnd_3545021 : Nat := 1820299703282479822734251

theorem tailTrace_3545021 : CollatzResearch.WordTrace tailWord_3545021 prefixEnd_3545021 1820299703282479822734251 := by
  unfold tailWord_3545021
  simp only [CollatzResearch.WordTrace]
  refine ⟨129297538090001833230258917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86198358726667888820172611 129297538090001833230258917)
  ·
    refine ⟨24243288391875343730673547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129297538090001833230258917 24243288391875343730673547)
    ·
      refine ⟨36364932587813015596010321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24243288391875343730673547 36364932587813015596010321)
      ·
        refine ⟨27273699440859761697007741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36364932587813015596010321 27273699440859761697007741)
        ·
          refine ⟨10227637290322410636377903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27273699440859761697007741 10227637290322410636377903)
          ·
            refine ⟨15341455935483615954566855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10227637290322410636377903 15341455935483615954566855)
            ·
              refine ⟨23012183903225423931850283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15341455935483615954566855 23012183903225423931850283)
              ·
                refine ⟨34518275854838135897775425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23012183903225423931850283 34518275854838135897775425)
                ·
                  refine ⟨25888706891128601923331569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34518275854838135897775425 25888706891128601923331569)
                  ·
                    refine ⟨19416530168346451442498677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25888706891128601923331569 19416530168346451442498677)
                    ·
                      refine ⟨1820299703282479822734251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19416530168346451442498677 1820299703282479822734251)
                      ·
                        rfl

theorem cell23_3545021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_3545021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3545021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3545021 prefixEnd_3545021 := by exact prefixLift 3545021
  have htrace : WordTrace (prefixWord ++ tailWord_3545021) baseStart_3545021 baseEnd_3545021 := by
    simpa [prefixWord, tailWord_3545021, baseEnd_3545021] using wordTrace_append hprefix tailTrace_3545021
  have hstable : (prefixWord ++ tailWord_3545021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545021).length < 2 ^ (prefixWord ++ tailWord_3545021).sum := by decide
  have hdescent : baseEnd_3545021 < baseStart_3545021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545094 : List Nat := [6, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2]
def baseStart_3545094 : Nat := 118140960795 + 3545094 * 2 ^ 59
def prefixEnd_3545094 : Nat := 4983230072969 + 3 ^ 40 * 3545094 * 2
def baseEnd_3545094 : Nat := 1820337187370258037121417

theorem tailTrace_3545094 : CollatzResearch.WordTrace tailWord_3545094 prefixEnd_3545094 1820337187370258037121417 := by
  unfold tailWord_3545094
  simp only [CollatzResearch.WordTrace]
  refine ⟨4040631269335542709302073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 86200133745824911131777557 4040631269335542709302073)
  ·
    refine ⟨3030473452001657031976555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4040631269335542709302073 3030473452001657031976555)
    ·
      refine ⟨4545710178002485547964833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3030473452001657031976555 4545710178002485547964833)
      ·
        refine ⟨3409282633501864160973625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4545710178002485547964833 3409282633501864160973625)
        ·
          refine ⟨2556961975126398120730219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3409282633501864160973625 2556961975126398120730219)
          ·
            refine ⟨3835442962689597181095329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2556961975126398120730219 3835442962689597181095329)
            ·
              refine ⟨2876582222017197885821497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3835442962689597181095329 2876582222017197885821497)
              ·
                refine ⟨2157436666512898414366123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2876582222017197885821497 2157436666512898414366123)
                ·
                  refine ⟨3236154999769347621549185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2157436666512898414366123 3236154999769347621549185)
                  ·
                    refine ⟨2427116249827010716161889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3236154999769347621549185 2427116249827010716161889)
                    ·
                      refine ⟨1820337187370258037121417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2427116249827010716161889 1820337187370258037121417)
                      ·
                        rfl

theorem cell23_3545094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_3545094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3545094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3545094 prefixEnd_3545094 := by exact prefixLift 3545094
  have htrace : WordTrace (prefixWord ++ tailWord_3545094) baseStart_3545094 baseEnd_3545094 := by
    simpa [prefixWord, tailWord_3545094, baseEnd_3545094] using wordTrace_append hprefix tailTrace_3545094
  have hstable : (prefixWord ++ tailWord_3545094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545094).length < 2 ^ (prefixWord ++ tailWord_3545094).sum := by decide
  have hdescent : baseEnd_3545094 < baseStart_3545094 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545138 : List Nat := [3, 2, 1, 1, 2, 4, 1, 1, 1, 3, 4]
def baseStart_3545138 : Nat := 118140960795 + 3545138 * 2 ^ 59
def prefixEnd_3545138 : Nat := 4983230072969 + 3 ^ 40 * 3545138 * 2
def baseEnd_3545138 : Nat := 1820359780519055864971213

theorem tailTrace_3545138 : CollatzResearch.WordTrace tailWord_3545138 prefixEnd_3545138 1820359780519055864971213 := by
  unfold tailWord_3545138
  simp only [CollatzResearch.WordTrace]
  refine ⟨32325451357644490553067017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86201203620385308141512045 32325451357644490553067017)
  ·
    refine ⟨24244088518233367914800263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32325451357644490553067017 24244088518233367914800263)
    ·
      refine ⟨36366132777350051872200395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24244088518233367914800263 36366132777350051872200395)
      ·
        refine ⟨54549199166025077808300593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36366132777350051872200395 54549199166025077808300593)
        ·
          refine ⟨40911899374518808356225445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54549199166025077808300593 40911899374518808356225445)
          ·
            refine ⟨7670981132722276566792271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40911899374518808356225445 7670981132722276566792271)
            ·
              refine ⟨11506471699083414850188407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7670981132722276566792271 11506471699083414850188407)
              ·
                refine ⟨17259707548625122275282611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11506471699083414850188407 17259707548625122275282611)
                ·
                  refine ⟨25889561322937683412923917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17259707548625122275282611 25889561322937683412923917)
                  ·
                    refine ⟨9708585496101631279846469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25889561322937683412923917 9708585496101631279846469)
                    ·
                      refine ⟨1820359780519055864971213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9708585496101631279846469 1820359780519055864971213)
                      ·
                        rfl

theorem cell23_3545138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 1, 3, 4].length) (baseStart_3545138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3545138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3545138 prefixEnd_3545138 := by exact prefixLift 3545138
  have htrace : WordTrace (prefixWord ++ tailWord_3545138) baseStart_3545138 baseEnd_3545138 := by
    simpa [prefixWord, tailWord_3545138, baseEnd_3545138] using wordTrace_append hprefix tailTrace_3545138
  have hstable : (prefixWord ++ tailWord_3545138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545138).length < 2 ^ (prefixWord ++ tailWord_3545138).sum := by decide
  have hdescent : baseEnd_3545138 < baseStart_3545138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545148 : List Nat := [2, 2, 2, 2, 2, 1, 1, 2, 5, 4]
def baseStart_3545148 : Nat := 118140960795 + 3545148 * 2 ^ 59
def prefixEnd_3545148 : Nat := 4983230072969 + 3 ^ 40 * 3545148 * 2
def baseEnd_3545148 : Nat := 606788305108533608615389

theorem tailTrace_3545148 : CollatzResearch.WordTrace tailWord_3545148 prefixEnd_3545148 606788305108533608615389 := by
  unfold tailWord_3545148
  simp only [CollatzResearch.WordTrace]
  refine ⟨64651085080270866960066049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86201446773694489280088065 64651085080270866960066049)
  ·
    refine ⟨48488313810203150220049537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64651085080270866960066049 48488313810203150220049537)
    ·
      refine ⟨36366235357652362665037153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48488313810203150220049537 36366235357652362665037153)
      ·
        refine ⟨27274676518239271998777865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36366235357652362665037153 27274676518239271998777865)
        ·
          refine ⟨20456007388679453999083399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27274676518239271998777865 20456007388679453999083399)
          ·
            refine ⟨30684011083019180998625099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20456007388679453999083399 30684011083019180998625099)
            ·
              refine ⟨46026016624528771497937649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30684011083019180998625099 46026016624528771497937649)
              ·
                refine ⟨34519512468396578623453237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46026016624528771497937649 34519512468396578623453237)
                ·
                  refine ⟨3236204293912179245948741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34519512468396578623453237 3236204293912179245948741)
                  ·
                    refine ⟨606788305108533608615389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3236204293912179245948741 606788305108533608615389)
                    ·
                      rfl

theorem cell23_3545148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 5, 4].length) (baseStart_3545148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3545148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3545148 prefixEnd_3545148 := by exact prefixLift 3545148
  have htrace : WordTrace (prefixWord ++ tailWord_3545148) baseStart_3545148 baseEnd_3545148 := by
    simpa [prefixWord, tailWord_3545148, baseEnd_3545148] using wordTrace_append hprefix tailTrace_3545148
  have hstable : (prefixWord ++ tailWord_3545148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545148).length < 2 ^ (prefixWord ++ tailWord_3545148).sum := by decide
  have hdescent : baseEnd_3545148 < baseStart_3545148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545151 : List Nat := [1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 6]
def baseStart_3545151 : Nat := 118140960795 + 3545151 * 2 ^ 59
def prefixEnd_3545151 : Nat := 4983230072969 + 3 ^ 40 * 3545151 * 2
def baseEnd_3545151 : Nat := 1820366455767564314108653

theorem tailTrace_3545151 : CollatzResearch.WordTrace tailWord_3545151 prefixEnd_3545151 1820366455767564314108653 := by
  unfold tailWord_3545151
  simp only [CollatzResearch.WordTrace]
  refine ⟨129302279579530865432491307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86201519719687243621660871 129302279579530865432491307)
  ·
    refine ⟨193953419369296298148736961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129302279579530865432491307 193953419369296298148736961)
    ·
      refine ⟨145465064526972223611552721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193953419369296298148736961 145465064526972223611552721)
      ·
        refine ⟨109098798395229167708664541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145465064526972223611552721 109098798395229167708664541)
        ·
          refine ⟨40912049398210937890749203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109098798395229167708664541 40912049398210937890749203)
          ·
            refine ⟨61368074097316406836123805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40912049398210937890749203 61368074097316406836123805)
            ·
              refine ⟨23013027786493652563546427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61368074097316406836123805 23013027786493652563546427)
              ·
                refine ⟨34519541679740478845319641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23013027786493652563546427 34519541679740478845319641)
                ·
                  refine ⟨25889656259805359133989731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34519541679740478845319641 25889656259805359133989731)
                  ·
                    refine ⟨38834484389708038700984597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25889656259805359133989731 38834484389708038700984597)
                    ·
                      refine ⟨1820366455767564314108653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38834484389708038700984597 1820366455767564314108653)
                      ·
                        rfl

theorem cell23_3545151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 6].length) (baseStart_3545151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3545151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3545151 prefixEnd_3545151 := by exact prefixLift 3545151
  have htrace : WordTrace (prefixWord ++ tailWord_3545151) baseStart_3545151 baseEnd_3545151 := by
    simpa [prefixWord, tailWord_3545151, baseEnd_3545151] using wordTrace_append hprefix tailTrace_3545151
  have hstable : (prefixWord ++ tailWord_3545151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545151).length < 2 ^ (prefixWord ++ tailWord_3545151).sum := by decide
  have hdescent : baseEnd_3545151 < baseStart_3545151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545161 : List Nat := [1, 2, 1, 1, 2, 2, 5, 1, 8]
def baseStart_3545161 : Nat := 118140960795 + 3545161 * 2 ^ 59
def prefixEnd_3545161 : Nat := 4983230072969 + 3 ^ 40 * 3545161 * 2
def baseEnd_3545161 : Nat := 202263510063789919442623

theorem tailTrace_3545161 : CollatzResearch.WordTrace tailWord_3545161 prefixEnd_3545161 202263510063789919442623 := by
  unfold tailWord_3545161
  simp only [CollatzResearch.WordTrace]
  refine ⟨129302644309494637140355337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86201762872996424760236891 129302644309494637140355337)
  ·
    refine ⟨96976983232120977855266503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129302644309494637140355337 96976983232120977855266503)
    ·
      refine ⟨145465474848181466782899755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96976983232120977855266503 145465474848181466782899755)
      ·
        refine ⟨218198212272272200174349633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145465474848181466782899755 218198212272272200174349633)
        ·
          refine ⟨163648659204204150130762225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218198212272272200174349633 163648659204204150130762225)
          ·
            refine ⟨122736494403153112598071669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163648659204204150130762225 122736494403153112598071669)
            ·
              refine ⟨11506546350295604306069219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 122736494403153112598071669 11506546350295604306069219)
              ·
                refine ⟨17259819525443406459103829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11506546350295604306069219 17259819525443406459103829)
                ·
                  refine ⟨202263510063789919442623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17259819525443406459103829 202263510063789919442623)
                  ·
                    rfl

theorem cell23_3545161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 8].length) (baseStart_3545161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3545161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3545161 prefixEnd_3545161 := by exact prefixLift 3545161
  have htrace : WordTrace (prefixWord ++ tailWord_3545161) baseStart_3545161 baseEnd_3545161 := by
    simpa [prefixWord, tailWord_3545161, baseEnd_3545161] using wordTrace_append hprefix tailTrace_3545161
  have hstable : (prefixWord ++ tailWord_3545161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545161).length < 2 ^ (prefixWord ++ tailWord_3545161).sum := by decide
  have hdescent : baseEnd_3545161 < baseStart_3545161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545245 : List Nat := [1, 4, 2, 1, 1, 4, 1, 1, 3, 1, 4]
def baseStart_3545245 : Nat := 118140960795 + 3545245 * 2 ^ 59
def prefixEnd_3545245 : Nat := 4983230072969 + 3 ^ 40 * 3545245 * 2
def baseEnd_3545245 : Nat := 1820414722949086946333221

theorem tailTrace_3545245 : CollatzResearch.WordTrace tailWord_3545245 prefixEnd_3545245 1820414722949086946333221 := by
  unfold tailWord_3545245
  simp only [CollatzResearch.WordTrace]
  refine ⟨129305708041190319486413189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86203805360793546324275459 129305708041190319486413189)
  ·
    refine ⟨24244820257723184903702473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129305708041190319486413189 24244820257723184903702473)
    ·
      refine ⟨18183615193292388677776855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24244820257723184903702473 18183615193292388677776855)
      ·
        refine ⟨27275422789938583016665283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18183615193292388677776855 27275422789938583016665283)
        ·
          refine ⟨40913134184907874524997925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27275422789938583016665283 40913134184907874524997925)
          ·
            refine ⟨7671212659670226473437111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40913134184907874524997925 7671212659670226473437111)
            ·
              refine ⟨11506818989505339710155667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7671212659670226473437111 11506818989505339710155667)
              ·
                refine ⟨17260228484258009565233501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11506818989505339710155667 17260228484258009565233501)
                ·
                  refine ⟨6472585681596753586962563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17260228484258009565233501 6472585681596753586962563)
                  ·
                    refine ⟨9708878522395130380443845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6472585681596753586962563 9708878522395130380443845)
                    ·
                      refine ⟨1820414722949086946333221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9708878522395130380443845 1820414722949086946333221)
                      ·
                        rfl

theorem cell23_3545245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_3545245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3545245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3545245 prefixEnd_3545245 := by exact prefixLift 3545245
  have htrace : WordTrace (prefixWord ++ tailWord_3545245) baseStart_3545245 baseEnd_3545245 := by
    simpa [prefixWord, tailWord_3545245, baseEnd_3545245] using wordTrace_append hprefix tailTrace_3545245
  have hstable : (prefixWord ++ tailWord_3545245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545245).length < 2 ^ (prefixWord ++ tailWord_3545245).sum := by decide
  have hdescent : baseEnd_3545245 < baseStart_3545245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545295 : List Nat := [1, 1, 2, 1, 1, 3, 6, 1, 1, 3, 3]
def baseStart_3545295 : Nat := 118140960795 + 3545295 * 2 ^ 59
def prefixEnd_3545295 : Nat := 4983230072969 + 3 ^ 40 * 3545295 * 2
def baseEnd_3545295 : Nat := 1820440396981811750707991

theorem tailTrace_3545295 : CollatzResearch.WordTrace tailWord_3545295 prefixEnd_3545295 1820440396981811750707991 := by
  unfold tailWord_3545295
  simp only [CollatzResearch.WordTrace]
  refine ⟨129307531691009178025733339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86205021127339452017155559 129307531691009178025733339)
  ·
    refine ⟨193961297536513767038600009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129307531691009178025733339 193961297536513767038600009)
    ·
      refine ⟨145470973152385325278950007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193961297536513767038600009 145470973152385325278950007)
      ·
        refine ⟨218206459728577987918425011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145470973152385325278950007 218206459728577987918425011)
        ·
          refine ⟨327309689592866981877637517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218206459728577987918425011 327309689592866981877637517)
          ·
            refine ⟨122741133597325118204114069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 327309689592866981877637517 122741133597325118204114069)
            ·
              refine ⟨5753490637374614915817847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 122741133597325118204114069 5753490637374614915817847)
              ·
                refine ⟨8630235956061922373726771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5753490637374614915817847 8630235956061922373726771)
                ·
                  refine ⟨12945353934092883560590157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8630235956061922373726771 12945353934092883560590157)
                  ·
                    refine ⟨4854507725284831335221309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12945353934092883560590157 4854507725284831335221309)
                    ·
                      refine ⟨1820440396981811750707991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4854507725284831335221309 1820440396981811750707991)
                      ·
                        rfl

theorem cell23_3545295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 1, 1, 3, 3].length) (baseStart_3545295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3545295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3545295 prefixEnd_3545295 := by exact prefixLift 3545295
  have htrace : WordTrace (prefixWord ++ tailWord_3545295) baseStart_3545295 baseEnd_3545295 := by
    simpa [prefixWord, tailWord_3545295, baseEnd_3545295] using wordTrace_append hprefix tailTrace_3545295
  have hstable : (prefixWord ++ tailWord_3545295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545295).length < 2 ^ (prefixWord ++ tailWord_3545295).sum := by decide
  have hdescent : baseEnd_3545295 < baseStart_3545295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545486 : List Nat := [4, 1, 1, 4, 1, 1, 1, 5, 1, 4]
def baseStart_3545486 : Nat := 118140960795 + 3545486 * 2 ^ 59
def prefixEnd_3545486 : Nat := 4983230072969 + 3 ^ 40 * 3545486 * 2
def baseEnd_3545486 : Nat := 606846157262273501139871

theorem tailTrace_3545486 : CollatzResearch.WordTrace tailWord_3545486 prefixEnd_3545486 606846157262273501139871 := by
  unfold tailWord_3545486
  simp only [CollatzResearch.WordTrace]
  refine ⟨16164312254164652205742039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86209665355544811763957541 16164312254164652205742039)
  ·
    refine ⟨24246468381246978308613059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16164312254164652205742039 24246468381246978308613059)
    ·
      refine ⟨36369702571870467462919589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24246468381246978308613059 36369702571870467462919589)
      ·
        refine ⟨6819319232225712649297423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36369702571870467462919589 6819319232225712649297423)
        ·
          refine ⟨10228978848338568973946135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6819319232225712649297423 10228978848338568973946135)
          ·
            refine ⟨15343468272507853460919203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10228978848338568973946135 15343468272507853460919203)
            ·
              refine ⟨23015202408761780191378805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15343468272507853460919203 23015202408761780191378805)
              ·
                refine ⟨2157675225821416892941763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23015202408761780191378805 2157675225821416892941763)
                ·
                  refine ⟨3236512838732125339412645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2157675225821416892941763 3236512838732125339412645)
                  ·
                    refine ⟨606846157262273501139871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3236512838732125339412645 606846157262273501139871)
                    ·
                      rfl

theorem cell23_3545486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 5, 1, 4].length) (baseStart_3545486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3545486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3545486 prefixEnd_3545486 := by exact prefixLift 3545486
  have htrace : WordTrace (prefixWord ++ tailWord_3545486) baseStart_3545486 baseEnd_3545486 := by
    simpa [prefixWord, tailWord_3545486, baseEnd_3545486] using wordTrace_append hprefix tailTrace_3545486
  have hstable : (prefixWord ++ tailWord_3545486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545486).length < 2 ^ (prefixWord ++ tailWord_3545486).sum := by decide
  have hdescent : baseEnd_3545486 < baseStart_3545486 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545509 : List Nat := [1, 3, 1, 2, 1, 1, 6, 1, 3, 1, 3]
def baseStart_3545509 : Nat := 118140960795 + 3545509 * 2 ^ 59
def prefixEnd_3545509 : Nat := 4983230072969 + 3 ^ 40 * 3545509 * 2
def baseEnd_3545509 : Nat := 1820550281841873913432007

theorem tailTrace_3545509 : CollatzResearch.WordTrace tailWord_3545509 prefixEnd_3545509 1820550281841873913432007 := by
  unfold tailWord_3545509
  simp only [CollatzResearch.WordTrace]
  refine ⟨129315336912233892574023581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86210224608155928382682387 129315336912233892574023581)
  ·
    refine ⟨48493251342087709715258843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129315336912233892574023581 48493251342087709715258843)
    ·
      refine ⟨72739877013131564572888265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48493251342087709715258843 72739877013131564572888265)
      ·
        refine ⟨54554907759848673429666199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72739877013131564572888265 54554907759848673429666199)
        ·
          refine ⟨81832361639773010144499299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54554907759848673429666199 81832361639773010144499299)
          ·
            refine ⟨122748542459659515216748949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81832361639773010144499299 122748542459659515216748949)
            ·
              refine ⟨5753837927796539775785107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 122748542459659515216748949 5753837927796539775785107)
              ·
                refine ⟨8630756891694809663677661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5753837927796539775785107 8630756891694809663677661)
                ·
                  refine ⟨3236533834385553623879123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8630756891694809663677661 3236533834385553623879123)
                  ·
                    refine ⟨4854800751578330435818685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3236533834385553623879123 4854800751578330435818685)
                    ·
                      refine ⟨1820550281841873913432007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4854800751578330435818685 1820550281841873913432007)
                      ·
                        rfl

theorem cell23_3545509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 1, 3, 1, 3].length) (baseStart_3545509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3545509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3545509 prefixEnd_3545509 := by exact prefixLift 3545509
  have htrace : WordTrace (prefixWord ++ tailWord_3545509) baseStart_3545509 baseEnd_3545509 := by
    simpa [prefixWord, tailWord_3545509, baseEnd_3545509] using wordTrace_append hprefix tailTrace_3545509
  have hstable : (prefixWord ++ tailWord_3545509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545509).length < 2 ^ (prefixWord ++ tailWord_3545509).sum := by decide
  have hdescent : baseEnd_3545509 < baseStart_3545509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545529 : List Nat := [1, 2, 1, 4, 3, 2, 2, 2, 1, 5]
def baseStart_3545529 : Nat := 118140960795 + 3545529 * 2 ^ 59
def prefixEnd_3545529 : Nat := 4983230072969 + 3 ^ 40 * 3545529 * 2
def baseEnd_3545529 : Nat := 606853517151654611727305

theorem tailTrace_3545529 : CollatzResearch.WordTrace tailWord_3545529 prefixEnd_3545529 606853517151654611727305 := by
  unfold tailWord_3545529
  simp only [CollatzResearch.WordTrace]
  refine ⟨129316066372161435989751641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86210710914774290659834427 129316066372161435989751641)
  ·
    refine ⟨96987049779121076992313731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129316066372161435989751641 96987049779121076992313731)
    ·
      refine ⟨145480574668681615488470597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96987049779121076992313731 145480574668681615488470597)
      ·
        refine ⟨27277607750377802904088237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145480574668681615488470597 27277607750377802904088237)
        ·
          refine ⟨10229102906391676089033089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27277607750377802904088237 10229102906391676089033089)
          ·
            refine ⟨7671827179793757066774817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10229102906391676089033089 7671827179793757066774817)
            ·
              refine ⟨5753870384845317800081113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7671827179793757066774817 5753870384845317800081113)
              ·
                refine ⟨4315402788633988350060835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5753870384845317800081113 4315402788633988350060835)
                ·
                  refine ⟨6473104182950982525091253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4315402788633988350060835 6473104182950982525091253)
                  ·
                    refine ⟨606853517151654611727305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6473104182950982525091253 606853517151654611727305)
                    ·
                      rfl

theorem cell23_3545529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 2, 1, 5].length) (baseStart_3545529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3545529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3545529 prefixEnd_3545529 := by exact prefixLift 3545529
  have htrace : WordTrace (prefixWord ++ tailWord_3545529) baseStart_3545529 baseEnd_3545529 := by
    simpa [prefixWord, tailWord_3545529, baseEnd_3545529] using wordTrace_append hprefix tailTrace_3545529
  have hstable : (prefixWord ++ tailWord_3545529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545529).length < 2 ^ (prefixWord ++ tailWord_3545529).sum := by decide
  have hdescent : baseEnd_3545529 < baseStart_3545529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545537 : List Nat := [1, 2, 7, 1, 1, 2, 1, 3, 1, 4]
def baseStart_3545537 : Nat := 118140960795 + 3545537 * 2 ^ 59
def prefixEnd_3545537 : Nat := 4983230072969 + 3 ^ 40 * 3545537 * 2
def baseEnd_3545537 : Nat := 606854886433399934627293

theorem tailTrace_3545537 : CollatzResearch.WordTrace tailWord_3545537 prefixEnd_3545537 606854886433399934627293 := by
  unfold tailWord_3545537
  simp only [CollatzResearch.WordTrace]
  refine ⟨129316358156132453356042865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86210905437421635570695243 129316358156132453356042865)
  ·
    refine ⟨96987268617099340017032149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129316358156132453356042865 96987268617099340017032149)
    ·
      refine ⟨2273139108213265781649191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 96987268617099340017032149 2273139108213265781649191)
      ·
        refine ⟨3409708662319898672473787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2273139108213265781649191 3409708662319898672473787)
        ·
          refine ⟨5114562993479848008710681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3409708662319898672473787 5114562993479848008710681)
          ·
            refine ⟨3835922245109886006533011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5114562993479848008710681 3835922245109886006533011)
            ·
              refine ⟨5753883367664829009799517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3835922245109886006533011 5753883367664829009799517)
              ·
                refine ⟨2157706262874310878674819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5753883367664829009799517 2157706262874310878674819)
                ·
                  refine ⟨3236559394311466318012229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2157706262874310878674819 3236559394311466318012229)
                  ·
                    refine ⟨606854886433399934627293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3236559394311466318012229 606854886433399934627293)
                    ·
                      rfl

theorem cell23_3545537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_3545537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3545537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3545537 prefixEnd_3545537 := by exact prefixLift 3545537
  have htrace : WordTrace (prefixWord ++ tailWord_3545537) baseStart_3545537 baseEnd_3545537 := by
    simpa [prefixWord, tailWord_3545537, baseEnd_3545537] using wordTrace_append hprefix tailTrace_3545537
  have hstable : (prefixWord ++ tailWord_3545537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545537).length < 2 ^ (prefixWord ++ tailWord_3545537).sum := by decide
  have hdescent : baseEnd_3545537 < baseStart_3545537 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545543 : List Nat := [1, 1, 4, 1, 1, 6, 1, 3, 1, 1, 3]
def baseStart_3545543 : Nat := 118140960795 + 3545543 * 2 ^ 59
def prefixEnd_3545543 : Nat := 4983230072969 + 3 ^ 40 * 3545543 * 2
def baseEnd_3545543 : Nat := 1820567740184126780406851

theorem tailTrace_3545543 : CollatzResearch.WordTrace tailWord_3545543 prefixEnd_3545543 1820567740184126780406851 := by
  unfold tailWord_3545543
  simp only [CollatzResearch.WordTrace]
  refine ⟨129316576994110716380761283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86211051329407144253840855 129316576994110716380761283)
  ·
    refine ⟨193974865491166074571141925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129316576994110716380761283 193974865491166074571141925)
    ·
      refine ⟨36370287279593638982089111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 193974865491166074571141925 36370287279593638982089111)
      ·
        refine ⟨54555430919390458473133667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36370287279593638982089111 54555430919390458473133667)
        ·
          refine ⟨81833146379085687709700501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54555430919390458473133667 81833146379085687709700501)
          ·
            refine ⟨3835928736519641611392211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 81833146379085687709700501 3835928736519641611392211)
            ·
              refine ⟨5753893104779462417088317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3835928736519641611392211 5753893104779462417088317)
              ·
                refine ⟨2157709914292298406408119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5753893104779462417088317 2157709914292298406408119)
                ·
                  refine ⟨3236564871438447609612179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2157709914292298406408119 3236564871438447609612179)
                  ·
                    refine ⟨4854847307157671414418269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3236564871438447609612179 4854847307157671414418269)
                    ·
                      refine ⟨1820567740184126780406851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4854847307157671414418269 1820567740184126780406851)
                      ·
                        rfl

theorem cell23_3545543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 3, 1, 1, 3].length) (baseStart_3545543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3545543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3545543 prefixEnd_3545543 := by exact prefixLift 3545543
  have htrace : WordTrace (prefixWord ++ tailWord_3545543) baseStart_3545543 baseEnd_3545543 := by
    simpa [prefixWord, tailWord_3545543, baseEnd_3545543] using wordTrace_append hprefix tailTrace_3545543
  have hstable : (prefixWord ++ tailWord_3545543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545543).length < 2 ^ (prefixWord ++ tailWord_3545543).sum := by decide
  have hdescent : baseEnd_3545543 < baseStart_3545543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545576 : List Nat := [2, 1, 4, 1, 1, 3, 4, 1, 2, 4]
def baseStart_3545576 : Nat := 118140960795 + 3545576 * 2 ^ 59
def prefixEnd_3545576 : Nat := 4983230072969 + 3 ^ 40 * 3545576 * 2
def baseEnd_3545576 : Nat := 606861561681908383764733

theorem tailTrace_3545576 : CollatzResearch.WordTrace tailWord_3545576 prefixEnd_3545576 606861561681908383764733 := by
  unfold tailWord_3545576
  simp only [CollatzResearch.WordTrace]
  refine ⟨64658890301495581508356291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86211853735327442011141721 64658890301495581508356291)
  ·
    refine ⟨96988335452243372262534437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64658890301495581508356291 96988335452243372262534437)
    ·
      refine ⟨18185312897295632299225207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96988335452243372262534437 18185312897295632299225207)
      ·
        refine ⟨27277969345943448448837811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18185312897295632299225207 27277969345943448448837811)
        ·
          refine ⟨40916954018915172673256717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27277969345943448448837811 40916954018915172673256717)
          ·
            refine ⟨15343857757093189752471269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40916954018915172673256717 15343857757093189752471269)
            ·
              refine ⟨2876973329454973078588363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15343857757093189752471269 2876973329454973078588363)
              ·
                refine ⟨4315459994182459617882545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2876973329454973078588363 4315459994182459617882545)
                ·
                  refine ⟨3236594995636844713411909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4315459994182459617882545 3236594995636844713411909)
                  ·
                    refine ⟨606861561681908383764733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3236594995636844713411909 606861561681908383764733)
                    ·
                      rfl

theorem cell23_3545576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 4, 1, 2, 4].length) (baseStart_3545576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3545576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3545576 prefixEnd_3545576 := by exact prefixLift 3545576
  have htrace : WordTrace (prefixWord ++ tailWord_3545576) baseStart_3545576 baseEnd_3545576 := by
    simpa [prefixWord, tailWord_3545576, baseEnd_3545576] using wordTrace_append hprefix tailTrace_3545576
  have hstable : (prefixWord ++ tailWord_3545576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545576).length < 2 ^ (prefixWord ++ tailWord_3545576).sum := by decide
  have hdescent : baseEnd_3545576 < baseStart_3545576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545586 : List Nat := [3, 2, 1, 4, 2, 1, 1, 1, 3, 2, 3]
def baseStart_3545586 : Nat := 118140960795 + 3545586 * 2 ^ 59
def prefixEnd_3545586 : Nat := 4983230072969 + 3 ^ 40 * 3545586 * 2
def baseEnd_3545586 : Nat := 1820589819852270112169153

theorem tailTrace_3545586 : CollatzResearch.WordTrace tailWord_3545586 prefixEnd_3545586 1820589819852270112169153 := by
  unfold tailWord_3545586
  simp only [CollatzResearch.WordTrace]
  refine ⟨32329536333238733681144153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86212096888636623149717741 32329536333238733681144153)
  ·
    refine ⟨24247152249929050260858115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32329536333238733681144153 24247152249929050260858115)
    ·
      refine ⟨36370728374893575391287173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24247152249929050260858115 36370728374893575391287173)
      ·
        refine ⟨6819511570292545385866345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36370728374893575391287173 6819511570292545385866345)
        ·
          refine ⟨5114633677719409039399759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6819511570292545385866345 5114633677719409039399759)
          ·
            refine ⟨7671950516579113559099639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5114633677719409039399759 7671950516579113559099639)
            ·
              refine ⟨11507925774868670338649459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7671950516579113559099639 11507925774868670338649459)
              ·
                refine ⟨17261888662303005507974189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11507925774868670338649459 17261888662303005507974189)
                ·
                  refine ⟨6473208248363627065490321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17261888662303005507974189 6473208248363627065490321)
                  ·
                    refine ⟨4854906186272720299117741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6473208248363627065490321 4854906186272720299117741)
                    ·
                      refine ⟨1820589819852270112169153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4854906186272720299117741 1820589819852270112169153)
                      ·
                        rfl

theorem cell23_3545586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_3545586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3545586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3545586 prefixEnd_3545586 := by exact prefixLift 3545586
  have htrace : WordTrace (prefixWord ++ tailWord_3545586) baseStart_3545586 baseEnd_3545586 := by
    simpa [prefixWord, tailWord_3545586, baseEnd_3545586] using wordTrace_append hprefix tailTrace_3545586
  have hstable : (prefixWord ++ tailWord_3545586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545586).length < 2 ^ (prefixWord ++ tailWord_3545586).sum := by decide
  have hdescent : baseEnd_3545586 < baseStart_3545586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545606 : List Nat := [6, 2, 1, 1, 1, 12]
def baseStart_3545606 : Nat := 118140960795 + 3545606 * 2 ^ 59
def prefixEnd_3545606 : Nat := 4983230072969 + 3 ^ 40 * 3545606 * 2
def baseEnd_3545606 : Nat := 7492181438129053637527

theorem tailTrace_3545606 : CollatzResearch.WordTrace tailWord_3545606 prefixEnd_3545606 7492181438129053637527 := by
  unfold tailWord_3545606
  simp only [CollatzResearch.WordTrace]
  refine ⟨4041214837277577441884521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 86212583195254985426869781 4041214837277577441884521)
  ·
    refine ⟨3030911127958183081413391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4041214837277577441884521 3030911127958183081413391)
    ·
      refine ⟨4546366691937274622120087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3030911127958183081413391 4546366691937274622120087)
      ·
        refine ⟨6819550037905911933180131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4546366691937274622120087 6819550037905911933180131)
        ·
          refine ⟨10229325056858867899770197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6819550037905911933180131 10229325056858867899770197)
          ·
            refine ⟨7492181438129053637527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 10229325056858867899770197 7492181438129053637527)
            ·
              rfl

theorem cell23_3545606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 12].length) (baseStart_3545606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3545606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3545606 prefixEnd_3545606 := by exact prefixLift 3545606
  have htrace : WordTrace (prefixWord ++ tailWord_3545606) baseStart_3545606 baseEnd_3545606 := by
    simpa [prefixWord, tailWord_3545606, baseEnd_3545606] using wordTrace_append hprefix tailTrace_3545606
  have hstable : (prefixWord ++ tailWord_3545606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545606).length < 2 ^ (prefixWord ++ tailWord_3545606).sum := by decide
  have hdescent : baseEnd_3545606 < baseStart_3545606 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545656 : List Nat := [2, 1, 2, 1, 4, 1, 2, 2, 4, 2, 2]
def baseStart_3545656 : Nat := 118140960795 + 3545656 * 2 ^ 59
def prefixEnd_3545656 : Nat := 4983230072969 + 3 ^ 40 * 3545656 * 2
def baseEnd_3545656 : Nat := 1820625763498084838293831

theorem tailTrace_3545656 : CollatzResearch.WordTrace tailWord_3545656 prefixEnd_3545656 1820625763498084838293831 := by
  unfold tailWord_3545656
  simp only [CollatzResearch.WordTrace]
  refine ⟨64660349221350668339812411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86213798961800891119749881 64660349221350668339812411)
  ·
    refine ⟨96990523832026002509718617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64660349221350668339812411 96990523832026002509718617)
    ·
      refine ⟨72742892874019501882288963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96990523832026002509718617 72742892874019501882288963)
      ·
        refine ⟨109114339311029252823433445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72742892874019501882288963 109114339311029252823433445)
        ·
          refine ⟨20458938620817984904393771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109114339311029252823433445 20458938620817984904393771)
          ·
            refine ⟨30688407931226977356590657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20458938620817984904393771 30688407931226977356590657)
            ·
              refine ⟨23016305948420233017442993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30688407931226977356590657 23016305948420233017442993)
              ·
                refine ⟨17262229461315174763082245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23016305948420233017442993 17262229461315174763082245)
                ·
                  refine ⟨3236668023996595268077921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17262229461315174763082245 3236668023996595268077921)
                  ·
                    refine ⟨2427501017997446451058441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3236668023996595268077921 2427501017997446451058441)
                    ·
                      refine ⟨1820625763498084838293831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2427501017997446451058441 1820625763498084838293831)
                      ·
                        rfl

theorem cell23_3545656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 4, 2, 2].length) (baseStart_3545656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3545656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3545656 prefixEnd_3545656 := by exact prefixLift 3545656
  have htrace : WordTrace (prefixWord ++ tailWord_3545656) baseStart_3545656 baseEnd_3545656 := by
    simpa [prefixWord, tailWord_3545656, baseEnd_3545656] using wordTrace_append hprefix tailTrace_3545656
  have hstable : (prefixWord ++ tailWord_3545656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545656).length < 2 ^ (prefixWord ++ tailWord_3545656).sum := by decide
  have hdescent : baseEnd_3545656 < baseStart_3545656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545660 : List Nat := [2, 2, 2, 2, 3, 3, 2, 1, 1, 3, 2]
def baseStart_3545660 : Nat := 118140960795 + 3545660 * 2 ^ 59
def prefixEnd_3545660 : Nat := 4983230072969 + 3 ^ 40 * 3545660 * 2
def baseEnd_3545660 : Nat := 1820627817420702822643813

theorem tailTrace_3545660 : CollatzResearch.WordTrace tailWord_3545660 prefixEnd_3545660 1820627817420702822643813 := by
  unfold tailWord_3545660
  simp only [CollatzResearch.WordTrace]
  refine ⟨64660422167343422681385217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86213896223124563575180289 64660422167343422681385217)
  ·
    refine ⟨48495316625507567011038913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64660422167343422681385217 48495316625507567011038913)
    ·
      refine ⟨36371487469130675258279185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48495316625507567011038913 36371487469130675258279185)
      ·
        refine ⟨27278615601848006443709389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36371487469130675258279185 27278615601848006443709389)
        ·
          refine ⟨10229480850693002416391021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27278615601848006443709389 10229480850693002416391021)
          ·
            refine ⟨3836055319009875906146633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10229480850693002416391021 3836055319009875906146633)
            ·
              refine ⟨2877041489257406929609975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3836055319009875906146633 2877041489257406929609975)
              ·
                refine ⟨4315562233886110394414963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2877041489257406929609975 4315562233886110394414963)
                ·
                  refine ⟨6473343350829165591622445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4315562233886110394414963 6473343350829165591622445)
                  ·
                    refine ⟨2427503756560937096858417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6473343350829165591622445 2427503756560937096858417)
                    ·
                      refine ⟨1820627817420702822643813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2427503756560937096858417 1820627817420702822643813)
                      ·
                        rfl

theorem cell23_3545660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 2, 1, 1, 3, 2].length) (baseStart_3545660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3545660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3545660 prefixEnd_3545660 := by exact prefixLift 3545660
  have htrace : WordTrace (prefixWord ++ tailWord_3545660) baseStart_3545660 baseEnd_3545660 := by
    simpa [prefixWord, tailWord_3545660, baseEnd_3545660] using wordTrace_append hprefix tailTrace_3545660
  have hstable : (prefixWord ++ tailWord_3545660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545660).length < 2 ^ (prefixWord ++ tailWord_3545660).sum := by decide
  have hdescent : baseEnd_3545660 < baseStart_3545660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545679 : List Nat := [1, 1, 2, 1, 1, 2, 6, 4, 5]
def baseStart_3545679 : Nat := 118140960795 + 3545679 * 2 ^ 59
def prefixEnd_3545679 : Nat := 4983230072969 + 3 ^ 40 * 3545679 * 2
def baseEnd_3545679 : Nat := 202293063728126472034025

theorem tailTrace_3545679 : CollatzResearch.WordTrace tailWord_3545679 prefixEnd_3545679 202293063728126472034025 := by
  unfold tailWord_3545679
  simp only [CollatzResearch.WordTrace]
  refine ⟨129321537321618011607712091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86214358214412007738474727 129321537321618011607712091)
  ·
    refine ⟨193982305982427017411568137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129321537321618011607712091 193982305982427017411568137)
    ·
      refine ⟨145486729486820263058676103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193982305982427017411568137 145486729486820263058676103)
      ·
        refine ⟨218230094230230394588014155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145486729486820263058676103 218230094230230394588014155)
        ·
          refine ⟨327345141345345591882021233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218230094230230394588014155 327345141345345591882021233)
          ·
            refine ⟨245508856009009193911515925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 327345141345345591882021233 245508856009009193911515925)
            ·
              refine ⟨11508227625422305964602309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 245508856009009193911515925 11508227625422305964602309)
              ·
                refine ⟨2157792679766682368362933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11508227625422305964602309 2157792679766682368362933)
                ·
                  refine ⟨202293063728126472034025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2157792679766682368362933 202293063728126472034025)
                  ·
                    rfl

theorem cell23_3545679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 4, 5].length) (baseStart_3545679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3545679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3545679 prefixEnd_3545679 := by exact prefixLift 3545679
  have htrace : WordTrace (prefixWord ++ tailWord_3545679) baseStart_3545679 baseEnd_3545679 := by
    simpa [prefixWord, tailWord_3545679, baseEnd_3545679] using wordTrace_append hprefix tailTrace_3545679
  have hstable : (prefixWord ++ tailWord_3545679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545679).length < 2 ^ (prefixWord ++ tailWord_3545679).sum := by decide
  have hdescent : baseEnd_3545679 < baseStart_3545679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545694 : List Nat := [4, 4, 1, 2, 1, 1, 2, 2, 1, 3, 2]
def baseStart_3545694 : Nat := 118140960795 + 3545694 * 2 ^ 59
def prefixEnd_3545694 : Nat := 4983230072969 + 3 ^ 40 * 3545694 * 2
def baseEnd_3545694 : Nat := 1820645275762955689618657

theorem tailTrace_3545694 : CollatzResearch.WordTrace tailWord_3545694 prefixEnd_3545694 1820645275762955689618657 := by
  unfold tailWord_3545694
  simp only [CollatzResearch.WordTrace]
  refine ⟨16165260552070458646188517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86214722944375779446338757 16165260552070458646188517)
  ·
    refine ⟨3030986353513210996160347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16165260552070458646188517 3030986353513210996160347)
    ·
      refine ⟨4546479530269816494240521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3030986353513210996160347 4546479530269816494240521)
      ·
        refine ⟨3409859647702362370680391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4546479530269816494240521 3409859647702362370680391)
        ·
          refine ⟨5114789471553543556020587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3409859647702362370680391 5114789471553543556020587)
          ·
            refine ⟨7672184207330315334030881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5114789471553543556020587 7672184207330315334030881)
            ·
              refine ⟨5754138155497736500523161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7672184207330315334030881 5754138155497736500523161)
              ·
                refine ⟨4315603616623302375392371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5754138155497736500523161 4315603616623302375392371)
                ·
                  refine ⟨6473405424934953563088557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4315603616623302375392371 6473405424934953563088557)
                  ·
                    refine ⟨2427527034350607586158209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6473405424934953563088557 2427527034350607586158209)
                    ·
                      refine ⟨1820645275762955689618657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2427527034350607586158209 1820645275762955689618657)
                      ·
                        rfl

theorem cell23_3545694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_3545694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3545694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3545694 prefixEnd_3545694 := by exact prefixLift 3545694
  have htrace : WordTrace (prefixWord ++ tailWord_3545694) baseStart_3545694 baseEnd_3545694 := by
    simpa [prefixWord, tailWord_3545694, baseEnd_3545694] using wordTrace_append hprefix tailTrace_3545694
  have hstable : (prefixWord ++ tailWord_3545694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545694).length < 2 ^ (prefixWord ++ tailWord_3545694).sum := by decide
  have hdescent : baseEnd_3545694 < baseStart_3545694 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545709 : List Nat := [1, 5, 1, 1, 3, 1, 2, 1, 1, 7]
def baseStart_3545709 : Nat := 118140960795 + 3545709 * 2 ^ 59
def prefixEnd_3545709 : Nat := 4983230072969 + 3 ^ 40 * 3545709 * 2
def baseEnd_3545709 : Nat := 606884325990924376977029

theorem tailTrace_3545709 : CollatzResearch.WordTrace tailWord_3545709 prefixEnd_3545709 606884325990924376977029 := by
  unfold tailWord_3545709
  simp only [CollatzResearch.WordTrace]
  refine ⟨129322631511509326731304181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86215087674339551154202787 129322631511509326731304181)
  ·
    refine ⟨12123996704203999381059767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 129322631511509326731304181 12123996704203999381059767)
    ·
      refine ⟨18185995056305999071589651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12123996704203999381059767 18185995056305999071589651)
      ·
        refine ⟨27278992584458998607384477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18185995056305999071589651 27278992584458998607384477)
        ·
          refine ⟨10229622219172124477769179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27278992584458998607384477 10229622219172124477769179)
          ·
            refine ⟨15344433328758186716653769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10229622219172124477769179 15344433328758186716653769)
            ·
              refine ⟨11508324996568640037490327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15344433328758186716653769 11508324996568640037490327)
              ·
                refine ⟨17262487494852960056235491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11508324996568640037490327 17262487494852960056235491)
                ·
                  refine ⟨25893731242279440084353237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17262487494852960056235491 25893731242279440084353237)
                  ·
                    refine ⟨606884325990924376977029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25893731242279440084353237 606884325990924376977029)
                    ·
                      rfl

theorem cell23_3545709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_3545709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3545709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3545709 prefixEnd_3545709 := by exact prefixLift 3545709
  have htrace : WordTrace (prefixWord ++ tailWord_3545709) baseStart_3545709 baseEnd_3545709 := by
    simpa [prefixWord, tailWord_3545709, baseEnd_3545709] using wordTrace_append hprefix tailTrace_3545709
  have hstable : (prefixWord ++ tailWord_3545709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545709).length < 2 ^ (prefixWord ++ tailWord_3545709).sum := by decide
  have hdescent : baseEnd_3545709 < baseStart_3545709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545739 : List Nat := [1, 1, 1, 1, 4, 1, 2, 5, 3, 4]
def baseStart_3545739 : Nat := 118140960795 + 3545739 * 2 ^ 59
def prefixEnd_3545739 : Nat := 4983230072969 + 3 ^ 40 * 3545739 * 2
def baseEnd_3545739 : Nat := 606889460797469337851983

theorem tailTrace_3545739 : CollatzResearch.WordTrace tailWord_3545739 prefixEnd_3545739 606889460797469337851983 := by
  unfold tailWord_3545739
  simp only [CollatzResearch.WordTrace]
  refine ⟨129323725701400641854896271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86215817134267094569930847 129323725701400641854896271)
  ·
    refine ⟨193985588552100962782344407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129323725701400641854896271 193985588552100962782344407)
    ·
      refine ⟨290978382828151444173516611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193985588552100962782344407 290978382828151444173516611)
      ·
        refine ⟨436467574242227166260274917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290978382828151444173516611 436467574242227166260274917)
        ·
          refine ⟨81837670170417593673801547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 436467574242227166260274917 81837670170417593673801547)
          ·
            refine ⟨122756505255626390510702321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81837670170417593673801547 122756505255626390510702321)
            ·
              refine ⟨92067378941719792883026741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122756505255626390510702321 92067378941719792883026741)
              ·
                refine ⟨8631316775786230582783757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92067378941719792883026741 8631316775786230582783757)
                ·
                  refine ⟨3236743790919836468543909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8631316775786230582783757 3236743790919836468543909)
                  ·
                    refine ⟨606889460797469337851983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3236743790919836468543909 606889460797469337851983)
                    ·
                      rfl

theorem cell23_3545739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 5, 3, 4].length) (baseStart_3545739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3545739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3545739 prefixEnd_3545739 := by exact prefixLift 3545739
  have htrace : WordTrace (prefixWord ++ tailWord_3545739) baseStart_3545739 baseEnd_3545739 := by
    simpa [prefixWord, tailWord_3545739, baseEnd_3545739] using wordTrace_append hprefix tailTrace_3545739
  have hstable : (prefixWord ++ tailWord_3545739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545739).length < 2 ^ (prefixWord ++ tailWord_3545739).sum := by decide
  have hdescent : baseEnd_3545739 < baseStart_3545739 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545823 : List Nat := [1, 1, 2, 3, 2, 3, 3, 1, 2, 3, 2]
def baseStart_3545823 : Nat := 118140960795 + 3545823 * 2 ^ 59
def prefixEnd_3545823 : Nat := 4983230072969 + 3 ^ 40 * 3545823 * 2
def baseEnd_3545823 : Nat := 1820711514767385684905563

theorem tailTrace_3545823 : CollatzResearch.WordTrace tailWord_3545823 prefixEnd_3545823 1820711514767385684905563 := by
  unfold tailWord_3545823
  simp only [CollatzResearch.WordTrace]
  refine ⟨129326789433096324200954123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86217859622064216133969415 129326789433096324200954123)
  ·
    refine ⟨193990184149644486301431185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129326789433096324200954123 193990184149644486301431185)
    ·
      refine ⟨145492638112233364726073389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193990184149644486301431185 145492638112233364726073389)
      ·
        refine ⟨54559739292087511772277521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145492638112233364726073389 54559739292087511772277521)
        ·
          refine ⟨40919804469065633829208141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54559739292087511772277521 40919804469065633829208141)
          ·
            refine ⟨15344926675899612685953053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40919804469065633829208141 15344926675899612685953053)
            ·
              refine ⟨5754347503462354757232395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15344926675899612685953053 5754347503462354757232395)
              ·
                refine ⟨8631521255193532135848593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5754347503462354757232395 8631521255193532135848593)
                ·
                  refine ⟨6473640941395149101886445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8631521255193532135848593 6473640941395149101886445)
                  ·
                    refine ⟨2427615353023180913207417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6473640941395149101886445 2427615353023180913207417)
                    ·
                      refine ⟨1820711514767385684905563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2427615353023180913207417 1820711514767385684905563)
                      ·
                        rfl

theorem cell23_3545823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 1, 2, 3, 2].length) (baseStart_3545823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3545823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3545823 prefixEnd_3545823 := by exact prefixLift 3545823
  have htrace : WordTrace (prefixWord ++ tailWord_3545823) baseStart_3545823 baseEnd_3545823 := by
    simpa [prefixWord, tailWord_3545823, baseEnd_3545823] using wordTrace_append hprefix tailTrace_3545823
  have hstable : (prefixWord ++ tailWord_3545823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545823).length < 2 ^ (prefixWord ++ tailWord_3545823).sum := by decide
  have hdescent : baseEnd_3545823 < baseStart_3545823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545849 : List Nat := [1, 2, 1, 3, 1, 1, 1, 4, 3, 2, 4]
def baseStart_3545849 : Nat := 118140960795 + 3545849 * 2 ^ 59
def prefixEnd_3545849 : Nat := 4983230072969 + 3 ^ 40 * 3545849 * 2
def baseEnd_3545849 : Nat := 1820724865264402583180443

theorem tailTrace_3545849 : CollatzResearch.WordTrace tailWord_3545849 prefixEnd_3545849 1820724865264402583180443 := by
  unfold tailWord_3545849
  simp only [CollatzResearch.WordTrace]
  refine ⟨129327737731002130641400601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86218491820668087094267067 129327737731002130641400601)
  ·
    refine ⟨96995803298251597981050451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129327737731002130641400601 96995803298251597981050451)
    ·
      refine ⟨145493704947377396971575677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96995803298251597981050451 145493704947377396971575677)
      ·
        refine ⟨54560139355266523864340879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145493704947377396971575677 54560139355266523864340879)
        ·
          refine ⟨81840209032899785796511319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54560139355266523864340879 81840209032899785796511319)
          ·
            refine ⟨122760313549349678694766979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81840209032899785796511319 122760313549349678694766979)
            ·
              refine ⟨184140470324024518042150469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122760313549349678694766979 184140470324024518042150469)
              ·
                refine ⟨34526338185754597132903213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 184140470324024518042150469 34526338185754597132903213)
                ·
                  refine ⟨12947376819657973924838705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34526338185754597132903213 12947376819657973924838705)
                  ·
                    refine ⟨9710532614743480443629029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12947376819657973924838705 9710532614743480443629029)
                    ·
                      refine ⟨1820724865264402583180443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9710532614743480443629029 1820724865264402583180443)
                      ·
                        rfl

theorem cell23_3545849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 3, 2, 4].length) (baseStart_3545849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3545849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3545849 prefixEnd_3545849 := by exact prefixLift 3545849
  have htrace : WordTrace (prefixWord ++ tailWord_3545849) baseStart_3545849 baseEnd_3545849 := by
    simpa [prefixWord, tailWord_3545849, baseEnd_3545849] using wordTrace_append hprefix tailTrace_3545849
  have hstable : (prefixWord ++ tailWord_3545849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545849).length < 2 ^ (prefixWord ++ tailWord_3545849).sum := by decide
  have hdescent : baseEnd_3545849 < baseStart_3545849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545863 : List Nat := [1, 1, 4, 4, 1, 3, 1, 1, 1, 6]
def baseStart_3545863 : Nat := 118140960795 + 3545863 * 2 ^ 59
def prefixEnd_3545863 : Nat := 4983230072969 + 3 ^ 40 * 3545863 * 2
def baseEnd_3545863 : Nat := 606910684664521842801793

theorem tailTrace_3545863 : CollatzResearch.WordTrace tailWord_3545863 prefixEnd_3545863 606910684664521842801793 := by
  unfold tailWord_3545863
  simp only [CollatzResearch.WordTrace]
  refine ⟨129328248352951411032410243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86218832235300940688273495 129328248352951411032410243)
  ·
    refine ⟨193992372529427116548615365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129328248352951411032410243 193992372529427116548615365)
    ·
      refine ⟨36373569849267584352865381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 193992372529427116548615365 36373569849267584352865381)
      ·
        refine ⟨6820044346737672066162259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36373569849267584352865381 6820044346737672066162259)
        ·
          refine ⟨10230066520106508099243389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6820044346737672066162259 10230066520106508099243389)
          ·
            refine ⟨3836274945039940537216271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10230066520106508099243389 3836274945039940537216271)
            ·
              refine ⟨5754412417559910805824407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3836274945039940537216271 5754412417559910805824407)
              ·
                refine ⟨8631618626339866208736611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5754412417559910805824407 8631618626339866208736611)
                ·
                  refine ⟨12947427939509799313104917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8631618626339866208736611 12947427939509799313104917)
                  ·
                    refine ⟨606910684664521842801793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12947427939509799313104917 606910684664521842801793)
                    ·
                      rfl

theorem cell23_3545863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 1, 1, 6].length) (baseStart_3545863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3545863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3545863 prefixEnd_3545863 := by exact prefixLift 3545863
  have htrace : WordTrace (prefixWord ++ tailWord_3545863) baseStart_3545863 baseEnd_3545863 := by
    simpa [prefixWord, tailWord_3545863, baseEnd_3545863] using wordTrace_append hprefix tailTrace_3545863
  have hstable : (prefixWord ++ tailWord_3545863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545863).length < 2 ^ (prefixWord ++ tailWord_3545863).sum := by decide
  have hdescent : baseEnd_3545863 < baseStart_3545863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545887 : List Nat := [1, 1, 2, 4, 2, 2, 3, 3, 1, 2, 2]
def baseStart_3545887 : Nat := 118140960795 + 3545887 * 2 ^ 59
def prefixEnd_3545887 : Nat := 4983230072969 + 3 ^ 40 * 3545887 * 2
def baseEnd_3545887 : Nat := 1820744377529273434505269

theorem tailTrace_3545887 : CollatzResearch.WordTrace tailWord_3545887 prefixEnd_3545887 1820744377529273434505269 := by
  unfold tailWord_3545887
  simp only [CollatzResearch.WordTrace]
  refine ⟨129329123704864463131283915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86219415803242975420855943 129329123704864463131283915)
  ·
    refine ⟨193993685557296694696925873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129329123704864463131283915 193993685557296694696925873)
    ·
      refine ⟨145495264167972521022694405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193993685557296694696925873 145495264167972521022694405)
      ·
        refine ⟨27280362031494847691755201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145495264167972521022694405 27280362031494847691755201)
        ·
          refine ⟨20460271523621135768816401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27280362031494847691755201 20460271523621135768816401)
          ·
            refine ⟨15345203642715851826612301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20460271523621135768816401 15345203642715851826612301)
            ·
              refine ⟨5754451366018444434979613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15345203642715851826612301 5754451366018444434979613)
              ·
                refine ⟨2157919262256916663117355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5754451366018444434979613 2157919262256916663117355)
                ·
                  refine ⟨3236878893385374994676033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2157919262256916663117355 3236878893385374994676033)
                  ·
                    refine ⟨2427659170039031246007025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3236878893385374994676033 2427659170039031246007025)
                    ·
                      refine ⟨1820744377529273434505269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2427659170039031246007025 1820744377529273434505269)
                      ·
                        rfl

theorem cell23_3545887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 3, 1, 2, 2].length) (baseStart_3545887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3545887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3545887 prefixEnd_3545887 := by exact prefixLift 3545887
  have htrace : WordTrace (prefixWord ++ tailWord_3545887) baseStart_3545887 baseEnd_3545887 := by
    simpa [prefixWord, tailWord_3545887, baseEnd_3545887] using wordTrace_append hprefix tailTrace_3545887
  have hstable : (prefixWord ++ tailWord_3545887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545887).length < 2 ^ (prefixWord ++ tailWord_3545887).sum := by decide
  have hdescent : baseEnd_3545887 < baseStart_3545887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545924 : List Nat := [2, 3, 4, 2, 1, 2, 1, 2, 1, 2, 3]
def baseStart_3545924 : Nat := 118140960795 + 3545924 * 2 ^ 59
def prefixEnd_3545924 : Nat := 4983230072969 + 3 ^ 40 * 3545924 * 2
def baseEnd_3545924 : Nat := 1820763376313489789742599

theorem tailTrace_3545924 : CollatzResearch.WordTrace tailWord_3545924 prefixEnd_3545924 1820763376313489789742599 := by
  unfold tailWord_3545924
  simp only [CollatzResearch.WordTrace]
  refine ⟨64665236602865209225190413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86220315470486945633587217 64665236602865209225190413)
  ·
    refine ⟨24249463726074453459446405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64665236602865209225190413 24249463726074453459446405)
    ·
      refine ⟨4546774448638960023646201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24249463726074453459446405 4546774448638960023646201)
      ·
        refine ⟨3410080836479220017734651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4546774448638960023646201 3410080836479220017734651)
        ·
          refine ⟨5115121254718830026601977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3410080836479220017734651 5115121254718830026601977)
          ·
            refine ⟨3836340941039122519951483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5115121254718830026601977 3836340941039122519951483)
            ·
              refine ⟨5754511411558683779927225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3836340941039122519951483 5754511411558683779927225)
              ·
                refine ⟨4315883558669012834945419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5754511411558683779927225 4315883558669012834945419)
                ·
                  refine ⟨6473825338003519252418129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4315883558669012834945419 6473825338003519252418129)
                  ·
                    refine ⟨4855369003502639439313597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6473825338003519252418129 4855369003502639439313597)
                    ·
                      refine ⟨1820763376313489789742599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4855369003502639439313597 1820763376313489789742599)
                      ·
                        rfl

theorem cell23_3545924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_3545924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3545924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3545924 prefixEnd_3545924 := by exact prefixLift 3545924
  have htrace : WordTrace (prefixWord ++ tailWord_3545924) baseStart_3545924 baseEnd_3545924 := by
    simpa [prefixWord, tailWord_3545924, baseEnd_3545924] using wordTrace_append hprefix tailTrace_3545924
  have hstable : (prefixWord ++ tailWord_3545924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545924).length < 2 ^ (prefixWord ++ tailWord_3545924).sum := by decide
  have hdescent : baseEnd_3545924 < baseStart_3545924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545943 : List Nat := [1, 1, 3, 2, 4, 1, 1, 1, 3, 4, 2]
def baseStart_3545943 : Nat := 118140960795 + 3545943 * 2 ^ 59
def prefixEnd_3545943 : Nat := 4983230072969 + 3 ^ 40 * 3545943 * 2
def baseEnd_3545943 : Nat := 1820773132445925215405011

theorem tailTrace_3545943 : CollatzResearch.WordTrace tailWord_3545943 prefixEnd_3545943 1820773132445925215405011 := by
  unfold tailWord_3545943
  simp only [CollatzResearch.WordTrace]
  refine ⟨129331166192661584695322483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86220777461774389796881655 129331166192661584695322483)
  ·
    refine ⟨193996749288992377042983725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129331166192661584695322483 193996749288992377042983725)
    ·
      refine ⟨72748780983372141391118897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193996749288992377042983725 72748780983372141391118897)
      ·
        refine ⟨54561585737529106043339173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72748780983372141391118897 54561585737529106043339173)
        ·
          refine ⟨10230297325786707383126095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54561585737529106043339173 10230297325786707383126095)
          ·
            refine ⟨15345445988680061074689143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10230297325786707383126095 15345445988680061074689143)
            ·
              refine ⟨23018168983020091612033715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15345445988680061074689143 23018168983020091612033715)
              ·
                refine ⟨34527253474530137418050573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23018168983020091612033715 34527253474530137418050573)
                ·
                  refine ⟨12947720052948801531768965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34527253474530137418050573 12947720052948801531768965)
                  ·
                    refine ⟨2427697509927900287206681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12947720052948801531768965 2427697509927900287206681)
                    ·
                      refine ⟨1820773132445925215405011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2427697509927900287206681 1820773132445925215405011)
                      ·
                        rfl

theorem cell23_3545943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 3, 4, 2].length) (baseStart_3545943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3545943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3545943 prefixEnd_3545943 := by exact prefixLift 3545943
  have htrace : WordTrace (prefixWord ++ tailWord_3545943) baseStart_3545943 baseEnd_3545943 := by
    simpa [prefixWord, tailWord_3545943, baseEnd_3545943] using wordTrace_append hprefix tailTrace_3545943
  have hstable : (prefixWord ++ tailWord_3545943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545943).length < 2 ^ (prefixWord ++ tailWord_3545943).sum := by decide
  have hdescent : baseEnd_3545943 < baseStart_3545943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545946 : List Nat := [3, 1, 1, 2, 1, 4, 2, 1, 2, 1, 5]
def baseStart_3545946 : Nat := 118140960795 + 3545946 * 2 ^ 59
def prefixEnd_3545946 : Nat := 4983230072969 + 3 ^ 40 * 3545946 * 2
def baseEnd_3545946 : Nat := 1820774672887888703667497

theorem tailTrace_3545946 : CollatzResearch.WordTrace tailWord_3545946 prefixEnd_3545946 1820774672887888703667497 := by
  unfold tailWord_3545946
  simp only [CollatzResearch.WordTrace]
  refine ⟨32332818902912679051920423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86220850407767144138454461 32332818902912679051920423)
  ·
    refine ⟨48499228354369018577880635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32332818902912679051920423 48499228354369018577880635)
    ·
      refine ⟨72748842531553527866820953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48499228354369018577880635 72748842531553527866820953)
      ·
        refine ⟨54561631898665145900115715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72748842531553527866820953 54561631898665145900115715)
        ·
          refine ⟨81842447847997718850173573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54561631898665145900115715 81842447847997718850173573)
          ·
            refine ⟨15345458971499572284407545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81842447847997718850173573 15345458971499572284407545)
            ·
              refine ⟨11509094228624679213305659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15345458971499572284407545 11509094228624679213305659)
              ·
                refine ⟨17263641342937018819958489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11509094228624679213305659 17263641342937018819958489)
                ·
                  refine ⟨12947731007202764114968867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17263641342937018819958489 12947731007202764114968867)
                  ·
                    refine ⟨19421596510804146172453301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12947731007202764114968867 19421596510804146172453301)
                    ·
                      refine ⟨1820774672887888703667497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19421596510804146172453301 1820774672887888703667497)
                      ·
                        rfl

theorem cell23_3545946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 2, 1, 5].length) (baseStart_3545946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3545946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3545946 prefixEnd_3545946 := by exact prefixLift 3545946
  have htrace : WordTrace (prefixWord ++ tailWord_3545946) baseStart_3545946 baseEnd_3545946 := by
    simpa [prefixWord, tailWord_3545946, baseEnd_3545946] using wordTrace_append hprefix tailTrace_3545946
  have hstable : (prefixWord ++ tailWord_3545946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545946).length < 2 ^ (prefixWord ++ tailWord_3545946).sum := by decide
  have hdescent : baseEnd_3545946 < baseStart_3545946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545973 : List Nat := [1, 3, 4, 1, 1, 3, 1, 1, 2, 2, 4]
def baseStart_3545973 : Nat := 118140960795 + 3545973 * 2 ^ 59
def prefixEnd_3545973 : Nat := 4983230072969 + 3 ^ 40 * 3545973 * 2
def baseEnd_3545973 : Nat := 1820788536865560098029873

theorem tailTrace_3545973 : CollatzResearch.WordTrace tailWord_3545973 prefixEnd_3545973 1820788536865560098029873 := by
  unfold tailWord_3545973
  simp only [CollatzResearch.WordTrace]
  refine ⟨129332260382552899818914573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86221506921701933212609715 129332260382552899818914573)
  ·
    refine ⟨48499597643457337432092965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129332260382552899818914573 48499597643457337432092965)
    ·
      refine ⟨9093674558148250768517431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48499597643457337432092965 9093674558148250768517431)
      ·
        refine ⟨13640511837222376152776147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9093674558148250768517431 13640511837222376152776147)
        ·
          refine ⟨20460767755833564229164221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13640511837222376152776147 20460767755833564229164221)
          ·
            refine ⟨7672787908437586585936583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20460767755833564229164221 7672787908437586585936583)
            ·
              refine ⟨11509181862656379878904875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7672787908437586585936583 11509181862656379878904875)
              ·
                refine ⟨17263772793984569818357313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11509181862656379878904875 17263772793984569818357313)
                ·
                  refine ⟨12947829595488427363767985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17263772793984569818357313 12947829595488427363767985)
                  ·
                    refine ⟨9710872196616320522825989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12947829595488427363767985 9710872196616320522825989)
                    ·
                      refine ⟨1820788536865560098029873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9710872196616320522825989 1820788536865560098029873)
                      ·
                        rfl

theorem cell23_3545973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_3545973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3545973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3545973 prefixEnd_3545973 := by exact prefixLift 3545973
  have htrace : WordTrace (prefixWord ++ tailWord_3545973) baseStart_3545973 baseEnd_3545973 := by
    simpa [prefixWord, tailWord_3545973, baseEnd_3545973] using wordTrace_append hprefix tailTrace_3545973
  have hstable : (prefixWord ++ tailWord_3545973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545973).length < 2 ^ (prefixWord ++ tailWord_3545973).sum := by decide
  have hdescent : baseEnd_3545973 < baseStart_3545973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546077 : List Nat := [1, 4, 3, 1, 2, 3, 1, 1, 3, 4]
def baseStart_3546077 : Nat := 118140960795 + 3546077 * 2 ^ 59
def prefixEnd_3546077 : Nat := 4983230072969 + 3 ^ 40 * 3546077 * 2
def baseEnd_3546077 : Nat := 606947312951209230376465

theorem tailTrace_3546077 : CollatzResearch.WordTrace tailWord_3546077 prefixEnd_3546077 606947312951209230376465 := by
  unfold tailWord_3546077
  simp only [CollatzResearch.WordTrace]
  refine ⟨129336053574176125580700485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86224035716117417053800323 129336053574176125580700485)
  ·
    refine ⟨24250510045158023546381341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129336053574176125580700485 24250510045158023546381341)
    ·
      refine ⟨9093941266934258829893003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24250510045158023546381341 9093941266934258829893003)
      ·
        refine ⟨13640911900401388244839505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9093941266934258829893003 13640911900401388244839505)
        ·
          refine ⟨10230683925301041183629629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13640911900401388244839505 10230683925301041183629629)
          ·
            refine ⟨3836506471987890443861111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10230683925301041183629629 3836506471987890443861111)
            ·
              refine ⟨5754759707981835665791667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3836506471987890443861111 5754759707981835665791667)
              ·
                refine ⟨8632139561972753498687501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5754759707981835665791667 8632139561972753498687501)
                ·
                  refine ⟨3237052335739782562007813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8632139561972753498687501 3237052335739782562007813)
                  ·
                    refine ⟨606947312951209230376465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3237052335739782562007813 606947312951209230376465)
                    ·
                      rfl

theorem cell23_3546077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_3546077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3546077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3546077 prefixEnd_3546077 := by exact prefixLift 3546077
  have htrace : WordTrace (prefixWord ++ tailWord_3546077) baseStart_3546077 baseEnd_3546077 := by
    simpa [prefixWord, tailWord_3546077, baseEnd_3546077] using wordTrace_append hprefix tailTrace_3546077
  have hstable : (prefixWord ++ tailWord_3546077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546077).length < 2 ^ (prefixWord ++ tailWord_3546077).sum := by decide
  have hdescent : baseEnd_3546077 < baseStart_3546077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546090 : List Nat := [3, 1, 3, 1, 2, 2, 4, 1, 6]
def baseStart_3546090 : Nat := 118140960795 + 3546090 * 2 ^ 59
def prefixEnd_3546090 : Nat := 4983230072969 + 3 ^ 40 * 3546090 * 2
def baseEnd_3546090 : Nat := 202316512678015126696315

theorem tailTrace_3546090 : CollatzResearch.WordTrace tailWord_3546090 prefixEnd_3546090 202316512678015126696315 := by
  unfold tailWord_3546090
  simp only [CollatzResearch.WordTrace]
  refine ⟨32334131930782257200230931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86224351815419352533949149 32334131930782257200230931)
  ·
    refine ⟨48501197896173385800346397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32334131930782257200230931 48501197896173385800346397)
    ·
      refine ⟨18187949211065019675129899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48501197896173385800346397 18187949211065019675129899)
      ·
        refine ⟨27281923816597529512694849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18187949211065019675129899 27281923816597529512694849)
        ·
          refine ⟨20461442862448147134521137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27281923816597529512694849 20461442862448147134521137)
          ·
            refine ⟨15346082146836110350890853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20461442862448147134521137 15346082146836110350890853)
            ·
              refine ⟨2877390402531770690792035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15346082146836110350890853 2877390402531770690792035)
              ·
                refine ⟨4316085603797656036188053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2877390402531770690792035 4316085603797656036188053)
                ·
                  refine ⟨202316512678015126696315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4316085603797656036188053 202316512678015126696315)
                  ·
                    rfl

theorem cell23_3546090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 4, 1, 6].length) (baseStart_3546090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3546090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3546090 prefixEnd_3546090 := by exact prefixLift 3546090
  have htrace : WordTrace (prefixWord ++ tailWord_3546090) baseStart_3546090 baseEnd_3546090 := by
    simpa [prefixWord, tailWord_3546090, baseEnd_3546090] using wordTrace_append hprefix tailTrace_3546090
  have hstable : (prefixWord ++ tailWord_3546090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546090).length < 2 ^ (prefixWord ++ tailWord_3546090).sum := by decide
  have hdescent : baseEnd_3546090 < baseStart_3546090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546117 : List Nat := [1, 3, 1, 1, 2, 3, 2, 5, 1, 1, 3]
def baseStart_3546117 : Nat := 118140960795 + 3546117 * 2 ^ 59
def prefixEnd_3546117 : Nat := 4983230072969 + 3 ^ 40 * 3546117 * 2
def baseEnd_3546117 : Nat := 1820862478079807534629211

theorem tailTrace_3546117 : CollatzResearch.WordTrace tailWord_3546117 prefixEnd_3546117 1820862478079807534629211 := by
  unfold tailWord_3546117
  simp only [CollatzResearch.WordTrace]
  refine ⟨129337512494031212412156605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86225008329354141608104403 129337512494031212412156605)
  ·
    refine ⟨48501567185261704654558727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129337512494031212412156605 48501567185261704654558727)
    ·
      refine ⟨72752350777892556981838091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48501567185261704654558727 72752350777892556981838091)
      ·
        refine ⟨109128526166838835472757137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72752350777892556981838091 109128526166838835472757137)
        ·
          refine ⟨81846394625129126604567853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109128526166838835472757137 81846394625129126604567853)
          ·
            refine ⟨30692397984423422476712945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81846394625129126604567853 30692397984423422476712945)
            ·
              refine ⟨23019298488317566857534709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30692397984423422476712945 23019298488317566857534709)
              ·
                refine ⟨2158059233279771892893879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23019298488317566857534709 2158059233279771892893879)
                ·
                  refine ⟨3237088849919657839340819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2158059233279771892893879 3237088849919657839340819)
                  ·
                    refine ⟨4855633274879486759011229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3237088849919657839340819 4855633274879486759011229)
                    ·
                      refine ⟨1820862478079807534629211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4855633274879486759011229 1820862478079807534629211)
                      ·
                        rfl

theorem cell23_3546117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 5, 1, 1, 3].length) (baseStart_3546117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3546117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3546117 prefixEnd_3546117 := by exact prefixLift 3546117
  have htrace : WordTrace (prefixWord ++ tailWord_3546117) baseStart_3546117 baseEnd_3546117 := by
    simpa [prefixWord, tailWord_3546117, baseEnd_3546117] using wordTrace_append hprefix tailTrace_3546117
  have hstable : (prefixWord ++ tailWord_3546117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546117).length < 2 ^ (prefixWord ++ tailWord_3546117).sum := by decide
  have hdescent : baseEnd_3546117 < baseStart_3546117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546160 : List Nat := [2, 1, 1, 1, 2, 4, 2, 4, 1, 2, 3]
def baseStart_3546160 : Nat := 118140960795 + 3546160 * 2 ^ 59
def prefixEnd_3546160 : Nat := 4983230072969 + 3 ^ 40 * 3546160 * 2
def baseEnd_3546160 : Nat := 1820884557747950866391513

theorem tailTrace_3546160 : CollatzResearch.WordTrace tailWord_3546160 prefixEnd_3546160 1820884557747950866391513 := by
  unfold tailWord_3546160
  simp only [CollatzResearch.WordTrace]
  refine ⟨64669540416437715377985967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86226053888583620503981289 64669540416437715377985967)
  ·
    refine ⟨97004310624656573066978951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64669540416437715377985967 97004310624656573066978951)
    ·
      refine ⟨145506465936984859600468427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97004310624656573066978951 145506465936984859600468427)
      ·
        refine ⟨218259698905477289400702641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145506465936984859600468427 218259698905477289400702641)
        ·
          refine ⟨163694774179107967050526981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218259698905477289400702641 163694774179107967050526981)
          ·
            refine ⟨30692770158582743821973809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 163694774179107967050526981 30692770158582743821973809)
            ·
              refine ⟨23019577618937057866480357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30692770158582743821973809 23019577618937057866480357)
              ·
                refine ⟨4316170803550698349965067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23019577618937057866480357 4316170803550698349965067)
                ·
                  refine ⟨6474256205326047524947601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4316170803550698349965067 6474256205326047524947601)
                  ·
                    refine ⟨4855692153994535643710701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6474256205326047524947601 4855692153994535643710701)
                    ·
                      refine ⟨1820884557747950866391513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4855692153994535643710701 1820884557747950866391513)
                      ·
                        rfl

theorem cell23_3546160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 4, 1, 2, 3].length) (baseStart_3546160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3546160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3546160 prefixEnd_3546160 := by exact prefixLift 3546160
  have htrace : WordTrace (prefixWord ++ tailWord_3546160) baseStart_3546160 baseEnd_3546160 := by
    simpa [prefixWord, tailWord_3546160, baseEnd_3546160] using wordTrace_append hprefix tailTrace_3546160
  have hstable : (prefixWord ++ tailWord_3546160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546160).length < 2 ^ (prefixWord ++ tailWord_3546160).sum := by decide
  have hdescent : baseEnd_3546160 < baseStart_3546160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546174 : List Nat := [4, 2, 1, 3, 1, 1, 4, 1, 1, 1, 4]
def baseStart_3546174 : Nat := 118140960795 + 3546174 * 2 ^ 59
def prefixEnd_3546174 : Nat := 4983230072969 + 3 ^ 40 * 3546174 * 2
def baseEnd_3546174 : Nat := 1820891746477113811616449

theorem tailTrace_3546174 : CollatzResearch.WordTrace tailWord_3546174 prefixEnd_3546174 1820891746477113811616449 := by
  unfold tailWord_3546174
  simp only [CollatzResearch.WordTrace]
  refine ⟨16167448931853088893372697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86226394303216474097987717 16167448931853088893372697)
  ·
    refine ⟨12125586698889816670029523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16167448931853088893372697 12125586698889816670029523)
    ·
      refine ⟨18188380048334725005044285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12125586698889816670029523 18188380048334725005044285)
      ·
        refine ⟨6820642518125521876891607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18188380048334725005044285 6820642518125521876891607)
        ·
          refine ⟨10230963777188282815337411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6820642518125521876891607 10230963777188282815337411)
          ·
            refine ⟨15346445665782424223006117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10230963777188282815337411 15346445665782424223006117)
            ·
              refine ⟨2877458562334204541813647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15346445665782424223006117 2877458562334204541813647)
              ·
                refine ⟨4316187843501306812720471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2877458562334204541813647 4316187843501306812720471)
                ·
                  refine ⟨6474281765251960219080707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4316187843501306812720471 6474281765251960219080707)
                  ·
                    refine ⟨9711422647877940328621061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6474281765251960219080707 9711422647877940328621061)
                    ·
                      refine ⟨1820891746477113811616449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9711422647877940328621061 1820891746477113811616449)
                      ·
                        rfl

theorem cell23_3546174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_3546174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3546174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3546174 prefixEnd_3546174 := by exact prefixLift 3546174
  have htrace : WordTrace (prefixWord ++ tailWord_3546174) baseStart_3546174 baseEnd_3546174 := by
    simpa [prefixWord, tailWord_3546174, baseEnd_3546174] using wordTrace_append hprefix tailTrace_3546174
  have hstable : (prefixWord ++ tailWord_3546174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546174).length < 2 ^ (prefixWord ++ tailWord_3546174).sum := by decide
  have hdescent : baseEnd_3546174 < baseStart_3546174 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546217 : List Nat := [1, 2, 1, 1, 1, 6, 1, 4, 1, 3, 2]
def baseStart_3546217 : Nat := 118140960795 + 3546217 * 2 ^ 59
def prefixEnd_3546217 : Nat := 4983230072969 + 3 ^ 40 * 3546217 * 2
def baseEnd_3546217 : Nat := 1820913826145257143378751

theorem tailTrace_3546217 : CollatzResearch.WordTrace tailWord_3546217 prefixEnd_3546217 1820913826145257143378751 := by
  unfold tailWord_3546217
  simp only [CollatzResearch.WordTrace]
  refine ⟨129341159793668929490796905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86227439862445952993864603 129341159793668929490796905)
  ·
    refine ⟨97005869845251697118097679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129341159793668929490796905 97005869845251697118097679)
    ·
      refine ⟨145508804767877545677146519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97005869845251697118097679 145508804767877545677146519)
      ·
        refine ⟨218263207151816318515719779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145508804767877545677146519 218263207151816318515719779)
        ·
          refine ⟨327394810727724477773579669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218263207151816318515719779 327394810727724477773579669)
          ·
            refine ⟨15346631752862084895636547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 327394810727724477773579669 15346631752862084895636547)
            ·
              refine ⟨23019947629293127343454821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15346631752862084895636547 23019947629293127343454821)
              ·
                refine ⟨4316240180492461376897779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23019947629293127343454821 4316240180492461376897779)
                ·
                  refine ⟨6474360270738692065346669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4316240180492461376897779 6474360270738692065346669)
                  ·
                    refine ⟨2427885101527009524505001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6474360270738692065346669 2427885101527009524505001)
                    ·
                      refine ⟨1820913826145257143378751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2427885101527009524505001 1820913826145257143378751)
                      ·
                        rfl

theorem cell23_3546217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 4, 1, 3, 2].length) (baseStart_3546217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3546217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3546217 prefixEnd_3546217 := by exact prefixLift 3546217
  have htrace : WordTrace (prefixWord ++ tailWord_3546217) baseStart_3546217 baseEnd_3546217 := by
    simpa [prefixWord, tailWord_3546217, baseEnd_3546217] using wordTrace_append hprefix tailTrace_3546217
  have hstable : (prefixWord ++ tailWord_3546217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546217).length < 2 ^ (prefixWord ++ tailWord_3546217).sum := by decide
  have hdescent : baseEnd_3546217 < baseStart_3546217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546250 : List Nat := [3, 1, 2, 3, 1, 1, 2, 1, 2, 4, 3]
def baseStart_3546250 : Nat := 118140960795 + 3546250 * 2 ^ 59
def prefixEnd_3546250 : Nat := 4983230072969 + 3 ^ 40 * 3546250 * 2
def baseEnd_3546250 : Nat := 1820930771006855514266099

theorem tailTrace_3546250 : CollatzResearch.WordTrace tailWord_3546250 prefixEnd_3546250 1820930771006855514266099 := by
  unfold tailWord_3546250
  simp only [CollatzResearch.WordTrace]
  refine ⟨32335590850637344031687051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86228242268366250751165469 32335590850637344031687051)
  ·
    refine ⟨48503386275956016047530577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32335590850637344031687051 48503386275956016047530577)
    ·
      refine ⟨36377539706967012035647933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48503386275956016047530577 36377539706967012035647933)
      ·
        refine ⟨13641577390112629513367975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36377539706967012035647933 13641577390112629513367975)
        ·
          refine ⟨20462366085168944270051963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13641577390112629513367975 20462366085168944270051963)
          ·
            refine ⟨30693549127753416405077945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20462366085168944270051963 30693549127753416405077945)
            ·
              refine ⟨23020161845815062303808459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30693549127753416405077945 23020161845815062303808459)
              ·
                refine ⟨34530242768722593455712689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23020161845815062303808459 34530242768722593455712689)
                ·
                  refine ⟨25897682076541945091784517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34530242768722593455712689 25897682076541945091784517)
                  ·
                    refine ⟨4855815389351614704709597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25897682076541945091784517 4855815389351614704709597)
                    ·
                      refine ⟨1820930771006855514266099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4855815389351614704709597 1820930771006855514266099)
                      ·
                        rfl

theorem cell23_3546250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_3546250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3546250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3546250 prefixEnd_3546250 := by exact prefixLift 3546250
  have htrace : WordTrace (prefixWord ++ tailWord_3546250) baseStart_3546250 baseEnd_3546250 := by
    simpa [prefixWord, tailWord_3546250, baseEnd_3546250] using wordTrace_append hprefix tailTrace_3546250
  have hstable : (prefixWord ++ tailWord_3546250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546250).length < 2 ^ (prefixWord ++ tailWord_3546250).sum := by decide
  have hdescent : baseEnd_3546250 < baseStart_3546250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546323 : List Nat := [1, 1, 1, 2, 1, 1, 1, 4, 1, 5, 5]
def baseStart_3546323 : Nat := 118140960795 + 3546323 * 2 ^ 59
def prefixEnd_3546323 : Nat := 4983230072969 + 3 ^ 40 * 3546323 * 2
def baseEnd_3546323 : Nat := 1820968255094633728653263

theorem tailTrace_3546323 : CollatzResearch.WordTrace tailWord_3546323 prefixEnd_3546323 1820968255094633728653263 := by
  unfold tailWord_3546323
  simp only [CollatzResearch.WordTrace]
  refine ⟨129345025931284909594155623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86230017287523273062770415 129345025931284909594155623)
  ·
    refine ⟨194017538896927364391233435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129345025931284909594155623 194017538896927364391233435)
    ·
      refine ⟨291026308345391046586850153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194017538896927364391233435 291026308345391046586850153)
      ·
        refine ⟨218269731259043284940137615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291026308345391046586850153 218269731259043284940137615)
        ·
          refine ⟨327404596888564927410206423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218269731259043284940137615 327404596888564927410206423)
          ·
            refine ⟨491106895332847391115309635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327404596888564927410206423 491106895332847391115309635)
            ·
              refine ⟨736660342999271086672964453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 491106895332847391115309635 736660342999271086672964453)
              ·
                refine ⟨138123814312363328751180835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 736660342999271086672964453 138123814312363328751180835)
                ·
                  refine ⟨207185721468544993126771253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138123814312363328751180835 207185721468544993126771253)
                  ·
                    refine ⟨19423661387676093105634805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 207185721468544993126771253 19423661387676093105634805)
                    ·
                      refine ⟨1820968255094633728653263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19423661387676093105634805 1820968255094633728653263)
                      ·
                        rfl

theorem cell23_3546323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 5, 5].length) (baseStart_3546323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3546323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3546323 prefixEnd_3546323 := by exact prefixLift 3546323
  have htrace : WordTrace (prefixWord ++ tailWord_3546323) baseStart_3546323 baseEnd_3546323 := by
    simpa [prefixWord, tailWord_3546323, baseEnd_3546323] using wordTrace_append hprefix tailTrace_3546323
  have hstable : (prefixWord ++ tailWord_3546323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546323).length < 2 ^ (prefixWord ++ tailWord_3546323).sum := by decide
  have hdescent : baseEnd_3546323 < baseStart_3546323 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546337 : List Nat := [1, 2, 3, 1, 3, 2, 3, 1, 2, 1, 4]
def baseStart_3546337 : Nat := 118140960795 + 3546337 * 2 ^ 59
def prefixEnd_3546337 : Nat := 4983230072969 + 3 ^ 40 * 3546337 * 2
def baseEnd_3546337 : Nat := 1820975443823796673878199

theorem tailTrace_3546337 : CollatzResearch.WordTrace tailWord_3546337 prefixEnd_3546337 1820975443823796673878199 := by
  unfold tailWord_3546337
  simp only [CollatzResearch.WordTrace]
  refine ⟨129345536553234189985165265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86230357702156126656776843 129345536553234189985165265)
  ·
    refine ⟨97009152414925642488873949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129345536553234189985165265 97009152414925642488873949)
    ·
      refine ⟨36378432155597115933327731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97009152414925642488873949 36378432155597115933327731)
      ·
        refine ⟨54567648233395673899991597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36378432155597115933327731 54567648233395673899991597)
        ·
          refine ⟨20462868087523377712496849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54567648233395673899991597 20462868087523377712496849)
          ·
            refine ⟨15347151065642533284372637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20462868087523377712496849 15347151065642533284372637)
            ·
              refine ⟨5755181649615949981639739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15347151065642533284372637 5755181649615949981639739)
              ·
                refine ⟨8632772474423924972459609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5755181649615949981639739 8632772474423924972459609)
                ·
                  refine ⟨6474579355817943729344707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8632772474423924972459609 6474579355817943729344707)
                  ·
                    refine ⟨9711869033726915594017061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6474579355817943729344707 9711869033726915594017061)
                    ·
                      refine ⟨1820975443823796673878199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9711869033726915594017061 1820975443823796673878199)
                      ·
                        rfl

theorem cell23_3546337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 1, 2, 1, 4].length) (baseStart_3546337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3546337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3546337 prefixEnd_3546337 := by exact prefixLift 3546337
  have htrace : WordTrace (prefixWord ++ tailWord_3546337) baseStart_3546337 baseEnd_3546337 := by
    simpa [prefixWord, tailWord_3546337, baseEnd_3546337] using wordTrace_append hprefix tailTrace_3546337
  have hstable : (prefixWord ++ tailWord_3546337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546337).length < 2 ^ (prefixWord ++ tailWord_3546337).sum := by decide
  have hdescent : baseEnd_3546337 < baseStart_3546337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546350 : List Nat := [4, 1, 2, 1, 1, 1, 3, 1, 2, 1, 6]
def baseStart_3546350 : Nat := 118140960795 + 3546350 * 2 ^ 59
def prefixEnd_3546350 : Nat := 4983230072969 + 3 ^ 40 * 3546350 * 2
def baseEnd_3546350 : Nat := 1820982119072305123015639

theorem tailTrace_3546350 : CollatzResearch.WordTrace tailWord_3546350 prefixEnd_3546350 1820982119072305123015639 := by
  unfold tailWord_3546350
  simp only [CollatzResearch.WordTrace]
  refine ⟨16168251337773386650673563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86230673801458062136925669 16168251337773386650673563)
  ·
    refine ⟨24252377006660079976010345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16168251337773386650673563 24252377006660079976010345)
    ·
      refine ⟨18189282754995059982007759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24252377006660079976010345 18189282754995059982007759)
      ·
        refine ⟨27283924132492589973011639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18189282754995059982007759 27283924132492589973011639)
        ·
          refine ⟨40925886198738884959517459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27283924132492589973011639 40925886198738884959517459)
          ·
            refine ⟨61388829298108327439276189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40925886198738884959517459 61388829298108327439276189)
            ·
              refine ⟨23020810986790622789728571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61388829298108327439276189 23020810986790622789728571)
              ·
                refine ⟨34531216480185934184592857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23020810986790622789728571 34531216480185934184592857)
                ·
                  refine ⟨25898412360139450638444643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34531216480185934184592857 25898412360139450638444643)
                  ·
                    refine ⟨38847618540209175957666965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25898412360139450638444643 38847618540209175957666965)
                    ·
                      refine ⟨1820982119072305123015639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38847618540209175957666965 1820982119072305123015639)
                      ·
                        rfl

theorem cell23_3546350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_3546350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3546350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3546350 prefixEnd_3546350 := by exact prefixLift 3546350
  have htrace : WordTrace (prefixWord ++ tailWord_3546350) baseStart_3546350 baseEnd_3546350 := by
    simpa [prefixWord, tailWord_3546350, baseEnd_3546350] using wordTrace_append hprefix tailTrace_3546350
  have hstable : (prefixWord ++ tailWord_3546350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546350).length < 2 ^ (prefixWord ++ tailWord_3546350).sum := by decide
  have hdescent : baseEnd_3546350 < baseStart_3546350 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546364 : List Nat := [2, 2, 2, 1, 5, 1, 2, 1, 3, 4]
def baseStart_3546364 : Nat := 118140960795 + 3546364 * 2 ^ 59
def prefixEnd_3546364 : Nat := 4983230072969 + 3 ^ 40 * 3546364 * 2
def baseEnd_3546364 : Nat := 606996435933822689413525

theorem tailTrace_3546364 : CollatzResearch.WordTrace tailWord_3546364 prefixEnd_3546364 606996435933822689413525 := by
  unfold tailWord_3546364
  simp only [CollatzResearch.WordTrace]
  refine ⟨64673260662068186798199073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86231014216090915730932097 64673260662068186798199073)
  ·
    refine ⟨48504945496551140098649305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64673260662068186798199073 48504945496551140098649305)
    ·
      refine ⟨36378709122413355073986979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48504945496551140098649305 36378709122413355073986979)
      ·
        refine ⟨54568063683620032610980469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36378709122413355073986979 54568063683620032610980469)
        ·
          refine ⟨5115755970339378057279419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54568063683620032610980469 5115755970339378057279419)
          ·
            refine ⟨7673633955509067085919129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5115755970339378057279419 7673633955509067085919129)
            ·
              refine ⟨5755225466631800314439347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7673633955509067085919129 5755225466631800314439347)
              ·
                refine ⟨8632838199947700471659021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5755225466631800314439347 8632838199947700471659021)
                ·
                  refine ⟨3237314324980387676872133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8632838199947700471659021 3237314324980387676872133)
                  ·
                    refine ⟨606996435933822689413525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3237314324980387676872133 606996435933822689413525)
                    ·
                      rfl

theorem cell23_3546364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 1, 3, 4].length) (baseStart_3546364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3546364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3546364 prefixEnd_3546364 := by exact prefixLift 3546364
  have htrace : WordTrace (prefixWord ++ tailWord_3546364) baseStart_3546364 baseEnd_3546364 := by
    simpa [prefixWord, tailWord_3546364, baseEnd_3546364] using wordTrace_append hprefix tailTrace_3546364
  have hstable : (prefixWord ++ tailWord_3546364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546364).length < 2 ^ (prefixWord ++ tailWord_3546364).sum := by decide
  have hdescent : baseEnd_3546364 < baseStart_3546364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546377 : List Nat := [1, 2, 1, 1, 3, 3, 5, 1, 6]
def baseStart_3546377 : Nat := 118140960795 + 3546377 * 2 ^ 59
def prefixEnd_3546377 : Nat := 4983230072969 + 3 ^ 40 * 3546377 * 2
def baseEnd_3546377 : Nat := 202332887005552946375335

theorem tailTrace_3546377 : CollatzResearch.WordTrace tailWord_3546377 prefixEnd_3546377 202332887005552946375335 := by
  unfold tailWord_3546377
  simp only [CollatzResearch.WordTrace]
  refine ⟨129346995473089276816621385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86231330315392851211080923 129346995473089276816621385)
  ·
    refine ⟨97010246604816957612466039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129346995473089276816621385 97010246604816957612466039)
    ·
      refine ⟨145515369907225436418699059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97010246604816957612466039 145515369907225436418699059)
      ·
        refine ⟨218273054860838154628048589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145515369907225436418699059 218273054860838154628048589)
        ·
          refine ⟨81852395572814307985518221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218273054860838154628048589 81852395572814307985518221)
          ·
            refine ⟨30694648339805365494569333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81852395572814307985518221 30694648339805365494569333)
            ·
              refine ⟨2877623281856753015115875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30694648339805365494569333 2877623281856753015115875)
              ·
                refine ⟨4316434922785129522673813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2877623281856753015115875 4316434922785129522673813)
                ·
                  refine ⟨202332887005552946375335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4316434922785129522673813 202332887005552946375335)
                  ·
                    rfl

theorem cell23_3546377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 5, 1, 6].length) (baseStart_3546377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3546377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3546377 prefixEnd_3546377 := by exact prefixLift 3546377
  have htrace : WordTrace (prefixWord ++ tailWord_3546377) baseStart_3546377 baseEnd_3546377 := by
    simpa [prefixWord, tailWord_3546377, baseEnd_3546377] using wordTrace_append hprefix tailTrace_3546377
  have hstable : (prefixWord ++ tailWord_3546377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546377).length < 2 ^ (prefixWord ++ tailWord_3546377).sum := by decide
  have hdescent : baseEnd_3546377 < baseStart_3546377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546421 : List Nat := [1, 3, 3, 1, 2, 4, 1, 1, 3, 1, 3]
def baseStart_3546421 : Nat := 118140960795 + 3546421 * 2 ^ 59
def prefixEnd_3546421 : Nat := 4983230072969 + 3 ^ 40 * 3546421 * 2
def baseEnd_3546421 : Nat := 1821018576198774345227813

theorem tailTrace_3546421 : CollatzResearch.WordTrace tailWord_3546421 prefixEnd_3546421 1821018576198774345227813 := by
  unfold tailWord_3546421
  simp only [CollatzResearch.WordTrace]
  refine ⟨129348600284929872331223117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86232400189953248220815411 129348600284929872331223117)
  ·
    refine ⟨48505725106848702124208669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129348600284929872331223117 48505725106848702124208669)
    ·
      refine ⟨18189646915068263296578251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48505725106848702124208669 18189646915068263296578251)
      ·
        refine ⟨27284470372602394944867377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18189646915068263296578251 27284470372602394944867377)
        ·
          refine ⟨20463352779451796208650533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27284470372602394944867377 20463352779451796208650533)
          ·
            refine ⟨3836878646147211789121975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20463352779451796208650533 3836878646147211789121975)
            ·
              refine ⟨5755317969220817683682963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3836878646147211789121975 5755317969220817683682963)
              ·
                refine ⟨8632976953831226525524445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5755317969220817683682963 8632976953831226525524445)
                ·
                  refine ⟨3237366357686709947071667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8632976953831226525524445 3237366357686709947071667)
                  ·
                    refine ⟨4856049536530064920607501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3237366357686709947071667 4856049536530064920607501)
                    ·
                      refine ⟨1821018576198774345227813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4856049536530064920607501 1821018576198774345227813)
                      ·
                        rfl

theorem cell23_3546421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 1, 3, 1, 3].length) (baseStart_3546421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3546421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3546421 prefixEnd_3546421 := by exact prefixLift 3546421
  have htrace : WordTrace (prefixWord ++ tailWord_3546421) baseStart_3546421 baseEnd_3546421 := by
    simpa [prefixWord, tailWord_3546421, baseEnd_3546421] using wordTrace_append hprefix tailTrace_3546421
  have hstable : (prefixWord ++ tailWord_3546421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546421).length < 2 ^ (prefixWord ++ tailWord_3546421).sum := by decide
  have hdescent : baseEnd_3546421 < baseStart_3546421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546444 : List Nat := [2, 2, 1, 3, 2, 2, 3, 2, 1, 1, 4]
def baseStart_3546444 : Nat := 118140960795 + 3546444 * 2 ^ 59
def prefixEnd_3546444 : Nat := 4983230072969 + 3 ^ 40 * 3546444 * 2
def baseEnd_3546444 : Nat := 1821030386253827755240207

theorem tailTrace_3546444 : CollatzResearch.WordTrace tailWord_3546444 prefixEnd_3546444 1821030386253827755240207 := by
  unfold tailWord_3546444
  simp only [CollatzResearch.WordTrace]
  refine ⟨64674719581923273629655193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86232959442564364839540257 64674719581923273629655193)
  ·
    refine ⟨48506039686442455222241395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64674719581923273629655193 48506039686442455222241395)
    ·
      refine ⟨72759059529663682833362093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48506039686442455222241395 72759059529663682833362093)
      ·
        refine ⟨27284647323623881062510785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72759059529663682833362093 27284647323623881062510785)
        ·
          refine ⟨20463485492717910796883089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27284647323623881062510785 20463485492717910796883089)
          ·
            refine ⟨15347614119538433097662317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20463485492717910796883089 15347614119538433097662317)
            ·
              refine ⟨5755355294826912411623369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15347614119538433097662317 5755355294826912411623369)
              ·
                refine ⟨4316516471120184308717527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5755355294826912411623369 4316516471120184308717527)
                ·
                  refine ⟨6474774706680276463076291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4316516471120184308717527 6474774706680276463076291)
                  ·
                    refine ⟨9712162060020414694614437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6474774706680276463076291 9712162060020414694614437)
                    ·
                      refine ⟨1821030386253827755240207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9712162060020414694614437 1821030386253827755240207)
                      ·
                        rfl

theorem cell23_3546444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 2, 1, 1, 4].length) (baseStart_3546444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3546444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3546444 prefixEnd_3546444 := by exact prefixLift 3546444
  have htrace : WordTrace (prefixWord ++ tailWord_3546444) baseStart_3546444 baseEnd_3546444 := by
    simpa [prefixWord, tailWord_3546444, baseEnd_3546444] using wordTrace_append hprefix tailTrace_3546444
  have hstable : (prefixWord ++ tailWord_3546444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546444).length < 2 ^ (prefixWord ++ tailWord_3546444).sum := by decide
  have hdescent : baseEnd_3546444 < baseStart_3546444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546464 : List Nat := [2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 5]
def baseStart_3546464 : Nat := 118140960795 + 3546464 * 2 ^ 59
def prefixEnd_3546464 : Nat := 4983230072969 + 3 ^ 40 * 3546464 * 2
def baseEnd_3546464 : Nat := 1821040655866917676990115

theorem tailTrace_3546464 : CollatzResearch.WordTrace tailWord_3546464 prefixEnd_3546464 1821040655866917676990115 := by
  unfold tailWord_3546464
  simp only [CollatzResearch.WordTrace]
  refine ⟨64675084311887045337519223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86233445749182727116692297 64675084311887045337519223)
  ·
    refine ⟨97012626467830568006278835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64675084311887045337519223 97012626467830568006278835)
    ·
      refine ⟨145518939701745852009418253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97012626467830568006278835 145518939701745852009418253)
      ·
        refine ⟨54569602388154694503531845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145518939701745852009418253 54569602388154694503531845)
        ·
          refine ⟨10231800447779005219412221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54569602388154694503531845 10231800447779005219412221)
          ·
            refine ⟨3836925167917126957279583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10231800447779005219412221 3836925167917126957279583)
            ·
              refine ⟨5755387751875690435919375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3836925167917126957279583 5755387751875690435919375)
              ·
                refine ⟨8633081627813535653879063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5755387751875690435919375 8633081627813535653879063)
                ·
                  refine ⟨12949622441720303480818595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8633081627813535653879063 12949622441720303480818595)
                  ·
                    refine ⟨19424433662580455221227893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12949622441720303480818595 19424433662580455221227893)
                    ·
                      refine ⟨1821040655866917676990115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19424433662580455221227893 1821040655866917676990115)
                      ·
                        rfl

theorem cell23_3546464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 5].length) (baseStart_3546464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3546464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3546464 prefixEnd_3546464 := by exact prefixLift 3546464
  have htrace : WordTrace (prefixWord ++ tailWord_3546464) baseStart_3546464 baseEnd_3546464 := by
    simpa [prefixWord, tailWord_3546464, baseEnd_3546464] using wordTrace_append hprefix tailTrace_3546464
  have hstable : (prefixWord ++ tailWord_3546464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546464).length < 2 ^ (prefixWord ++ tailWord_3546464).sum := by decide
  have hdescent : baseEnd_3546464 < baseStart_3546464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546471 : List Nat := [1, 1, 5, 1, 4, 1, 2, 2, 2, 4]
def baseStart_3546471 : Nat := 118140960795 + 3546471 * 2 ^ 59
def prefixEnd_3546471 : Nat := 4983230072969 + 3 ^ 40 * 3546471 * 2
def baseEnd_3546471 : Nat := 607014750077166383200861

theorem tailTrace_3546471 : CollatzResearch.WordTrace tailWord_3546471 prefixEnd_3546471 607014750077166383200861 := by
  unfold tailWord_3546471
  simp only [CollatzResearch.WordTrace]
  refine ⟨129350423934748730870543267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86233615956499153913695511 129350423934748730870543267)
  ·
    refine ⟨194025635902123096305814901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129350423934748730870543267 194025635902123096305814901)
    ·
      refine ⟨18189903365824040278670147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 194025635902123096305814901 18189903365824040278670147)
      ·
        refine ⟨27284855048736060418005221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18189903365824040278670147 27284855048736060418005221)
        ·
          refine ⟨5115910321638011328375979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27284855048736060418005221 5115910321638011328375979)
          ·
            refine ⟨7673865482457016992563969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5115910321638011328375979 7673865482457016992563969)
            ·
              refine ⟨5755399111842762744422977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7673865482457016992563969 5755399111842762744422977)
              ·
                refine ⟨4316549333882072058317233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5755399111842762744422977 4316549333882072058317233)
                ·
                  refine ⟨3237412000411554043737925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4316549333882072058317233 3237412000411554043737925)
                  ·
                    refine ⟨607014750077166383200861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3237412000411554043737925 607014750077166383200861)
                    ·
                      rfl

theorem cell23_3546471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 2, 2, 4].length) (baseStart_3546471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3546471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3546471 prefixEnd_3546471 := by exact prefixLift 3546471
  have htrace : WordTrace (prefixWord ++ tailWord_3546471) baseStart_3546471 baseEnd_3546471 := by
    simpa [prefixWord, tailWord_3546471, baseEnd_3546471] using wordTrace_append hprefix tailTrace_3546471
  have hstable : (prefixWord ++ tailWord_3546471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546471).length < 2 ^ (prefixWord ++ tailWord_3546471).sum := by decide
  have hdescent : baseEnd_3546471 < baseStart_3546471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546472 : List Nat := [2, 1, 4, 2, 4, 1, 2, 2, 1, 1, 3]
def baseStart_3546472 : Nat := 118140960795 + 3546472 * 2 ^ 59
def prefixEnd_3546472 : Nat := 4983230072969 + 3 ^ 40 * 3546472 * 2
def baseEnd_3546472 : Nat := 1821044763712153645690079

theorem tailTrace_3546472 : CollatzResearch.WordTrace tailWord_3546472 prefixEnd_3546472 1821044763712153645690079 := by
  unfold tailWord_3546472
  simp only [CollatzResearch.WordTrace]
  refine ⟨64675230203872554020664835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86233640271830072027553113 64675230203872554020664835)
  ·
    refine ⟨97012845305808831030997253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64675230203872554020664835 97012845305808831030997253)
    ·
      refine ⟨18189908494839155818311985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97012845305808831030997253 18189908494839155818311985)
      ·
        refine ⟨13642431371129366863733989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18189908494839155818311985 13642431371129366863733989)
        ·
          refine ⟨2557955882086756286950123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13642431371129366863733989 2557955882086756286950123)
          ·
            refine ⟨3836933823130134430425185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2557955882086756286950123 3836933823130134430425185)
            ·
              refine ⟨2877700367347600822818889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3836933823130134430425185 2877700367347600822818889)
              ·
                refine ⟨2158275275510700617114167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2877700367347600822818889 2158275275510700617114167)
                ·
                  refine ⟨3237412913266050925671251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2158275275510700617114167 3237412913266050925671251)
                  ·
                    refine ⟨4856119369899076388506877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3237412913266050925671251 4856119369899076388506877)
                    ·
                      refine ⟨1821044763712153645690079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4856119369899076388506877 1821044763712153645690079)
                      ·
                        rfl

theorem cell23_3546472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 2, 2, 1, 1, 3].length) (baseStart_3546472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3546472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3546472 prefixEnd_3546472 := by exact prefixLift 3546472
  have htrace : WordTrace (prefixWord ++ tailWord_3546472) baseStart_3546472 baseEnd_3546472 := by
    simpa [prefixWord, tailWord_3546472, baseEnd_3546472] using wordTrace_append hprefix tailTrace_3546472
  have hstable : (prefixWord ++ tailWord_3546472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546472).length < 2 ^ (prefixWord ++ tailWord_3546472).sum := by decide
  have hdescent : baseEnd_3546472 < baseStart_3546472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546480 : List Nat := [2, 1, 1, 1, 4, 2, 1, 1, 1, 9]
def baseStart_3546480 : Nat := 118140960795 + 3546480 * 2 ^ 59
def prefixEnd_3546480 : Nat := 4983230072969 + 3 ^ 40 * 3546480 * 2
def baseEnd_3546480 : Nat := 607016290519129871463347

theorem tailTrace_3546480 : CollatzResearch.WordTrace tailWord_3546480 prefixEnd_3546480 607016290519129871463347 := by
  unfold tailWord_3546480
  simp only [CollatzResearch.WordTrace]
  refine ⟨64675376095858062703810447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86233834794477416938413929 64675376095858062703810447)
  ·
    refine ⟨97013064143787094055715671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64675376095858062703810447 97013064143787094055715671)
    ·
      refine ⟨145519596215680641083573507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97013064143787094055715671 145519596215680641083573507)
      ·
        refine ⟨218279394323520961625360261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145519596215680641083573507 218279394323520961625360261)
        ·
          refine ⟨40927386435660180304755049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 218279394323520961625360261 40927386435660180304755049)
          ·
            refine ⟨30695539826745135228566287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40927386435660180304755049 30695539826745135228566287)
            ·
              refine ⟨46043309740117702842849431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30695539826745135228566287 46043309740117702842849431)
              ·
                refine ⟨69064964610176554264274147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46043309740117702842849431 69064964610176554264274147)
                ·
                  refine ⟨103597446915264831396411221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69064964610176554264274147 103597446915264831396411221)
                  ·
                    refine ⟨607016290519129871463347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 103597446915264831396411221 607016290519129871463347)
                    ·
                      rfl

theorem cell23_3546480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 1, 9].length) (baseStart_3546480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3546480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3546480 prefixEnd_3546480 := by exact prefixLift 3546480
  have htrace : WordTrace (prefixWord ++ tailWord_3546480) baseStart_3546480 baseEnd_3546480 := by
    simpa [prefixWord, tailWord_3546480, baseEnd_3546480] using wordTrace_append hprefix tailTrace_3546480
  have hstable : (prefixWord ++ tailWord_3546480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546480).length < 2 ^ (prefixWord ++ tailWord_3546480).sum := by decide
  have hdescent : baseEnd_3546480 < baseStart_3546480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
